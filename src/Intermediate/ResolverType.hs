{-
 Copyright (C) 2012 Jimmy Liang, Kacper Bak <http://gsd.uwaterloo.ca>

 Permission is hereby granted, free of charge, to any person obtaining a copy of
 this software and associated documentation files (the "Software"), to deal in
 the Software without restriction, including without limitation the rights to
 use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 of the Software, and to permit persons to whom the Software is furnished to do
 so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.
-}
module Intermediate.ResolverType (resolveTModule) where

import Control.Monad.State
import Data.Function
import Data.Maybe
import Data.Map hiding (map, lookup)
import qualified Data.Map as Map
import Debug.Trace
import List (find)

import Common
import Intermediate.Intclafer

-- Internal structure for type checking.
-- A tuple for storing the symbol table, a clafer's uid, its type, and its parent uid.
-- Every clafer has a parent except the root.
data TCEnv = TCEnv {
    tcTable :: SymbolTable,
    tcThis :: String,
    tcType :: IType,
    tcParent :: Maybe String,
    tcReferenceTable :: Map String Bool -- Maps the Clafer uid to whether it is a reference or not.
} deriving Show

-- Internal structure for building the symbol table.
data STEnv = STEnv {
    stClafers :: [IClafer],
    -- The uid of the parent. Every clafer has a parent except the root.
    stParent :: Maybe String
} deriving Show

-- The symbol table maps a clafer's uid to its type and parent's uid.
-- Every clafer has a parent except the root.
type SymbolTable = Map String (IType, Maybe String)
type TypedIExp = (IExp, IType)



-- Get the TCEnv of the parent
parentTCEnv :: TCEnv -> TCEnv
parentTCEnv t@(TCEnv table this itype (Just parent) _) = uidTCEnv t parent
parentTCEnv (TCEnv table this itype Nothing _)         = error "Root does not have a parent"
    
-- Get the TCEnv of the clafer matching the uid
uidTCEnv :: TCEnv -> String -> TCEnv
uidTCEnv (TCEnv table _ _ _ referenceTable) uid =
    case Map.lookup uid table of
    Just (newType, newParent) -> TCEnv table uid newType newParent referenceTable
    Nothing -> error $ "Unknown uid " ++ uid
    
    
identTCEnv :: TCEnv -> String -> TCEnv
identTCEnv env "this"   = env
identTCEnv env "parent" = parentTCEnv env
identTCEnv env "ref"    = env
identTCEnv env uid      = uidTCEnv env uid


-- The only exported function. Type checks and resolves the types.
-- Done in 2 steps
--   1. Traverse every clafer and build a symbol table
--   2. Traverse every constraint and resolve the types and type check
resolveTModule :: (IModule, GEnv) -> IModule
resolveTModule (imodule, genv) =
    imodule {mDecls = resolveTElements tcEnv $ mDecls imodule}
    where
    symbolTable = symbolTableIElements (STEnv (sClafers genv) Nothing) (mDecls imodule)
    tcEnv = TCEnv symbolTable "root" TClafer Nothing referenceTable
    referenceTable = Map.empty


{-
 -
 -  Symbol table building functions
 -
 -}
-- Build a symbol table from the elements
symbolTableIElements :: STEnv -> [IElement] -> SymbolTable
symbolTableIElements env elements = foldr (union.symbolTableIElement env) empty elements

symbolTableIElement :: STEnv -> IElement -> SymbolTable
symbolTableIElement env (IEClafer x) = symbolTableIClafer env x
-- Constraints do not add symbols to the symbol table
symbolTableIElement env (IEConstraint _ _) = empty
-- Goald do not add symbols to the symbol table
symbolTableIElement env (IEGoal _ _) = empty

symbolTableIClafer :: STEnv -> IClafer -> SymbolTable
symbolTableIClafer env c =
    let cuid = uid c :: String
        children = symbolTableIElements env{stParent = Just cuid} $ elements c :: SymbolTable
    in
    insert cuid (itypeOfClafer env cuid, stParent env) children

itypeOfClafer :: STEnv -> String -> IType
itypeOfClafer env id = 
    let clafer = findClaferFromUid env id :: IClafer
        hierarchy = findHierarchy getSuper (stClafers env) clafer :: [IClafer]
    in
    -- Find the last IClafer (ie. highest in the hierarchy) and get super type
    typeOfISuper $ super $ last hierarchy

-- Find the clafer with the given uid
findClaferFromUid :: STEnv -> String -> IClafer
findClaferFromUid (STEnv clafers _) id = fromJust $ find (((==) id).uid) clafers
                                
-- Get the super's type (primitive => only one super so we only need to look at the first one)
-- The PExp must be a ClaferID
typeOfISuper :: ISuper -> IType
typeOfISuper (ISuper _ ((PExp _ _ _ (IClaferId _ sident _)):_)) = case sident of
                                                                    "clafer" -> TClafer
                                                                    "int" -> TInteger
                                                                    "integer" -> TInteger
                                                                    "string" -> TString
                                                                    x -> error $ sident ++ " not a native super type"



{-
 -
 -  Type checking and type resolving functions
 -
 -}
-- Type check the elements
resolveTElements :: TCEnv -> [IElement] -> [IElement]
resolveTElements env es = map (resolveTElement env) es

resolveTElement :: TCEnv -> IElement -> IElement
resolveTElement env (IEClafer clafer) = IEClafer $ resolveTClafer env clafer
resolveTElement env (IEConstraint isHard pexp) = IEConstraint isHard resolvedPExp where (_, resolvedPExp) = resolveTPExp env pexp    
resolveTElement env (IEGoal isMaximize pexp) = IEGoal isMaximize resolvedPExp where (_, resolvedPExp) = resolveTPExp env pexp    
                                                                                        
resolveTClafer :: TCEnv -> IClafer -> IClafer
resolveTClafer env clafer = 
    clafer{
        elements = resolveTElements cenv $ elements clafer,
        super = typeTheSuper $ super clafer}
    where cenv = uidTCEnv env (uid clafer)

-- Sets the type in all the supers to IClafer
typeTheSuper :: ISuper -> ISuper
typeTheSuper (ISuper isOverlapping supers) = ISuper isOverlapping $ map typeThePExp supers
typeThePExp :: PExp -> PExp
typeThePExp x = x{iType=Just TClafer}

resolveTPExpPreferValue :: TCEnv -> PExp -> (TCEnv, PExp)
resolveTPExpPreferValue env (PExp _ pid pos x) =
    let (newEnv, (exp, typed)) = resolveTExpPreferValue env x in
    (newEnv, PExp (Just typed) pid pos exp)
    
resolveTPExp :: TCEnv -> PExp -> (TCEnv, PExp)
resolveTPExp env (PExp _ pid pos x) =
    let (newEnv, (exp, typed)) = resolveTExp env x in
    (newEnv, PExp (Just typed) pid pos exp)



{-
    There are two ways to retrieve the type of an IExp:
        resolveTExpPreferValue or resolveTExp
    
    Some functions prefer/require working with values, ie. int, string, etc. In this case,
    call resolveTExpPreferValue and a value type will return if the expression allows.
    Functions that prefer/require working with IClafer calls resolveTExp.
    
    Returns a tuple of the type checked expression and the type.
-}
resolveTExpPreferValue:: TCEnv -> IExp -> (TCEnv, TypedIExp)
-- Clafer reference
-- Return the value type of the reference from the symbol table (possibly IClafer)
resolveTExpPreferValue env e@(IClaferId _ sident _) =
    (env', (e, t))
    where
    env' = identTCEnv env sident
    t = tcType env'
-- Join function
{- 
 - Join function is a special case.
 - The expression a.b can produce a value if b can produce a value.
 - Join function is the only function that passes along the TCEnv of its children
 - This is needed to support parent and this relation.
 -
 - for example: ((parent.parent).this)
 - In the first join, the left child (parent) will create a TCEnv for the parent of the current TCEnv.
 - The right child (parent) will create a TCEnv for the parent of that parent (hence grandparent of the orignal TCEnv).
 - The grandparent TCEnv will be given to the outer join to pass to its right child (this).
 - this refers to the current TCEnv so the example expression is evaluated to the grandparent of the current TCEnv.
 -}
resolveTExpPreferValue env (IFunExp "." [exp1, exp2]) =
    let (env1, a1) = resolveTPExpLeftJoin env exp1
        (env2, a2) = resolveTPExpPreferValue env1 exp2
    in
    (env2, typeCheckFunction (typeOf a2) "." [E TClafer, EAny] [a1, a2])
-- Otherwise, the IExp has no value expression so return its standard expression
resolveTExpPreferValue env x = resolveTExp env x



resolveTExp:: TCEnv -> IExp -> (TCEnv, TypedIExp)
resolveTExp env e@(IClaferId _ sident _) =
    (env', (e, t))
    where
    env' = identTCEnv env sident
    t = TClafer
    
resolveTExp env (IFunExp "." [exp1, exp2]) =
    let (env1, a1) = resolveTPExpLeftJoin env exp1
        (env2, a2) = resolveTPExp env1 exp2
    in
    (env2, typeCheckFunction (typeOf a2) "." [E TClafer, EAny] [a1, a2])
resolveTExp env e@(IInt _) =          (env, (e, TInteger))
resolveTExp env e@(IDouble _) =       (env, (e, TReal))
resolveTExp env e@(IStr _) =          (env, (e, TString))
resolveTExp env e@(IDeclPExp quant decls bpexp) = (env, (IDeclPExp quant decls' bpexp', TBoolean))
    where
    (env', decls') = resolveTDecls env decls
    (_, bpexp') = resolveTPExp env' bpexp
    
    resolveTDecls env [] = (env, [])
    resolveTDecls env (d : ds) =
        (env'', d' : ds')
        where
        (env', d') = resolveTDecl env d
        (env'', ds') = resolveTDecls env' ds
    resolveTDecl env (IDecl isDisj decls body) =
        (env', IDecl isDisj decls body')
        where
        (_, body') = resolveTPExpPreferValue env body
        env' = env{tcTable = foldr (flip insert $ (typeOf body', Nothing)) (tcTable env) decls}


-- Unary functions
resolveTExp env (IFunExp op [exp]) = (env, result)
    where
    result
        | op == iNot  = typeCheckFunction TBoolean    op [E TBoolean] [a1]
        | op == iCSet = typeCheckFunction TInteger    op [E TClafer] [a1]
        | op == iMin  = typeCheckFunction (typeOf a1) op allNumeric         [a1]
        | op == iGMax = typeCheckFunction (typeOf a1) op allNumeric         [a1]
        | op == iGMin = typeCheckFunction (typeOf a1) op allNumeric         [a1]        
        | otherwise   = error $ "Unknown unary function '" ++ op ++ "'"
    (_, a1) = resolveTPExp env exp

-- Binary functions
resolveTExp env (IFunExp op [exp1, exp2]) = (env, result)
    where
    result
        | op `elem` logBinOps = 
            typeCheckFunction TBoolean op (exact [TBoolean, TBoolean])  [a1, a2]
        | op `elem` [iLt, iGt, iLte, iGte] =
            typeCheckFunction TBoolean op allNumeric  [a1PreferValue, a2PreferValue]
        | op `elem` [iEq, iNeq] =
            if isExact (typeOf a1PreferValue) TString then -- String equality
                typeCheckFunction TBoolean op [E TString, E TString] [a1PreferValue, a2PreferValue]
            else if isNumeric $ typeOf a1PreferValue then -- Numeric equality
                typeCheckFunction TBoolean op allNumeric [a1PreferValue, a2PreferValue]
            else -- Set equality
                typeCheckFunction TBoolean op [E TClafer, E TClafer] [a1PreferValue, a2PreferValue]
        | op `elem` relSetBinOps = 
            typeCheckFunction TBoolean op [E TClafer, E TClafer]  [a1, a2]
        | op `elem` [iUnion, iDifference, iIntersection] =
            typeCheckFunction TClafer op [E TClafer, E TClafer]  [a1, a2]
        | op `elem` [iUnion, iDifference, iIntersection] =
            typeCheckFunction TClafer op [E TClafer, E TClafer]  [a1, a2]
        | op `elem` [iDomain, iRange] =
            typeCheckFunction TClafer op [E TClafer, EAny]  [a1, a2PreferValue]
        | op `elem` [iSub, iMul, iDiv] =
            typeCheckFunction (coerceIfNeeded (typeOf a1PreferValue) (typeOf a2PreferValue)) op allNumeric [a1PreferValue, a2PreferValue]
        | op == iPlus =
            if isExact (typeOf a1PreferValue) TString then -- String addition
                typeCheckFunction TString op [E TString, E TString] [a1PreferValue, a2PreferValue]
            else -- Numeric addition or fail
                typeCheckFunction (coerceIfNeeded (typeOf a1PreferValue) (typeOf a2PreferValue)) op allNumeric [a1PreferValue, a2PreferValue]
    (_, a1) = resolveTPExp env exp1
    (_, a2) = resolveTPExp env exp2
    (_, a1PreferValue) = resolveTPExpPreferValue env exp1
    (_, a2PreferValue) = resolveTPExpPreferValue env exp2

--Ternary functions
resolveTExp env (IFunExp "=>else" [exp1, exp2, exp3]) = (env, result)
    where
    result
        | isExact (typeOf a2) TString = -- String expression
            typeCheckFunction TBoolean "=>else" [E TBoolean, E TString, E TString] [a1, a2, a3]
        | isNumeric $ typeOf a2 = -- Numeric expression
            typeCheckFunction TBoolean "=>else" [E TBoolean, ENumeric, ENumeric] [a1, a2, a3]
        | otherwise = -- Clafer expression
            typeCheckFunction TBoolean "=>else" [E TBoolean, E TClafer, E TClafer] [a1, a2, a3]
    (_, a1) = resolveTPExpPreferValue env exp1
    (_, a2) = resolveTPExpPreferValue env exp2
    (_, a3) = resolveTPExpPreferValue env exp3


resolveTPExpLeftJoin :: TCEnv -> PExp -> (TCEnv, PExp)
resolveTPExpLeftJoin env (PExp _ pid pos e@(IClaferId _ "this" _)) =
    (env, PExp (Just TClafer) pid pos e)
resolveTPExpLeftJoin env pexp = resolveTPExp env pexp


--resolveTDecl :: IDecl ->  IDecl
--resolveTDecl x = liftM x{body = resolveTPExp $ body x}

typeOf::PExp->IType
typeOf = fromJust.iType

coerceIfNeeded:: IType -> IType -> IType
coerceIfNeeded TInteger TReal = TReal -- Coerce to real
coerceIfNeeded TReal TInteger = TReal -- Coerce to real
coerceIfNeeded x _ = x                -- No coercing

-- Expects that each argument is numeric
allNumeric :: [TExpect]
allNumeric = repeat ENumeric

-- Expects that each argument is of the exact type
exact :: [IType] -> [TExpect]
exact = map E

-- Type checks each argument.
--   Each argument must match exactly with the expect type (aka E), is numeric (ENumeric), is Clafer or
--   don't care (EAny).
--   E is an EXACT match, ie. TInteger does not match with TReal. Use ENumeric where necessary.
--   Returns a tuple of a IFunExp and its type if type checking passes.
typeCheckFunction :: IType -> String -> [TExpect] -> [PExp] -> (IExp, IType)
typeCheckFunction returnType op expected inferredChildren =
    let inferred = map typeOf inferredChildren in
        if all (uncurry checkExpect) (zip expected inferred) then 
            (IFunExp op inferredChildren, returnType)
        else error ("function " ++ op ++ " expected arguments of type " ++ show (take (length inferred) expected)
            ++ ", received " ++ show inferred)

-- Convenience function, returns true iff the type is a numerical type.
isNumeric :: IType -> Bool
isNumeric itype = checkExpect ENumeric itype

-- Convenience function, returns true iff the type is exact type.
isExact :: IType -> IType -> Bool
isExact a b = checkExpect (E a) b

-- Return true iff IType matches the expected type.
checkExpect :: TExpect -> IType -> Bool
-- Check exact match.
checkExpect (E exact) itype = exact == itype
-- Check is numeric.
checkExpect ENumeric TInteger = True
checkExpect ENumeric TReal    = True
checkExpect ENumeric _        = False
-- Check allows anything
checkExpect EAny _ = True


data TExpect =
    E IType |        -- The exact type
    ENumeric | -- TInteger or TReal
    EAny       -- No expectations
instance Show TExpect where
    show (E itype) = show itype
    show ENumeric = (show TInteger) ++ "/" ++ (show TReal)
    show EAny = "*"
