{-
 This file is part of the Clafer Translator (clafer).

 Copyright (C) 2010 Kacper Bak <http://gsd.uwaterloo.ca/kbak>

 clafer is free software: you can redistribute it and/or modify
 it under the terms of the GNU Lesser General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 clafer is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Lesser General Public License for more details.

 You should have received a copy of the GNU Lesser General Public License
 along with clafer. (See files COPYING and COPYING.LESSER.)  If not,
 see <http://www.gnu.org/licenses/>.
-}
module Intermediate.ResolverType where

import Control.Monad.State
import Data.Function
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace
import List

import Common
import Intermediate.Intclafer


type SymbolTable = Map String IType
type TypeState = State ([IClafer], [IClafer], SymbolTable)

        
resolveTModule :: (IModule, GEnv) -> IModule
resolveTModule (imodule, genv) = 
    imodule{mDecls = evalState (resolveTElements $ mDecls imodule) (sClafers genv, [], Map.empty)}

-- Returns the type of the clafer with given uid
itypeOfClafer :: String -> TypeState IType
itypeOfClafer id =
    do
        (_, _, symbolTable) <- get
        -- Search symbol table
        -- Calculate and store in symbol table if not yet cached
        case (Map.lookup id symbolTable) of
                Just x -> return x
                Nothing -> updateSymbolTable id

-- Calculate the type and store in symbol table
updateSymbolTable :: String -> TypeState IType
updateSymbolTable id =
    do
        itype <- itypeOfClaferCalculate id
        (clafers, path, symbolTable) <- get
        case id of
            "this" -> itypeOfClafer $ uid $ head path
            "parent" -> itypeOfClafer $ uid $ head $ tail path
            _ -> do
                     put $ (clafers, path, Map.insert id itype symbolTable)
                     return itype
        

-- Perform the calculation required to find the type of the clafer with given uid
itypeOfClaferCalculate :: String -> TypeState IType
itypeOfClaferCalculate id = do (clafers, _, symbolTable) <- get
                               let clafer = findClaferFromUid id clafers
                               let hierarchy = findHierarchy clafers clafer
                               return $ topTypeOfHierarchy hierarchy

-- Find the clafer with the given uid
findClaferFromUid :: String -> [IClafer] -> IClafer
findClaferFromUid id clafers = fromJust $ trace id $ find (((==) id).uid) clafers

-- Find the last IClafer (ie. highest in the hierarchy) and get super type
topTypeOfHierarchy :: [IClafer] -> IType
topTypeOfHierarchy clafers = typeOfISuper.super.last $ clafers
                                
-- Get the super's type (primitive => only one super so we only need to look at the first one)
-- The PExp must be a ClaferID
typeOfISuper :: ISuper -> IType
typeOfISuper (ISuper _ ((PExp _ _ (IClaferId _ sident _)):_)) = case sident of
                                                                    "clafer" -> TClafer
                                                                    "int" -> TInteger
                                                                    "integer" -> TInteger
                                                                    "string" -> TString
                                                                    x -> error $ sident ++ " not a native super type"

resolveTElements :: [IElement] -> TypeState [IElement]
resolveTElements es = unfoldStates $ map resolveTElement es

resolveTElement :: IElement -> TypeState IElement
resolveTElement (IEClafer clafer) = IEClafer `liftM` resolveTClafer clafer
resolveTElement (IEConstraint isHard pexp) = IEConstraint isHard `liftM` resolveTPExp pexp    

resolveTClafer :: IClafer -> TypeState IClafer
resolveTClafer clafer = 
    do
        -- Push this clafer onto the path
        (a, path1, b) <- get
        put (a, clafer:path1, b)
        
        e <- resolveTElements $ elements clafer
        
        -- Pop this clafer from the path
        (c, _:path, d) <- get
        put (c, path, d)
        
        return clafer{elements = e, super = typeTheSuper $ super clafer}

-- Sets the type in all the supers to IClafer
typeTheSuper :: ISuper -> ISuper
typeTheSuper (ISuper isOverlapping supers) = ISuper isOverlapping $ map typeThePExp supers
typeThePExp :: PExp -> PExp
typeThePExp x = x{iType=Just TClafer}

resolveTPExpPreferValue :: PExp -> TypeState PExp
resolveTPExpPreferValue (PExp _ pid x) =
    do
        (exp, typed) <- resolveTExpPreferValue x
        return $ PExp (Just typed) pid exp
    
resolveTPExp :: PExp -> TypeState PExp
resolveTPExp (PExp _ pid x) =
    do
        (exp, typed) <- resolveTExp x
        return $ PExp (Just typed) pid exp

{-
    There are two ways to retrieve the type of an IExp:
        resolveTExpPreferValue or resolveTExp
    
    Some functions prefer/require working with values, ie. int, string, etc. In this case,
    call resolveTExpPreferValue and a value type will return if the expression allows.
    Functions that prefer/require working with IClafer calls resolveTExp.
    
    Returns a tuple of the type checked expression and the type.
-}
resolveTExpPreferValue:: IExp -> TypeState (IExp, IType)
-- Clafer reference
-- Return the value type of the reference from the symbol table (possibly IClafer)
resolveTExpPreferValue e@(IClaferId _ sident _) = 
    ((,) e) `liftM` (itypeOfClafer sident)
-- Join function
-- Join function is a special case
-- The expression a.b can produce a value if b can produce a value
resolveTExpPreferValue (IFunExp "." [exp1, exp2]) =
    do
        a1 <- resolveTPExp exp1        
        a2 <- resolveTPExpPreferValue exp2
        return $ typeCheckFunction (typeOf a2) "." (exact [TClafer, typeOf a2]) [a1, a2]
-- Otherwise, the IExp has no value expression so return its standard expression
resolveTExpPreferValue x = resolveTExp x



resolveTExp:: IExp -> TypeState (IExp, IType)
resolveTExp e@(IInt _) = return (e, TInteger)
resolveTExp e@(IDouble _) = return (e, TReal)
resolveTExp e@(IStr _) = return (e, TString)
resolveTExp e@(IDeclPExp _ _ _) = return (e, TBoolean)
resolveTExp e@(IClaferId _ _ _) = return (e, TClafer)

-- Unary functions
resolveTExp (IFunExp op [exp]) =
    do
        a1 <- (resolveTPExp exp)
        return $
            if op == iNot then
                typeCheckFunction TBoolean op (exact [TBoolean]) [a1]
            else if op == iCSet then
                typeCheckFunction TInteger op (exact [TClafer]) [a1]
            else if op == iMin then
                typeCheckFunction (typeOf a1) op allNumeric [a1]
            else error $ "Unknown unary function '" ++ op ++ "'"

-- Binary functions
resolveTExp (IFunExp op [exp1, exp2])
        | op `elem` logBinOps = 
            typeCheckFunction TBoolean op (exact [TBoolean, TBoolean]) `liftT` [a1, a2]
        | op `elem` [iLt, iGt, iLte, iGte] =
            typeCheckFunction TBoolean op allNumeric `liftT` [a1PreferValue, a2PreferValue]
        | op `elem` [iEq, iNeq] =
            do
                a <- a1PreferValue
                b <- a2PreferValue
                return $
                    if typeOf a == TString then -- String equality
                        typeCheckFunction TBoolean op (exact [TString, TString]) [a, b]
                    else if isNumeric $ typeOf a then -- Numeric equality
                        typeCheckFunction TBoolean op allNumeric [a, b]
                    else -- Set equality
                        typeCheckFunction TBoolean op (exact [TClafer, TClafer]) [a, b]
        | op `elem` relSetBinOps = 
            typeCheckFunction TBoolean op (exact [TClafer, TClafer]) `liftT` [a1, a2]
        | op `elem` setBinOps =
            typeCheckFunction TClafer op (exact [TClafer, TClafer]) `liftT` [a1, a2]
        | op `elem` [iSub, iMul, iDiv] =
            do
                a <- a1PreferValue
                b <- a2PreferValue
                return $ typeCheckFunction (coerceIfNeeded (typeOf a) (typeOf b)) op allNumeric [a, b]
        | op == iPlus =
            do
                a <- a1PreferValue
                b <- a2PreferValue
                return $
                    if typeOf a == TString then -- String addition
                        typeCheckFunction TString op (exact [TString, TString]) [a, b]
                    else -- Numeric addition or fail
                        typeCheckFunction (coerceIfNeeded (typeOf a) (typeOf b)) op allNumeric [a, b]
        where
            a1 = resolveTPExp exp1
            a2 = resolveTPExp exp2
            a1PreferValue = resolveTPExpPreferValue exp1
            a2PreferValue = resolveTPExpPreferValue exp2

--Ternary functions
resolveTExp (IFunExp op [exp1, exp2, exp3])
    | op == iIfThenElse =
        do
            a1 <- resolveTPExpPreferValue exp1
            a2 <- resolveTPExpPreferValue exp2
            a3 <- resolveTPExpPreferValue exp3
            return $
                if typeOf a2 == TString then -- String expression
                    typeCheckFunction TBoolean op (exact [TBoolean, TString, TString]) [a1, a2, a3]
                else if isNumeric $ typeOf a2 then -- Numeric expression
                    typeCheckFunction TBoolean op [TExpect TBoolean, TExpectNumeric, TExpectNumeric] [a1, a2, a3]
                else -- Set expression
                    typeCheckFunction TBoolean op (exact [TBoolean, TString, TString]) [a1, a2, a3]

--resolveTDecl :: IDecl -> TypeState IDecl
--resolveTDecl x = liftM x{body = resolveTPExp $ body x}

typeOf::PExp->IType
typeOf = fromJust.iType

coerceIfNeeded::IType->IType->IType
coerceIfNeeded TInteger TReal = TReal -- Coerce to real
coerceIfNeeded TReal TInteger = TReal -- Coerce to real
coerceIfNeeded x _ = x                -- No coercing

-- Convenience function
liftT :: ([PExp] -> a) -> [TypeState PExp] -> TypeState a
liftT f x = f `liftM` (unfoldStates x)
        
-- Turn a list of monads to a monad of list
unfoldStates :: [TypeState a] -> TypeState [a]
unfoldStates = foldr (liftM2 (:)) (return [])

-- Expects that each argument is numeric
allNumeric :: [TExpect]
allNumeric = repeat TExpectNumeric

-- Expects that each argument is of the exact type
exact :: [IType] -> [TExpect]
exact = map TExpect

-- Type checks each argument.
--   Each argument must match exactly with the expect type (aka TExpect) or is numeric (TExpectNumeric).
--   TExpect is an EXACT match, ie. TInteger does not match with TReal. Use TExpectNumeric where necessary.
--   Returns a tuple of a IFunExp and its type if type checking passes.
typeCheckFunction :: IType -> String -> [TExpect] -> [PExp] -> (IExp, IType)
typeCheckFunction returnType op expected inferredChildren =
    let inferred = map typeOf inferredChildren in
        if all (uncurry checkExpect) (zip expected inferred) then 
            (IFunExp op inferredChildren, returnType)
        else error ("function " ++ op ++ " expected arguments of type " ++ (show $ take (length inferred) expected)
            ++ ", received " ++ (show inferred))

-- Convenience function, returns true iff the type is a numerical type.
isNumeric :: IType -> Bool
isNumeric itype = checkExpect TExpectNumeric itype

-- Return true iff IType matches the expected type.
checkExpect :: TExpect -> IType -> Bool
-- Check exact match.
checkExpect (TExpect expect) itype = expect == itype
-- Check is numeric.
checkExpect TExpectNumeric TInteger = True
checkExpect TExpectNumeric TReal = True
checkExpect TExpectNumeric _ = False

data TExpect = TExpect IType | TExpectNumeric
instance Show TExpect where
    show (TExpect itype) = show itype
    show TExpectNumeric = (show TInteger) ++ "/" ++ (show TReal)
