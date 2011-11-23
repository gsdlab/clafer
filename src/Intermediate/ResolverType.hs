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

import Data.Function
import Data.Maybe

import Common
import Intermediate.Intclafer

resolveTModule :: (IModule, GEnv) -> IModule
resolveTModule (imodule, genv) = 
  imodule{mDecls = map (resolveTDeclaration (decls, genv)) decls}
  where
  decls = mDecls imodule


resolveTDeclaration :: ([IDeclaration], GEnv) -> IDeclaration -> IDeclaration
resolveTDeclaration _ x = case x of
  IClaferDecl clafer  -> IClaferDecl $ resolveTClafer clafer
  IConstDecl constraint  -> IConstDecl $ propagate $ resolveTPExp constraint


resolveTClafer :: IClafer -> IClafer
resolveTClafer clafer =
  clafer {super = resolveTSuper $ super clafer,
          elements = map resolveTElement $ elements clafer}


resolveTSuper :: ISuper -> ISuper
resolveTSuper (ISuper isOverlapping pexps) = ISuper isOverlapping $ map resolveTPExp pexps


resolveTElement :: IElement -> IElement
resolveTElement x = case x of
  ISubclafer clafer  -> ISubclafer $ resolveTClafer clafer
  ISubconstraint constraint  -> ISubconstraint $ propagate $ resolveTPExp constraint


resolveTPExp :: PExp -> PExp
resolveTPExp x = resolveTIExp $ (Intermediate.Intclafer.exp) x


resolveTIExp :: IExp -> PExp
resolveTIExp x = case x of
  IDeclPExp quant decls pexp -> PExp (Just IBoolean) $
    IDeclPExp quant (map resolveTDecl decls) (resolveTPExp pexp)
  y@(IFunExp op _) -> result
    where
    result
      | op == iNot  = appType y (map Just [IBoolean]) (Just IBoolean)
      | op == iCSet =
          appType y (map Just [ISet]) (Just $ INumeric (Just IInteger))
      | op `elem` logBinOps =
          appType y (map Just [IBoolean, IBoolean]) (Just IBoolean)
      | op `elem` relGenBinOps =
          appType y [Nothing, Nothing] (Just IBoolean)
      | op `elem` relSetBinOps =
          appType y (map Just [ISet, ISet]) (Just IBoolean)
      | op == iPlus = case fromJust $ iType p of
          IString  _ -> p
          INumeric _ -> p
          _ -> error "IPlus type error"
      | op `elem` [iSub, iMul, iDiv] =
          appType y (map Just [INumeric Nothing, INumeric Nothing])
                    (Just $ INumeric Nothing)
      | op `elem` setBinOps =
          appType y (map Just [ISet, ISet]) (Just ISet)
      | op == iIfThenElse =
          infer $ appType y [Just IBoolean, Nothing, Nothing] Nothing
      where
      p = appType y [Nothing, Nothing] Nothing
  IInt n -> PExp (Just $ INumeric $ Just IInteger) x
  IDouble n -> PExp (Just $ INumeric $ Just IReal) x
  IStr str -> PExp (Just $ IString $ Just ILiteral) x
  IClaferId _ _ _ -> PExp (Just ISet) x

infer :: PExp -> PExp
infer x = x{iType = iType $ typeExp (iType x) $ typeExp (iType exp0) exp1}
  where
  (exp1:exp0:_) = reverse $ exps $ (Intermediate.Intclafer.exp) x
  

appType :: IExp -> [Maybe IType] -> Maybe IType -> PExp
appType (IFunExp op exps) eTypes rType =
  PExp rType (IFunExp op (check eTypes (map resolveTPExp exps)))


check :: [Maybe IType] -> [PExp] -> [PExp]
check eTypes exps = map (uncurry typeExp) $ zip eTypes exps


typeExp :: Maybe IType -> PExp -> PExp
typeExp eType x@(PExp iType exp)
  | eType == iType  = x
  | isNothing eType = x
  | otherwise       = PExp (Just $ resolveT (fromJust eType) (fromJust iType)) exp

-- integer cast to real
resolveT (INumeric (Just IInteger)) x@(INumeric (Just IReal)) = x
resolveT x@(INumeric (Just IReal)) (INumeric (Just IInteger)) = x

-- set and numeric set
resolveT (INumeric (Just IInteger)) ISet = INumeric (Just ISetInteger)
resolveT ISet (INumeric (Just IInteger)) = INumeric (Just ISetInteger)
resolveT (INumeric (Just IReal)) ISet = INumeric (Just ISetReal)
resolveT ISet (INumeric (Just IReal)) = INumeric (Just ISetReal)
resolveT x@(INumeric _) ISet = x
resolveT ISet x@(INumeric _) = x

-- numeric and numeric set
resolveT (INumeric (Just IInteger)) x@(INumeric (Just ISetInteger)) = x
resolveT x@(INumeric (Just ISetInteger)) (INumeric (Just IInteger)) = x

-- all other numeric cases
resolveT (INumeric _) (INumeric _) = (INumeric (Just ISetReal))

-- strings
resolveT (IString _) (IString _) = IString (Just ISetString)
resolveT (IString _) ISet = IString (Just ISetString)
resolveT ISet (IString _) = IString (Just ISetString)

resolveT ISet IBoolean = IBoolean
resolveT IBoolean ISet = IBoolean

resolveT x y = error $ "Type error: " ++ (show x) ++ " " ++ (show y)

resolveTDecl :: IDecl -> IDecl
resolveTDecl x = x{body = resolveTPExp $ body x}

propagate :: PExp -> PExp
propagate x = propagateTIExp IBoolean  x


propagateTIExp :: IType -> PExp -> PExp
propagateTIExp piType x@(PExp iType y) = case y of
  IDeclPExp quant decls pexp -> PExp iType $ IDeclPExp quant decls $ propagate pexp
  IFunExp op pexps -> result
    where
    result
      | op `elem` relGenBinOps ++ arithBinOps =
          PExp iType y{exps = map (propagateTIExp (fromJust iType)) pexps}
      | op == iJoin = 
          PExp iType y{exps = head pexps :
                       (map (propagateTIExp (fromJust iType)) $ tail pexps)}
              
      | otherwise = x
  IClaferId _ _ _ -> PExp (Just $ propagateT piType) y
  _ -> x


propagateT :: IType -> IType
propagateT IBoolean = ISet
propagateT (IString _) = IString (Just ILiteral)
propagateT (INumeric (Just ISetInteger)) = INumeric (Just IInteger)
propagateT (INumeric (Just ISetReal)) = INumeric (Just IReal)
propagateT x = x