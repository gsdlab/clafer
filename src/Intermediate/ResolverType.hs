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
resolveTModule (imodule, _) = 
  imodule{mDecls = map resolveTElement $ mDecls imodule}


resolveTClafer :: IClafer -> IClafer
resolveTClafer clafer =
  clafer {super = resolveTSuper $ super clafer,
          elements = map resolveTElement $ elements clafer}


resolveTSuper :: ISuper -> ISuper
resolveTSuper (ISuper isOverlapping pexps) = ISuper isOverlapping $ map resolveTPExp pexps


resolveTElement :: IElement -> IElement
resolveTElement x = case x of
  IEClafer clafer  -> IEClafer $ resolveTClafer clafer
  IEConstraint isHard pexp  -> IEConstraint isHard $ propagate $ resolveTPExp pexp


resolveTPExp :: PExp -> PExp
resolveTPExp (PExp _ pid x) = case x of
  IDeclPExp quant decls pexp -> PExp (Just IBoolean) pid $
    IDeclPExp quant (map resolveTDecl decls) (resolveTPExp pexp)
  y@(IFunExp op _) -> result
    where
    result
      | op == iNot  = appType pid y (map Just [IBoolean]) (Just IBoolean)
      | op == iCSet =
          appType pid y (map Just [ISet]) (Just $ INumeric (Just IInteger))
      | op == iMin  = 
          appType pid y [Nothing] (Just $ INumeric Nothing)
      | op `elem` logBinOps =
          appType pid y (map Just [IBoolean, IBoolean]) (Just IBoolean)
      | op `elem` relGenBinOps =
          appType pid y [Nothing, Nothing] (Just IBoolean)
      | op `elem` relSetBinOps =
          appType pid y (map Just [ISet, ISet]) (Just IBoolean)
      | op == iPlus = case fromJust $ iType p of
          IString  _ -> p
          INumeric _ -> p
          _ -> error "IPlus type error"
      | op `elem` [iSub, iMul, iDiv] =
          appType pid y (map Just [INumeric Nothing, INumeric Nothing])
                    (Just $ INumeric Nothing)
      | op `elem` setBinOps =
          appType pid y (map Just [ISet, ISet]) (Just ISet)
      | op == iIfThenElse =
          infer $ appType pid y [Just IBoolean, Nothing, Nothing] Nothing
      where
      p = infer $ appType pid y [Nothing, Nothing] Nothing
  IInt n -> PExp (Just $ INumeric $ Just IInteger) pid x
  IDouble n -> PExp (Just $ INumeric $ Just IReal) pid x
  IStr str -> PExp (Just $ IString $ Just ILiteral) pid x
  IClaferId _ _ _ -> PExp (Just ISet) pid x


infer :: PExp -> PExp
infer x = x{iType = iType $ typeExp (iType x) $ typeExp (iType exp0) exp1}
  where
  (exp1:exp0:_) = reverse $ exps $ (Intermediate.Intclafer.exp) x
  

appType :: String -> IExp -> [Maybe IType] -> Maybe IType -> PExp
appType pid (IFunExp op exps) eTypes rType =
  PExp rType pid (IFunExp op (check eTypes (map resolveTPExp exps)))


check :: [Maybe IType] -> [PExp] -> [PExp]
check eTypes exps = map (uncurry typeExp) $ zip eTypes exps


typeExp :: Maybe IType -> PExp -> PExp
typeExp eType x@(PExp iType pid exp)
  | eType == iType  = x
  | isNothing eType = x
  | otherwise       = PExp (Just $ resolveT (fromJust eType) (fromJust iType)) pid exp

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
propagateTIExp piType x@(PExp iType pid y) = case y of
  IDeclPExp quant decls pexp -> PExp iType pid $ IDeclPExp quant decls $ propagate pexp
  IFunExp op pexps@((PExp iType1 _ _):(PExp iType2 _ _):[]) -> result
    where
    result
      | op `elem` relGenBinOps =
          PExp iType pid y{exps = map (propagateTIExp iType') pexps}
      | op `elem` arithBinOps ++ [iMin] =
          PExp iType pid y{exps = map (propagateTIExp (fromJust iType)) pexps}
      | op == iJoin = 
          PExp iType pid y{exps = head pexps :
                       (map (propagateTIExp (fromJust iType)) $ tail pexps)}
              
      | otherwise = x
    iType' = resolveT (fromJust iType1) (fromJust iType2)
  IClaferId _ _ _ -> PExp (Just $ propagateT piType) pid y
  _ -> x


propagateT :: IType -> IType
propagateT IBoolean = ISet
propagateT (IString _) = IString (Just ILiteral)
propagateT (INumeric (Just ISetInteger)) = INumeric (Just IInteger)
propagateT (INumeric (Just ISetReal)) = INumeric (Just IReal)
propagateT x = x