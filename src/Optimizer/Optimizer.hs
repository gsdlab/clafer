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
module Optimizer.Optimizer where

import Data.Maybe
import Data.List
import Control.Monad.State
import Data.Function
import Data.Map (Map)
import qualified Data.Map as Map

import Common
import Front.Absclafer
import Intermediate.Intclafer

optimizeModule :: ClaferArgs -> (IModule, GEnv) -> IModule
optimizeModule args (imodule, genv) =
  imodule{mDecls = em $ rm $ map (optimizeElement (1, ExIntegerNum 1)) $
                   markTopModule $ mDecls imodule}
  where
  rm = if keep_unused args then id else remUnusedAbs
  em = if flatten_inheritance args then flip (curry expModule) genv else id

optimizeElement :: Interval -> IElement -> IElement
optimizeElement interval x = case x of
  IEClafer clafer  -> IEClafer $ optimizeClafer interval clafer
  IEConstraint _ constraint  -> x


optimizeClafer :: Interval -> IClafer -> IClafer
optimizeClafer interval clafer = clafer {glCard = glCard',
  elements = map (optimizeElement glCard') $ elements clafer}
  where
  glCard' = multInt (fromJust $ card clafer) interval


multInt :: Interval -> Interval -> Interval
multInt (m, n) (m', n') = (m * m', multExInt n n')


multExInt :: ExInteger -> ExInteger -> ExInteger
multExInt (ExIntegerNum 0) _ = ExIntegerNum 0
multExInt _ (ExIntegerNum 0) = ExIntegerNum 0
multExInt ExIntegerAst _ = ExIntegerAst
multExInt _ ExIntegerAst = ExIntegerAst
multExInt (ExIntegerNum m) (ExIntegerNum n) = ExIntegerNum $ m * n

-- -----------------------------------------------------------------------------

remUnusedAbs :: [IElement] -> [IElement]
remUnusedAbs decls = decls \\ unusedAbs
  where
  unusedAbs = map IEClafer $ findUnusedAbs clafers $ map uid $
              filter (not.isAbstract) clafers
  clafers   = toClafers decls


findUnusedAbs :: [IClafer] -> [String] -> [IClafer]
findUnusedAbs maybeUsed [] = maybeUsed
findUnusedAbs [] _   = []
findUnusedAbs maybeUsed used = findUnusedAbs maybeUsed' $ getUniqExtended used'
  where
  (used', maybeUsed') = partition (\c -> uid c `elem` used) maybeUsed


getUniqExtended used = nub $ used >>= getExtended


getExtended :: IClafer -> [String]
getExtended clafer =
  sName ++ ((getSubclafers $ elements clafer) >>= getExtended)
  where
  sName = if not $ isOverlapping $ super clafer then [getSuper clafer] else []

-- -----------------------------------------------------------------------------
-- inheritance  expansions

expModule :: ([IElement], GEnv) -> [IElement]
expModule (decls, genv) = evalState (mapM expElement decls) genv


expClafer clafer = do
  super' <- expSuper $ super clafer
  elements' <- mapM expElement $ elements clafer
  return $ clafer {super = super', elements = elements'}


expSuper x = case x of
  ISuper False _ -> return x
  ISuper True pexps -> ISuper True `liftM` mapM expPExp pexps


expElement x = case x of
  IEClafer clafer  -> IEClafer `liftM` expClafer clafer
  IEConstraint isHard constraint  -> IEConstraint isHard `liftM` expPExp constraint


expPExp (PExp t pid exp) = PExp t pid `liftM` expIExp exp

expIExp x = case x of
  IDeclPExp quant decls pexp -> do
    decls' <- mapM expDecl decls
    pexp' <- expPExp pexp
    return $ IDeclPExp quant decls' pexp'
  IFunExp op exps -> if op == iJoin
                     then expNav x else IFunExp op `liftM` mapM expPExp exps
  IClaferId _ _ _ -> expNav x
  _ -> return x

expDecl x = case x of
  IDecl disj locids pexp -> IDecl disj locids `liftM` expPExp pexp

expNav x = do
  xs <- split' x return
  xs' <- mapM (expNav' "") xs
  return $ mkIFunExp iUnion $ map fst xs'


expNav' context x = case x of
  IFunExp _ ((PExp iType0 pid0 exp0):(PExp iType pid exp):_)  -> do    
    (exp0', context') <- expNav' context exp0
    (exp', context'') <- expNav' context' exp
    return (IFunExp iJoin [PExp iType0 pid0 exp0', PExp iType pid exp'], context'')
  IClaferId modName id isTop -> do
    st <- gets stable
    if Map.member id st
      then do
        let impls  = (Map.!) st id
        let (impls', context') = maybe (impls, "")
             (\x -> ([[head x]], head x)) $
             find (\x -> context == (head.tail) x) impls
        return (mkIFunExp iUnion $ map (\x -> IClaferId modName x isTop) $
                map head impls', context')
      else do
        return (x, id)


split' x f = case x of
  IFunExp _ ((PExp iType pid0 exp0):pexp:_) ->
    split' exp0 (\s -> f $ IFunExp iJoin [PExp iType pid0 s, pexp])
  IClaferId modName id isTop -> do
    st <- gets stable
    mapM f $ map (\x -> IClaferId modName x isTop) $ maybe [id] (map head) $ Map.lookup id st

-- -----------------------------------------------------------------------------
-- checking if all clafers have unique names and don't extend other clafers

allUnique :: IModule -> Bool
allUnique imodule = and un && (null $
  filter (\xs -> 1 < length xs) $ group $ sort $ concat idents) && identsOk
  where
  (un, idents) = unzip $ map allUniqueElement $ mDecls imodule
  identsOk     = and $ map (checkConstraintElement (concat idents)) $ mDecls imodule

allUniqueClafer clafer =
  (getSuper clafer `elem` "clafer" : primitiveTypes  && and un,
   ident clafer : concat idents)
  where
  (un, idents) = unzip $ map allUniqueElement $ elements clafer

allUniqueElement :: IElement -> (Bool, [String])
allUniqueElement x = case x of
  IEClafer clafer -> allUniqueClafer clafer
  IEConstraint _ _ -> (True, [])


checkConstraintElement idents x = case x of
  IEClafer clafer -> and $ map (checkConstraintElement idents) $ elements clafer
  IEConstraint _ pexp -> checkConstraintPExp idents pexp 

checkConstraintPExp idents (PExp _ _ exp) = checkConstraintIExp idents exp

checkConstraintIExp idents x = case x of
   IDeclPExp _ oDecls pexp ->
     checkConstraintPExp ((oDecls >>= (checkConstraintIDecl idents)) ++ idents) pexp
   IClaferId _ ident _ -> if ident `elem` idents then True
                          else error $ ident ++ " not found"
   _ -> True

checkConstraintIDecl idents (IDecl _ decls pexp)
  | checkConstraintPExp idents pexp = decls
  | otherwise                       = []

-- -----------------------------------------------------------------------------
findDupModule :: ClaferArgs -> IModule -> IModule
findDupModule args imodule = imodule{mDecls = decls'}
  where
  decls = mDecls imodule
  decls'
    | check_duplicates args = findDupModule' decls
    | otherwise             = decls


findDupModule' :: [IElement] -> [IElement]
findDupModule' declarations
  | null dups = map findDupElement declarations
  | otherwise = error $ show dups
  where
  dups = findDuplicates $ toClafers declarations


findDupClafer clafer = if null dups
  then clafer{elements = map findDupElement $ elements clafer}
  else error $ (show $ ident clafer) ++ show dups
  where
  dups = findDuplicates $ getSubclafers $ elements clafer

findDupElement x = case x of
  IEClafer clafer -> IEClafer $ findDupClafer clafer
  IEConstraint _ _ -> x


findDuplicates :: [IClafer] -> [String]
findDuplicates clafers =
  map head $ filter (\xs -> 1 < length xs) $ group $ sort $ map ident clafers

-- -----------------------------------------------------------------------------
-- marks top clafers

markTopModule :: [IElement] -> [IElement]
markTopModule decls = map (markTopElement (
      [this, parent, children, strType, intType, integerType] ++
      (map uid $ toClafers decls))) decls


markTopClafer :: [String] -> IClafer -> IClafer
markTopClafer clafers clafer =
  clafer {super = markTopSuper clafers $ super clafer, 
          elements = map (markTopElement clafers) $ elements clafer}


markTopSuper :: [String] -> ISuper -> ISuper
markTopSuper clafers x = x{supers = map (markTopPExp clafers) $ supers x}


markTopElement :: [String] -> IElement -> IElement
markTopElement clafers x = case x of
  IEClafer clafer  -> IEClafer $ markTopClafer clafers clafer
  IEConstraint isHard pexp  -> IEConstraint isHard $ markTopPExp clafers pexp


markTopPExp clafers (PExp t pid iexp) = PExp t pid $ markTopIExp clafers iexp


markTopIExp :: [String] -> IExp -> IExp
markTopIExp clafers x = case x of
  IDeclPExp quant decl pexp -> IDeclPExp quant (map (markTopDecl clafers) decl)
                                (markTopPExp ((decl >>= decls) ++ clafers) pexp)
  IFunExp op exps -> IFunExp op $ map (markTopPExp clafers) exps
  IClaferId modName sident _ ->
    IClaferId modName sident $ sident `elem` clafers
  _ -> x


markTopDecl :: [String] -> IDecl -> IDecl
markTopDecl clafers x = case x of
  IDecl disj locids pexp -> IDecl disj locids $ markTopPExp clafers pexp
