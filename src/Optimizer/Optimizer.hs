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
  imodule{mDecls = em $ rm $ map optimizeDeclaration $ markTopModule $ mDecls imodule}
  where
  rm = if keep_unused args then id else remUnusedAbs
  em = if flatten_inheritance args then flip (curry expModule) genv else id

optimizeDeclaration :: IDeclaration -> IDeclaration
optimizeDeclaration x = case x of
  IClaferDecl clafer -> IClaferDecl $ optimizeClafer (1, ExIntegerNum 1) clafer
  IConstDecl constraint  -> x


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


optimizeElement :: Interval -> IElement -> IElement
optimizeElement interval x = case x of
  ISubclafer clafer  -> ISubclafer $ optimizeClafer interval clafer
  ISubconstraint constraint  -> x

-- -----------------------------------------------------------------------------

remUnusedAbs :: [IDeclaration] -> [IDeclaration]
remUnusedAbs decls = decls \\ unusedAbs
  where
  unusedAbs = map IClaferDecl $ findUnusedAbs clafers $ map uid $
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

expModule :: ([IDeclaration], GEnv) -> [IDeclaration]
expModule (decls, genv) = evalState (mapM expDeclaration decls) genv


expDeclaration x = case x of
  IClaferDecl clafer  -> IClaferDecl `liftM` expClafer clafer
  IConstDecl constraint  -> IConstDecl `liftM` expPExp constraint


expClafer clafer = do
  super' <- expSuper $ super clafer
  elements' <- mapM expElement $ elements clafer
  return $ clafer {super = super', elements = elements'}


expSuper x = case x of
  ISuper False _ -> return x
  ISuper True pexps -> ISuper True `liftM` mapM expPExp pexps


expElement x = case x of
  ISubclafer clafer  -> ISubclafer `liftM` expClafer clafer
  ISubconstraint constraint  -> ISubconstraint `liftM` expPExp constraint


expPExp (PExp t exp) = PExp t `liftM` expIExp exp

expIExp x = case x of
  IDeclPExp quant decls pexp -> do
    decls' <- mapM expDecl decls
    pexp' <- expPExp pexp
    return $ IDeclPExp quant decls' pexp'
  IFunExp IJoin _ -> expNav x
  IFunExp op exps -> IFunExp op `liftM` mapM expPExp exps
  IClaferId _ _ _ -> expNav x
  _ -> return x

expDecl x = case x of
  IDecl disj locids pexp -> IDecl disj locids `liftM` expPExp pexp

expNav x = do
  xs <- split' x return
  xs' <- mapM (expNav' "") xs
  return $ mkUnion $ map fst xs'


expNav' context x = case x of
  IFunExp IJoin ((PExp iType0 exp0):(PExp iType exp):_)  -> do    
    (exp0', context') <- expNav' context exp0
    (exp', context'') <- expNav' context' exp
    return (IFunExp IJoin [PExp iType0 exp0', PExp iType exp'], context'')
  IClaferId modName id isTop -> do
    st <- gets stable
    if Map.member id st
      then do
        let impls  = (Map.!) st id
        let (impls', context') = maybe (impls, "")
             (\x -> ([[head x]], head x)) $
             find (\x -> context == (head.tail) x) impls
        return (mkUnion $ map (\x -> IClaferId modName x isTop) $
                map head impls', context')
      else do
        return (x, id)


mkUnion (x:[]) = x
mkUnion xs = foldl1 (\x y -> IFunExp IUnion $ map (PExp (Just ISet)) [x,y]) xs


split' x f = case x of
  IFunExp IJoin ((PExp iType exp0):pexp:_) ->
    split' exp0 (\s -> f $ IFunExp IJoin [PExp iType s, pexp])
  IClaferId modName id isTop -> do
    st <- gets stable
    mapM f $ map (\x -> IClaferId modName x isTop) $ maybe [id] (map head) $ Map.lookup id st

-- -----------------------------------------------------------------------------
-- checking if all clafers have unique names and don't extend other clafers

allUnique :: IModule -> Bool
allUnique imodule = and un && (null $
  filter (\xs -> 1 < length xs) $ group $ sort $ concat idents)
  where
  (un, idents) = unzip $ map allUniqueDeclaration $ mDecls imodule


allUniqueDeclaration x = case x of
  IClaferDecl clafer  -> allUniqueClafer clafer
  IConstDecl constraint  -> (True, [])


allUniqueClafer clafer =
  ("clafer" == getSuper clafer && and un, ident clafer : concat idents)
  where
  (un, idents) = unzip $ map allUniqueElement $ elements clafer

allUniqueElement :: IElement -> (Bool, [String])
allUniqueElement x = case x of
  ISubclafer clafer -> allUniqueClafer clafer
  ISubconstraint ilexp -> (True, [])

-- -----------------------------------------------------------------------------
findDupModule :: ClaferArgs -> IModule -> IModule
findDupModule args imodule = imodule{mDecls = decls'}
  where
  decls = mDecls imodule
  decls'
    | check_duplicates args = findDupModule' decls
    | otherwise             = decls


findDupModule' :: [IDeclaration] -> [IDeclaration]
findDupModule' declarations
  | null dups = map findDupDeclaration declarations
  | otherwise = error $ show dups
  where
  dups = findDuplicates $ toClafers declarations


findDupDeclaration x = case x of
  IClaferDecl clafer  -> IClaferDecl $ findDupClafer clafer
  IConstDecl constraint  -> x


findDupClafer clafer = if null dups
  then clafer{elements = map findDupElement $ elements clafer}
  else error $ (show $ ident clafer) ++ show dups
  where
  dups = findDuplicates $ getSubclafers $ elements clafer

findDupElement x = case x of
  ISubclafer clafer -> ISubclafer $ findDupClafer clafer
  ISubconstraint ilexp -> x


findDuplicates :: [IClafer] -> [String]
findDuplicates clafers =
  map head $ filter (\xs -> 1 < length xs) $ group $ sort $ map ident clafers

-- -----------------------------------------------------------------------------
-- marks top clafers

markTopModule :: [IDeclaration] -> [IDeclaration]
markTopModule decls = map (markTopDeclaration (
      [this, parent, children, strType, intType, integerType] ++
      (map uid $ toClafers decls))) decls


markTopDeclaration :: [String] -> IDeclaration -> IDeclaration
markTopDeclaration clafers x = case x of
  IClaferDecl clafer  -> IClaferDecl $ markTopClafer clafers clafer
  IConstDecl constraint  -> IConstDecl $ markTopPExp clafers constraint


markTopClafer :: [String] -> IClafer -> IClafer
markTopClafer clafers clafer =
  clafer {super = markTopSuper clafers $ super clafer, 
          elements = map (markTopElement clafers) $ elements clafer}


markTopSuper :: [String] -> ISuper -> ISuper
markTopSuper clafers x = x{supers = map (markTopPExp clafers) $ supers x}


markTopElement :: [String] -> IElement -> IElement
markTopElement clafers x = case x of
  ISubclafer clafer  -> ISubclafer $ markTopClafer clafers clafer
  ISubconstraint constraint  -> ISubconstraint $ markTopPExp clafers constraint


markTopPExp clafers (PExp t iexp) = PExp t $ markTopIExp clafers iexp


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
