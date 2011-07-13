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
optimizeModule args (declarations, genv) =
  em $ rm $ map optimizeDeclaration $ markTopModule declarations
  where
  rm = if keep_unused args then id else remUnusedAbs
  em = if unroll_inheritance args then flip (curry expModule) genv else id

optimizeDeclaration :: IDeclaration -> IDeclaration
optimizeDeclaration x = case x of
  IClaferDecl clafer -> IClaferDecl $ optimizeClafer (1, ExIntegerNum 1) clafer
  IConstDecl constraint  -> x


optimizeClafer :: Interval -> IClafer -> IClafer
optimizeClafer interval clafer = clafer {glCard = glCard',
  elements = map (optimizeElement glCard') $ elements clafer}
  where
  glCard' = optimizeCard (fromJust $ card clafer) interval


optimizeCard :: Interval -> Interval -> Interval
optimizeCard (m, n) (m', n') = (min m m', maxEx n n')
  where
  maxEx ExIntegerAst _ = ExIntegerAst
  maxEx _ ExIntegerAst = ExIntegerAst
  maxEx (ExIntegerNum m) (ExIntegerNum n) = ExIntegerNum $ max m n


optimizeElement :: Interval -> IElement -> IElement
optimizeElement interval x = case x of
  ISubclafer clafer  -> ISubclafer $ optimizeClafer interval clafer
  ISubconstraint constraint  -> x

-- -----------------------------------------------------------------------------

remUnusedAbs :: IModule -> IModule
remUnusedAbs declarations = declarations \\ unusedAbs
  where
  unusedAbs = map IClaferDecl $ findUnusedAbs clafers $ map uid $
              filter (not.isAbstract) clafers
  clafers   = toClafers declarations


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

expModule :: (IModule, GEnv) -> IModule
expModule (declarations, genv) =
  evalState (mapM expDeclaration declarations) genv


expDeclaration x = case x of
  IClaferDecl clafer  -> IClaferDecl `liftM` expClafer clafer
  IConstDecl constraint  -> IConstDecl `liftM` expLExp constraint


expClafer clafer = do
  super' <- expSuper $ super clafer
  elements' <- mapM expElement $ elements clafer
  return $ clafer {super = super', elements = elements'}


expSuper x = case x of
  ISuper False _ -> return x
  ISuper True sexps -> ISuper True `liftM` mapM expSExp sexps


expElement x = case x of
  ISubclafer clafer  -> ISubclafer `liftM` expClafer clafer
  ISubconstraint constraint  -> ISubconstraint `liftM` expLExp constraint


expLExp x = case x of
  IEIff lexp0 lexp  -> eLExp IEIff lexp0 lexp
  IEImpliesElse lexp0 lexp Nothing  ->
    eLExp (\l0 l -> IEImpliesElse l0 l Nothing) lexp0 lexp
  IEImpliesElse lexp0 lexp1 (Just lexp)  -> do
    lexp0' <- expLExp lexp0
    lexp1' <- expLExp lexp1
    lexp'  <- expLExp lexp
    return $ IEImpliesElse lexp0' lexp1' $ Just lexp'
  IEOr lexp0 lexp  -> eLExp IEOr lexp0 lexp
  IEXor lexp0 lexp  -> eLExp IEXor lexp0 lexp
  IEAnd lexp0 lexp  -> eLExp IEAnd lexp0 lexp
  IENeg lexp  -> IENeg `liftM` expLExp lexp
  IETerm term  -> IETerm `liftM` expTerm term
  where
  eLExp cons lexp0 lexp = mkExp cons expLExp lexp0 lexp


mkExp cons f exp0 exp = do
    exp0' <- f exp0
    exp'  <- f exp
    return $ cons exp0' exp'


expTerm x = case x of
  ITermCmpExp cmpexp t -> (\c -> ITermCmpExp c t) `liftM` expCmpExp cmpexp
  ITermQuantSet quant sexp -> ITermQuantSet quant `liftM` expSExp sexp
  ITermQuantDeclExp decls lexp -> do
    decls' <- mapM expDecl decls
    lexp' <- expLExp lexp
    return $ ITermQuantDeclExp decls' lexp'


expDecl x = case x of
  IDecl exquant disj locids sexp -> IDecl exquant disj locids `liftM` expSExp sexp

expCmpExp x = case x of
  IELt exp0 exp  -> eExp IELt exp0 exp
  IEGt exp0 exp  -> eExp IEGt exp0 exp
  IEEq exp0 exp  -> eExp IEEq exp0 exp
  IEREq exp0 exp  -> eExp IEREq exp0 exp
  IELte exp0 exp  -> eExp IELte exp0 exp
  IEGte exp0 exp  -> eExp IEGte exp0 exp
  IENeq exp0 exp  -> eExp IENeq exp0 exp
  IERNeq exp0 exp  -> eExp IERNeq exp0 exp
  IEIn exp0 exp  -> eExp IEIn exp0 exp
  IENin exp0 exp  -> eExp IENin exp0 exp
  where
  eExp cons exp0 exp = mkExp cons expExp exp0 exp


expExp x = case x of
  IESetExp sexp  -> IESetExp `liftM` expSExp sexp
  _ -> return x


expSExp x = case x of
  ISExpUnion sexp0 sexp  -> eSExp ISExpUnion sexp0 sexp
  ISExpIntersection sexp0 sexp  -> eSExp ISExpIntersection sexp0 sexp
  ISExpDomain sexp0 sexp  -> eSExp ISExpDomain sexp0 sexp
  ISExpRange sexp0 sexp  -> eSExp ISExpRange sexp0 sexp
  ISExpJoin sexp0 sexp  -> expNav x
  ISExpIdent id t -> expNav x
  where
  eSExp cons sexp0 sexp = mkExp cons expSExp sexp0 sexp


expNav x = do
  xs <- split' x return
  xs' <- mapM (expNav' "") xs
  return $ mkUnion $ map fst xs'


expNav' context x = case x of
  ISExpJoin sexp0 sexp  -> do
    (sexp0', context') <- expNav' context sexp0
    (sexp', context'') <- expNav' context' sexp
    return (ISExpJoin sexp0' sexp', context'')
  ISExpIdent id t -> do
    st <- gets stable
    if Map.member id st
      then do
        let impls  = (Map.!) st id
        let (impls', context') = maybe (impls, "")
             (\x -> ([[head x]], head x)) $
             find (\x -> context == (head.tail) x) impls
        return (mkUnion $ map (\x -> ISExpIdent x t) $ map head impls',
                context')
      else do
        return (x, id)


mkUnion (x:[]) = x
mkUnion xs = foldl1 ISExpUnion xs


split' x f = case x of
  ISExpJoin sexp0 sexp  -> split' sexp0 (\s -> f $ ISExpJoin s sexp)
  ISExpIdent id t -> do
    st <- gets stable
    mapM f $ map (flip ISExpIdent t) $ maybe [id] (map head) $ Map.lookup id st

-- -----------------------------------------------------------------------------
-- checking if all clafers have unique names and don't extend other clafers

allUnique :: IModule -> Bool
allUnique declarations = and un && (null $
  filter (\xs -> 1 < length xs) $ group $ sort $ concat idents)
  where
  (un, idents) = unzip $ map allUniqueDeclaration declarations


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
findDupModule args declarations
  | check_duplicates args = findDupModule' declarations
  | otherwise             = declarations


findDupModule' :: IModule -> IModule
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

markTopModule :: IModule -> IModule
markTopModule declarations =
  map (markTopDeclaration (
      [this, parent, children, strType, intType, integerType] ++
      (map uid $ toClafers declarations))) declarations


markTopDeclaration :: [String] -> IDeclaration -> IDeclaration
markTopDeclaration clafers x = case x of
  IClaferDecl clafer  -> IClaferDecl $ markTopClafer clafers clafer
  IConstDecl constraint  -> IConstDecl $ markTopLExp clafers constraint


markTopClafer :: [String] -> IClafer -> IClafer
markTopClafer clafers clafer =
  clafer {super = markTopSuper clafers $ super clafer, 
          elements = map (markTopElement clafers) $ elements clafer}


markTopSuper :: [String] -> ISuper -> ISuper
markTopSuper clafers x = x{supers = map (markTopSExp clafers) $ supers x}


markTopElement :: [String] -> IElement -> IElement
markTopElement clafers x = case x of
  ISubclafer clafer  -> ISubclafer $ markTopClafer clafers clafer
  ISubconstraint constraint  -> ISubconstraint $ markTopLExp clafers constraint


markTopLExp :: [String] -> ILExp -> ILExp
markTopLExp clafers x = case x of
  IEIff lexp0 lexp  -> on IEIff (markTopLExp clafers) lexp0 lexp
  IEImpliesElse lexp0 lexp Nothing  -> on (\l0 l -> IEImpliesElse l0 l Nothing)
                                       (markTopLExp clafers) lexp0 lexp
  IEImpliesElse lexp0 lexp1 (Just lexp)  ->
      on (\l0 l1 -> IEImpliesElse l0 l1 $ Just $ markTopLExp clafers lexp)
      (markTopLExp clafers) lexp0 lexp1
  IEOr lexp0 lexp  -> on IEOr (markTopLExp clafers) lexp0 lexp
  IEXor lexp0 lexp  -> on IEXor (markTopLExp clafers) lexp0 lexp
  IEAnd lexp0 lexp  -> on IEAnd (markTopLExp clafers) lexp0 lexp
  IENeg lexp  -> IENeg $ markTopLExp clafers lexp
  IETerm term  -> IETerm $ markTopTerm clafers term


markTopTerm :: [String] -> ITerm -> ITerm
markTopTerm clafers x = case x of
  ITermCmpExp cmpexp t -> ITermCmpExp (markTopCmpExp clafers cmpexp) t
  ITermQuantSet quant sexp -> ITermQuantSet quant $ markTopSExp clafers sexp
  ITermQuantDeclExp decl lexp -> ITermQuantDeclExp (map (markTopDecl clafers) decl) $ markTopLExp ((decl >>= decls) ++ clafers) lexp


markTopCmpExp :: [String] -> ICmpExp -> ICmpExp
markTopCmpExp clafers x = case x of
  IELt exp0 exp  -> on IELt (markTopExp clafers) exp0 exp
  IEGt exp0 exp  -> on IEGt (markTopExp clafers) exp0 exp
  IEEq exp0 exp  -> on IEEq (markTopExp clafers) exp0 exp
  IEREq exp0 exp  -> on IEREq (markTopExp clafers) exp0 exp
  IELte exp0 exp  -> on IELte (markTopExp clafers) exp0 exp
  IEGte exp0 exp  -> on IEGte (markTopExp clafers) exp0 exp
  IENeq exp0 exp  -> on IENeq (markTopExp clafers) exp0 exp
  IERNeq exp0 exp  -> on IERNeq (markTopExp clafers) exp0 exp
  IEIn exp0 exp  -> on IEIn (markTopExp clafers) exp0 exp
  IENin exp0 exp  -> on IENin (markTopExp clafers) exp0 exp


markTopDecl :: [String] -> IDecl -> IDecl
markTopDecl clafers x = case x of
  IDecl exquant disj locids sexp -> IDecl exquant disj locids $ markTopSExp clafers sexp


markTopExp :: [String] -> IExp -> IExp
markTopExp clafers x = case x of
  IESetExp sexp  -> IESetExp $ markTopSExp clafers sexp
  IENumExp aexp -> IENumExp $ markTopAExp clafers aexp
  IEStrExp strexp -> x


markTopSExp :: [String] -> ISExp -> ISExp
markTopSExp clafers x = case x of
  ISExpUnion sexp0 sexp -> on ISExpUnion res sexp0 sexp
  ISExpIntersection sexp0 sexp  -> on ISExpIntersection res sexp0 sexp
  ISExpDomain sexp0 sexp  -> on ISExpDomain res sexp0 sexp
  ISExpRange sexp0 sexp  -> on ISExpRange res sexp0 sexp
  ISExpJoin sexp0 sexp -> ISExpJoin (res sexp0) sexp
  ISExpIdent sident _ -> ISExpIdent sident $ sident `elem` clafers
  where
  res = markTopSExp clafers


markTopAExp :: [String] -> IAExp -> IAExp
markTopAExp clafers x = case x of
  IEAdd aexp0 aexp -> on IEAdd (markTopAExp clafers) aexp0 aexp
  IESub aexp0 aexp -> on IESub (markTopAExp clafers) aexp0 aexp
  IEMul aexp0 aexp -> on IEMul (markTopAExp clafers) aexp0 aexp
  IEUmn aexp -> IEUmn $ markTopAExp clafers aexp
  IECSetExp sexp -> IECSetExp $ markTopSExp clafers sexp
  IEInt n    -> x