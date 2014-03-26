{-# LANGUAGE FlexibleContexts #-}
{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Optimizer.Optimizer where

import Data.Maybe
import Data.List
import Control.Monad.State
import qualified Data.Map as Map

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Intermediate.Intclafer

-- | Apply optimizations for unused abstract clafers and inheritance flattening
optimizeModule :: ClaferArgs -> (IModule, GEnv) -> IModule
optimizeModule args (imodule, genv) =
  imodule{_mDecls = em $ rm $ map (optimizeElement (1, 1)) $
                   markTopModule $ _mDecls imodule}
  where
  rm = if keep_unused args then makeZeroUnusedAbs else remUnusedAbs
  em = if flatten_inheritance args then flip (curry expModule) genv else id

optimizeElement :: Interval -> IElement -> IElement
optimizeElement interval' x = case x of
  IEClafer c  -> IEClafer $ optimizeClafer interval' c
  IEConstraint _ _  -> x
  IEGoal _ _ -> x

optimizeClafer :: Interval -> IClafer -> IClafer
optimizeClafer interval' c = c {_glCard = glCard',
  _elements = map (optimizeElement glCard') $ _elements c}
  where
  glCard' = multInt (fromJust $ _card c) interval'


multInt :: Interval -> Interval -> Interval
multInt (m, n) (m', n') = (m * m', multExInt n n')

multExInt :: Integer -> Integer -> Integer
multExInt 0 _ = 0
multExInt _  0 = 0
multExInt m n = if m == -1 || n == -1 then -1 else m * n

-- -----------------------------------------------------------------------------

makeZeroUnusedAbs :: [IElement] -> [IElement]
makeZeroUnusedAbs decls' = map (\x -> if (x `elem` unusedAbs) then IEClafer (getIClafer x){_card = Just (0, 0)} else x) decls'
  where
  unusedAbs = map IEClafer $ findUnusedAbs clafers $ map _uid $
              filter (not._isAbstract) clafers
  clafers   = toClafers decls' 
  getIClafer (IEClafer c) = c
  getIClafer _ = error "Function makeZeroUnusedAbs from Optimizer expected paramter of type IClafer got a differnt IElement" --This should never happen

remUnusedAbs :: [IElement] -> [IElement]
remUnusedAbs decls' = decls' \\ unusedAbs
  where
  unusedAbs = map IEClafer $ findUnusedAbs clafers $ map _uid $
              filter (not._isAbstract) clafers
  clafers   = toClafers decls'


findUnusedAbs :: [IClafer] -> [String] -> [IClafer]
findUnusedAbs maybeUsed [] = maybeUsed
findUnusedAbs [] _   = []
findUnusedAbs maybeUsed used = findUnusedAbs maybeUsed' $ getUniqExtended used'
  where
  (used', maybeUsed') = partition (\c -> _uid c `elem` used) maybeUsed

getUniqExtended :: [IClafer] -> [String]
getUniqExtended used = nub $ used >>= getExtended


getExtended :: IClafer -> [String]
getExtended c =
  sName ++ ((getSubclafers $ _elements c) >>= getExtended)
  where
  sName = if not $ _isOverlapping $ _super c then [getSuper c] else []

-- -----------------------------------------------------------------------------
-- inheritance  expansions

expModule :: ([IElement], GEnv) -> [IElement]
expModule (decls', genv) = evalState (mapM expElement decls') genv

expClafer :: MonadState GEnv m => IClafer -> m IClafer
expClafer claf = do
  super' <- expSuper $ _super claf
  elements' <- mapM expElement $ _elements claf
  return $ claf {_super = super', _elements = elements'}

expSuper :: MonadState GEnv m => ISuper -> m ISuper
expSuper x = case x of
  ISuper False _ -> return x
  ISuper True pexps -> ISuper True `liftM` mapM expPExp pexps

expElement :: MonadState GEnv m => IElement -> m IElement
expElement x = case x of
  IEClafer claf  -> IEClafer `liftM` expClafer claf
  IEConstraint isHard' constraint  -> IEConstraint isHard' `liftM` expPExp constraint
  IEGoal isMaximize' goal -> IEGoal isMaximize' `liftM` expPExp goal

expPExp :: MonadState GEnv m => PExp -> m PExp
expPExp (PExp t pid' pos' exp') = PExp t pid' pos' `liftM` expIExp exp'

expIExp :: MonadState GEnv m => IExp -> m IExp
expIExp x = case x of
  IDeclPExp quant' decls' pexp -> do
    decls'' <- mapM expDecl decls'
    pexp' <- expPExp pexp
    return $ IDeclPExp quant' decls'' pexp'
  IFunExp op' exps' -> if op' == iJoin
                     then expNav x else IFunExp op' `liftM` mapM expPExp exps'
  IClaferId _ _ _ -> expNav x
  _ -> return x

expDecl :: MonadState GEnv m => IDecl -> m IDecl
expDecl x = case x of
  IDecl disj locids pexp -> IDecl disj locids `liftM` expPExp pexp

expNav :: MonadState GEnv m => IExp -> m IExp
expNav x = do
  xs <- split' x return
  xs' <- mapM (expNav' "") xs
  return $ mkIFunExp iUnion $ map fst xs'

expNav' :: MonadState GEnv m => String -> IExp -> m (IExp, String)
expNav' context (IFunExp _ (p0:p:_)) = do    
  (exp0', context') <- expNav' context  $ Language.Clafer.Intermediate.Intclafer._exp p0
  (exp', context'') <- expNav' context' $ Language.Clafer.Intermediate.Intclafer._exp p
  return (IFunExp iJoin [ p0 {Language.Clafer.Intermediate.Intclafer._exp = exp0'}
                        , p  {Language.Clafer.Intermediate.Intclafer._exp = exp'}], context'')
expNav' context x@(IClaferId modName' id' isTop') = do
  st <- gets stable
  if Map.member id' st
    then do
      let impls  = (Map.!) st id'
      let (impls', context') = maybe (impls, "")
           (\y -> ([[head y]], head y)) $
           find (\z -> context == (head.tail) z) impls
      return (mkIFunExp iUnion $ map (\u -> IClaferId modName' u isTop') $
              map head impls', context')
    else do
      return (x, id')
expNav' _ _ = error "Function expNav' from Optimizer expects an argument of type ClaferId or IFunExp but was given another IExp"

split' :: MonadState GEnv m => IExp -> (IExp -> m IExp) -> m [IExp] 
split'(IFunExp _ (p:pexp:_)) f =
    split' (Language.Clafer.Intermediate.Intclafer._exp p) (\s -> f $ IFunExp iJoin
      [p {Language.Clafer.Intermediate.Intclafer._exp = s}, pexp])
split' (IClaferId modName' id' isTop') f = do
    st <- gets stable
    mapM f $ map (\y -> IClaferId modName' y isTop') $ maybe [id'] (map head) $ Map.lookup id' st
split' _ _ = error "Function split' from Optimizer expects an argument of type ClaferId or IFunExp but was given another IExp"

-- -----------------------------------------------------------------------------
-- checking if all clafers have unique names and don't extend other clafers

allUnique :: IModule -> Bool
allUnique imodule = and un && (null $
  filter (\xs -> 1 < length xs) $ group $ sort $ concat idents) && identsOk
  where
  (un, idents) = unzip $ map allUniqueElement $ _mDecls imodule
  identsOk     = and $ map (checkConstraintElement (concat idents)) $ _mDecls imodule

allUniqueClafer :: IClafer -> (Bool, [String])
allUniqueClafer claf =
  (getSuper claf `elem` "clafer" : primitiveTypes  && and un,
   _ident claf : concat idents)
  where
  (un, idents) = unzip $ map allUniqueElement $ _elements claf

allUniqueElement :: IElement -> (Bool, [String])
allUniqueElement x = case x of
  IEClafer claf -> allUniqueClafer claf
  IEConstraint _ _ -> (True, [])
  IEGoal _ _ -> (True, [])

checkConstraintElement :: [String] -> IElement -> Bool
checkConstraintElement idents x = case x of
  IEClafer claf -> and $ map (checkConstraintElement idents) $ _elements claf
  IEConstraint _ pexp -> checkConstraintPExp idents pexp 
  IEGoal _ _ ->  True

checkConstraintPExp :: [String] -> PExp -> Bool
checkConstraintPExp idents pexp = checkConstraintIExp idents $
                                  Language.Clafer.Intermediate.Intclafer._exp pexp

checkConstraintIExp :: [String] -> IExp -> Bool
checkConstraintIExp idents x = case x of
   IDeclPExp _ oDecls' pexp ->
     checkConstraintPExp ((oDecls' >>= (checkConstraintIDecl idents)) ++ idents) pexp
   IClaferId _ ident' _ -> if ident' `elem` (specialNames ++ idents) then True
                          else error $ "optimizer: " ++ ident' ++ " not found"
   _ -> True

checkConstraintIDecl :: [String] -> IDecl -> [String]
checkConstraintIDecl idents (IDecl _ decls' pexp)
  | checkConstraintPExp idents pexp = decls'
  | otherwise                       = []

-- -----------------------------------------------------------------------------
findDupModule :: ClaferArgs -> IModule -> IModule
findDupModule args imodule = imodule{_mDecls = decls'}
  where
  decls'' = _mDecls imodule
  decls'
    | check_duplicates args = findDupModule' decls''
    | otherwise                        = decls''


findDupModule' :: [IElement] -> [IElement]
findDupModule' declarations
  | null dups = map findDupElement declarations
  | otherwise = error $ show dups
  where
  dups = findDuplicates $ toClafers declarations

findDupClafer :: IClafer -> IClafer
findDupClafer claf = if null dups
  then claf{_elements = map findDupElement $ _elements claf}
  else error $ (show $ _ident claf) ++ show dups
  where
  dups = findDuplicates $ getSubclafers $ _elements claf

findDupElement :: IElement -> IElement
findDupElement x = case x of
  IEClafer claf -> IEClafer $ findDupClafer claf
  IEConstraint _ _ -> x
  IEGoal _ _ -> x


findDuplicates :: [IClafer] -> [String]
findDuplicates clafers =
  map head $ filter (\xs -> 1 < length xs) $ group $ sort $ map _ident clafers

-- -----------------------------------------------------------------------------
-- marks top clafers

markTopModule :: [IElement] -> [IElement]
markTopModule decls' = map (markTopElement (
      [this, parent, children, strType, intType, integerType] ++
      (map _uid $ toClafers decls'))) decls'


markTopClafer :: [String] -> IClafer -> IClafer
markTopClafer clafers c =
  c {_super = markTopSuper clafers $ _super c, 
     _elements = map (markTopElement clafers) $ _elements c}


markTopSuper :: [String] -> ISuper -> ISuper
markTopSuper clafers x = x{_supers = map (markTopPExp clafers) $ _supers x}


markTopElement :: [String] -> IElement -> IElement
markTopElement clafers x = case x of
  IEClafer c  -> IEClafer $ markTopClafer clafers c
  IEConstraint isHard' pexp  -> IEConstraint isHard' $ markTopPExp clafers pexp
  IEGoal isMaximize' pexp -> IEGoal isMaximize' $ markTopPExp clafers pexp

markTopPExp :: [String] -> PExp -> PExp
markTopPExp clafers pexp =
  pexp {Language.Clafer.Intermediate.Intclafer._exp = markTopIExp clafers $
        Language.Clafer.Intermediate.Intclafer._exp pexp}


markTopIExp :: [String] -> IExp -> IExp
markTopIExp clafers x = case x of
  IDeclPExp quant' decl pexp -> IDeclPExp quant' (map (markTopDecl clafers) decl)
                                (markTopPExp ((decl >>= _decls) ++ clafers) pexp)
  IFunExp op' exps' -> IFunExp op' $ map (markTopPExp clafers) exps'
  IClaferId modName' sident' _ ->
    IClaferId modName' sident' $ sident' `elem` clafers
  _ -> x


markTopDecl :: [String] -> IDecl -> IDecl
markTopDecl clafers x = case x of
  IDecl disj locids pexp -> IDecl disj locids $ markTopPExp clafers pexp
