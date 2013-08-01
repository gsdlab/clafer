{-# LANGUAGE FlexibleContexts #-}
{-
 Copyright (C) 2012 Kacper Bak <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.ResolverInheritance where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import Data.Maybe
import Data.Graph
import Data.Tree
import Data.List
import qualified Data.Map as Map

import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ResolverName
import Prelude hiding (exp)


-- -----------------------------------------------------------------------------
-- Non-overlapping inheritance
resolveNModule :: (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveNModule (imodule, genv') =
  do
    let decls' = mDecls imodule
    decls'' <- mapM (resolveNElement decls') decls'
    return (imodule{mDecls = decls''}, genv' {sClafers = bfs toNodeShallow $ toClafers decls''})
    


resolveNClafer :: [IElement] -> IClafer -> Resolve IClafer
resolveNClafer declarations clafer =
  do
    super'    <- resolveNSuper declarations clafer
    elements' <- mapM (resolveNElement declarations) $ elements clafer
    return $ clafer {super = super',
            elements = elements'}



resolveNSuper :: [IElement] -> IClafer -> Resolve ISuper
resolveNSuper declarations x = case (super x) of
  ISuper False s [PExp _ pid' pos' (IClaferId _ id' isTop')] ->
    if isPrimitive id' || id' == "clafer"
      then return (super x)
      else do
        r <- resolveN x pos' declarations id'
        id'' <- case r of
          Nothing -> throwError $ SemanticErr pos' $ "No superclafer found: " ++ id'
          Just mo  -> return $ fst mo
        return $ ISuper False s [idToPExp pid' pos' "" id'' isTop']
  _ -> return (super x)

resolveNElement :: [IElement] -> IElement -> Resolve IElement
resolveNElement declarations x = case x of
  IEClafer clafer  -> IEClafer <$> resolveNClafer declarations clafer
  IEConstraint _ _  -> return x
  IEGoal _ _ -> return x

resolveN :: IClafer -> Span -> [IElement] -> String -> Resolve (Maybe (String, [IClafer]))
resolveN clafer' pos' declarations id' =
  findUnique pos' id' $ map (\x -> (x, [x])) $ 
    filter (\c -> (isAbstract c) || ((rSpan $ super clafer') == (Just $ cinPos c))) $ 
      bfsClafers $ toClafers declarations

-- -----------------------------------------------------------------------------
-- Overlapping inheritance

resolveOModule :: (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveOModule (imodule, genv') =
  do
    let decls' = mDecls imodule
    decls'' <- mapM (resolveOElement (defSEnv genv' decls')) decls'
    return (imodule {mDecls = decls''}, genv' {sClafers = bfs toNodeShallow $ toClafers decls''})


resolveOClafer :: SEnv -> IClafer -> Resolve IClafer
resolveOClafer env clafer =
  do
    super' <- resolveOSuper env {context = Just clafer} $ super clafer
    elements' <- mapM (resolveOElement env {context = Just clafer}) $ elements clafer
    return $ clafer {super = super', elements = elements'}


resolveOSuper :: SEnv -> ISuper -> Resolve ISuper
resolveOSuper env x = case x of
  ISuper True s exps' -> do
    exps''     <- mapM (resolvePExp env) exps'
    let isOverlap = not (length exps'' == 1 && isPrimitive (getSuperId exps''))
    return $ ISuper isOverlap s exps''
  _ -> return x


resolveOElement :: SEnv -> IElement -> Resolve IElement
resolveOElement env x = case x of
  IEClafer clafer  -> IEClafer <$> resolveOClafer env clafer
  IEConstraint _ _ -> return x
  IEGoal _ _ -> return x
  
-- -----------------------------------------------------------------------------
-- inherited and default cardinalities

analyzeModule :: (IModule, GEnv) -> IModule
analyzeModule (imodule, genv') =
  imodule{mDecls = map (analyzeElement (defSEnv genv' decls')) decls'}
  where
  decls' = mDecls imodule


analyzeClafer :: SEnv -> IClafer -> IClafer
analyzeClafer env clafer =
  clafer' {elements = map (analyzeElement env {context = Just clafer'}) $
           elements clafer'}
  where
  clafer' = clafer {gcard = analyzeGCard env clafer,
                    card  = analyzeCard  env clafer}


-- only for non-overlapping
analyzeGCard :: SEnv -> IClafer -> Maybe IGCard
analyzeGCard env clafer = gcard' `mplus` (Just $ IGCard False (0, -1))
  where
  gcard'
    | isOverlapping $ super clafer = gcard clafer
    | otherwise                    = listToMaybe $ mapMaybe gcard $
                                     findHierarchy getSuper (clafers env) clafer


analyzeCard :: SEnv -> IClafer -> Maybe Interval
analyzeCard env clafer = card clafer `mplus` Just card'
  where
  card'
    | isAbstract clafer = (0, -1)
    | (isJust $ context env) && pGcard == (0, -1) 
      || (isTopLevel $ cinPos clafer) = (1, 1) 
    | otherwise = (0, 1)
  pGcard = interval $ fromJust $ gcard $ fromJust $ context env
  isTopLevel (Span (Pos _ c) _) = c==1
  isTopLevel (Span (PosPos _ _ c) _) = c==1
  isTopLevel (PosSpan _ (Pos _ c) _) = c==1
  isTopLevel (PosSpan _ (PosPos _ _ c) _) = c==1

analyzeElement :: SEnv -> IElement -> IElement
analyzeElement env x = case x of
  IEClafer clafer  -> IEClafer $ analyzeClafer env clafer
  IEConstraint _ _ -> x
  IEGoal _ _ -> x

-- -----------------------------------------------------------------------------
-- Expand inheritance
resolveEModule :: (IModule, GEnv) -> (IModule, GEnv)
resolveEModule (imodule, genv') = (imodule{mDecls = decls''}, genv'')
  where
  decls' = mDecls imodule
  (decls'', genv'') = runState (mapM (resolveEElement []
                                    (unrollableModule imodule)
                                    False decls') decls') genv'

-- -----------------------------------------------------------------------------
unrollableModule :: IModule -> [String]
unrollableModule imodule = getDirUnrollables $
  mapMaybe unrollabeDeclaration $ mDecls imodule

unrollabeDeclaration :: IElement -> Maybe (String, [String])
unrollabeDeclaration x = case x of
  IEClafer clafer -> if isAbstract clafer
                        then Just (uid clafer, unrollableClafer clafer)
                        else Nothing
  IEConstraint _ _ -> Nothing
  IEGoal _ _ -> Nothing

unrollableClafer :: IClafer -> [String]
unrollableClafer clafer
  | isOverlapping $ super clafer = []
  | getSuper clafer == "clafer"  = deps
  | otherwise                    = getSuper clafer : deps
  where
  deps = (toClafers $ elements clafer) >>= unrollableClafer


getDirUnrollables :: [(String, [String])] -> [String]
getDirUnrollables dependencies = (filter isUnrollable $ map (map v2n) $
                                  map flatten (scc graph)) >>= map fst3
  where
  (graph, v2n, _) = graphFromEdges $map (\(c, ss) -> (c, c, ss)) dependencies
  isUnrollable (x:[]) = fst3 x `elem` trd3 x
  isUnrollable _ = True

-- -----------------------------------------------------------------------------
resolveEClafer :: MonadState GEnv m => [String] -> [String] -> Bool -> [IElement] -> IClafer -> m IClafer
resolveEClafer predecessors unrollables absAncestor declarations clafer = do
  sClafers' <- gets sClafers
  clafer' <- renameClafer absAncestor clafer
  let predecessors' = uid clafer' : predecessors
  (sElements, super', superList) <-
      resolveEInheritance predecessors' unrollables absAncestor declarations
        (findHierarchy getSuper sClafers' clafer)
  let sClafer = Map.fromList $ zip (map uid superList) $ repeat [predecessors']
  modify (\e -> e {stable = Map.delete "clafer" $
                            Map.unionWith ((nub.).(++)) sClafer $
                            stable e})
  elements' <-
      mapM (resolveEElement predecessors' unrollables absAncestor declarations)
            $ elements clafer
  return $ clafer' {super = super', elements = elements' ++ sElements}

renameClafer :: MonadState GEnv m => Bool -> IClafer -> m IClafer
renameClafer False clafer = return clafer
renameClafer True  clafer = renameClafer' clafer

renameClafer' :: MonadState GEnv m => IClafer -> m IClafer
renameClafer' clafer = do
  uid' <- genId $ ident clafer
  return $ clafer {uid = uid'}


genId :: MonadState GEnv m => String -> m String
genId id' = do
  modify (\e -> e {num = 1 + num e})
  n <- gets num
  return $ concat ["c", show n, "_",  id']

resolveEInheritance :: MonadState GEnv m => [String] -> [String] -> Bool -> [IElement] -> [IClafer]  -> m ([IElement], ISuper, [IClafer])
resolveEInheritance predecessors unrollables absAncestor declarations allSuper
  | isOverlapping $ super clafer = return ([], super clafer, [clafer])
  | otherwise = do
    let superList = (if absAncestor then id else tail) allSuper
    let unrollSuper = filter (\s -> uid s `notElem` unrollables) $ tail allSuper
    elements' <-
        mapM (resolveEElement predecessors unrollables True declarations) $
             unrollSuper >>= elements
    let super' = if (getSuper clafer `elem` unrollables)
                 then super clafer
                 else ISuper False (rSpan $ super clafer) [idToPExp "" noSpan "" "clafer" False]
    return (elements', super', superList)
  where
  clafer = head allSuper

resolveEElement :: MonadState GEnv m => [String] -> [String] -> Bool -> [IElement] -> IElement -> m IElement
resolveEElement predecessors unrollables absAncestor declarations x = case x of
  IEClafer clafer  -> if isAbstract clafer then return x else IEClafer `liftM`
    resolveEClafer predecessors unrollables absAncestor declarations clafer
  IEConstraint _ _  -> return x
  IEGoal _ _ -> return x