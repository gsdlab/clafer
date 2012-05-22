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

import Monad
import Control.Monad.State
import Data.Maybe
import Data.Graph
import Data.Tree
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ResolverName

-- -----------------------------------------------------------------------------
-- Non-overlapping inheritance
resolveNModule :: (IModule, GEnv) -> (IModule, GEnv)
resolveNModule (imodule, genv) =
  (imodule{mDecls = decls'}, genv {sClafers = bfs toNodeShallow $ toClafers decls'})
  where
  decls = mDecls imodule
  decls' = map (resolveNElement decls) decls


resolveNClafer :: [IElement] -> IClafer -> IClafer
resolveNClafer declarations clafer =
  clafer {super = resolveNSuper declarations $ super clafer,
          elements = map (resolveNElement declarations) $ elements clafer}


resolveNSuper :: [IElement] -> ISuper -> ISuper
resolveNSuper declarations x = case x of
  ISuper False [PExp _ pid pos (IClaferId _ id isTop)] ->
    if isPrimitive id || id == "clafer"
      then x else ISuper False [idToPExp pid pos "" id' isTop]
    where
    id' = fst $ fromMaybe (error $ "No superclafer found: " ++ id) $
          resolveN declarations id
  _ -> x


resolveNElement :: [IElement] -> IElement -> IElement
resolveNElement declarations x = case x of
  IEClafer clafer  -> IEClafer $ resolveNClafer declarations clafer
  IEConstraint _ _  -> x
  IEGoal _ _ -> x

resolveN :: [IElement] -> String -> Maybe (String, [IClafer])
resolveN declarations id =
  findUnique id $ map (\x -> (x, [x])) $ filter isAbstract $ bfsClafers $
  toClafers declarations

-- -----------------------------------------------------------------------------
-- Overlapping inheritance

resolveOModule :: (IModule, GEnv) -> (IModule, GEnv)
resolveOModule (imodule, genv) =
  (imodule {mDecls = decls'}, genv {sClafers = bfs toNodeShallow $ toClafers decls'})
  where
  decls = mDecls imodule
  decls' = map (resolveOElement (defSEnv genv decls)) decls


resolveOClafer :: SEnv -> IClafer -> IClafer
resolveOClafer env clafer =
  clafer {super = resolveOSuper env {context = Just clafer} $ super clafer,
          elements = map (resolveOElement env {context = Just clafer}) $
          elements clafer}


resolveOSuper :: SEnv -> ISuper -> ISuper
resolveOSuper env x = case x of
  ISuper True exps -> ISuper isOverlap  exps'
    where
    exps'     = map (resolvePExp env) exps
    isOverlap = not (length exps' == 1 && isPrimitive (getSuperId exps'))
  _ -> x


resolveOElement :: SEnv -> IElement -> IElement
resolveOElement env x = case x of
  IEClafer clafer  -> IEClafer $ resolveOClafer env clafer
  IEConstraint _ _ -> x
  IEGoal _ _ -> x
  
-- -----------------------------------------------------------------------------
-- inherited and default cardinalities

analyzeModule :: (IModule, GEnv) -> IModule
analyzeModule (imodule, genv) =
  imodule{mDecls = map (analyzeElement (defSEnv genv decls)) decls}
  where
  decls = mDecls imodule


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
    | isAbstract clafer                          = (0, -1)
    | (isJust $ context env) && isKeyword pGcard = (0, 1)
    | otherwise                                  = (1, 1)
  pGcard = fromJust $ gcard $ fromJust $ context env


analyzeElement :: SEnv -> IElement -> IElement
analyzeElement env x = case x of
  IEClafer clafer  -> IEClafer $ analyzeClafer env clafer
  IEConstraint _ _ -> x
  IEGoal _ _ -> x

-- -----------------------------------------------------------------------------
-- Expand inheritance
resolveEModule :: (IModule, GEnv) -> (IModule, GEnv)
resolveEModule (imodule, genv) = (imodule{mDecls = decls'}, genv')
  where
  decls = mDecls imodule
  (decls', genv') = runState (mapM (resolveEElement []
                                    (unrollableModule imodule)
                                    False decls) decls) genv

-- -----------------------------------------------------------------------------
unrollableModule :: IModule -> [String]
unrollableModule imodule = getDirUnrollables $
  mapMaybe unrollabeDeclaration $ mDecls imodule

unrollabeDeclaration x = case x of
  IEClafer clafer -> if isAbstract clafer
                        then Just (uid clafer, unrollableClafer clafer)
                        else Nothing
  IEConstraint _ _ -> Nothing
  IEGoal _ _ -> Nothing


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
  (graph, v2n, k2v) = graphFromEdges $map (\(c, ss) -> (c, c, ss)) dependencies
  isUnrollable (x:[]) = fst3 x `elem` trd3 x
  isUnrollable _ = True

-- -----------------------------------------------------------------------------
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


renameClafer False clafer = return clafer
renameClafer True  clafer = renameClafer' clafer


renameClafer' clafer = do
  uid' <- genId $ ident clafer
  return $ clafer {uid = uid'}


genId id = do
  modify (\e -> e {num = 1 + num e})
  n <- gets num
  return $ concat ["c", show n, "_",  id]


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
                 else ISuper False [idToPExp "" noPos "" "clafer" False]
    return (elements', super', superList)
  where
  clafer = head allSuper


resolveEElement predecessors unrollables absAncestor declarations x = case x of
  IEClafer clafer  -> if isAbstract clafer then return x else IEClafer `liftM`
    resolveEClafer predecessors unrollables absAncestor declarations clafer
  IEConstraint _ _  -> return x
  IEGoal _ _ -> return x