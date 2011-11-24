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
module Intermediate.ResolverInheritance where

import Monad
import Control.Monad.State
import Data.Maybe
import Data.Graph
import Data.Tree
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Common
import Front.Absclafer
import Intermediate.Intclafer
import Intermediate.ResolverName

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
  ISuper False [PExp _ pid (IClaferId _ id isTop)] ->
    if isPrimitive id || id == "clafer"
      then x else ISuper False [idToPExp pid "" id' isTop]
    where
    id' = fst $ fromMaybe (error $ "No superclafer found: " ++ id) $
          resolveN declarations id
  _ -> x


resolveNElement :: [IElement] -> IElement -> IElement
resolveNElement declarations x = case x of
  IEClafer clafer  -> IEClafer $ resolveNClafer declarations clafer
  IEConstraint _ _  -> x


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
  ISuper True exps -> ISuper True $ map (resolvePExp env) exps
  _ -> x


resolveOElement :: SEnv -> IElement -> IElement
resolveOElement env x = case x of
  IEClafer clafer  -> IEClafer $ resolveOClafer env clafer
  IEConstraint _ _ -> x

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
analyzeGCard env clafer = gcard' `mplus` (Just $ IGCard False (0, ExIntegerAst))
  where
  gcard'
    | isOverlapping $ super clafer = gcard clafer
    | otherwise                    = listToMaybe $ mapMaybe gcard $
                                     findHierarchy (clafers env) clafer


analyzeCard :: SEnv -> IClafer -> Maybe Interval
analyzeCard env clafer = card clafer `mplus` Just card'
  where
  card'
    | isAbstract clafer                          = (0, ExIntegerAst)
    | (isJust $ context env) && isKeyword pGcard = (0, ExIntegerNum 1)
    | otherwise                                  = (1, ExIntegerNum 1)
  pGcard = fromJust $ gcard $ fromJust $ context env


analyzeElement :: SEnv -> IElement -> IElement
analyzeElement env x = case x of
  IEClafer clafer  -> IEClafer $ analyzeClafer env clafer
  IEConstraint _ _ -> x

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
        (findHierarchy sClafers' clafer)
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
                 else ISuper False [idToPExp "" "" "clafer" False]
    return (elements', super', superList)
  where
  clafer = head allSuper


resolveEElement predecessors unrollables absAncestor declarations x = case x of
  IEClafer clafer  -> if isAbstract clafer then return x else IEClafer `liftM`
    resolveEClafer predecessors unrollables absAncestor declarations clafer
  IEConstraint _ _  -> return x