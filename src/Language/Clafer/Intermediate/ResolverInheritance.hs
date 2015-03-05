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
import Language.Clafer.Front.AbsClafer
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ResolverName


-- | Resolve Non-overlapping inheritance
resolveNModule :: (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveNModule (imodule, genv') =
  do
    let decls' = _mDecls imodule
    decls'' <- mapM (resolveNElement decls') decls'
    let imodule' = imodule{_mDecls = decls''}
    return
      ( imodule'
      , genv'{sClafers = bfs toNodeShallow $ toClafers decls'', uidClaferMap = createUidIClaferMap imodule'})



resolveNClafer :: [IElement] -> IClafer -> Resolve IClafer
resolveNClafer declarations clafer =
  do
    (super', superIClafer')    <- resolveNSuper declarations $ _super clafer
    elements' <- mapM (resolveNElement declarations) $ _elements clafer
    return $ clafer {_super = super',
            _elements = elements'}


resolveNSuper :: [IElement] -> Maybe PExp -> Resolve (Maybe PExp, Maybe IClafer)
resolveNSuper _ Nothing = return (Nothing, Nothing)
resolveNSuper declarations (Just (PExp _ pid' pos' (IClaferId _ id' _ _))) =
    if isPrimitive id'
      then throwError $ SemanticErr pos' $ "Primitive types are not allowed as super types: " ++ id'
      else do
        r <- resolveN pos' declarations id'
        (id'', [superClafer']) <- case r of
          Nothing -> throwError $ SemanticErr pos' $ "No superclafer found: " ++ id'
          Just m  -> return m
        return $ (Just $ PExp (Just $ TClafer [id'']) pid' pos' (IClaferId "" id'' (isTopLevel superClafer') (Just $ id''))
                 , Just superClafer')
resolveNSuper _ x = return (x, Nothing)


resolveNElement :: [IElement] -> IElement -> Resolve IElement
resolveNElement declarations x = case x of
  IEClafer clafer  -> IEClafer <$> resolveNClafer declarations clafer
  IEConstraint _ _  -> return x
  IEGoal _ _ -> return x

resolveN :: Span -> [IElement] -> String -> Resolve (Maybe (String, [IClafer]))
resolveN pos' declarations id' =
  findUnique pos' id' $ map (\x -> (x, [x])) $ filter _isAbstract $ bfsClafers $
    toClafers declarations

-- | Resolve overlapping inheritance
resolveOModule :: (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveOModule (imodule, genv') =
  do
    let decls' = _mDecls imodule
    decls'' <- mapM (resolveOElement (defSEnv genv' decls')) decls'
    let imodule' = imodule{_mDecls = decls''}
    return ( imodule'
           , genv'{sClafers = bfs toNodeShallow $ toClafers decls'', uidClaferMap = createUidIClaferMap imodule'})


resolveOClafer :: SEnv -> IClafer -> Resolve IClafer
resolveOClafer env clafer =
  do
    reference' <- resolveOReference env {context = Just clafer} $ _reference clafer
    elements' <- mapM (resolveOElement env {context = Just clafer}) $ _elements clafer
    return $ clafer {_reference = reference', _elements = elements'}


resolveOReference :: SEnv -> Maybe IReference -> Resolve (Maybe IReference)
resolveOReference _   Nothing                      = return Nothing
resolveOReference env (Just (IReference is' exp')) = Just <$> IReference is' <$> resolvePExp env exp'


resolveOElement :: SEnv -> IElement -> Resolve IElement
resolveOElement env x = case x of
  IEClafer clafer  -> IEClafer <$> resolveOClafer env clafer
  IEConstraint _ _ -> return x
  IEGoal _ _ -> return x


-- | Resolve inherited and default cardinalities
analyzeModule :: (IModule, GEnv) -> IModule
analyzeModule (imodule, genv') =
  imodule{_mDecls = map (analyzeElement (defSEnv genv' decls')) decls'}
  where
  decls' = _mDecls imodule


analyzeClafer :: SEnv -> IClafer -> IClafer
analyzeClafer env clafer =
  clafer' {_elements = map (analyzeElement env {context = Just clafer'}) $
           _elements clafer'}
  where
  clafer' = clafer {_gcard = analyzeGCard env clafer,
                    _card  = analyzeCard  env clafer}


-- only for non-overlapping
analyzeGCard :: SEnv -> IClafer -> Maybe IGCard
analyzeGCard env clafer = gcard' `mplus` (Just $ IGCard False (0, -1))
  where
  gcard'
    | isNothing $ _super clafer = _gcard clafer
    | otherwise                 = listToMaybe $ mapMaybe _gcard $ findHierarchy getSuper (uidClaferMap $ genv env) clafer


analyzeCard :: SEnv -> IClafer -> Maybe Interval
analyzeCard env clafer = _card clafer `mplus` Just card'
  where
  card'
    | _isAbstract clafer = (0, -1)
    | (isJust $ context env) && pGcard == (0, -1)
      || (isTopLevel clafer) = (1, 1)
    | otherwise = (0, 1)
  pGcard = _interval $ fromJust $ _gcard $ fromJust $ context env

analyzeElement :: SEnv -> IElement -> IElement
analyzeElement env x = case x of
  IEClafer clafer  -> IEClafer $ analyzeClafer env clafer
  IEConstraint _ _ -> x
  IEGoal _ _ -> x

-- | Expand inheritance
resolveEModule :: (IModule, GEnv) -> (IModule, GEnv)
resolveEModule (imodule, genv') = (imodule', newGenv)
  where
  decls' = _mDecls imodule
  imodule' = imodule{_mDecls = decls''}
  newGenv = genv''{uidClaferMap = createUidIClaferMap imodule'}
  (decls'', genv'') = runState (mapM (resolveEElement []
                                    (unrollableModule imodule)
                                    False decls') decls') genv'

-- -----------------------------------------------------------------------------
unrollableModule :: IModule -> [String]
unrollableModule imodule = getDirUnrollables $
  mapMaybe unrollabeDeclaration $ _mDecls imodule

unrollabeDeclaration :: IElement -> Maybe (String, [String])
unrollabeDeclaration x = case x of
  IEClafer clafer -> if _isAbstract clafer
                        then Just (_uid clafer, unrollableClafer clafer)
                        else Nothing
  IEConstraint _ _ -> Nothing
  IEGoal _ _ -> Nothing

unrollableClafer :: IClafer -> [String]
unrollableClafer clafer = (getSuper clafer) ++ deps
  where
  deps = (toClafers $ _elements clafer) >>= unrollableClafer


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
  uidClaferMap' <- gets uidClaferMap
  clafer' <- renameClafer absAncestor (_parentUID clafer) clafer
  let predecessors' = _uid clafer' : predecessors
  (sElements, super', superList) <-
      resolveEInheritance predecessors' unrollables absAncestor declarations
        (findHierarchy getSuper uidClaferMap' clafer)
  let sClafer = Map.fromList $ zip (map _uid superList) $ repeat [predecessors']
  modify (\e -> e {stable = Map.delete "clafer" $
                            Map.unionWith ((nub.).(++)) sClafer $
                            stable e})
  elements' <-
      mapM (resolveEElement predecessors' unrollables absAncestor declarations)
            $ _elements clafer
  return $ clafer' {_super = super', _elements = elements' ++ sElements}

renameClafer :: MonadState GEnv m => Bool -> UID -> IClafer -> m IClafer
renameClafer False _ clafer = return clafer
renameClafer True  puid clafer = renameClafer' puid clafer

renameClafer' :: MonadState GEnv m => UID -> IClafer -> m IClafer
renameClafer' puid clafer = do
  let claferIdent = _ident clafer
  identCountMap' <- gets identCountMap
  let count = Map.findWithDefault 0 claferIdent identCountMap'
  modify (\e -> e { identCountMap = Map.alter (\_ -> Just (count+1)) claferIdent identCountMap' } )
  return $ clafer { _uid = genId claferIdent count, _parentUID = puid }

genId :: String -> Int -> String
genId id' count = concat ["c", show count, "_",  id']

resolveEInheritance :: MonadState GEnv m => [String] -> [String] -> Bool -> [IElement] -> [IClafer]  -> m ([IElement], Maybe PExp, [IClafer])
resolveEInheritance predecessors unrollables absAncestor declarations allSuper = do
    let superList = (if absAncestor then id else tail) allSuper
    let unrollSuper = filter (\s -> _uid s `notElem` unrollables) $ tail allSuper
    elements' <-
        mapM (resolveEElement predecessors unrollables True declarations) $
             unrollSuper >>= _elements

    let super' = case (`elem` unrollables) <$> getSuper clafer of
                    [True] -> _super clafer
                    _      ->  Nothing
    return (elements', super', superList)
  where
  clafer = head allSuper

resolveEElement :: MonadState GEnv m => [String] -> [String] -> Bool -> [IElement] -> IElement -> m IElement
resolveEElement predecessors unrollables absAncestor declarations x = case x of
  IEClafer clafer  -> if _isAbstract clafer then return x else IEClafer `liftM`
    resolveEClafer predecessors unrollables absAncestor declarations clafer
  IEConstraint _ _  -> return x
  IEGoal _ _ -> return x

-- -----------------------------------------------------------------------------

resolveRedefinition :: (IModule, GEnv) -> Resolve IModule
resolveRedefinition    (iModule, _)  =
  if (not $ null improperClafers)
    then throwError $ SemanticErr noSpan ("Refinement errors in the following places:\n" ++  improperClafers)
    else return iModule
  where
    uidIClaferMap' = createUidIClaferMap iModule
    improperClafers :: String
    improperClafers = foldMapIR isImproper iModule

    isImproper :: Ir -> String
    isImproper (IRClafer claf@IClafer{_cinPos = (Span (Pos l c) _) ,_ident=i}) =
      let
        match = matchNestedInheritance uidIClaferMap' claf
      in
        if (isProperNesting uidIClaferMap' match)
        then let
               (properCardinalityRefinement, properBagToSetRefinement, properTargetSubtyping) = isProperRefinement uidIClaferMap' match
             in if (properCardinalityRefinement)
             then if (properBagToSetRefinement)
                  then if (properTargetSubtyping)
                       then ""
                       else ("Improper target subtyping for clafer '" ++ i ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n")
                  else ("Improper bag to set refinement for clafer '" ++ i ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n")
             else ("Improper cardinality refinement for clafer '" ++ i ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n")
        else ("Improperly nested clafer '" ++ i ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n")
    isImproper _ = ""
