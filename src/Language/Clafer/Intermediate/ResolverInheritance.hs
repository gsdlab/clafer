{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-
 Copyright (C) 2012-2017 Kacper Bak, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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

import           Control.Applicative
import           Control.Lens  ((^.), (&), (%%~), (.~))
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Maybe
import           Data.Graph
import           Data.Tree
import           Data.List
import qualified Data.Map as Map
import           Data.StringMap (StringMap)
import qualified Data.StringMap as SMap
import           Prelude

import           Language.ClaferT
import           Language.Clafer.Common
import           Language.Clafer.Front.AbsClafer
import           Language.Clafer.Intermediate.Intclafer
import           Language.Clafer.Intermediate.ResolverName

-- | Resolve Non-overlapping inheritance
resolveNModule :: (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveNModule (imodule, genv') =
  do
    let
      unresolvedDecls = _mDecls imodule
      abstractClafers = filter _isAbstract $ bfsClafers $ toClafers unresolvedDecls
    resolvedDecls <- mapM (resolveNElement abstractClafers Nothing) unresolvedDecls
    let
      relocatedDecls = relocateTopLevelAbstractToParents resolvedDecls    -- F> Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> <F
      uidClaferMap' = createUidIClaferMap imodule{_mDecls = relocatedDecls}
    resolvedHierarchyDecls <- mapM (resolveHierarchy uidClaferMap') relocatedDecls
    let
        resolvedHierarchiesIModule = imodule{_mDecls = resolvedHierarchyDecls}
    return
      ( resolvedHierarchiesIModule
      , genv'{ sClafers = bfs toNodeShallow $ toClafers resolvedHierarchyDecls
             , uidClaferMap = createUidIClaferMap resolvedHierarchiesIModule}
      )

-- | Resolves the super of the clafer, given its parent (with the resolved super).
resolveNClafer :: [IClafer] -> Maybe IClafer -> IClafer -> Resolve IClafer
resolveNClafer abstractClafers parent clafer =
  do
    -- a clafer cannot extend itself <https://github.com/gsdlab/clafer/issues/86>
    let abstractClafers' = filter ((/= _uid clafer) . _uid) abstractClafers
    -- unless it redefines another clafer with its name <https://github.com/gsdlab/clafer/issues/77>
    case _super clafer of
      Just (PExp _ _ _ (IClaferId _ id' _ _))
        | _isAbstract clafer && id' == _ident clafer && id' `notElem` map _ident abstractClafers'
        -> throwError $ SemanticErr (_cinPos clafer) $ "ResolverInheritance: clafer " ++ _uid clafer ++ " inherits from itself"
      _ -> return ()
    (super', superIClafer')    <- resolveNSuper abstractClafers' parent $ _super clafer
    -- F> Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> F>
    let
      parentUID' =
        case superIClafer' of
          (Just superIClafer'') ->
            if _isAbstract clafer && isTopLevel clafer && not (isTopLevel superIClafer'')
            then _parentUID superIClafer''   -- make clafer a sibling of the superIClafer'
            else _parentUID clafer
          Nothing               -> _parentUID clafer
    -- <F Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> <F
    elements' <- mapM (resolveNElement abstractClafers (Just clafer{_super = super'})) $ _elements clafer
    return $ clafer
      { _super = super'
      , _parentUID = parentUID'
      , _modifiers = IClaferModifiers
          (_isAbstract clafer)
          (_isInitial clafer || (fromMaybe False $ _isInitial <$> superIClafer'))  -- the clafer is declared as initial or inherits it
          (_isFinal clafer || (fromMaybe False $ _isFinal <$> superIClafer'))      -- the clafer is declared as final or inherits it
      , _elements = elements'
      }

resolveNSuper :: [IClafer] -> Maybe IClafer -> Maybe PExp -> Resolve (Maybe PExp, Maybe IClafer)
resolveNSuper _ _ Nothing = return (Nothing, Nothing)
resolveNSuper abstractClafers parent (Just (PExp _ pid' pos' (IClaferId _ id' _ _))) =
    if isPrimitive id'
      then throwError $ SemanticErr pos' $ "Primitive types are not allowed as super types: " ++ id'
      else do
        r <- case inheritedSuper of
          Just c  -> return $ Just (_uid c, [c])
          Nothing -> resolveN pos' abstractClafers id'
        ~(id'', [superClafer']) <- case r of
          Nothing -> throwError $ SemanticErr pos' ("No superclafer found: " ++ id')
          Just m  -> return m
        return (Just $ PExp (Just $ TClafer [id'']) pid' pos' (IClaferId "" id'' (isTopLevel superClafer') (GlobalBind id''))
                 , Just superClafer')
  where
    -- A redefinition, e.g., `fa : fa -> T`, extends the nearest clafer with that
    -- name which the parent inherits, even if other abstract clafers have the name.
    inheritedSuper = listToMaybe
      [ c | s <- maybe [] (superChain abstractClafers) parent
          , IEClafer c <- _elements s
          , _isAbstract c
          , _ident c == id'
          , c `elem` abstractClafers ]
resolveNSuper _ _ x = return (x, Nothing)

-- | The abstract supers of the clafer, nearest first. A super is found by its
-- uid when resolved, or by its name when it is unique.
superChain :: [IClafer] -> IClafer -> [IClafer]
superChain abstractClafers = go []
  where
    go visited c = case getSuper c of
      [s] | Just sup <- find ((== s) . _uid) abstractClafers <|> unique s
          , _uid sup `notElem` visited
          -> sup : go (_uid sup : visited) sup
      _   -> []
    unique s = case filter ((== s) . _ident) abstractClafers of
      [sup] -> Just sup
      _     -> Nothing


resolveNElement :: [IClafer] -> Maybe IClafer -> IElement -> Resolve IElement
resolveNElement abstractClafers parent x = case x of
  IEClafer clafer  -> IEClafer <$> resolveNClafer abstractClafers parent clafer
  IEConstraint _ _  -> return x
  IEGoal _ _ -> return x

resolveN :: Span -> [IClafer] -> String -> Resolve (Maybe (String, [IClafer]))
resolveN pos' abstractClafers id' =
  findUnique pos' id' $ map (\x -> (x, [x])) abstractClafers


resolveHierarchy :: UIDIClaferMap -> IElement           -> Resolve IElement
resolveHierarchy    uidClaferMap'    (IEClafer iClafer') = IEClafer <$> (super.traverse.iType.traverse %%~ addHierarchy $ iClafer')
  where
    addHierarchy :: IType      -> Resolve IType
    addHierarchy    (TClafer _) = TClafer <$> checkForLoop (tail $ mapHierarchy _uid getSuper uidClaferMap' iClafer')
    addHierarchy    x           = return x
    checkForLoop :: [String] -> Resolve [String]
    checkForLoop    supers    = case find (_uid iClafer' ==) supers of
                                  Nothing -> return supers
                                  Just _ -> throwError $ SemanticErr (_cinPos iClafer') $ "ResolverInheritance: clafer " ++ _uid iClafer' ++ " inherits from itself"
resolveHierarchy    _                x                   = return x


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
resolveOReference env (Just (IReference is' mods exp')) = Just <$> IReference is' mods <$> resolvePExp env exp'


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
  (graph, v2n, _) = graphFromEdges $ map (\(c, ss) -> (c, c, ss)) dependencies
  isUnrollable [x] = fst3 x `elem` trd3 x
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
  -- counted by the UID's name, so that, e.g., a' and a__prime__ get different UIDs
  let uidName = uidIdent $ _ident clafer
  identCountMap' <- gets identCountMap
  let count = Map.findWithDefault 0 uidName identCountMap'
  modify (\e -> e { identCountMap = Map.alter (\_ -> Just (count+1)) uidName identCountMap' } )
  return $ clafer { _uid = genId uidName count, _parentUID = puid }

genId :: String -> Int -> String
genId id' count = concat ["c", show count, "_",  id']

-- | The name of a clafer as used in its UID. Clafer names may contain apostrophes,
-- but the UIDs are identifiers in the Alloy and Choco (JavaScript) outputs, where
-- an apostrophe is not allowed (in Alloy 6, it is the next-state operator):
-- name' becomes name__prime__.
uidIdent :: String -> String
uidIdent = concatMap (\c -> if c == '\'' then "__prime__" else [c])

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

-- F> Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> F>
relocateTopLevelAbstractToParents :: [IElement]      -> [IElement]
relocateTopLevelAbstractToParents    originalElements =
  let
    (elementsToBeRelocated, remainingElements) = partition needsRelocation originalElements
  in
    case elementsToBeRelocated of
      [] -> originalElements
      _  -> map (insertElements $ mkParentUIDIElementMap elementsToBeRelocated) remainingElements
  where
    needsRelocation :: IElement -> Bool
    needsRelocation    IEClafer{_iClafer} = not $ isTopLevel _iClafer
    needsRelocation    _                  = False

    -- creates a map from parentUID to a list of elements to be added as children of a clafer with that UID
    mkParentUIDIElementMap :: [IElement] -> StringMap [IElement]
    mkParentUIDIElementMap    elems       = foldl'
        (\accumMap' (parentUID', elem') -> SMap.insertWith (++) parentUID' [elem'] accumMap')
        SMap.empty
        (map (\e -> (_parentUID $ _iClafer e, e)) elems)

    insertElements :: StringMap [IElement] -> IElement     -> IElement
    insertElements    parentMap               targetElement = let
        targetUID = targetElement ^. iClafer . uid
        newChildren = SMap.findWithDefault [] targetUID parentMap
        currentElements = targetElement ^. iClafer . elements
        newElements =  map (insertElements parentMap) currentElements
                    ++ newChildren
      in
        targetElement & iClafer . elements .~ newElements
-- <F Top-level abstract clafer extending a nested abstract clafer <https://github.com/gsdlab/clafer/issues/67> <F
