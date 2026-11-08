{-# LANGUAGE FlexibleContexts #-}
{-
 Copyright (C) 2012-2017 Kacper Bak <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.Resolver where

import Control.Monad
import Control.Monad.State
import Data.List (mapAccumL)
import qualified Data.Map as Map
import qualified Data.StringMap as SMap

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ResolverName
import Language.Clafer.Intermediate.ResolverType
import Language.Clafer.Intermediate.ResolverInheritance
import Language.Clafer.Intermediate.ResolverRoot
import Language.Clafer.Intermediate.UIDs (assignUIDs)

-- | Run the various resolvers. With -f (skip_resolver), the names are the UIDs, as in an
-- | explicit model: the clafers are not renamed, but all names are still resolved and checked.
resolveModule :: ClaferArgs -> IModule -> Resolve (IModule, GEnv)
resolveModule    args'         imodule =
  do
    r <- resolveNModule $ nameModule (skip_resolver args') imodule
    resolveNamesModule =<< resolveOModule (rem' r)
  where
  rem' = if flatten_inheritance args' then resolveEModule else id


-- | Name resolver
-- | Gives every clafer its UID (see "Language.Clafer.Intermediate.UIDs"), or with -f its name,
-- | and every expression its id.
nameModule :: Bool -> IModule -> (IModule, GEnv)
nameModule skipResolver imodule = (imodule', genv'')
  where
    paths = concatMap (claferPaths []) $ _mDecls imodule
    uids = if skipResolver then map last paths else assignUIDs paths
    named = snd $ mapAccumL withUIDs uids $ _mDecls imodule
    (decls', genv') = runState (mapM (nameElement "root") named) $ GEnv Map.empty 0 Map.empty [] SMap.empty
    imodule' = imodule{_mDecls = decls'}
    genv'' = genv'{uidClaferMap = createUidIClaferMap imodule'}

-- | The names of the clafers and their ancestors, from the top level, in pre-order.
claferPaths :: [String] -> IElement -> [[String]]
claferPaths path (IEClafer claf) = path' : concatMap (claferPaths path') (_elements claf)
  where path' = path ++ [_ident claf]
claferPaths _ _ = []

-- | Sets the UIDs of the clafers, in pre-order.
withUIDs :: [UID] -> IElement -> ([UID], IElement)
withUIDs (uid' : uids) (IEClafer claf) = (uids', IEClafer claf{_uid = uid', _elements = elements'})
  where (uids', elements') = mapAccumL withUIDs uids $ _elements claf
withUIDs uids x = (uids, x)


nameElement :: MonadState GEnv m => UID -> IElement -> m IElement
nameElement puid x = case x of
  IEClafer claf -> IEClafer <$> nameClafer puid claf
  IEConstraint isHard' pexp -> IEConstraint isHard' <$> namePExp pexp
  IEGoal isMaximize' pexp -> IEGoal isMaximize' <$> namePExp pexp


nameClafer :: MonadState GEnv m => UID -> IClafer -> m IClafer
nameClafer puid claf = do
  let puid' = if _isAbstract claf && puid == "root" then baseClafer else puid
  elements' <- mapM (nameElement (_uid claf)) $ _elements claf
  return $ claf {_parentUID = puid', _elements = elements'}


namePExp :: MonadState GEnv m => PExp -> m PExp
namePExp pexp@(PExp _ _ _ exp') = do
  n <- gets expCount
  modify (\e -> e {expCount = 1 + n})
  exp'' <- nameIExp exp'
  return $ pexp {_pid = concat [ "e", show n, "_"], _exp = exp''}

nameIExp :: MonadState GEnv m => IExp -> m IExp
nameIExp x = case x of
  IDeclPExp quant' decls' pexp -> do
    decls'' <- mapM nameIDecl decls'
    pexp'  <- namePExp pexp
    return $ IDeclPExp quant' decls'' pexp'
  IFunExp op' pexps -> IFunExp op' `liftM` mapM namePExp pexps
  _ -> return x

nameIDecl :: MonadState GEnv m => IDecl -> m IDecl
nameIDecl (IDecl isDisj' dels body') = IDecl isDisj' dels `liftM` (namePExp body')

-- -----------------------------------------------------------------------------
resolveNamesModule :: (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveNamesModule (imodule, genv') =
  do
    imodule' <- foldM (flip ($)) imodule $ map (\f -> flip (curry f) genv') funs
    return (imodule', genv'{uidClaferMap = createUidIClaferMap imodule'})
  where
  funs :: [(IModule, GEnv) -> Resolve IModule]
  funs = [ return . analyzeModule, resolveModuleNames, resolveRedefinition, resolveTModule, resolveRootModule]
