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
module Language.Clafer.Intermediate.Resolver where

import Control.Monad
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.StringMap as SMap

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ResolverName
import Language.Clafer.Intermediate.ResolverType
import Language.Clafer.Intermediate.ResolverInheritance

-- | Run the various resolvers
resolveModule :: ClaferArgs -> IModule -> Resolve (IModule, GEnv)
resolveModule    args'         imodule =
  do
    r <- resolveNModule $ nameModule (skip_resolver args') imodule
    resolveNamesModule args' =<< (rom' $ rem' r)
  where
  rem' = if flatten_inheritance args' then resolveEModule else id
  rom' = if skip_resolver args' then return . id else resolveOModule


-- | Name resolver
nameModule :: Bool -> IModule -> (IModule, GEnv)
nameModule skipResolver imodule = (imodule', genv'')
  where
    (decls', genv') = runState (mapM (nameElement skipResolver "root") $ _mDecls imodule) $ GEnv Map.empty 0 Map.empty [] SMap.empty
    imodule' = imodule{_mDecls = decls'}
    genv'' = genv'{uidClaferMap = createUidIClaferMap imodule'}


nameElement :: MonadState GEnv m => Bool -> UID -> IElement -> m IElement
nameElement skipResolver puid x = case x of
  IEClafer claf -> IEClafer `liftM` (nameClafer skipResolver puid claf)
  IEConstraint isHard' pexp -> IEConstraint isHard' `liftM` (namePExp pexp)
  IEGoal isMaximize' pexp -> IEGoal isMaximize' `liftM` (namePExp pexp)


nameClafer :: MonadState GEnv m => Bool -> UID -> IClafer -> m IClafer
nameClafer skipResolver puid claf = do
  claf' <- if skipResolver then return claf{_uid = _ident claf, _parentUID = puid} else renameClafer True puid claf
  elements' <- mapM (nameElement skipResolver (_uid claf')) $ _elements claf
  return $ claf' {_elements = elements'}


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
  IFunExp op' pexps -> IFunExp op' `liftM` (mapM namePExp pexps)
  _ -> return x

nameIDecl :: MonadState GEnv m => IDecl -> m IDecl
nameIDecl (IDecl isDisj' dels body') = IDecl isDisj' dels `liftM` (namePExp body')

-- -----------------------------------------------------------------------------
resolveNamesModule :: ClaferArgs -> (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveNamesModule args' (imodule, genv') =
  do
    imodule' <- foldM (flip ($)) imodule $ map (\f -> flip (curry f) genv') funs
    return (imodule', genv'{uidClaferMap = createUidIClaferMap imodule'})
  where
  funs :: [(IModule, GEnv) -> Resolve IModule]
  funs
    | skip_resolver args' = [return . analyzeModule, resolveRedefinition, resolveTModule]
    | otherwise = [ return . analyzeModule, resolveModuleNames, resolveRedefinition, resolveTModule]
