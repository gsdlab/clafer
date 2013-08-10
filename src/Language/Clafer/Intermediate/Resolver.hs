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

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ResolverName
import Language.Clafer.Intermediate.ResolverType
import Language.Clafer.Intermediate.ResolverInheritance

resolveModule :: ClaferArgs -> IModule -> Resolve (IModule, GEnv, [IModule])
resolveModule args' declarations =
  do
    r <- resolveNModule $ nameModule (skip_resolver args') declarations
    resolveNamesModule args' =<< (rom' $ rem' r)
  where
  rem' = if flatten_inheritance args' then resolveEModule else id
  rom' = if skip_resolver args' then return . id else resolveOModule


-- -----------------------------------------------------------------------------
nameModule :: Bool -> IModule -> (IModule, GEnv,[IModule])
nameModule skipResolver imodule = (imodule{mDecls = decls'}, genv', irModuleList')
  where
    (decls', genv') = runState (mapM (nameElement skipResolver) $ mDecls imodule) $ GEnv 0 Map.empty []
    irModule' = imodule{mDecls = decls'}
    irModuleList' = [irModule']

nameElement :: MonadState GEnv m => Bool -> IElement -> m IElement
nameElement skipResolver x = case x of
  IEClafer claf -> IEClafer `liftM` (nameClafer skipResolver claf)
  IEConstraint isHard' pexp -> IEConstraint isHard' `liftM` (namePExp pexp)
  IEGoal isMaximize' pexp -> IEGoal isMaximize' `liftM` (namePExp pexp)


nameClafer :: MonadState GEnv m => Bool -> IClafer -> m IClafer
nameClafer skipResolver claf = do
  claf' <- if skipResolver then return claf{uid = ident claf} else (renameClafer (not skipResolver)) claf
  elements' <- mapM (nameElement skipResolver) $ elements claf
  return $ claf' {elements = elements'}


namePExp :: MonadState GEnv m => PExp -> m PExp
namePExp pexp@(PExp _ _ s exp') = do
  let pid' = genPExpName s exp'
  exp'' <- nameIExp exp'
  return $ pexp {pid = pid', Language.Clafer.Intermediate.Intclafer.exp = exp''}

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
resolveNamesModule :: ClaferArgs -> (IModule, GEnv, [IModule]) -> Resolve (IModule, GEnv, [IModule])
resolveNamesModule args' (declarations, genv', modulesList) =
  do
    (res,list') <- foldM (\acc f -> applyFunc genv' acc f ) ( declarations, modulesList ) funs
    return (res,genv',list')
  where
  funs :: [(IModule, GEnv, [IModule]) -> Resolve (IModule, [IModule])]
  funs
    | skip_resolver args' = [return . analyzeModule, resolveTModule]
    | otherwise = [ return . analyzeModule, resolveModuleNames, resolveTModule]
    
applyFunc :: GEnv -> (IModule, [IModule]) -> ((IModule, GEnv, [IModule]) -> Resolve (IModule, [IModule])) -> Resolve (IModule, [IModule])
applyFunc genv' (irModule, irModulesList) func = 
    func (irModule, genv', irModulesList)
