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

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Maybe
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ResolverName
import Language.Clafer.Intermediate.ResolverType
import Language.Clafer.Intermediate.ResolverInheritance

resolveModule :: ClaferArgs -> IModule -> Either ClaferPErr (IModule, GEnv)
resolveModule args declarations =
  do
    r <- resolveNModule $ nameModule (fromJust $ skip_resolver args) declarations
    return $ resolveNamesModule args $ rom $ rem r
  where
  rem = if fromJust $ flatten_inheritance args then resolveEModule else id
  rom = if fromJust $ skip_resolver args then id else resolveOModule


-- -----------------------------------------------------------------------------
nameModule :: Bool -> IModule -> (IModule, GEnv)
nameModule skipResolver imodule = (imodule{mDecls = decls'}, genv')
  where
  (decls', genv') = runState (mapM (nameElement skipResolver) $ mDecls imodule) $ GEnv 0 Map.empty []

nameElement skipResolver x = case x of
  IEClafer clafer -> IEClafer `liftM` (nameClafer skipResolver clafer)
  IEConstraint isHard pexp -> IEConstraint isHard `liftM` (namePExp pexp)
  IEGoal isMaximize pexp -> IEGoal isMaximize `liftM` (namePExp pexp)


nameClafer skipResolver clafer = do
  clafer' <- if skipResolver then return clafer{uid = ident clafer} else (renameClafer (not skipResolver)) clafer
  elements' <- mapM (nameElement skipResolver) $ elements clafer
  return $ clafer' {elements = elements'}


namePExp pexp@(PExp _ _ _ exp) = do
  pid' <- genId "exp"
  exp' <- nameIExp exp
  return $ pexp {pid = pid', Language.Clafer.Intermediate.Intclafer.exp = exp'}

nameIExp x = case x of
  IDeclPExp quant decls pexp -> do
    decls' <- mapM nameIDecl decls
    pexp'  <- namePExp pexp
    return $ IDeclPExp quant decls' pexp'
  IFunExp op pexps -> IFunExp op `liftM` (mapM namePExp pexps)
  _ -> return x

nameIDecl (IDecl isDisj dels body) = IDecl isDisj dels `liftM` (namePExp body)

-- -----------------------------------------------------------------------------
resolveNamesModule :: ClaferArgs -> (IModule, GEnv) -> (IModule, GEnv)
resolveNamesModule args (declarations, genv) = (res, genv)
  where
  res = foldr ($) declarations $ map (\f -> flip (curry f) genv) funs
  funs
    | fromJust $ skip_resolver args = [resolveTModule, analyzeModule]
    | otherwise = [resolveTModule, resolveModuleNames, analyzeModule]
