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
module Intermediate.Resolver where

import List
import Monad
import Data.Maybe
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

import Common
import Front.Absclafer
import Intermediate.Intclafer
import Intermediate.ResolverName
import Intermediate.ResolverInheritance
import Intermediate.ResolverType

resolveModule :: ClaferArgs -> IModule -> (IModule, GEnv)
resolveModule args declarations = resolveNamesModule args $ rom $ rem $ resolveNModule $ nameModule (force_resolver args) declarations
  where
  rem = if flatten_inheritance args then resolveEModule else id
  rom = if force_resolver args then resolveOModule else id


-- -----------------------------------------------------------------------------
nameModule :: Bool -> IModule -> (IModule, GEnv)
nameModule forceResolver imodule = (imodule{mDecls = decls'}, genv')
  where
  (decls', genv') = runState (mapM (nameElement forceResolver) $ mDecls imodule) $ GEnv 0 Map.empty []

nameElement forceResolver x = case x of
  IEClafer clafer -> IEClafer `liftM` (nameClafer forceResolver clafer)
  IEConstraint isHard pexp -> IEConstraint isHard `liftM` (namePExp pexp)


nameClafer forceResolver clafer = do
  clafer' <- if forceResolver then (renameClafer forceResolver) clafer else return clafer{uid = ident clafer}
  elements' <- mapM (nameElement forceResolver) $ elements clafer
  return $ clafer' {elements = elements'}


namePExp pexp@(PExp _ _ exp) = do
  pid' <- genId "exp"
  exp' <- nameIExp exp
  return $ pexp {pid = pid', Intermediate.Intclafer.exp = exp'}

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
    | force_resolver args = [resolveTModule, resolveModuleNames, analyzeModule]
    | otherwise = [resolveTModule, analyzeModule]