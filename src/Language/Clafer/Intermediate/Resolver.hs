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
import qualified Data.Map as Map

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ResolverName
import Language.Clafer.Intermediate.ResolverType
import Language.Clafer.Intermediate.ResolverInheritance

-- | Run the various resolvers
resolveModule :: ClaferArgs -> IModule -> Resolve (IModule, GEnv)
resolveModule    args'         iModule  =
  do
    r <- resolveNModule (iModule, GEnv Map.empty [])
    resolveNamesModule args' =<< (rom' $ rem' r)
  where
  rem' = if flatten_inheritance args' then resolveEModule else id
  rom' = if skip_resolver args' then return . id else resolveOModule

-- -----------------------------------------------------------------------------
resolveNamesModule :: ClaferArgs -> (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveNamesModule args' (declarations, genv') =
  do
    res <- foldM (flip ($)) declarations $ map (\f -> flip (curry f) genv') funs
    return (res, genv')
  where
  funs :: [(IModule, GEnv) -> Resolve IModule]
  funs
    | skip_resolver args' = [return . analyzeModule, resolveTModule]
    | otherwise = [ return . analyzeModule, resolveModuleNames, resolveTModule]
