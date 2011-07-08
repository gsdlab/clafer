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
resolveModule args declarations = resolveNamesModule args $ rem $ resolveNModule $ nameModule args declarations
  where
  rem  = if unroll_inheritance args then resolveEModule else id


-- -----------------------------------------------------------------------------
nameModule :: ClaferArgs -> IModule -> (IModule, GEnv)
nameModule args declarations =
  runState (mapM (nameDeclaration f) declarations) $ GEnv 0 Map.empty []
  where
  f = if force_resolver args then renameClafer' else copyUid



nameDeclaration f x = case x of
  IClaferDecl clafer  -> IClaferDecl `liftM` (nameClafer f clafer)
  IConstDecl constraint  -> return x


nameClafer f clafer = do
  clafer' <- f clafer
  elements' <- mapM (nameElement f) $ elements clafer
  return $ clafer' {elements = elements'}


nameElement f x = case x of
  ISubclafer clafer -> ISubclafer `liftM` (nameClafer f clafer)
  ISubconstraint ilexp -> return x


copyUid clafer = return clafer{uid = ident clafer}

-- -----------------------------------------------------------------------------
resolveNamesModule :: ClaferArgs -> (IModule, GEnv) -> (IModule, GEnv)
resolveNamesModule args (declarations, genv) = (res, genv)
  where
  res = foldr ($) declarations $ map (\f -> flip (curry f) genv) funs
  funs
    | force_resolver args = [resolveTModule, resolveModuleNames, analyzeModule, resolveOModule]
    | otherwise = [resolveTModule, analyzeModule]
