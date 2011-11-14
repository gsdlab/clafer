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
resolveModule args declarations = resolveNamesModule args $ rom $ rem $ resolveNModule $ nameModule args declarations
  where
  rem = if flatten_inheritance args then resolveEModule else id
  rom = if force_resolver args then resolveOModule else id


-- -----------------------------------------------------------------------------
nameModule :: ClaferArgs -> IModule -> (IModule, GEnv)
nameModule args imodule = (imodule{mDecls = decls'}, genv')
  where
  decls = mDecls imodule
  f = if force_resolver args then renameClafer' else copyUid
  (decls', genv') = runState (mapM (nameDeclaration f) decls) $ GEnv 0 Map.empty []


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
    | force_resolver args = [resolveTModule, resolveModuleNames, analyzeModule]
    | otherwise = [resolveTModule, analyzeModule]
