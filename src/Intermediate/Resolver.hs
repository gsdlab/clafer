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
resolveModule args declarations = resolveNamesModule $ rem $ resolveNModule $ dups $ nameModule declarations
  where
  rem  = if unroll_inheritance args then resolveEModule else id
  dups = if check_duplicates args then findDupModule else id


-- -----------------------------------------------------------------------------
nameModule :: IModule -> (IModule, GEnv)
nameModule declarations = runState (mapM nameDeclaration declarations) $ GEnv 0 Map.empty []


nameDeclaration x = case x of
  IClaferDecl clafer  -> IClaferDecl `liftM` (nameClafer clafer)
  IConstDecl constraint  -> return x


nameClafer clafer = do
  clafer' <- renameClafer' clafer
  elements' <- mapM nameElement $ elements clafer
  return $ clafer' {elements = elements'}


nameElement x = case x of
  ISubclafer clafer -> ISubclafer `liftM` (nameClafer clafer)
  ISubconstraint ilexp -> return x

-- -----------------------------------------------------------------------------
resolveNamesModule :: (IModule, GEnv) -> (IModule, GEnv)
resolveNamesModule (declarations, genv) = (res, genv)
  where
  res = foldr ($) declarations $ map (\f -> flip (curry f) genv)
    [resolveTModule, resolveModuleNames, analyzeModule, resolveOModule]


findDupModule :: (IModule, GEnv) -> (IModule, GEnv)
findDupModule (declarations, genv)
  | null dups = (map findDupDeclaration declarations, genv)
  | otherwise = error $ show dups
  where
  dups = findDuplicates $ toClafers declarations


findDupDeclaration x = case x of
  IClaferDecl clafer  -> IClaferDecl $ findDupClafer clafer
  IConstDecl constraint  -> x


findDupClafer clafer = if null dups
  then clafer{elements = map findDupElement $ elements clafer}
  else error $ (show $ uid clafer) ++ show dups
  where
  dups = findDuplicates $ getSubclafers $ elements clafer

findDupElement x = case x of
  ISubclafer clafer -> ISubclafer $ findDupClafer clafer
  ISubconstraint ilexp -> x


findDuplicates :: [IClafer] -> [String]
findDuplicates clafers =
  map head $ filter (\xs -> 1 < length xs) $ group $ sort $ map ident clafers
