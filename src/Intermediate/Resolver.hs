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
resolveModule args declarations = resolveNamesModule args $ rem $ resolveNModule $ dups $ nameModule args declarations
  where
  rem  = if unroll_inheritance args then resolveEModule else id
  dups = if check_duplicates args then findDupModule else id


-- -----------------------------------------------------------------------------
nameModule :: ClaferArgs -> IModule -> (IModule, GEnv)
nameModule args declarations
  | unique_identifiers args = ([IClaferDecl root], genv)
  | otherwise = (decls, genv)
  where
  f = if unique_identifiers args then copyUid else renameClafer'
  (decls, genv) =
      runState (mapM (nameDeclaration f) declarations) $ GEnv 0 Map.empty []
  root = IClafer False Nothing "root" "root"
         (ISuper False [ISExpIdent "clafer" True])
         (Just (1, ExIntegerNum 1))
         (1, ExIntegerNum 1)
         (map declToElem decls)

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


declToElem x = case x of
  IClaferDecl clafer -> ISubclafer clafer
  IConstDecl constraint  -> ISubconstraint constraint

-- -----------------------------------------------------------------------------
resolveNamesModule :: ClaferArgs -> (IModule, GEnv) -> (IModule, GEnv)
resolveNamesModule args (declarations, genv) = (res, genv)
  where
  res = foldr ($) declarations $ map (\f -> flip (curry f) genv) funs
  funs
    | unique_identifiers args = [resolveTModule, analyzeModule]
    | otherwise               = [resolveTModule, resolveModuleNames, analyzeModule, resolveOModule]

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
