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
resolveModule args declarations = resolveNamesModule $ rem $ resolveNModule $ nameModule declarations
  where
  rem = (if unroll_inheritance args then resolveEModule else id)


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