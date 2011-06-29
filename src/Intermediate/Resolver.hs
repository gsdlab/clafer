module Intermediate.Resolver where

import List
import Monad
import Data.Maybe
import Control.Monad.State

import Common
import Front.Absclafer
import Intermediate.Intclafer
import Intermediate.ResolverName
import Intermediate.ResolverInheritance


resolveModule :: IModule -> IModule
resolveModule declarations = resolveNamesModule $ nameModule declarations


-- -----------------------------------------------------------------------------
data NEnv = NEnv {num :: Int}

nameModule :: IModule -> IModule
nameModule declarations = evalState (mapM nameDeclaration declarations) (NEnv 0)


nameDeclaration x = case x of
  IClaferDecl clafer  -> IClaferDecl `liftM` (nameClafer clafer)
  IConstDecl constraint  -> return x


nameClafer clafer = do
  modify (\e -> e {num = 1 + num e})
  n <- gets num
  elements' <- mapM nameElement $ elements clafer
  return $ clafer
    {uid = concat ["c", show n, "_",  ident clafer], elements = elements'}


nameElement x = case x of
  ISubclafer clafer -> ISubclafer `liftM` (nameClafer clafer)
  ISubconstraint ilexp -> return x

-- -----------------------------------------------------------------------------
resolveNamesModule :: IModule -> IModule
resolveNamesModule declarations = multiProcess
  (map (\f -> \ps us -> f (ps ++ us) (head us))
   [resolveDeclaration, analyzeDeclaration,
    resolveODeclaration, resolveNDeclaration])
  declarations
