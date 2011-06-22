module Intermediate.Namer where

import Intermediate.Intclafer
import Monad
import Control.Monad.State

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
  return $ clafer {uid = show n, elements = elements'}

nameElement x = case x of
  ISubclafer clafer -> ISubclafer `liftM` (nameClafer clafer)
  ISubconstraint ilexp -> return x