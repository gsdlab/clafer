module Common where

import Absclafer

-- -----------------------------------------------------------------------------
-- basic functions shared by desugarer, analyzer and code generator

type Result = String


transIdent :: Ident -> Result
transIdent x = case x of
  Ident str  -> str


transName :: Name -> (Maybe Result, Result)
transName x = case x of
  Name modids id  -> (Nothing, transIdent id)

