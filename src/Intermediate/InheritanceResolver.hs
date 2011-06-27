module Intermediate.InheritanceResolver where

import Data.Maybe

import Common
import Front.Absclafer
import Intermediate.Intclafer
import Intermediate.NameResolver

-- -----------------------------------------------------------------------------
-- Non-overlapping inheritance
resolveNDeclaration :: IModule -> IDeclaration -> IDeclaration
resolveNDeclaration declarations x = case x of
  IClaferDecl clafer  -> IClaferDecl $ resolveNClafer declarations clafer
  IConstDecl constraint  -> x


resolveNClafer :: IModule -> IClafer -> IClafer
resolveNClafer declarations clafer =
  clafer {super = resolveNSuper declarations $ super clafer,
          elements = map (resolveNElement declarations) $ elements clafer}


resolveNSuper :: IModule -> ISuper -> ISuper
resolveNSuper declarations x = case x of
  ISuper False [SExpIdent (Ident "clafer")] -> x
  ISuper False [SExpIdent id] -> ISuper False [SExpIdent $ Ident id']
    where
    id' = fromMaybe (error "No superclafer found") $
          resolveN declarations $ transIdent id
  _ -> x


resolveNElement :: IModule -> IElement -> IElement
resolveNElement declarations x = case x of
  ISubclafer clafer  -> ISubclafer $ resolveNClafer declarations clafer
  ISubconstraint constraint  -> x


resolveN :: IModule -> String -> Maybe String
resolveN declarations id =
  findUnique id $ filter isAbstract $ bfsClafers $ toClafers declarations

-- -----------------------------------------------------------------------------
-- Overlapping inheritance
resolveODeclaration :: IModule -> IDeclaration -> IDeclaration
resolveODeclaration declarations x = case x of
  IClaferDecl clafer  -> IClaferDecl $ resolveOClafer env clafer
  IConstDecl constraint  -> x
  where
  env = SEnv (toClafers declarations) Nothing []


resolveOClafer :: SEnv -> IClafer -> IClafer
resolveOClafer env clafer =
  clafer {super = resolveOSuper env {context = Just clafer} $ super clafer,
          elements = map (resolveOElement env {context = Just clafer}) $
          elements clafer}


resolveOSuper :: SEnv -> ISuper -> ISuper
resolveOSuper env x = case x of
  ISuper True sexps -> ISuper True $ map (resolveSExp env) sexps
  _ -> x


resolveOElement :: SEnv -> IElement -> IElement
resolveOElement env x = case x of
  ISubclafer clafer  -> ISubclafer $ resolveOClafer env clafer
  ISubconstraint constraint  -> x
