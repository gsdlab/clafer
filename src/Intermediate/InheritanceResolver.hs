module Intermediate.InheritanceResolver where

import Monad
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

-- -----------------------------------------------------------------------------
-- inherited and default cardinalities
analyzeDeclaration :: IModule -> IDeclaration -> IDeclaration
analyzeDeclaration declarations x = case x of
  IClaferDecl clafer  -> IClaferDecl $ analyzeClafer env clafer
  IConstDecl constraint  -> x
  where
  env = SEnv (toClafers declarations) Nothing []


analyzeClafer :: SEnv -> IClafer -> IClafer
analyzeClafer env clafer =
  clafer' {elements = map (analyzeElement env {context = Just clafer'}) $
           elements clafer'}
  where
  clafer' = clafer {gcard = analyzeGCard env clafer,
                    card  = analyzeCard  env clafer}


-- only for non-overlapping
analyzeGCard :: SEnv -> IClafer -> Maybe IGCard
analyzeGCard env clafer = gcard' `mplus` (Just $ IGCard False (0, ExIntegerAst))
  where
  gcard'
    | isOverlapping $ super clafer = gcard clafer
    | otherwise                    = listToMaybe $ mapMaybe gcard $
                                     findHierarchy (clafers env) clafer


analyzeCard :: SEnv -> IClafer -> Maybe Interval
analyzeCard env clafer = card clafer `mplus` Just card'
  where
  card'
    | isAbstract clafer                          = (0, ExIntegerAst)
    | (isJust $ context env) && isKeyword pGcard = (0, ExIntegerNum 1)
    | otherwise                                  = (1, ExIntegerNum 1)
  pGcard = fromJust $ gcard $ fromJust $ context env


analyzeElement :: SEnv -> IElement -> IElement
analyzeElement env x = case x of
  ISubclafer clafer  -> ISubclafer $ analyzeClafer env clafer
  ISubconstraint constraint  -> x
