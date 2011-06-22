module Intermediate.Desugarer where

import Front.Absclafer
import Intermediate.Intclafer
import Monad
import Common

desugarModule :: Module -> IModule
desugarModule x = case x of
  Module declarations  -> map desugarDeclaration $ declarations >>= desugarEnums


sugarModule :: IModule -> Module
sugarModule x = Module $ map sugarDeclaration x


-- desugars enumeration to abstract and global singleton features
desugarEnums :: Declaration -> [Declaration]
desugarEnums x = case x of
  EnumDecl id enumids  -> absEnum : map mkEnum enumids
    where
    absEnum = ClaferDecl $ Clafer
              Abstract GCardEmpty id SuperEmpty CardEmpty ElementsEmpty
    mkEnum (EnumIdIdent eId) = ClaferDecl $ Clafer AbstractEmpty GCardEmpty
                                  eId (SuperExtends $ Name [] id) CardEmpty
                                  ElementsEmpty
  _ -> [x]


desugarDeclaration :: Declaration -> IDeclaration
desugarDeclaration x = case x of
  EnumDecl id enumids  -> error "desugared"
  ClaferDecl clafer  -> IClaferDecl $ desugarClafer clafer
  ConstDecl constraint  -> IConstDecl $ desugarConstraint constraint


sugarDeclaration :: IDeclaration -> Declaration
sugarDeclaration x = case x of
  IClaferDecl clafer  -> ClaferDecl $ sugarClafer clafer
  IConstDecl constraint  -> ConstDecl $ sugarConstraint constraint


desugarClafer :: Clafer -> IClafer
desugarClafer x = case x of
  Clafer abstract gcard id super card elements  ->
    IClafer (desugarAbstract abstract) (desugarGCard gcard) (transIdent id)
      (desugarSuper super) (desugarCard card) (desugarElements elements)


sugarClafer :: IClafer -> Clafer
sugarClafer x = case x of
  IClafer abstract gcard id super card elements  ->
    Clafer (sugarAbstract abstract) (sugarGCard gcard) (Ident id)
      (sugarSuper super) (sugarCard card) (sugarElements elements)


desugarConstraint :: Constraint -> ILExp
desugarConstraint (Constraint lexps) = (if length lexps > 1 then foldl1 IEAnd
  else head) $ map desugarLExp lexps


sugarConstraint :: ILExp -> Constraint
sugarConstraint ilexp = Constraint $ map sugarLExp [ilexp]


desugarAbstract :: Abstract -> Bool
desugarAbstract x = case x of
  AbstractEmpty  -> False
  Abstract  -> True


sugarAbstract :: Bool -> Abstract
sugarAbstract x = case x of
  False -> AbstractEmpty
  True -> Abstract


desugarElements :: Elements -> [IElement]
desugarElements x = case x of
  ElementsEmpty  -> []
  Elements elements  -> map desugarElement elements


sugarElements :: [IElement] -> Elements
sugarElements x = Elements $ map sugarElement x


desugarElement :: Element -> IElement
desugarElement x = case x of
  Subclafer clafer  -> ISubclafer $ desugarClafer clafer
  ClaferUse name card elements  -> ISubclafer $ desugarClafer $ Clafer
    AbstractEmpty GCardEmpty (Ident $ snd $ transName name) (SuperExtends name) card
                  elements
  Subconstraint constraint  -> ISubconstraint $ desugarConstraint constraint


sugarElement :: IElement -> Element
sugarElement x = case x of
  ISubclafer clafer  -> Subclafer $ sugarClafer clafer
  ISubconstraint constraint  -> Subconstraint $ sugarConstraint constraint


desugarSuper :: Super -> ISuper
desugarSuper x = case x of
  SuperEmpty  -> ISuper False []
  SuperColon name  -> ISuper False [nameToSExp name]
  SuperExtends name  -> ISuper False [nameToSExp name]
  SuperArrow modids sexp  -> ISuper True [sexp]
  where
  nameToSExp (Name _ id) = SExpIdent id


sugarSuper :: ISuper -> Super
sugarSuper x = case x of
  ISuper _ [] -> SuperEmpty
  ISuper False [SExpIdent id] -> SuperColon $ Name [] id
  ISuper True [sexp] -> SuperArrow [] sexp


desugarGCard :: GCard -> Maybe Interval
desugarGCard x = case x of
  GCardEmpty  -> Nothing
  GCardXor -> Just (1, ExIntegerNum 1)
  GCardOr  -> Just (1, ExIntegerAst)
  GCardMux -> Just (0, ExIntegerNum 1)
  GCardOpt -> Just (0, ExIntegerAst)
  GCardInterval (GNCard i ex)  -> Just (i, ex)


sugarGCard :: Maybe Interval -> GCard
sugarGCard x = case x of
  Nothing -> GCardEmpty
  Just (i, ex) -> GCardInterval $ GNCard i ex


desugarCard :: Card -> Maybe Interval
desugarCard x = case x of
  CardEmpty  -> Nothing
  CardLone  ->  Just (0, ExIntegerNum 1)
  CardSome  ->  Just (1, ExIntegerAst)
  CardAny  ->   Just (0, ExIntegerAst)
  CardInterval (NCard i ex)  -> Just (i, ex)


sugarCard :: Maybe Interval -> Card
sugarCard x = case x of
  Nothing -> CardEmpty
  Just (i, ex) -> CardInterval $ NCard i ex


desugarLExp :: LExp -> ILExp
desugarLExp x = case x of
  EIff lexp0 iff lexp  -> IEIff (desugarLExp lexp0) (desugarLExp lexp)
  EImplies lexp0 implies lexp  -> IEImpliesElse (desugarLExp lexp0)
                                  (desugarLExp lexp) Nothing
  EImpliesElse lexp0 implies lexp1 lexp  -> IEImpliesElse (desugarLExp lexp0)
                                            (desugarLExp lexp1)
                                            (Just $ desugarLExp lexp)
  EOr lexp0 or lexp  -> IEOr (desugarLExp lexp0) (desugarLExp lexp)
  EXor lexp0 xor lexp  -> IEXor (desugarLExp lexp0) (desugarLExp lexp)
  EAnd lexp0 and lexp  -> IEAnd (desugarLExp lexp0) (desugarLExp lexp)
  ENeg neg lexp  -> IENeg (desugarLExp lexp)
  ETerm term  -> IETerm $ desugarTerm term


sugarLExp :: ILExp -> LExp
sugarLExp x = case x of
  IEIff lexp0 lexp -> EIff (sugarLExp lexp0) Iff (sugarLExp lexp)
  IEImpliesElse lexp0 lexp Nothing -> EImplies (sugarLExp lexp0) Implies (sugarLExp lexp)
  IEImpliesElse lexp0 lexp1 (Just lexp) -> EImpliesElse (sugarLExp lexp0) Implies (sugarLExp lexp1) (sugarLExp lexp)
  IEOr lexp0 lexp -> EOr (sugarLExp lexp0) Or (sugarLExp lexp)
  IEXor lexp0 lexp -> EXor (sugarLExp lexp0) Xor (sugarLExp lexp)
  IEAnd lexp0 lexp -> EAnd (sugarLExp lexp0) And (sugarLExp lexp)
  IENeg lexp -> ENeg Neg (sugarLExp lexp)
  IETerm term -> ETerm (sugarTerm term)


desugarTerm :: Term -> ITerm
desugarTerm x = case x of
  TermCmpExp cmpexp  -> ITermCmpExp cmpexp
  TermSet sexp  -> ITermQuantSet QuantSome sexp
  TermQuantSet quant sexp  -> ITermQuantSet quant sexp
  TermQuantDeclExp decls lexp  -> ITermQuantDeclExp decls (desugarLExp lexp)


sugarTerm :: ITerm -> Term
sugarTerm x = case x of
  ITermCmpExp cmpexp -> TermCmpExp cmpexp
  ITermQuantSet quant sexp -> TermQuantSet quant sexp
  ITermQuantDeclExp decls lexp -> TermQuantDeclExp decls (sugarLExp lexp)
