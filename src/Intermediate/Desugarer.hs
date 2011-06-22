module Intermediate.Desugarer where

import Front.Absclafer
import Intermediate.Intclafer
import Monad
import Common

desugarModule :: Module -> IModule
desugarModule x = case x of
  Module declarations  ->
      map desugarDeclaration $ declarations >>= desugarEnums


-- desugars enumeration to abstract and global singleton features
desugarEnums :: Declaration -> [Declaration]
desugarEnums x = case x of
  EnumDecl id enumids  -> absEnum : map (mkEnum id) enumids
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


desugarClafer :: Clafer -> IClafer
desugarClafer x = case x of
  Clafer abstract gcard id super card elements  ->
    IClafer (desugarAbstract abstract) (desugarGCard gcard) id
      (desugarSuper super) (desugarCard card) (desugarElements elements)


desugarConstraint :: Constraint -> ILExp
desugarConstraint x = case x of
  Constraint lexps  -> TODO (add &&) map desugarLExp lexps


desugarAbstract :: Abstract -> Bool
desugarAbstract x = case x of
  AbstractEmpty  -> False
  Abstract  -> True


desugarElements :: Elements -> [IElement]
desugarElements x = case x of
  ElementsEmpty  -> []
  Elements elements  -> map desugarElement elements


desugarElement :: Element -> IElement
desugarElement x = case x of
  Subclafer clafer  -> ISubclafer $ desugarClafer clafer
  ClaferUse name card elements  -> ISubclafer $ desugarClafer $ Clafer
    AbstractEmpty GCardEmpty (Ident $ snd $ transName name) (Super name) card
                  elements
  Subconstraint constraint  -> ISubconstraint $ desugarConstraint constraint


desugarSuper :: Super -> ISuper
desugarSuper x = case x of
  SuperEmpty  -> ISuper False []
  SuperColon name  -> ISuper False $ [nameToSExp name]
  SuperExtends name  -> ISuper False $ [nameToSExp name]
  SuperArrow modids sexp  -> ISuper True $ [sexp]
  where
  nameToSExp (Name _ id) = SExpIdent id


desugarGCard :: GCard -> Maybe Interval
desugarGCard x = case x of
  GCardEmpty  -> Empty
  GCardXor -> Just (1, ExIntegerNum 1)
  GCardOr  -> Just (1, ExIntegerAst)
  GCardMux -> Just (0, ExIntegerNum 1)
  GCardOpt -> Just (0, ExIntegerAst)
  GCardInterval (GNCard i ex)  -> Just (i, ex)


desugarCard :: Card -> Maybe Interval
desugarCard x = case x of
  CardEmpty  -> Empty
  CardLone  ->  Just (0, ExIntegerNum 1)
  CardSome  ->  Just (1, ExIntegerAst)
  CardAny  ->   Just (0, ExIntegerAst)
  CardInterval (NCard i ex)  -> Just (i, ex)


desugarLExp :: LExp -> ILExp
desugarLExp x = case x of
  EIff lexp0 iff lexp  -> IEIff (desugarLExp lexp0) (desugarLExp lexp)
  EImplies lexp0 implies lexp  -> IEImpliesElse (desugarLExp lexp0)
                                  (desugarLExp lexp) Empty
  EImpliesElse lexp0 implies lexp1 lexp  -> IEImpliesElse (desugarLExp lexp0)
                                            (desugarLExp lexp1)
                                            (desugarLExp lexp)
  EOr lexp0 or lexp  -> IEOr (desugarLExp lexp0) (desugarLExp lexp)
  EXor lexp0 xor lexp  -> IEXor (desugarLExp lexp0) (desugarLExp lexp)
  EAnd lexp0 and lexp  -> IEAnd (desugarLExp lexp0) (desugarLExp lexp)
  ENeg neg lexp  -> IENeg (desugarLExp lexp)
  ETerm term  -> desugarTerm term


desugarTerm :: Term -> ITerm
desugarTerm x = case x of
  TermCmpExp cmpexp  -> ITermCmpExp cmpexp
  TermSet sexp  -> TermQuantSet QuantSome sexp
  TermQuantSet quant sexp  -> ITermQuantSet quant sexp
  TermQuantDeclExp decls lexp  -> ITermQuantDeclExp decls (desugarLExp lexp)
