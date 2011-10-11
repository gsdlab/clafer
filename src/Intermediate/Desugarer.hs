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
module Intermediate.Desugarer where

import Front.Absclafer
import Intermediate.Intclafer
import Monad
import Common
import Data.Function

desugarModule :: Module -> IModule
desugarModule x = case x of
  Module declarations  -> map desugarDeclaration $ declarations >>= desugarEnums


declToElem x = case x of
  IClaferDecl clafer -> ISubclafer clafer
  IConstDecl constraint  -> ISubconstraint constraint


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
            "" (desugarSuper super) (desugarCard card) (0, ExIntegerAst)
            (desugarElements elements)


sugarClafer :: IClafer -> Clafer
sugarClafer x = case x of
  IClafer abstract gcard id uid super card _ elements  ->
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
  ElementsList elements  -> map desugarElement elements


sugarElements :: [IElement] -> Elements
sugarElements x = ElementsList $ map sugarElement x


desugarElement :: ElementCl -> IElement
desugarElement x = case x of
  Subclafer clafer  -> ISubclafer $ desugarClafer clafer
  ClaferUse name card elements  -> ISubclafer $ desugarClafer $ Clafer
    AbstractEmpty GCardEmpty (Ident $ snd $ transName name) (SuperExtends name) card
                  elements
  Subconstraint constraint  -> ISubconstraint $ desugarConstraint constraint


sugarElement :: IElement -> ElementCl
sugarElement x = case x of
  ISubclafer clafer  -> Subclafer $ sugarClafer clafer
  ISubconstraint constraint  -> Subconstraint $ sugarConstraint constraint


desugarSuper :: Super -> ISuper
desugarSuper x = case x of
  SuperEmpty  -> ISuper False [ISExpIdent baseClafer True]
  SuperColon name  -> ISuper False [nameToSExp name]
  SuperExtends name  -> ISuper False [nameToSExp name]
  SuperArrow modids sexp  -> ISuper True [desugarSExp sexp]
  where
  nameToSExp (Name _ id) = ISExpIdent (transIdent id) True


sugarSuper :: ISuper -> Super
sugarSuper x = case x of
  ISuper _ [] -> SuperEmpty
  ISuper False [ISExpIdent id _] -> SuperColon $ Name [] $ Ident id
  ISuper True [sexp] -> SuperArrow [] $ sugarSExp sexp


desugarGCard :: GCard -> Maybe IGCard
desugarGCard x = case x of
  GCardEmpty  -> Nothing
  GCardXor -> Just $ IGCard True (1, ExIntegerNum 1)
  GCardOr  -> Just $ IGCard True (1, ExIntegerAst)
  GCardMux -> Just $ IGCard True (0, ExIntegerNum 1)
  GCardOpt -> Just $ IGCard True (0, ExIntegerAst)
  GCardInterval (GNCard i ex)  -> Just $ IGCard False (i, ex)


sugarGCard :: Maybe IGCard -> GCard
sugarGCard x = case x of
  Nothing -> GCardEmpty
  Just (IGCard _ (i, ex)) -> GCardInterval $ GNCard i ex


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
  TermCmpExp cmpexp  -> ITermCmpExp (desugarCmpExp cmpexp) Nothing
  TermSet sexp  -> ITermQuantSet QuantSome $ desugarSExp sexp
  TermQuantSet quant sexp  -> ITermQuantSet quant $ desugarSExp sexp
  TermQuantDeclExp decls lexp  ->
      ITermQuantDeclExp (map desugarDecl decls) (desugarLExp lexp)


sugarTerm :: ITerm -> Term
sugarTerm x = case x of
  ITermCmpExp cmpexp _ -> TermCmpExp $ sugarCmpExp cmpexp
  ITermQuantSet quant sexp -> TermQuantSet quant $ sugarSExp sexp
  ITermQuantDeclExp decls lexp ->
      TermQuantDeclExp (map sugarDecl decls) (sugarLExp lexp)


desugarCmpExp :: CmpExp -> ICmpExp
desugarCmpExp x = case x of
  ELt exp0 exp -> on IELt desugarExp exp0 exp
  EGt exp0 exp -> on IEGt desugarExp exp0 exp
  EREq exp0 exp -> on IEREq desugarExp exp0 exp
  EEq exp0 exp -> on IEEq desugarExp exp0 exp
  ELte exp0 exp -> on IELte desugarExp exp0 exp
  EGte exp0 exp -> on IEGte desugarExp exp0 exp
  ENeq exp0 exp -> on IENeq desugarExp exp0 exp
  ERNeq exp0 exp -> on IERNeq desugarExp exp0 exp
  EIn exp0 exp -> on IEIn desugarExp exp0 exp
  ENin exp0 exp -> on IENin desugarExp exp0 exp


sugarCmpExp :: ICmpExp -> CmpExp
sugarCmpExp x = case x of
  IELt exp0 exp -> on ELt sugarExp exp0 exp
  IEGt exp0 exp -> on EGt sugarExp exp0 exp
  IEREq exp0 exp -> on EREq sugarExp exp0 exp
  IEEq exp0 exp -> on EEq sugarExp exp0 exp
  IELte exp0 exp -> on ELte sugarExp exp0 exp
  IEGte exp0 exp -> on EGte sugarExp exp0 exp
  IENeq exp0 exp -> on ENeq sugarExp exp0 exp
  IERNeq exp0 exp -> on ERNeq sugarExp exp0 exp
  IEIn exp0 exp -> on EIn sugarExp exp0 exp
  IENin exp0 exp -> on ENin sugarExp exp0 exp


desugarExp :: Exp -> IExp
desugarExp x = case x of
  ENumExp aexp -> IENumExp $ desugarAExp aexp
  EStrExp strexp -> IEStrExp strexp


sugarExp :: IExp -> Exp
sugarExp x = case x of
  IENumExp aexp -> ENumExp $ sugarAExp aexp
  IEStrExp strexp -> EStrExp strexp


desugarSExp :: SExp -> ISExp
desugarSExp x = case x of
  SExpUnion sexp0 sexp  -> on ISExpUnion desugarSExp sexp0 sexp
  SExpIntersection sexp0 sexp  -> on ISExpIntersection desugarSExp sexp0 sexp
  SExpDomain sexp0 sexp  -> on ISExpDomain desugarSExp sexp0 sexp
  SExpRange sexp0 sexp  -> on ISExpRange desugarSExp sexp0 sexp
  SExpJoin sexp0 sexp  -> on ISExpJoin desugarSExp sexp0 sexp
  SExpIdent id  -> ISExpIdent (transIdent id) False


sugarSExp :: ISExp -> SExp
sugarSExp x = case x of
  ISExpUnion sexp0 sexp  -> on SExpUnion sugarSExp sexp0 sexp
  ISExpIntersection sexp0 sexp  -> on SExpIntersection sugarSExp sexp0 sexp
  ISExpDomain sexp0 sexp  -> on SExpDomain sugarSExp sexp0 sexp
  ISExpRange sexp0 sexp  -> on SExpRange sugarSExp sexp0 sexp
  ISExpJoin sexp0 sexp  -> on SExpJoin sugarSExp sexp0 sexp
  ISExpIdent id _ -> SExpIdent $ Ident id



desugarDecl :: Decl -> IDecl
desugarDecl x = case x of
  Decl exquant disj locids sexp  -> IDecl exquant (desugarDisj disj)
                                    (map desugarLocId locids) $
                                    desugarSExp sexp


sugarDecl :: IDecl -> Decl
sugarDecl x = case x of
  IDecl exquant disj locids sexp  -> Decl exquant (sugarDisj disj)
                                     (map sugarLocId locids) $ sugarSExp sexp


desugarDisj :: Disj -> Bool
desugarDisj x = case x of
  DisjEmpty -> False
  Disj -> True


sugarDisj :: Bool -> Disj
sugarDisj x = case x of
  False -> DisjEmpty
  True -> Disj


desugarLocId :: LocId -> String
desugarLocId x = case x of
  LocIdIdent id  -> transIdent id


sugarLocId :: String -> LocId
sugarLocId x = LocIdIdent $ Ident x


desugarAExp :: AExp -> IAExp
desugarAExp x = case x of
  EAdd aexp0 aexp  -> on IEAdd desugarAExp aexp0 aexp
  ESub aexp0 aexp  -> on IESub desugarAExp aexp0 aexp
  EMul aexp0 aexp  -> on IEMul desugarAExp aexp0 aexp
  ECSetExp sexp  -> IECSetExp $ desugarSExp sexp
  EASetExp sexp  -> IEASetExp $ desugarSExp sexp
  EInt n  -> IEInt n


sugarAExp :: IAExp -> AExp
sugarAExp x = case x of
  IEAdd aexp0 aexp  -> on EAdd sugarAExp aexp0 aexp
  IESub aexp0 aexp  -> on ESub sugarAExp aexp0 aexp
  IEMul aexp0 aexp  -> on EMul sugarAExp aexp0 aexp
  IECSetExp sexp  -> ECSetExp $ sugarSExp sexp
  IEASetExp sexp  -> EASetExp $ sugarSExp sexp
  IEInt n  -> EInt n
