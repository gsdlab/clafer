{-
 Copyright (C) 2012 Kacper Bak <http://gsd.uwaterloo.ca>

 Permission is hereby granted, free of charge, to any person obtaining a copy of
 this software and associated documentation files (the "Software"), to deal in
 the Software without restriction, including without limitation the rights to
 use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 of the Software, and to permit persons to whom the Software is furnished to do
 so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.
-}
module Language.Clafer.Intermediate.Tracing (traceIrModule, traceAstModule, Ast(..)) where

import Data.Map (Map)
import qualified Data.Map as Map
import Language.Clafer.Front.AbsClafer
import Language.Clafer.Intermediate.Intclafer

traceIrModule :: IModule -> Map Span [Ir] --Map Span [Union (IRClafer IClafer) (IRPExp PExp)]
traceIrModule = foldMapIR getMap
  where
    insert :: Span -> Ir -> Map Span [Ir] -> Map Span [Ir]
    insert k a = Map.insertWith (++) k [a]
    getMap :: Ir -> Map Span [Ir] --Map Span [Union (IRClafer IClafer) (IRPExp PExp)]
    getMap (IRPExp (p@PExp{_inPos = s})) = insert s (IRPExp p) Map.empty
    getMap (IRClafer (c@IClafer{_cinPos = s})) = insert s (IRClafer c) Map.empty
    getMap _ = Map.empty

traceAstModule :: Module -> Map Span [Ast]
traceAstModule x =
  foldr
    ins
    Map.empty
    (traverseModule x)
  where
  ins y = Map.insertWith (++) (i y) [y]
  i (AstModule a) = getSpan a
  i (AstDeclaration a) = getSpan a
  i (AstClafer a) = getSpan a
  i (AstConstraint a) = getSpan a
  i (AstSoftConstraint a) = getSpan a
  i (AstGoal a) = getSpan a
  i (AstAbstract a) = getSpan a
  i (AstElements a) = getSpan a
  i (AstElement a) = getSpan a
  i (AstSuper a) = getSpan a
  i (AstReference a) = getSpan a
  i (AstInit a) = getSpan a
  i (AstInitHow a) = getSpan a
  i (AstGCard a) = getSpan a
  i (AstCard a) = getSpan a
  i (AstNCard a) = getSpan a
  i (AstExInteger a) = getSpan a
  i (AstName a) = getSpan a
  i (AstExp a) = getSpan a
  i (AstSetExp a) = getSpan a
  i (AstDecl a) = getSpan a
  i (AstQuant a) = getSpan a
  i (AstEnumId a) = getSpan a
  i (AstModId a) = getSpan a
  i (AstLocId a) = getSpan a

traverseModule :: Module -> [Ast]
traverseModule x@(Module _ d) = AstModule x : concatMap traverseDeclaration d

traverseDeclaration :: Declaration -> [Ast]
traverseDeclaration x =
  AstDeclaration x :
    case x of
    EnumDecl _ _ e -> concatMap traverseEnumId e
    ElementDecl _ e -> traverseElement e

traverseClafer :: Clafer -> [Ast]
traverseClafer x@(Clafer _ a _ gcard' _ super' ref' card' init' _ g) =
  AstClafer x : (traverseAbstract a ++ traverseGCard gcard' ++ traverseSuper super' ++ traverseReference ref' ++ traverseCard card' ++ traverseInit init' ++ traverseElements g)

traverseConstraint :: Constraint -> [Ast]
traverseConstraint x@(Constraint _ e) = AstConstraint x : concatMap traverseExp e

traverseSoftConstraint :: SoftConstraint -> [Ast]
traverseSoftConstraint x@(SoftConstraint _ e) = AstSoftConstraint x : concatMap traverseExp e

traverseGoal :: Goal -> [Ast]
traverseGoal x@(Goal _ e) = AstGoal x : concatMap traverseExp e

traverseAbstract :: Abstract -> [Ast]
traverseAbstract x =
  AstAbstract x : [{- no other children -}]

traverseElements :: Elements -> [Ast]
traverseElements x =
  AstElements x :
    case x of
    ElementsEmpty _ -> []
    ElementsList _ e -> concatMap traverseElement e

traverseElement :: Element -> [Ast]
traverseElement x =
  AstElement x :
    case x of
    Subclafer _ c -> traverseClafer c
    ClaferUse _ n c e -> traverseName n ++ traverseCard c ++ traverseElements e
    Subconstraint _ c -> traverseConstraint c
    Subgoal _ g -> traverseGoal g
    Subsoftconstraint _ c -> traverseSoftConstraint c

traverseSuper :: Super -> [Ast]
traverseSuper x =
  AstSuper x :
    case x of
    SuperEmpty _ -> []
    SuperSome _ se -> traverseSetExp se

traverseReference :: Reference -> [Ast]
traverseReference x =
  AstReference x :
    case x of
    ReferenceEmpty _ -> []
    ReferenceSet _ se -> traverseSetExp se
    ReferenceBag _ se -> traverseSetExp se

traverseInit :: Init -> [Ast]
traverseInit x =
  AstInit x :
    case x of
    InitEmpty _ -> []
    InitSome _ ih e -> traverseInitHow ih ++ traverseExp e

traverseInitHow :: InitHow -> [Ast]
traverseInitHow x =
  AstInitHow x : [{- no other children -}]

traverseGCard :: GCard -> [Ast]
traverseGCard x =
  AstGCard x :
    case x of
    GCardEmpty _ -> []
    GCardXor _ -> []
    GCardOr _ -> []
    GCardMux _ -> []
    GCardOpt _ -> []
    GCardInterval _ n -> traverseNCard n

traverseCard :: Card -> [Ast]
traverseCard x =
  AstCard x :
    case x of
    CardEmpty _ -> []
    CardLone _ -> []
    CardSome _ -> []
    CardAny _ -> []
    CardNum _ _ -> []
    CardInterval _ n -> traverseNCard n

traverseNCard :: NCard -> [Ast]
traverseNCard x@(NCard _ _ e) = AstNCard x : traverseExInteger e

traverseExInteger :: ExInteger -> [Ast]
traverseExInteger x =
  AstExInteger x : [{- no other children -}]

traverseName :: Name -> [Ast]
traverseName x@(Path _ m) = AstName x : concatMap traverseModId m

traverseExp :: Exp -> [Ast]
traverseExp x =
  AstExp x :
    case x of
    DeclAllDisj _ d e -> traverseDecl d ++ traverseExp e
    DeclAll _ d e -> traverseDecl d ++ traverseExp e
    DeclQuantDisj _ q d e -> traverseQuant q ++ traverseDecl d ++ traverseExp e
    DeclQuant _ q d e -> traverseQuant q ++ traverseDecl d ++ traverseExp e
    EGMax _ e -> traverseExp e
    EGMin _ e -> traverseExp e
    EIff _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EImplies _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EOr _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EXor _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EAnd _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    ENeg _ e -> traverseExp e
    ELt _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EGt _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EEq _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    ELte _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EGte _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    ENeq _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EIn _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    ENin _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    QuantExp _ q e -> traverseQuant q ++ traverseExp e
    EAdd _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    ESub _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EMul _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    EDiv _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    ECSetExp _ e -> traverseExp e
    EMinExp _ e -> traverseExp e
    EImpliesElse _ e1 e2 e3 -> traverseExp e1 ++ traverseExp e2 ++ traverseExp e3
    EInt _ _ -> []
    EDouble _ _ -> []
    EStr _ _ -> []
    ESetExp _ s -> traverseSetExp s
    _ -> error "Invalid argument given to function traverseExp from Tracing"

traverseSetExp :: SetExp -> [Ast]
traverseSetExp x =
  AstSetExp x :
    case x of
    Union _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    UnionCom _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    Difference _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    Intersection _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    Domain _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    Range _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    Join _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    ClaferId _ n -> traverseName n

traverseDecl :: Decl -> [Ast]
traverseDecl x@(Decl _ l s) =
  AstDecl x : (concatMap traverseLocId l ++ traverseSetExp s)

traverseQuant :: Quant -> [Ast]
traverseQuant x =
  AstQuant x : [{- no other children -}]

traverseEnumId :: EnumId -> [Ast]
traverseEnumId _ = []

traverseModId :: ModId -> [Ast]
traverseModId _ = []

traverseLocId :: LocId -> [Ast]
traverseLocId _ = []

data Ast =
  AstModule Module |
  AstDeclaration Declaration |
  AstClafer Clafer |
  AstConstraint Constraint |
  AstSoftConstraint SoftConstraint |
  AstGoal Goal |
  AstAbstract Abstract |
  AstElements Elements |
  AstElement Element |
  AstSuper Super |
  AstReference Reference |
  AstInit Init |
  AstInitHow InitHow |
  AstGCard GCard |
  AstCard Card |
  AstNCard NCard |
  AstExInteger ExInteger |
  AstName Name |
  AstExp Exp |
  AstSetExp SetExp |
  AstDecl Decl |
  AstQuant Quant |
  AstEnumId EnumId |
  AstModId ModId |
  AstLocId LocId
  deriving (Eq, Show)
