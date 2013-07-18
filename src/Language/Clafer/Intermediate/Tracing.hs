{-# LANGUAGE RankNTypes, KindSignatures, FlexibleContexts #-}
module Language.Clafer.Intermediate.Tracing (traceIrModule, traceAstModule, Ast(..)) where

import Data.Map (Map)
import qualified Data.Map as Map
import Language.Clafer.Front.Absclafer
import Language.Clafer.Front.Mapper
import Language.Clafer.Intermediate.Intclafer

insert :: forall a. Span -> a -> Map Span [a] -> Map Span [a]
insert k a = Map.insertWith (++) k [a]

traceIrModule :: IModule -> Map Span [Ir] --Map Span [Union (IRClafer IClafer) (IRPExp PExp)]
traceIrModule = foldMapIR getMap 
  where
    getMap :: Ir -> Map Span [Ir] --Map Span [Union (IRClafer IClafer) (IRPExp PExp)]
    getMap (IRPExp (p@PExp{inPos = s})) = insert s (IRPExp p) Map.empty
    getMap (IRClafer (c@IClafer{cinPos = s})) = insert s (IRClafer c) Map.empty
    getMap _ = Map.empty

traceAstModule :: Module -> Map Span [Ast]
traceAstModule x =
  foldr
    ins
    Map.empty
    (traverseModule x)
  where
  ins y = insert (i y) y
  i (AstModule a) = range a
  i (AstDeclaration a) = range a
  i (AstClafer a) = range a
  i (AstConstraint a) = range a
  i (AstSoftConstraint a) = range a
  i (AstGoal a) = range a
  i (AstAbstract a) = range a
  i (AstElements a) = range a
  i (AstElement a) = range a
  i (AstSuper a) = range a
  i (AstSuperHow a) = range a
  i (AstInit a) = range a
  i (AstInitHow a) = range a
  i (AstGCard a) = range a
  i (AstCard a) = range a
  i (AstNCard a) = range a
  i (AstExInteger a) = range a
  i (AstName a) = range a
  i (AstExp a) = range a
  i (AstSetExp a) = range a
  i (AstDecl a) = range a
  i (AstQuant a) = range a
  i (AstEnumId a) = range a
  i (AstModId a) = range a
  i (AstLocId a) = range a

traverseModule :: Module -> [Ast]
traverseModule x@(PosModule _ d) = AstModule x : concatMap traverseDeclaration d
traverseModule x@(Module d) = AstModule x : concatMap traverseDeclaration d -- should never happen

traverseDeclaration :: Declaration -> [Ast]
traverseDeclaration x =
  AstDeclaration x :
    case x of
    PosEnumDecl _ _ e -> concatMap traverseEnumId e
    PosElementDecl _ e -> traverseElement e
    EnumDecl _ e -> concatMap traverseEnumId e  -- These bottom two should not happen
    ElementDecl e -> traverseElement e          -- should always be given a Pos

traverseClafer :: Clafer -> [Ast]
traverseClafer x@(PosClafer _ a b _ d e f g) = AstClafer x : (traverseAbstract a ++ traverseGCard b ++ traverseSuper d ++ traverseCard e ++ traverseInit f ++ traverseElements g)
traverseClafer x@(Clafer a b _ d e f g) = AstClafer x : (traverseAbstract a ++ traverseGCard b ++ traverseSuper d ++ traverseCard e ++ traverseInit f ++ traverseElements g) -- Should never happen

traverseConstraint :: Constraint -> [Ast]
traverseConstraint x@(PosConstraint _ e) = AstConstraint x : concatMap traverseExp e
traverseConstraint x@(Constraint e) = AstConstraint x : concatMap traverseExp e -- This should never happen

traverseSoftConstraint :: SoftConstraint -> [Ast]
traverseSoftConstraint x@(PosSoftConstraint _ e) = AstSoftConstraint x : concatMap traverseExp e
traverseSoftConstraint x@(SoftConstraint e) = AstSoftConstraint x : concatMap traverseExp e -- This should never happen

traverseGoal :: Goal -> [Ast]
traverseGoal x@(PosGoal _ e) = AstGoal x : concatMap traverseExp e
traverseGoal x@(Goal e) = AstGoal x : concatMap traverseExp e -- This should never happen

traverseAbstract :: Abstract -> [Ast]
traverseAbstract x =
  AstAbstract x : [{- no other children -}]

traverseElements :: Elements -> [Ast]
traverseElements x =
  AstElements x :
    case x of
    PosElementsEmpty _ -> []
    PosElementsList _ e -> concatMap traverseElement e
    ElementsEmpty -> [] -- These bottom two should not happen, should always be given a Pos
    ElementsList e -> concatMap traverseElement e

traverseElement :: Element -> [Ast]
traverseElement x =
  AstElement x :
    case x of
    PosSubclafer _ c -> traverseClafer c
    PosClaferUse _ n c e -> traverseName n ++ traverseCard c ++ traverseElements e
    PosSubconstraint _ c -> traverseConstraint c
    PosSubgoal _ g -> traverseGoal g
    PosSubsoftconstraint _ c -> traverseSoftConstraint c
    Subclafer c -> traverseClafer c                                           -- This and bellow should never happen
    ClaferUse n c e -> traverseName n ++ traverseCard c ++ traverseElements e -- should always be given a Pos
    Subconstraint c -> traverseConstraint c
    Subgoal g -> traverseGoal g
    Subsoftconstraint c -> traverseSoftConstraint c

traverseSuper :: Super -> [Ast]
traverseSuper x =
  AstSuper x :
    case x of
    PosSuperEmpty _ -> []
    PosSuperSome _ sh se -> traverseSuperHow sh ++ traverseSetExp se
    SuperEmpty -> [] -- These bottom two should not happen, should always be given a Pos
    SuperSome sh se -> traverseSuperHow sh ++ traverseSetExp se

traverseSuperHow :: SuperHow -> [Ast]
traverseSuperHow x =
  AstSuperHow x : [{- no other children -}]

traverseInit :: Init -> [Ast]
traverseInit x =
  AstInit x :
    case x of
    PosInitEmpty _ -> []
    PosInitSome _ ih e -> traverseInitHow ih ++ traverseExp e
    InitEmpty -> [] -- These bottom two should not happen, should always be given a Pos
    InitSome ih e -> traverseInitHow ih ++ traverseExp e

traverseInitHow :: InitHow -> [Ast]
traverseInitHow x =
  AstInitHow x : [{- no other children -}]

traverseGCard :: GCard -> [Ast]
traverseGCard x =
  AstGCard x :
    case x of
    PosGCardEmpty _ -> []
    PosGCardXor _ -> []
    PosGCardOr _ -> []
    PosGCardMux _ -> []
    PosGCardOpt _ -> []
    PosGCardInterval _ n -> traverseNCard n
    GCardEmpty -> [] -- This and bellow should not happen
    GCardXor -> []   -- should always be given a Pos
    GCardOr -> []
    GCardMux -> []
    GCardOpt -> []
    GCardInterval n -> traverseNCard n

traverseCard :: Card -> [Ast]
traverseCard x =
  AstCard x :
    case x of
    PosCardEmpty _ -> []
    PosCardLone _ -> []
    PosCardSome _ -> []
    PosCardAny _ -> []
    PosCardNum _ _ -> []
    PosCardInterval _ n -> traverseNCard n
    CardEmpty -> [] -- This and Bellow Should not happen
    CardLone -> []  -- Should always been given a Pos
    CardSome -> []
    CardAny -> []
    CardNum _ -> []
    CardInterval n -> traverseNCard n

traverseNCard :: NCard -> [Ast]
traverseNCard x@(PosNCard _ _ e) = AstNCard x : traverseExInteger e
traverseNCard x@(NCard _ e) = AstNCard x : traverseExInteger e -- Should never happen

traverseExInteger :: ExInteger -> [Ast]
traverseExInteger x =
  AstExInteger x : [{- no other children -}]

traverseName :: Name -> [Ast]
traverseName x@(PosPath _ m) = AstName x : concatMap traverseModId m
traverseName x@(Path m) = AstName x : concatMap traverseModId m -- Should never happen

traverseExp :: Exp -> [Ast]
traverseExp x =
  AstExp x :
    case x of
    PosDeclAllDisj _ d e -> traverseDecl d ++ traverseExp e
    PosDeclAll _ d e -> traverseDecl d ++ traverseExp e
    PosDeclQuantDisj _ q d e -> traverseQuant q ++ traverseDecl d ++ traverseExp e
    PosDeclQuant _ q d e -> traverseQuant q ++ traverseDecl d ++ traverseExp e
    PosEGMax _ e -> traverseExp e
    PosEGMin _ e -> traverseExp e
    PosEIff _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEImplies _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEOr _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEXor _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEAnd _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosENeg _ e -> traverseExp e
    PosELt _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEGt _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEEq _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosELte _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEGte _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosENeq _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEIn _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosENin _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosQuantExp _ q e -> traverseQuant q ++ traverseExp e
    PosEAdd _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosESub _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEMul _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosEDiv _ e1 e2 -> traverseExp e1 ++ traverseExp e2
    PosECSetExp _ e -> traverseExp e
    PosEMinExp _ e -> traverseExp e
    PosEImpliesElse _ e1 e2 e3 -> traverseExp e1 ++ traverseExp e2 ++ traverseExp e3
    PosEInt _ _ -> []
    PosEDouble _ _ -> []
    PosEStr _ _ -> []
    PosESetExp _ s -> traverseSetExp s
    DeclAllDisj d e -> traverseDecl d ++ traverseExp e                        -- This and Bellow should not happen
    DeclAll d e -> traverseDecl d ++ traverseExp e                            -- Should always be given a Pos
    DeclQuantDisj q d e -> traverseQuant q ++ traverseDecl d ++ traverseExp e
    DeclQuant q d e -> traverseQuant q ++ traverseDecl d ++ traverseExp e
    EGMax e -> traverseExp e
    EGMin e -> traverseExp e
    EIff e1 e2 -> traverseExp e1 ++ traverseExp e2
    EImplies e1 e2 -> traverseExp e1 ++ traverseExp e2
    EOr e1 e2 -> traverseExp e1 ++ traverseExp e2
    EXor e1 e2 -> traverseExp e1 ++ traverseExp e2
    EAnd e1 e2 -> traverseExp e1 ++ traverseExp e2
    ENeg e -> traverseExp e
    ELt e1 e2 -> traverseExp e1 ++ traverseExp e2
    EGt e1 e2 -> traverseExp e1 ++ traverseExp e2
    EEq e1 e2 -> traverseExp e1 ++ traverseExp e2
    ELte e1 e2 -> traverseExp e1 ++ traverseExp e2
    EGte e1 e2 -> traverseExp e1 ++ traverseExp e2
    ENeq e1 e2 -> traverseExp e1 ++ traverseExp e2
    EIn e1 e2 -> traverseExp e1 ++ traverseExp e2
    ENin e1 e2 -> traverseExp e1 ++ traverseExp e2
    QuantExp q e -> traverseQuant q ++ traverseExp e
    EAdd e1 e2 -> traverseExp e1 ++ traverseExp e2
    ESub e1 e2 -> traverseExp e1 ++ traverseExp e2
    EMul e1 e2 -> traverseExp e1 ++ traverseExp e2
    EDiv e1 e2 -> traverseExp e1 ++ traverseExp e2
    ECSetExp e -> traverseExp e
    EMinExp e -> traverseExp e
    EImpliesElse e1 e2 e3 -> traverseExp e1 ++ traverseExp e2 ++ traverseExp e3
    EInt _ -> []
    EDouble _ -> []
    EStr _ -> []
    ESetExp s -> traverseSetExp s
    _ -> error "Invalid argument given to function traverseExp from Tracing" -- Should never happen

traverseSetExp :: SetExp -> [Ast]
traverseSetExp x =
  AstSetExp x :
    case x of
    PosUnion _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    PosUnionCom _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    PosDifference _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    PosIntersection _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    PosDomain _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    PosRange _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    PosJoin _ s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    PosClaferId _ n -> traverseName n
    Union s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2    -- This and Bellow Should not happen
    UnionCom s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2 -- It should also be given a Pos
    Difference s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    Intersection s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    Domain s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    Range s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    Join s1 s2 -> traverseSetExp s1 ++ traverseSetExp s2
    ClaferId n -> traverseName n

traverseDecl :: Decl -> [Ast]
traverseDecl x@(PosDecl _ l s) =
  AstDecl x : (concatMap traverseLocId l ++ traverseSetExp s)
traverseDecl x@(Decl l s) = 
  AstDecl x : (concatMap traverseLocId l ++ traverseSetExp s) -- Should never happen

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
  AstSuperHow SuperHow |
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