module Language.Clafer.Intermediate.Tracing (traceIrModule, traceAstModule, Ir(..), Ast(..)) where

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Language.Clafer.Front.Absclafer
import Language.Clafer.Front.Mapper
import Language.Clafer.Intermediate.Intclafer
import qualified Language.Clafer.Intermediate.Intclafer as I

insert k a = Map.insertWith (++) k [a]

traceIrModule :: IModule -> Map Span [Ir]
traceIrModule IModule{mDecls = decls} =
  foldr
    traceIrElement
    Map.empty
    decls

traceIrElement (IEClafer clafer) m = traceIrClafer clafer m
traceIrElement IEConstraint{cpexp = pexp} m = traceIrPExp pexp m
traceIrElement IEGoal{cpexp = pexp} m = traceIrPExp pexp m

traceIrClafer c@IClafer{cinPos = span, super = super, elements = elements} m =
  foldr
    traceIrElement
    (traceIrSuper super $ insert span (IRClafer c) m)
    elements
    
traceIrSuper ISuper{supers = supers} m =
  foldr
    traceIrPExp
    m
    supers
    
traceIrPExp p@PExp{inPos = span, I.exp = e} m =
  traceIrExp
    e
    (insert span (IRPExp p) m)
    
traceIrExp IDeclPExp{oDecls = decls, bpexp = pexp} m =
  foldr
    traceIrPExp
    m
    (pexp : map body decls)
traceIrExp IFunExp{exps = exps} m =
  foldr
    traceIrPExp
    m
    exps
traceIrExp _ m = m


traceAstModule :: Module -> Map Span [Ast]
traceAstModule x =
  foldr
    ins
    Map.empty
    (traverseModule x)
  where
  ins x = insert (i x) x
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

traverseModule x@(PosModule _ d) = AstModule x : concatMap traverseDeclaration d

traverseDeclaration x =
  AstDeclaration x :
    case x of
    PosEnumDecl _ _ e -> concatMap traverseEnumId e
    PosElementDecl _ e -> traverseElement e

traverseClafer x@(PosClafer s a b _ d e f g) = AstClafer x : (traverseAbstract a ++ traverseGCard b ++ traverseSuper d ++ traverseCard e ++ traverseInit f ++ traverseElements g)

traverseConstraint x@(PosConstraint s e) = AstConstraint x : concatMap traverseExp e

traverseSoftConstraint x@(PosSoftConstraint s e) = AstSoftConstraint x : concatMap traverseExp e

traverseGoal x@(PosGoal s e) = AstGoal x : concatMap traverseExp e

traverseAbstract x =
  AstAbstract x : [{- no other children -}]

traverseElements x =
  AstElements x :
    case x of
    PosElementsEmpty _ -> []
    PosElementsList _ e -> concatMap traverseElement e

traverseElement x =
  AstElement x :
    case x of
    PosSubclafer _ c -> traverseClafer c
    PosClaferUse _ n c e -> traverseName n ++ traverseCard c ++ traverseElements e
    PosSubconstraint _ c -> traverseConstraint c
    PosSubgoal _ g -> traverseGoal g
    PosSubsoftconstraint _ c -> traverseSoftConstraint c

traverseSuper x =
  AstSuper x :
    case x of
    PosSuperEmpty _ -> []
    PosSuperSome _ sh se -> traverseSuperHow sh ++ traverseSetExp se

traverseSuperHow x =
  AstSuperHow x : [{- no other children -}]

traverseInit x =
  AstInit x :
    case x of
    PosInitEmpty _ -> []
    PosInitSome _ ih e -> traverseInitHow ih ++ traverseExp e

traverseInitHow x =
  AstInitHow x : [{- no other children -}]

traverseGCard x =
  AstGCard x :
    case x of
    PosGCardEmpty _ -> []
    PosGCardXor _ -> []
    PosGCardOr _ -> []
    PosGCardMux _ -> []
    PosGCardOpt _ -> []
    PosGCardInterval _ n -> traverseNCard n

traverseCard x =
  AstCard x :
    case x of
    PosCardEmpty _ -> []
    PosCardLone _ -> []
    PosCardSome _ -> []
    PosCardAny _ -> []
    PosCardNum _ _ -> []
    PosCardInterval _ n -> traverseNCard n

traverseNCard x@(PosNCard _ _ e) = AstNCard x : traverseExInteger e

traverseExInteger x =
  AstExInteger x : [{- no other children -}]

traverseName x@(PosPath _ m) = AstName x : concatMap traverseModId m

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

traverseDecl x@(PosDecl _ l s) =
  AstDecl x : (concatMap traverseLocId l ++ traverseSetExp s)

traverseQuant x =
  AstQuant x : [{- no other children -}]

traverseEnumId _ = []

traverseModId _ = []

traverseLocId _ = []

data Ir =
  IRClafer IClafer |
  IRPExp PExp
  deriving Show
  
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
  deriving Show
