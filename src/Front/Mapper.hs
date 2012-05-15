module Front.Mapper where

import Front.Absclafer

transModule x = case x of
  Module declarations  -> posModule $ map transDeclaration declarations
  _  -> error "no mapping"

posModule declarations = PosModule n0 n declarations
  where
  (n0, n) = case map getPosDeclaration declarations of
              [] -> (0, 0)
              (x:_) -> x

transDeclaration x = case x of
  PosEnumDecl n0 n posident enumids  -> x
  ElementDecl element  -> posElementDecl $ transElement element
  _  -> error "no mapping"

getPosDeclaration x = case x of
  PosEnumDecl n0 n  _ _  -> (n0, n)
  PosElementDecl n0 n _ -> (n0, n)

posElementDecl element = uncurry PosElementDecl (getPosElement element) element

transClafer x = case x of
  Clafer abstract gcard posident super card init elements  -> posClafer (transAbstract abstract) (transGCard gcard) posident (transSuper super) (transCard card) (transInit init) (transElements elements)
  _  -> error "no mapping"

getPosClafer (PosClafer n0 n _ _ _ _ _ _ _) = (n0, n)

posClafer abstract gcard posident super card init elements = uncurry PosClafer
  (getPosAbstract abstract >- getPosGCard gcard >- getPosPosIdent posident >-
   getPosSuper super >- getPosCard card >- getPosInit init >-
   getPosElements elements) abstract gcard posident super card init elements

(>-) (0, 0) (m, n) = (m, n)
(>-) (m, n) (0, 0) = (m, n)
(>-) (m, n) _ = (m, n)

transConstraint x = case x of
  PosConstraint n0 n exps  -> PosConstraint n0 n $ map transExp exps
  _  -> error "no mapping"

getPosConstraint (PosConstraint n0 n _) = (n0, n)

transSoftConstraint x = case x of
  PosSoftConstraint n0 n exps  -> PosSoftConstraint n0 n $ map transExp exps
  _  -> error "no mapping"

getPosSoftConstraint (PosSoftConstraint n0 n _) = (n0, n)

transGoal x = case x of
  PosGoal n0 n exps  -> PosGoal n0 n $ map transExp exps
  _  -> error "no mapping"

getPosGoal (PosGoal n0 n _) = (n0, n)

transAbstract x = case x of
  AbstractEmpty  -> PosAbstractEmpty 0 0
  PosAbstract n0 n  -> x
  _  -> error "no mapping"

getPosAbstract x = case x of
  PosAbstractEmpty n0 n -> (n0, n)
  PosAbstract n0 n  -> (n0, n)

transElements x = case x of
  ElementsEmpty  -> PosElementsEmpty 0 0
  PosElementsList n0 n elements  -> PosElementsList n0 n $ map transElement elements
  _  -> error "no mapping"

getPosElements x = case x of
  PosElementsEmpty n0 n -> (n0, n)
  PosElementsList n0 n _  -> (n0, n)

transElement x = case x of
  Subclafer clafer  -> posSubclafer $ transClafer clafer
  PosClaferUse n0 n name card elements  -> PosClaferUse n0 n (transName name) (transCard card) (transElements elements)
  Subconstraint constraint  -> posSubconstraint $ transConstraint constraint
  Subgoal goal  -> posSubgoal $ transGoal goal
  Subsoftconstraint softconstraint  -> posSubsoftconstraint $ transSoftConstraint softconstraint
  _  -> error "no mapping"

getPosElement x = case x of
  PosSubclafer n0 n _  -> (n0, n)
  PosClaferUse n0 n _ _ _  -> (n0, n)
  PosSubconstraint n0 n _  -> (n0, n)
  PosSubgoal n0 n goal  -> (n0, n)
  PosSubsoftconstraint n0 n _  -> (n0, n)

posSubclafer clafer = uncurry PosSubclafer (getPosClafer clafer) clafer

posSubconstraint constraint = uncurry PosSubconstraint (getPosConstraint constraint) constraint

posSubgoal goal = uncurry PosSubgoal (getPosGoal goal) goal

posSubsoftconstraint softconstraint = uncurry PosSubsoftconstraint (getPosSoftConstraint softconstraint) softconstraint

transSuper x = case x of
  SuperEmpty  -> PosSuperEmpty 0 0
  SuperSome superhow setexp  -> posSuperSome superhow $ transSetExp setexp
  _  -> error "no mapping"

getPosSuper x = case x of
  PosSuperEmpty n0 n -> (n0, n)
  PosSuperSome n0 n superhow setexp  -> (n0, n)

posSuperSome superhow setexp = uncurry PosSuperSome
  (getPosSuperHow superhow >- getPosSetExp setexp) superhow setexp

getPosSuperHow x = case x of
  PosSuperColon n0 n -> (n0, n)
  PosSuperArrow n0 n -> (n0, n)
  PosSuperMArrow n0 n -> (n0, n)

transInit x = case x of
  InitEmpty  -> PosInitEmpty 0 0
  InitSome inithow exp  -> posInitSome inithow $ transExp exp
  _  -> error "no mapping"

getPosInit x = case x of
  PosInitEmpty n0 n -> (n0, n)
  PosInitSome n0 n _ _  -> (n0, n)

posInitSome inithow exp = uncurry PosInitSome (getPosInitHow inithow >- getPosExp exp) inithow exp

getPosInitHow x = case x of
  PosInitHow_1 n0 n -> (n0, n)
  PosInitHow_2 n0 n -> (n0, n)

transGCard x = case x of
  GCardEmpty  -> PosGCardEmpty 0 0
  PosGCardXor n0 n  -> x
  PosGCardOr n0 n  ->  x
  PosGCardMux n0 n  -> x
  PosGCardOpt n0 n  -> x
  GCardInterval ncard  -> posGCardInterval $ transNCard ncard
  _  -> error "no mapping"

getPosGCard x = case x of
  PosGCardEmpty n0 n ->(n0, n)
  PosGCardXor n0 n  -> (n0, n)
  PosGCardOr n0 n  ->  (n0, n)
  PosGCardMux n0 n  -> (n0, n)
  PosGCardOpt n0 n  -> (n0, n)
  PosGCardInterval n0 n ncard  -> (n0, n)

posGCardInterval ncard = uncurry PosGCardInterval (getPosNCard ncard) ncard

transCard x = case x of
  CardEmpty  -> PosCardEmpty 0 0
  PosCardLone n0 n  -> x
  PosCardSome n0 n  -> x
  PosCardAny n0 n  ->  x
  CardNum posinteger  -> posCardNum posinteger
  CardInterval ncard  -> posCardInterval $ transNCard ncard
  _  -> error "no mapping"

getPosCard x = case x of
  PosCardEmpty n0 n  -> (n0, n)
  PosCardLone n0 n  -> (n0, n)
  PosCardSome n0 n  -> (n0, n)
  PosCardAny n0 n  ->  (n0, n)
  PosCardNum n0 n _  -> (n0, n)
  PosCardInterval n0 n _  -> (n0, n)

posCardNum posinteger = uncurry PosCardNum (getPosPosInteger posinteger) posinteger

posCardInterval ncard = uncurry PosCardInterval (getPosNCard ncard) ncard

transNCard x = case x of
  NCard posinteger exinteger  -> posNCard posinteger (transExInteger exinteger)
  _  -> error "no mapping"

getPosNCard (PosNCard n0 n _ _) = (n0, n)

posNCard posinteger exinteger = uncurry PosNCard (getPosPosInteger posinteger >- getPosExInteger exinteger) posinteger exinteger

transExInteger x = case x of
  PosExIntegerAst n0 n  -> x
  ExIntegerNum posinteger  -> posExIntegerNum posinteger
  _  -> error "no mapping"

getPosExInteger x = case x of
  PosExIntegerAst n0 n -> (n0, n)
  PosExIntegerNum n0 n _ -> (n0, n)

posExIntegerNum posinteger = uncurry PosExIntegerNum (getPosPosInteger posinteger) posinteger

transName x = case x of
  Path modids  -> posPath $ map transModId modids
  _  -> error "no mapping"

getPosName (PosPath n0 n _) = (n0, n)

posPath modids = PosPath n0 n modids
  where
  (n0, n) = case map getPosModId modids of
              [] -> (0, 0)
              (x:_) -> x

transExp x = case x of
  PosDeclAllDisj n0 n decl exp  -> PosDeclAllDisj n0 n (transDecl decl) (transExp exp)
  PosDeclAll n0 n decl exp  -> PosDeclAll n0 n (transDecl decl) (transExp exp)
  DeclQuantDisj quant decl exp  -> posDeclQuantDisj (transQuant quant) (transDecl decl) (transExp exp)
  DeclQuant quant decl exp  -> posDeclQuant (transQuant quant) (transDecl decl) (transExp exp)
  PosEGMax n0 n exp  -> PosEGMax n0 n $ transExp exp
  PosEGMin n0 n exp  -> PosEGMin n0 n $ transExp exp
  EIff exp0 exp  -> posBin PosEIff exp0 exp
  EImplies exp0 exp  -> posBin PosEImplies exp0 exp
  EOr exp0 exp  -> posBin PosEOr exp0 exp
  EXor exp0 exp  -> posBin PosEXor exp0 exp
  EAnd exp0 exp  -> posBin PosEAnd exp0 exp
  PosENeg n0 n exp -> PosENeg n0 n $ transExp exp
  ELt exp0 exp  -> posBin PosELt exp0 exp
  EGt exp0 exp  -> posBin PosEGt exp0 exp
  EEq exp0 exp  -> posBin PosEEq exp0 exp
  ELte exp0 exp  -> posBin PosELte exp0 exp
  EGte exp0 exp  -> posBin PosEGte exp0 exp
  ENeq exp0 exp  -> posBin PosENeq exp0 exp
  EIn exp0 exp  -> posBin PosEIn exp0 exp
  ENin exp0 exp  -> posBin PosENin exp0 exp
  QuantExp quant exp  -> posQuantExp (transQuant quant) (transExp exp)
  EAdd exp0 exp  -> posBin PosEAdd exp0 exp
  ESub exp0 exp  -> posBin PosESub exp0 exp
  EMul exp0 exp  -> posBin PosESub exp0 exp
  EDiv exp0 exp  -> posBin PosEDiv exp0 exp
  PosECSetExp n0 n exp  -> PosECSetExp n0 n $ transExp exp
  PosEMinExp n0 n exp  -> PosEMinExp n0 n $ transExp exp
  PosEImpliesElse n0 n exp1 exp2 exp  -> PosEImpliesElse n0 n (transExp exp1) (transExp exp2) (transExp exp)
  EInt posinteger  -> posEInt posinteger
  EDouble posdouble  -> posEDouble posdouble
  EStr posstring  -> posEStr posstring
  ESetExp setexp  -> posESetExp $ transSetExp setexp
  _  -> error "no mapping"

getPosExp x = case x of
  PosDeclAllDisj n0 n _ _ -> (n0, n)
  PosDeclAll n0 n _ _ -> (n0, n)
  PosDeclQuantDisj n0 n _ _ _ -> (n0, n)
  PosDeclQuant n0 n _ _ _ -> (n0, n)
  PosEGMax n0 n exp  -> (n0, n)
  PosEGMin n0 n exp  -> (n0, n)
  PosEIff n0 n _ _ -> (n0, n)
  PosEImplies n0 n _ _ -> (n0, n)
  PosEOr n0 n _ _ -> (n0, n)
  PosEXor n0 n _ _ -> (n0, n)
  PosEAnd n0 n _ _ -> (n0, n)
  PosENeg n0 n _ -> (n0, n)
  PosELt n0 n _ _ -> (n0, n)
  PosEGt n0 n _ _ -> (n0, n)
  PosEEq n0 n _ _ -> (n0, n)
  PosELte n0 n _ _ -> (n0, n)
  PosEGte n0 n _ _ -> (n0, n)
  PosENeq n0 n _ _ -> (n0, n)
  PosEIn n0 n _ _ -> (n0, n)
  PosENin n0 n _ _ -> (n0, n)
  PosQuantExp n0 n _ _ -> (n0, n)
  PosEAdd n0 n _ _ -> (n0, n)
  PosESub n0 n _ _ -> (n0, n)
  PosEMul n0 n _ _ -> (n0, n)
  PosEDiv n0 n _ _ -> (n0, n)
  PosECSetExp n0 n _  -> (n0, n)
  PosEMinExp n0 n _  -> (n0, n)
  PosEImpliesElse n0 n _ _ _ -> (n0, n)
  PosEInt n0 n _  -> (n0, n)
  PosEDouble n0 n _  -> (n0, n)
  PosEStr n0 n _  -> (n0, n)
  PosESetExp n0 n _  -> (n0, n)

posDeclQuantDisj quant decl exp = uncurry PosDeclQuantDisj
  (getPosQuant quant >- getPosDecl decl >- getPosExp exp) quant decl exp

posDeclQuant quant decl exp = uncurry PosDeclQuant
  (getPosQuant quant >- getPosDecl decl >- getPosExp exp) quant decl exp

posBin op exp0 exp = posBin' op exp0 exp transExp getPosExp

posBin' op exp0 exp f g = uncurry op (g exp0' >- g exp') exp0' exp'
  where
  exp0' = f exp0
  exp'  = f  exp

posQuantExp quant exp = uncurry PosQuantExp (getPosQuant quant >- getPosExp exp) quant exp

posEInt posinteger = uncurry PosEInt (getPosPosInteger posinteger) posinteger

posEDouble posdouble = uncurry PosEDouble (getPosPosDouble posdouble) posdouble

posEStr posstring = uncurry PosEStr (getPosPosString posstring) posstring

posESetExp setexp = uncurry PosESetExp (getPosSetExp setexp) setexp

transSetExp x = case x of
  Union setexp0 setexp  -> posSBin PosUnion setexp0 setexp
  UnionCom setexp0 setexp  -> posSBin PosUnionCom setexp0 setexp
  Difference setexp0 setexp  -> posSBin PosDifference setexp0 setexp
  Intersection setexp0 setexp  -> posSBin PosIntersection setexp0 setexp
  Domain setexp0 setexp  -> posSBin PosDomain setexp0 setexp
  Range setexp0 setexp  -> posSBin PosRange setexp0 setexp
  Join setexp0 setexp  -> posSBin PosJoin setexp0 setexp
  ClaferId name  -> posClaferId $ transName name
  _  -> error "no mapping"

getPosSetExp x = case x of
  PosUnion n0 n _ _ -> (n0, n)
  PosUnionCom n0 n _ _ -> (n0, n)
  PosDifference n0 n _ _ -> (n0, n)
  PosIntersection n0 n _ _ -> (n0, n)
  PosDomain n0 n _ _ -> (n0, n)
  PosRange n0 n _ _ -> (n0, n)
  PosJoin n0 n _ _ -> (n0, n)
  PosClaferId n0 n _  -> (n0, n)

posSBin op exp0 exp = posBin' op exp0 exp transSetExp getPosSetExp

posClaferId name = uncurry PosClaferId (getPosName name) name

transDecl x = case x of
  Decl locids setexp  -> posDecl (map transLocId locids) (transSetExp setexp)
  _  -> error "no mapping"

getPosDecl (PosDecl n0 n _ _) = (n0, n)

posDecl locids setexp = uncurry PosDecl (l >- getPosSetExp setexp) locids setexp
  where
  l = case map getPosLocId locids of
        [] -> (0, 0)
        (x:_) -> x

transQuant x = case x of
  PosQuantNo n0 n  -> x
  PosQuantLone n0 n  -> x
  PosQuantOne n0 n  ->  x
  PosQuantSome n0 n  -> x
  _  -> error "no mapping"

getPosQuant x = case x of
  PosQuantNo n0 n  -> (n0, n)
  PosQuantLone n0 n  -> (n0, n)
  PosQuantOne n0 n  ->  (n0, n)
  PosQuantSome n0 n  -> (n0, n)

transEnumId x = case x of
  EnumIdIdent posident  -> posEnumIdIdent posident
  _  -> error "no mapping"

posEnumIdIdent posident = uncurry PosEnumIdIdent (getPosPosIdent posident) posident

transModId x = case x of
  ModIdIdent posident  -> posModIdIdent posident
  _  -> error "no mapping"

getPosModId x = case x of
  ModIdIdent posident  -> getPosPosIdent posident

posModIdIdent posident = uncurry PosModIdIdent (getPosPosIdent posident) posident

transLocId x = case x of
  LocIdIdent posident  -> posLocIdIdent posident
  _  -> error "no mapping"

getPosLocId (PosLocIdIdent n0 n _) = (n0, n)

posLocIdIdent posident = uncurry PosLocIdIdent (getPosPosIdent posident) posident

getPosPosInteger (PosInteger ((n0, n), _)) = (toInteger n0, toInteger n)
getPosPosDouble  (PosDouble ((n0, n), _)) = (toInteger n0, toInteger n)
getPosPosString  (PosString ((n0, n), _)) = (toInteger n0, toInteger n)
getPosPosIdent   (PosIdent ((n0, n), _)) = (toInteger n0, toInteger n)