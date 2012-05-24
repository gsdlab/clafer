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
module Language.Clafer.Front.Mapper where

import Language.Clafer.Front.Absclafer

mapModule :: Module -> Module
mapModule x = case x of
  Module declarations  -> posModule $ map mapDeclaration declarations
  _  -> error "no module mapping"

posModule :: [Declaration] -> Module
posModule declarations = PosModule n0 n declarations
  where
  (n0, n) = case map getPosDeclaration declarations of
              [] -> (0, 0)
              (x:_) -> x

mapDeclaration :: Declaration -> Declaration
mapDeclaration x = case x of
  PosEnumDecl n0 n posident enumids  -> x
  ElementDecl element  -> posElementDecl $ mapElement element
  _  -> error "no declaration mapping"

getPosDeclaration :: Declaration -> (Integer, Integer)
getPosDeclaration x = case x of
  PosEnumDecl n0 n  _ _  -> (n0, n)
  PosElementDecl n0 n _ -> (n0, n)

posElementDecl :: Element -> Declaration
posElementDecl element = uncurry PosElementDecl (getPosElement element) element

mapClafer :: Clafer -> Clafer
mapClafer x = case x of
  Clafer abstract gcard posident super card init elements  -> posClafer (mapAbstract abstract) (mapGCard gcard) posident (mapSuper super) (mapCard card) (mapInit init) (mapElements elements)
  _  -> error "no elementDecl mapping"

getPosClafer :: Clafer -> (Integer, Integer)
getPosClafer (PosClafer n0 n _ _ _ _ _ _ _) = (n0, n)

posClafer :: Abstract
                        -> GCard
                        -> PosIdent
                        -> Super
                        -> Card
                        -> Init
                        -> Elements
                        -> Clafer
posClafer abstract gcard posident super card init elements = uncurry PosClafer
  (getPosAbstract abstract >- getPosGCard gcard >- getPosPosIdent posident >-
   getPosSuper super >- getPosCard card >- getPosInit init >-
   getPosElements elements) abstract gcard posident super card init elements

(>-) :: (Num t1, Num t) => (t, t1) -> (t, t1) -> (t, t1)
(>-) (0, 0) (m, n) = (m, n)
(>-) (m, n) (0, 0) = (m, n)
(>-) (m, n) _ = (m, n)

mapConstraint :: Constraint -> Constraint
mapConstraint x = case x of
  PosConstraint n0 n exps  -> PosConstraint n0 n $ map mapExp exps
  _  -> error "no constraint mapping"

getPosConstraint :: Constraint -> (Integer, Integer)
getPosConstraint (PosConstraint n0 n _) = (n0, n)

mapSoftConstraint :: SoftConstraint -> SoftConstraint
mapSoftConstraint x = case x of
  PosSoftConstraint n0 n exps  -> PosSoftConstraint n0 n $ map mapExp exps
  _  -> error "no softConstraint mapping"

getPosSoftConstraint :: SoftConstraint -> (Integer, Integer)
getPosSoftConstraint (PosSoftConstraint n0 n _) = (n0, n)

mapGoal :: Goal -> Goal
mapGoal x = case x of
  PosGoal n0 n exps  -> PosGoal n0 n $ map mapExp exps
  _  -> error "no goal mapping"

getPosGoal :: Goal -> (Integer, Integer)
getPosGoal (PosGoal n0 n _) = (n0, n)

mapAbstract :: Abstract -> Abstract
mapAbstract x = case x of
  AbstractEmpty  -> PosAbstractEmpty 0 0
  PosAbstract n0 n  -> x
  _  -> error "no abstract mapping"

getPosAbstract :: Abstract -> (Integer, Integer)
getPosAbstract x = case x of
  PosAbstractEmpty n0 n -> (n0, n)
  PosAbstract n0 n  -> (n0, n)

mapElements :: Elements -> Elements
mapElements x = case x of
  ElementsEmpty  -> PosElementsEmpty 0 0
  PosElementsList n0 n elements  -> PosElementsList n0 n $ map mapElement elements
  _  -> error "no elements mapping"

getPosElements :: Elements -> (Integer, Integer)
getPosElements x = case x of
  PosElementsEmpty n0 n -> (n0, n)
  PosElementsList n0 n _  -> (n0, n)

mapElement :: Element -> Element
mapElement x = case x of
  Subclafer clafer  -> posSubclafer $ mapClafer clafer
  PosClaferUse n0 n name card elements  -> PosClaferUse n0 n (mapName name) (mapCard card) (mapElements elements)
  Subconstraint constraint  -> posSubconstraint $ mapConstraint constraint
  Subgoal goal  -> posSubgoal $ mapGoal goal
  Subsoftconstraint softconstraint  -> posSubsoftconstraint $ mapSoftConstraint softconstraint
  _  -> error "no element mapping"

getPosElement :: Element -> (Integer, Integer)
getPosElement x = case x of
  PosSubclafer n0 n _  -> (n0, n)
  PosClaferUse n0 n _ _ _  -> (n0, n)
  PosSubconstraint n0 n _  -> (n0, n)
  PosSubgoal n0 n goal  -> (n0, n)
  PosSubsoftconstraint n0 n _  -> (n0, n)

posSubclafer :: Clafer -> Element
posSubclafer clafer = uncurry PosSubclafer (getPosClafer clafer) clafer

posSubconstraint :: Constraint -> Element
posSubconstraint constraint = uncurry PosSubconstraint (getPosConstraint constraint) constraint

posSubgoal :: Goal -> Element
posSubgoal goal = uncurry PosSubgoal (getPosGoal goal) goal

posSubsoftconstraint :: SoftConstraint -> Element
posSubsoftconstraint softconstraint = uncurry PosSubsoftconstraint (getPosSoftConstraint softconstraint) softconstraint

mapSuper :: Super -> Super
mapSuper x = case x of
  SuperEmpty  -> PosSuperEmpty 0 0
  SuperSome superhow setexp  -> posSuperSome superhow $ mapSetExp setexp
  _  -> error "no super mapping"

getPosSuper :: Super -> (Integer, Integer)
getPosSuper x = case x of
  PosSuperEmpty n0 n -> (n0, n)
  PosSuperSome n0 n superhow setexp  -> (n0, n)

posSuperSome :: SuperHow -> SetExp -> Super
posSuperSome superhow setexp = uncurry PosSuperSome
  (getPosSuperHow superhow >- getPosSetExp setexp) superhow setexp

getPosSuperHow :: SuperHow -> (Integer, Integer)
getPosSuperHow x = case x of
  PosSuperColon n0 n -> (n0, n)
  PosSuperArrow n0 n -> (n0, n)
  PosSuperMArrow n0 n -> (n0, n)

mapInit :: Init -> Init
mapInit x = case x of
  InitEmpty  -> PosInitEmpty 0 0
  InitSome inithow exp  -> posInitSome inithow $ mapExp exp
  _  -> error "no init mapping"

getPosInit :: Init -> (Integer, Integer)
getPosInit x = case x of
  PosInitEmpty n0 n -> (n0, n)
  PosInitSome n0 n _ _  -> (n0, n)

posInitSome :: InitHow -> Exp -> Init
posInitSome inithow exp = uncurry PosInitSome (getPosInitHow inithow >- getPosExp exp) inithow exp

getPosInitHow :: InitHow -> (Integer, Integer)
getPosInitHow x = case x of
  PosInitHow_1 n0 n -> (n0, n)
  PosInitHow_2 n0 n -> (n0, n)

mapGCard :: GCard -> GCard
mapGCard x = case x of
  GCardEmpty  -> PosGCardEmpty 0 0
  PosGCardXor n0 n  -> x
  PosGCardOr n0 n  ->  x
  PosGCardMux n0 n  -> x
  PosGCardOpt n0 n  -> x
  GCardInterval ncard  -> posGCardInterval $ mapNCard ncard
  _  -> error "no gcard mapping"

getPosGCard :: GCard -> (Integer, Integer)
getPosGCard x = case x of
  PosGCardEmpty n0 n ->(n0, n)
  PosGCardXor n0 n  -> (n0, n)
  PosGCardOr n0 n  ->  (n0, n)
  PosGCardMux n0 n  -> (n0, n)
  PosGCardOpt n0 n  -> (n0, n)
  PosGCardInterval n0 n ncard  -> (n0, n)

posGCardInterval :: NCard -> GCard
posGCardInterval ncard = uncurry PosGCardInterval (getPosNCard ncard) ncard

mapCard :: Card -> Card
mapCard x = case x of
  CardEmpty  -> PosCardEmpty 0 0
  PosCardLone n0 n  -> x
  PosCardSome n0 n  -> x
  PosCardAny n0 n  ->  x
  CardNum posinteger  -> posCardNum posinteger
  CardInterval ncard  -> posCardInterval $ mapNCard ncard
  _  -> error "no card mapping"

getPosCard :: Card -> (Integer, Integer)
getPosCard x = case x of
  PosCardEmpty n0 n  -> (n0, n)
  PosCardLone n0 n  -> (n0, n)
  PosCardSome n0 n  -> (n0, n)
  PosCardAny n0 n  ->  (n0, n)
  PosCardNum n0 n _  -> (n0, n)
  PosCardInterval n0 n _  -> (n0, n)

posCardNum :: PosInteger -> Card
posCardNum posinteger = uncurry PosCardNum (getPosPosInteger posinteger) posinteger

posCardInterval :: NCard -> Card
posCardInterval ncard = uncurry PosCardInterval (getPosNCard ncard) ncard

mapNCard :: NCard -> NCard
mapNCard x = case x of
  NCard posinteger exinteger  -> posNCard posinteger (mapExInteger exinteger)
  _  -> error "no ncard mapping"

getPosNCard :: NCard -> (Integer, Integer)
getPosNCard (PosNCard n0 n _ _) = (n0, n)

posNCard :: PosInteger -> ExInteger -> NCard
posNCard posinteger exinteger = uncurry PosNCard (getPosPosInteger posinteger >- getPosExInteger exinteger) posinteger exinteger

mapExInteger :: ExInteger -> ExInteger
mapExInteger x = case x of
  PosExIntegerAst n0 n  -> x
  ExIntegerNum posinteger  -> posExIntegerNum posinteger
  _  -> error "no exinteger mapping"

getPosExInteger :: ExInteger -> (Integer, Integer)
getPosExInteger x = case x of
  PosExIntegerAst n0 n -> (n0, n)
  PosExIntegerNum n0 n _ -> (n0, n)

posExIntegerNum :: PosInteger -> ExInteger
posExIntegerNum posinteger = uncurry PosExIntegerNum (getPosPosInteger posinteger) posinteger

mapName :: Name -> Name
mapName x = case x of
  Path modids  -> posPath $ map mapModId modids
  _  -> error "no name mapping"

getPosName :: Name -> (Integer, Integer)
getPosName (PosPath n0 n _) = (n0, n)

posPath :: [ModId] -> Name
posPath modids = PosPath n0 n modids
  where
  (n0, n) = case map getPosModId modids of
              [] -> (0, 0)
              (x:_) -> x

mapExp :: Exp -> Exp
mapExp x = case x of
  PosDeclAllDisj n0 n decl exp  -> PosDeclAllDisj n0 n (mapDecl decl) (mapExp exp)
  PosDeclAll n0 n decl exp  -> PosDeclAll n0 n (mapDecl decl) (mapExp exp)
  DeclQuantDisj quant decl exp  -> posDeclQuantDisj (mapQuant quant) (mapDecl decl) (mapExp exp)
  DeclQuant quant decl exp  -> posDeclQuant (mapQuant quant) (mapDecl decl) (mapExp exp)
  PosEGMax n0 n exp  -> PosEGMax n0 n $ mapExp exp
  PosEGMin n0 n exp  -> PosEGMin n0 n $ mapExp exp
  EIff exp0 exp  -> posBin PosEIff exp0 exp
  EImplies exp0 exp  -> posBin PosEImplies exp0 exp
  EOr exp0 exp  -> posBin PosEOr exp0 exp
  EXor exp0 exp  -> posBin PosEXor exp0 exp
  EAnd exp0 exp  -> posBin PosEAnd exp0 exp
  PosENeg n0 n exp -> PosENeg n0 n $ mapExp exp
  ELt exp0 exp  -> posBin PosELt exp0 exp
  EGt exp0 exp  -> posBin PosEGt exp0 exp
  EEq exp0 exp  -> posBin PosEEq exp0 exp
  ELte exp0 exp  -> posBin PosELte exp0 exp
  EGte exp0 exp  -> posBin PosEGte exp0 exp
  ENeq exp0 exp  -> posBin PosENeq exp0 exp
  EIn exp0 exp  -> posBin PosEIn exp0 exp
  ENin exp0 exp  -> posBin PosENin exp0 exp
  QuantExp quant exp  -> posQuantExp (mapQuant quant) (mapExp exp)
  EAdd exp0 exp  -> posBin PosEAdd exp0 exp
  ESub exp0 exp  -> posBin PosESub exp0 exp
  EMul exp0 exp  -> posBin PosESub exp0 exp
  EDiv exp0 exp  -> posBin PosEDiv exp0 exp
  PosECSetExp n0 n exp  -> PosECSetExp n0 n $ mapExp exp
  PosEMinExp n0 n exp  -> PosEMinExp n0 n $ mapExp exp
  PosEImpliesElse n0 n exp1 exp2 exp  -> PosEImpliesElse n0 n (mapExp exp1) (mapExp exp2) (mapExp exp)
  EInt posinteger  -> posEInt posinteger
  EDouble posdouble  -> posEDouble posdouble
  EStr posstring  -> posEStr posstring
  ESetExp setexp  -> posESetExp $ mapSetExp setexp
  x  -> error $ "no exp mapping: " ++ show x

getPosExp :: Exp -> (Integer, Integer)
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

posDeclQuantDisj :: Quant -> Decl -> Exp -> Exp
posDeclQuantDisj quant decl exp = uncurry PosDeclQuantDisj
  (getPosQuant quant >- getPosDecl decl >- getPosExp exp) quant decl exp

posDeclQuant :: Quant -> Decl -> Exp -> Exp
posDeclQuant quant decl exp = uncurry PosDeclQuant
  (getPosQuant quant >- getPosDecl decl >- getPosExp exp) quant decl exp

posBin :: (Integer -> Integer -> Exp -> Exp -> t) -> Exp -> Exp -> t
posBin op exp0 exp = posBin' op exp0 exp mapExp getPosExp

posBin' :: (Num a, Num b) =>
                      (a -> b -> t2 -> t2 -> t)
                      -> t1
                      -> t1
                      -> (t1 -> t2)
                      -> (t2 -> (a, b))
                      -> t
posBin' op exp0 exp f g = uncurry op (g exp0' >- g exp') exp0' exp'
  where
  exp0' = f exp0
  exp'  = f  exp

posQuantExp :: Quant -> Exp -> Exp
posQuantExp quant exp = uncurry PosQuantExp (getPosQuant quant >- getPosExp exp) quant exp

posEInt :: PosInteger -> Exp
posEInt posinteger = uncurry PosEInt (getPosPosInteger posinteger) posinteger

posEDouble :: PosDouble -> Exp
posEDouble posdouble = uncurry PosEDouble (getPosPosDouble posdouble) posdouble

posEStr :: PosString -> Exp
posEStr posstring = uncurry PosEStr (getPosPosString posstring) posstring

posESetExp :: SetExp -> Exp
posESetExp setexp = uncurry PosESetExp (getPosSetExp setexp) setexp

mapSetExp x = case x of
  Union setexp0 setexp  -> posSBin PosUnion setexp0 setexp
  UnionCom setexp0 setexp  -> posSBin PosUnionCom setexp0 setexp
  Difference setexp0 setexp  -> posSBin PosDifference setexp0 setexp
  Intersection setexp0 setexp  -> posSBin PosIntersection setexp0 setexp
  Domain setexp0 setexp  -> posSBin PosDomain setexp0 setexp
  Range setexp0 setexp  -> posSBin PosRange setexp0 setexp
  Join setexp0 setexp  -> posSBin PosJoin setexp0 setexp
  ClaferId name  -> posClaferId $ mapName name
  _  -> error "no setExp mapping"

getPosSetExp :: SetExp -> (Integer, Integer)
getPosSetExp x = case x of
  PosUnion n0 n _ _ -> (n0, n)
  PosUnionCom n0 n _ _ -> (n0, n)
  PosDifference n0 n _ _ -> (n0, n)
  PosIntersection n0 n _ _ -> (n0, n)
  PosDomain n0 n _ _ -> (n0, n)
  PosRange n0 n _ _ -> (n0, n)
  PosJoin n0 n _ _ -> (n0, n)
  PosClaferId n0 n _  -> (n0, n)

mapSetExp :: SetExp -> SetExp
posSBin op exp0 exp = posBin' op exp0 exp mapSetExp getPosSetExp

posClaferId :: Name -> SetExp
posClaferId name = uncurry PosClaferId (getPosName name) name

mapDecl :: Decl -> Decl
mapDecl x = case x of
  Decl locids setexp  -> posDecl (map mapLocId locids) (mapSetExp setexp)
  _  -> error "no decl mapping"

getPosDecl :: Decl -> (Integer, Integer)
getPosDecl (PosDecl n0 n _ _) = (n0, n)

posDecl :: [LocId] -> SetExp -> Decl
posDecl locids setexp = uncurry PosDecl (l >- getPosSetExp setexp) locids setexp
  where
  l = case map getPosLocId locids of
        [] -> (0, 0)
        (x:_) -> x

mapQuant :: Quant -> Quant
mapQuant x = case x of
  PosQuantNo n0 n  -> x
  PosQuantLone n0 n  -> x
  PosQuantOne n0 n  ->  x
  PosQuantSome n0 n  -> x
  _  -> error "no quant mapping"

getPosQuant :: Quant -> (Integer, Integer)
getPosQuant x = case x of
  PosQuantNo n0 n  -> (n0, n)
  PosQuantLone n0 n  -> (n0, n)
  PosQuantOne n0 n  ->  (n0, n)
  PosQuantSome n0 n  -> (n0, n)

mapEnumId :: EnumId -> EnumId
mapEnumId x = case x of
  EnumIdIdent posident  -> posEnumIdIdent posident
  _  -> error "no enumId mapping"

posEnumIdIdent :: PosIdent -> EnumId
posEnumIdIdent posident = uncurry PosEnumIdIdent (getPosPosIdent posident) posident

mapModId :: ModId -> ModId
mapModId x = case x of
  ModIdIdent posident  -> posModIdIdent posident
  _  -> error "no modId mapping"

getPosModId :: ModId -> (Integer, Integer)
getPosModId x = case x of
  ModIdIdent posident  -> getPosPosIdent posident

posModIdIdent :: PosIdent -> ModId
posModIdIdent posident = uncurry PosModIdIdent (getPosPosIdent posident) posident

mapLocId :: LocId -> LocId
mapLocId x = case x of
  LocIdIdent posident  -> posLocIdIdent posident
  _  -> error "no locId mapping"

getPosLocId :: LocId -> (Integer, Integer)
getPosLocId (PosLocIdIdent n0 n _) = (n0, n)

posLocIdIdent :: PosIdent -> LocId
posLocIdIdent posident = uncurry PosLocIdIdent (getPosPosIdent posident) posident

getPosPosInteger (PosInteger ((n0, n), _)) = (toInteger n0, toInteger n)
getPosPosDouble  (PosDouble ((n0, n), _)) = (toInteger n0, toInteger n)
getPosPosString  (PosString ((n0, n), _)) = (toInteger n0, toInteger n)
getPosPosIdent   (PosIdent ((n0, n), _)) = (toInteger n0, toInteger n)