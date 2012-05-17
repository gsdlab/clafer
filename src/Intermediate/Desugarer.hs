{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
module Intermediate.Desugarer where

import Front.Absclafer
import Intermediate.Intclafer
import Monad
import Common
import Data.Function

desugarModule :: Module -> IModule
desugarModule x = case x of
  Module declarations  -> desugarModule $ PosModule 0 0 declarations
  PosModule l c declarations  -> IModule "" $
      declarations >>= desugarEnums >>= desugarDeclaration
--      [ImoduleFragment $ declarations >>= desugarEnums >>= desugarDeclaration]


sugarModule :: IModule -> Module
sugarModule x = Module $ map sugarDeclaration $ mDecls x -- (fragments x >>= mDecls)


-- desugars enumeration to abstract and global singleton features
desugarEnums :: Declaration -> [Declaration]
desugarEnums x = case x of
  EnumDecl id enumids  -> desugarEnums $ PosEnumDecl 0 0 id enumids
  PosEnumDecl l c id enumids  -> absEnum : map mkEnum enumids
    where
    absEnum = ElementDecl $ Subclafer $ Clafer
              Abstract GCardEmpty id SuperEmpty CardEmpty InitEmpty (ElementsList [])
    mkEnum (EnumIdIdent eId) = ElementDecl $ Subclafer $ Clafer AbstractEmpty GCardEmpty
                                  eId (SuperSome SuperColon (ClaferId $ Path [ModIdIdent id])) CardEmpty InitEmpty (ElementsList [])
  _ -> [x]


desugarDeclaration :: Declaration -> [IElement]
desugarDeclaration x = case x of
  ElementDecl element  -> desugarDeclaration $ PosElementDecl 0 0 element
  PosElementDecl l c element  -> desugarElement element
  _  -> error "desugared"


sugarDeclaration :: IElement -> Declaration
sugarDeclaration x = case x of
  IEClafer clafer  -> ElementDecl $ Subclafer $ sugarClafer clafer
  IEConstraint True constraint  ->
      ElementDecl $ Subconstraint $ sugarConstraint constraint
  IEConstraint False softconstraint  ->
      ElementDecl $ Subsoftconstraint $ sugarSoftConstraint softconstraint
  IEGoal _ goal -> ElementDecl $ Subgoal $sugarGoal goal


desugarClafer :: Clafer -> IClafer
desugarClafer x = case x of
  Clafer abstract gcard id super card init elements  -> 
      desugarClafer $ PosClafer 0 0 abstract gcard id super card init elements
  PosClafer l c abstract gcard id super card init elements  -> 
    IClafer (desugarAbstract abstract) (desugarGCard gcard) (transIdent id)
            "" (desugarSuper super) (desugarCard card) (0, -1)
            ((desugarInit init) ++ desugarElements elements)


sugarClafer :: IClafer -> Clafer
sugarClafer x = case x of
  IClafer abstract gcard id uid super card _ elements  ->
    Clafer (sugarAbstract abstract) (sugarGCard gcard) (mkIdent uid)
      (sugarSuper super) (sugarCard card) InitEmpty (sugarElements elements)


desugarSuper :: Super -> ISuper
desugarSuper x = case x of
  SuperEmpty  -> desugarSuper $ PosSuperEmpty 0 0
  SuperSome superhow setexp -> desugarSuper $ PosSuperSome 0 0 superhow setexp
  PosSuperEmpty l c ->
      ISuper False [PExp (Just TClafer) "" noPos $ mkLClaferId baseClafer True]
  PosSuperSome l c superhow setexp ->
      ISuper (desugarSuperHow superhow) [desugarSetExp setexp]


desugarSuperHow :: SuperHow -> Bool
desugarSuperHow x = case x of
  SuperColon  -> desugarSuperHow $ PosSuperColon 0 0
  PosSuperColon l c -> False
  _  -> True


desugarInit :: Init -> [IElement]
desugarInit x = case x of
  InitEmpty  -> desugarInit $ PosInitEmpty 0 0
  InitSome inithow exp  -> desugarInit $ PosInitSome 0 0 inithow exp
  PosInitEmpty l c  -> []
  PosInitSome l c inithow exp  ->
      [IEConstraint (desugarInitHow inithow)
      (pExpDefPidPos (IFunExp "=" [mkPLClaferId "this" False, desugarExp exp]))]


desugarInitHow :: InitHow -> Bool
desugarInitHow x = case x of
  InitHow_1  -> desugarInitHow $ PosInitHow_1 0 0
  InitHow_2  -> desugarInitHow $ PosInitHow_2 0 0
  PosInitHow_1 l c -> True
  PosInitHow_2 l c -> False


desugarName x = case x of
  Path path -> desugarName $ PosPath 0 0 path
  PosPath l c path ->
      IClaferId (concatMap ((++ modSep).desugarModId) (init path))
                (desugarModId $ last path) True

desugarModId x = case x of
  ModIdIdent id -> desugarModId $ PosModIdIdent 0 0 id
  PosModIdIdent l c id -> transIdent id

sugarModId modid = ModIdIdent $ mkIdent modid


sugarSuper :: ISuper -> Super
sugarSuper x = case x of
  ISuper _ [] -> SuperEmpty
  ISuper isOverlapping [pexp] -> SuperSome (sugarSuperHow isOverlapping) (sugarSetExp pexp)


sugarSuperHow x = case x of
  False -> SuperColon
  True  -> SuperMArrow


sugarInitHow :: Bool -> InitHow
sugarInitHow x = case x of
  True  -> InitHow_1
  False -> InitHow_2


desugarConstraint :: Constraint -> PExp
desugarConstraint x = case x of
  Constraint exps -> desugarConstraint $ PosConstraint 0 0 exps
  PosConstraint l c exps -> desugarPath $ desugarExp $
    (if length exps > 1 then foldl1 EAnd else head) exps

desugarSoftConstraint :: SoftConstraint -> PExp
desugarSoftConstraint x = case x of
  SoftConstraint exps -> desugarSoftConstraint $ PosSoftConstraint 0 0 exps
  PosSoftConstraint l c exps -> desugarPath $ desugarExp $
    (if length exps > 1 then foldl1 EAnd else head) exps

desugarGoal :: Goal -> PExp
desugarGoal x = case x of
  Goal exps -> desugarGoal $ PosGoal 0 0 exps
  PosGoal l c exps -> desugarPath $ desugarExp $
    (if length exps > 1 then foldl1 EAnd else head) exps

sugarConstraint :: PExp -> Constraint
sugarConstraint pexp = Constraint $ map sugarExp [pexp]

sugarSoftConstraint :: PExp -> SoftConstraint
sugarSoftConstraint pexp = SoftConstraint $ map sugarExp [pexp]

sugarGoal :: PExp -> Goal
sugarGoal pexp = Goal $ map sugarExp [pexp]

desugarAbstract :: Abstract -> Bool
desugarAbstract x = case x of
  AbstractEmpty  -> desugarAbstract $ PosAbstractEmpty 0 0
  Abstract  -> desugarAbstract $ PosAbstract 0 0
  PosAbstractEmpty l c  -> False
  PosAbstract l c -> True


sugarAbstract :: Bool -> Abstract
sugarAbstract x = case x of
  False -> AbstractEmpty
  True -> Abstract


desugarElements :: Elements -> [IElement]
desugarElements x = case x of
  ElementsEmpty -> desugarElements $ PosElementsEmpty 0 0
  ElementsList elements  -> desugarElements $ PosElementsList 0 0 elements
  PosElementsEmpty l c -> []
  PosElementsList l c elements  -> elements >>= desugarElement


sugarElements :: [IElement] -> Elements
sugarElements x = ElementsList $ map sugarElement x


desugarElement :: Element -> [IElement]
desugarElement x = case x of
  Subclafer clafer  -> desugarElement $ PosSubclafer 0 0 clafer
  ClaferUse name card elements  ->
      desugarElement $ PosClaferUse 0 0 name card elements
  Subconstraint constraint  -> desugarElement $ PosSubconstraint 0 0 constraint
  Subsoftconstraint softconstraint ->
      desugarElement $ PosSubsoftconstraint 0 0 softconstraint
  Subgoal goal -> desugarElement $ PosSubgoal 0 0 goal
  PosSubclafer l c clafer  ->
      (IEClafer $ desugarClafer clafer) :
      (mkArrowConstraint clafer >>= desugarElement)
  PosClaferUse l c name card elements  -> [IEClafer $ desugarClafer $ Clafer
      AbstractEmpty GCardEmpty (mkIdent $ sident $ desugarName name)
      (SuperSome SuperColon (ClaferId name)) card InitEmpty elements]
  PosSubconstraint l c constraint  ->
      [IEConstraint True $ desugarConstraint constraint]
  PosSubsoftconstraint l c softconstraint ->
      [IEConstraint False $ desugarSoftConstraint softconstraint]
  PosSubgoal l c goal -> [IEGoal True $ desugarGoal goal]

sugarElement :: IElement -> Element
sugarElement x = case x of
  IEClafer clafer  -> Subclafer $ sugarClafer clafer
  IEConstraint True constraint -> Subconstraint $ sugarConstraint constraint
  IEConstraint False softconstraint -> Subsoftconstraint $ sugarSoftConstraint softconstraint
  IEGoal _ goal -> Subgoal $ sugarGoal goal


mkArrowConstraint (Clafer abstract gcard id super card init elements) =
    mkArrowConstraint $ PosClafer 0 0 abstract gcard id super card init elements
mkArrowConstraint (PosClafer l c _ _ ident super _ _ _) = 
  if isSuperSomeArrow super then  [Subconstraint $
       Constraint [DeclAllDisj
       (Decl [LocIdIdent $ mkIdent "x", LocIdIdent $ mkIdent "y"]
             (ClaferId  $ Path [ModIdIdent ident]))
       (ENeq (ESetExp $ Join (ClaferId $ Path [ModIdIdent $ mkIdent "x"])
                             (ClaferId $ Path [ModIdIdent $ mkIdent "ref"]))
             (ESetExp $ Join (ClaferId $ Path [ModIdIdent $ mkIdent "y"])
                             (ClaferId $ Path [ModIdIdent $ mkIdent "ref"])))]]
  else []


isSuperSomeArrow (SuperSome arrow _) = isSuperArrow arrow
isSuperSomeArrow (PosSuperSome _ _ arrow _) = isSuperArrow arrow
isSuperSomeArrow _ = False

isSuperArrow SuperArrow = True
isSuperArrow (PosSuperArrow _ _) = True
isSuperArrow _ = False

desugarGCard :: GCard -> Maybe IGCard
desugarGCard x = case x of
  GCardEmpty  -> desugarGCard $ PosGCardEmpty 0 0
  GCardXor -> desugarGCard $ PosGCardXor 0 0
  GCardOr  -> desugarGCard $ PosGCardOr 0 0
  GCardMux -> desugarGCard $ PosGCardMux 0 0
  GCardOpt -> desugarGCard $ PosGCardOpt 0 0
  GCardInterval card -> desugarGCard $ PosGCardInterval 0 0 card
  PosGCardEmpty l c  -> Nothing
  PosGCardXor l c -> Just $ IGCard True (1, 1)
  PosGCardOr l c  -> Just $ IGCard True (1, -1)
  PosGCardMux l c -> Just $ IGCard True (0, 1)
  PosGCardOpt l c -> Just $ IGCard True (0, -1)
  PosGCardInterval l c card@(NCard i ex) ->
      Just $ IGCard (isOptionalDef card) (mkInteger i, desugarExInteger ex)

isOptionalDef (PosNCard l c m n) = isOptionalDef $ NCard m n
isOptionalDef (NCard m n) = (0 == mkInteger m) && (not $ isExIntegerAst n)

isExIntegerAst ExIntegerAst = True
isExIntegerAst (PosExIntegerAst _ _) = True
isExIntegerAst _ = False

sugarGCard :: Maybe IGCard -> GCard
sugarGCard x = case x of
  Nothing -> GCardEmpty
  Just (IGCard _ (i, ex)) -> GCardInterval $ NCard (PosInteger ((0, 0), show i)) (sugarExInteger ex)


desugarCard :: Card -> Maybe Interval
desugarCard x = case x of
  CardEmpty  -> desugarCard $ PosCardEmpty 0 0
  CardLone  ->  desugarCard $ PosCardLone 0 0
  CardSome  ->  desugarCard $ PosCardSome 0 0
  CardAny  -> desugarCard $ PosCardAny 0 0
  CardNum n  -> desugarCard $ PosCardNum 0 0 n
  CardInterval card  -> desugarCard $ PosCardInterval 0 0 card
  PosCardEmpty l c  -> Nothing
  PosCardLone l c  ->  Just (0, 1)
  PosCardSome l c  ->  Just (1, -1)
  PosCardAny l c ->  Just (0, -1)
  PosCardNum l c n  -> Just (mkInteger n, mkInteger n)
  PosCardInterval l c (NCard i ex)  -> Just (mkInteger i, desugarExInteger ex)


desugarExInteger ExIntegerAst = -1
desugarExInteger (PosExIntegerAst l c) = -1
desugarExInteger (ExIntegerNum n) = mkInteger n
desugarExInteger (PosExIntegerNum l c n) = mkInteger n

sugarCard :: Maybe Interval -> Card
sugarCard x = case x of
  Nothing -> CardEmpty
  Just (i, ex) ->
      CardInterval $ NCard (PosInteger ((0, 0), show i)) (sugarExInteger ex)


sugarExInteger n = if n == -1 then ExIntegerAst else (ExIntegerNum $ PosInteger ((0, 0), show n))

desugarExp :: Exp -> PExp
desugarExp x = pExpDefPidPos $ desugarExp' x

desugarExp' :: Exp -> IExp
desugarExp' x = case x of
  DeclAllDisj decl exp -> desugarExp' $ PosDeclAllDisj 0 0 decl exp
  DeclAll decl exp -> desugarExp' $ PosDeclAll 0 0 decl exp
  DeclQuantDisj quant decl exp ->
      desugarExp' $ PosDeclQuantDisj 0 0 quant decl exp
  DeclQuant quant decl exp -> desugarExp' $ PosDeclQuant 0 0 quant decl exp
  EIff exp0 exp  -> desugarExp' $ PosEIff 0 0 exp0 exp
  EImplies exp0 exp  -> desugarExp' $ PosEImplies 0 0 exp0 exp
  EImpliesElse exp0 exp1 exp  -> desugarExp' $ PosEImpliesElse 0 0 exp0 exp1 exp
  EOr exp0 exp  -> desugarExp' $ PosEOr 0 0 exp0 exp
  EXor exp0 exp  -> desugarExp' $ PosEXor 0 0 exp0 exp
  EAnd exp0 exp  -> desugarExp' $ PosEAnd 0 0 exp0 exp
  QuantExp quant exp  -> desugarExp' $ PosQuantExp 0 0 quant exp
  ELt  exp0 exp  -> desugarExp' $ PosELt 0 0 exp0 exp
  EGt  exp0 exp  -> desugarExp' $ PosEGt 0 0 exp0 exp
  EEq  exp0 exp  -> desugarExp' $ PosEEq 0 0 exp0 exp
  ELte exp0 exp  -> desugarExp' $ PosELte 0 0 exp0 exp
  EGte exp0 exp  -> desugarExp' $ PosEGte 0 0 exp0 exp
  ENeq exp0 exp  -> desugarExp' $ PosENeq 0 0 exp0 exp
  EIn  exp0 exp  -> desugarExp' $ PosEIn 0 0 exp0 exp
  ENin exp0 exp  -> desugarExp' $ PosENin 0 0 exp0 exp
  EAdd exp0 exp  -> desugarExp' $ PosEAdd 0 0 exp0 exp
  ESub exp0 exp  -> desugarExp' $ PosESub 0 0 exp0 exp
  EMul exp0 exp  -> desugarExp' $ PosEMul 0 0 exp0 exp
  EDiv exp0 exp  -> desugarExp' $ PosEDiv 0 0 exp0 exp
  ECSetExp exp   -> desugarExp' $ PosECSetExp 0 0 exp
  EMinExp exp    -> desugarExp' $ PosEMinExp 0 0 exp
  EGMax exp -> desugarExp' $ PosEGMax 0 0 exp
  EGMin exp -> desugarExp' $ PosEGMin 0 0 exp
  EInt n -> desugarExp' $ PosEInt 0 0 n
  EDouble n -> desugarExp' $ PosEDouble 0 0 n
  EStr str  -> desugarExp' $ PosEStr 0 0 str
  ESetExp sexp -> desugarExp' $ PosESetExp 0 0 sexp
  PosDeclAllDisj l c decl exp ->
      IDeclPExp IAll [desugarDecl True decl] (dpe exp)
  PosDeclAll l c decl exp -> IDeclPExp IAll [desugarDecl False decl] (dpe exp)
  PosDeclQuantDisj l c quant decl exp ->
      IDeclPExp (desugarQuant quant) [desugarDecl True decl] (dpe exp)
  PosDeclQuant l c quant decl exp ->
      IDeclPExp (desugarQuant quant) [desugarDecl False decl] (dpe exp)
  PosEIff l c exp0 exp  -> dop iIff [exp0, exp]
  PosEImplies l c exp0 exp  -> dop iImpl [exp0, exp]
  PosEImpliesElse l c exp0 exp1 exp  -> dop iIfThenElse [exp0, exp1, exp]
  PosEOr l c exp0 exp  -> dop iOr   [exp0, exp]
  PosEXor l c exp0 exp  -> dop iXor [exp0, exp]
  PosEAnd l c exp0 exp  -> dop iAnd [exp0, exp]
  PosENeg l c exp  -> dop iNot [exp]
  PosQuantExp l c quant exp ->
      IDeclPExp (desugarQuant quant) [] (desugarExp exp)
  PosELt  l c exp0 exp  -> dop iLt  [exp0, exp]
  PosEGt  l c exp0 exp  -> dop iGt  [exp0, exp]
  PosEEq  l c exp0 exp  -> dop iEq  [exp0, exp]
  PosELte l c exp0 exp  -> dop iLte [exp0, exp]
  PosEGte l c exp0 exp  -> dop iGte [exp0, exp]
  PosENeq l c exp0 exp  -> dop iNeq [exp0, exp]
  PosEIn  l c exp0 exp  -> dop iIn  [exp0, exp]
  PosENin l c exp0 exp  -> dop iNin [exp0, exp]
  PosEAdd l c exp0 exp  -> dop iPlus [exp0, exp]
  PosESub l c exp0 exp  -> dop iSub [exp0, exp]
  PosEMul l c exp0 exp  -> dop iMul [exp0, exp]
  PosEDiv l c exp0 exp  -> dop iDiv [exp0, exp]
  PosECSetExp l c exp   -> dop iCSet [exp]
  PosEMinExp l c exp    -> dop iMin [exp]  
  PosEGMax l c exp -> dop iGMax [exp]
  PosEGMin l c exp -> dop iGMin [exp]  
  PosEInt l c n  -> IInt $ mkInteger n
  PosEDouble l c (PosDouble n) -> IDouble $ read $ snd n
  PosEStr l c (PosString str)  -> IStr $ snd str
  PosESetExp l c sexp -> desugarSetExp' sexp
  where
  dop = desugarOp desugarExp
  dpe = desugarPath.desugarExp


desugarOp f op exps = IFunExp op $ map (trans.f) exps
  where
  trans = if op `elem` ([iNot, iIfThenElse] ++ logBinOps)
          then desugarPath else id


desugarSetExp :: SetExp -> PExp
desugarSetExp x = pExpDefPidPos $ desugarSetExp' x


desugarSetExp' :: SetExp -> IExp
desugarSetExp' x = case x of
  Union exp0 exp        -> desugarSetExp' $ PosUnion 0 0 exp0 exp
  UnionCom exp0 exp     -> desugarSetExp' $ PosUnionCom 0 0 exp0 exp
  Difference exp0 exp   -> desugarSetExp' $ PosDifference 0 0 exp0 exp
  Intersection exp0 exp -> desugarSetExp' $ PosIntersection 0 0 exp0 exp
  Domain exp0 exp       -> desugarSetExp' $ PosDomain 0 0 exp0 exp
  Range exp0 exp        -> desugarSetExp' $ PosRange 0 0 exp0 exp
  Join exp0 exp         -> desugarSetExp' $ PosJoin 0 0 exp0 exp
  ClaferId name  -> desugarSetExp' $ PosClaferId 0 0 name
  PosUnion l c exp0 exp        -> dop iUnion        [exp0, exp]
  PosUnionCom l c exp0 exp     -> dop iUnion        [exp0, exp]
  PosDifference l c exp0 exp   -> dop iDifference   [exp0, exp]
  PosIntersection l c exp0 exp -> dop iIntersection [exp0, exp]
  PosDomain l c exp0 exp       -> dop iDomain       [exp0, exp]
  PosRange l c exp0 exp        -> dop iRange        [exp0, exp]
  PosJoin l c exp0 exp         -> dop iJoin         [exp0, exp]
  PosClaferId l c name  -> desugarName name

  where
  dop = desugarOp desugarSetExp


sugarExp :: PExp -> Exp
sugarExp x = sugarExp' $ Intermediate.Intclafer.exp x


sugarExp' :: IExp -> Exp
sugarExp' x = case x of
  IDeclPExp quant [] pexp -> QuantExp (sugarQuant quant) (sugarExp pexp)
  IDeclPExp IAll (decl@(IDecl True _ _):[]) pexp ->
    DeclAllDisj   (sugarDecl decl) (sugarExp pexp)
  IDeclPExp IAll  (decl@(IDecl False _ _):[]) pexp ->
    DeclAll       (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant (decl@(IDecl True _ _):[]) pexp ->
    DeclQuantDisj (sugarQuant quant) (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant (decl@(IDecl False _ _):[]) pexp ->
    DeclQuant     (sugarQuant quant) (sugarDecl decl) (sugarExp pexp)
  IFunExp op exps ->
    if op `elem` unOps then (sugarUnOp op) (exps'!!0)
    else if op `elem` setBinOps then (ESetExp $ sugarSetExp' x)
    else if op `elem` binOps then (sugarOp op) (exps'!!0) (exps'!!1)
    else (sugarTerOp op) (exps'!!0) (exps'!!1) (exps'!!2)
    where
    exps' = map sugarExp exps
  IInt n -> EInt $ PosInteger ((0, 0), show n)
  IDouble n -> EDouble $ PosDouble ((0, 0), show n)
  IStr str -> EStr $ PosString ((0, 0), str)
  IClaferId _ _ _ -> ESetExp $ sugarSetExp' x
  where
  sugarUnOp op
    | op == iNot           = ENeg
    | op == iCSet          = ECSetExp
    | op == iMin           = EMinExp
    | op == iGMax          = EGMax
    | op == iGMin          = EGMin    
  sugarOp op
    | op == iIff           = EIff
    | op == iImpl          = EImplies
    | op == iOr            = EOr
    | op == iXor           = EXor
    | op == iAnd           = EAnd 
    | op == iLt            = ELt
    | op == iGt            = EGt
    | op == iEq            = EEq  
    | op == iLte           = ELte
    | op == iGte           = EGte
    | op == iNeq           = ENeq
    | op == iIn            = EIn
    | op == iNin           = ENin
    | op == iPlus          = EAdd
    | op == iSub           = ESub
    | op == iMul           = EMul
    | op == iDiv           = EDiv
  sugarTerOp op
    | op == iIfThenElse    = EImpliesElse


sugarSetExp :: PExp -> SetExp
sugarSetExp x = sugarSetExp' $ Intermediate.Intclafer.exp x


sugarSetExp' :: IExp -> SetExp
sugarSetExp' x = case x of
  IFunExp op exps -> (sugarOp op) (exps'!!0) (exps'!!1)
    where
    exps' = map sugarSetExp exps
    sugarOp op
      | op == iUnion         = Union
      | op == iDifference    = Difference
      | op == iIntersection  = Intersection
      | op == iDomain        = Domain
      | op == iRange         = Range
      | op == iJoin          = Join
  IClaferId "" id _ -> ClaferId $ Path [ModIdIdent $ mkIdent id]
  IClaferId modName id _ -> ClaferId $ Path $ (sugarModId modName) : [sugarModId id]

desugarPath :: PExp -> PExp
desugarPath (PExp iType pid pos x) = reducePExp $ PExp iType pid pos result
  where
  result
    | isSet x     = IDeclPExp ISome [] (pExpDefPidPos x)
    | isNegSome x = IDeclPExp INo   [] $ bpexp $ Intermediate.Intclafer.exp $ head $ exps x
    | otherwise   =  x
  isNegSome (IFunExp op [PExp _ _ _ (IDeclPExp ISome [] _)]) = op == iNot
  isNegSome _ = False


isSet :: IExp -> Bool
isSet (IClaferId _ _ _)  = True
isSet (IFunExp op _) = op `elem` setBinOps
isSet _ = False


-- reduce parent
reducePExp (PExp t pid pos x) = PExp t pid pos $ reduceIExp x

reduceIExp x = case x of
  IDeclPExp quant decls pexp -> IDeclPExp quant decls $ reducePExp pexp
  IFunExp op exps -> redNav $ IFunExp op $ map redExps exps
    where
    (redNav, redExps) = if op == iJoin then (reduceNav, id) else (id, reducePExp) 
  _  -> x

reduceNav x@(IFunExp op exps@((PExp _ _ _ iexp@(IFunExp _ (pexp0:pexp:_))):pPexp:_)) = 
  if op == iJoin && isParent pPexp && isClaferName pexp
  then reduceNav $ Intermediate.Intclafer.exp pexp0
  else x{exps = (head exps){Intermediate.Intclafer.exp = reduceIExp iexp} :
                tail exps}
reduceNav x = x


desugarDecl :: Bool -> Decl -> IDecl
desugarDecl isDisj x = case x of
  Decl locids exp  -> desugarDecl isDisj $ PosDecl 0 0 locids exp
  PosDecl l c locids exp  ->
    IDecl isDisj (map desugarLocId locids) (desugarSetExp exp)


sugarDecl :: IDecl -> Decl
sugarDecl x = case x of
  IDecl disj locids exp  ->
    Decl (map sugarLocId locids) (sugarSetExp exp)


desugarLocId :: LocId -> String
desugarLocId x = case x of
  LocIdIdent id  -> desugarLocId $ PosLocIdIdent 0 0 id
  PosLocIdIdent l c id  -> transIdent id


sugarLocId :: String -> LocId
sugarLocId x = LocIdIdent $ mkIdent x


desugarQuant x = case x of
  QuantNo -> desugarQuant $ PosQuantNo 0 0
  QuantLone -> desugarQuant $ PosQuantLone 0 0
  QuantOne -> desugarQuant $ PosQuantOne 0 0
  QuantSome -> desugarQuant $ PosQuantSome 0 0
  PosQuantNo l c -> INo
  PosQuantLone l c -> ILone
  PosQuantOne l c -> IOne
  PosQuantSome l c -> ISome


sugarQuant x = case x of
  INo -> QuantNo
  ILone -> QuantLone
  IOne -> QuantOne
  ISome -> QuantSome