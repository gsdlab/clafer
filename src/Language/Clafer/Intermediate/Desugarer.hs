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
module Language.Clafer.Intermediate.Desugarer where

import Control.Monad
import Data.Function

import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Front.Mapper
import Language.Clafer.Intermediate.Intclafer


desugarModule :: Module -> IModule
desugarModule x = case x of
  Module declarations  -> desugarModule $ PosModule noSpan declarations
  PosModule s declarations  -> IModule "" $
      declarations >>= desugarEnums >>= desugarDeclaration
--      [ImoduleFragment $ declarations >>= desugarEnums >>= desugarDeclaration]


sugarModule :: IModule -> Module
sugarModule x = Module $ map sugarDeclaration $ mDecls x -- (fragments x >>= mDecls)


-- desugars enumeration to abstract and global singleton features
desugarEnums :: Declaration -> [Declaration]
desugarEnums x = case x of
  EnumDecl id enumids  -> desugarEnums $ PosEnumDecl noSpan id enumids
  PosEnumDecl s id enumids  -> absEnum : map mkEnum enumids
    where
    absEnum = ElementDecl $ Subclafer $ Clafer
              Abstract GCardEmpty id SuperEmpty CardEmpty InitEmpty (ElementsList [])
    mkEnum (PosEnumIdIdent s eId) = ElementDecl $ Subclafer $ Clafer AbstractEmpty GCardEmpty
                                  eId (SuperSome SuperColon (PosClaferId noSpan $ Path [ModIdIdent id])) CardEmpty InitEmpty (ElementsList [])
    mkEnum (EnumIdIdent eId) = ElementDecl $ Subclafer $ Clafer AbstractEmpty GCardEmpty
                                  eId (SuperSome SuperColon (PosClaferId noSpan $ Path [ModIdIdent id])) CardEmpty InitEmpty (ElementsList [])
  _ -> [x]


desugarDeclaration :: Declaration -> [IElement]
desugarDeclaration x = case x of
  ElementDecl element  -> desugarDeclaration $ PosElementDecl noSpan element
  PosElementDecl s element  -> desugarElement element
  _  -> error "desugared"


sugarDeclaration :: IElement -> Declaration
sugarDeclaration x = case x of
  IEClafer clafer  -> ElementDecl $ Subclafer $ sugarClafer clafer
  IEConstraint True constraint  ->
      ElementDecl $ Subconstraint $ sugarConstraint constraint
  IEConstraint False softconstraint  ->
      ElementDecl $ Subsoftconstraint $ sugarSoftConstraint softconstraint
  IEGoal _ goal -> ElementDecl $ Subgoal $sugarGoal goal


desugarClafer :: Clafer -> [IElement]
desugarClafer (Clafer abstract gcard id super card init elements)  = 
    desugarClafer $ PosClafer noSpan abstract gcard id super card init elements
desugarClafer (PosClafer s abstract gcard id super card init elements)  = 
    (IEClafer $ IClafer s (desugarAbstract abstract) (desugarGCard gcard) (transIdent id)
            "" (desugarSuper super) (desugarCard card) (0, -1)
            (desugarElements elements)) : (desugarInit id init)


sugarClafer :: IClafer -> Clafer
sugarClafer x = case x of
  IClafer _ abstract gcard id uid super card _ elements  ->
    Clafer (sugarAbstract abstract) (sugarGCard gcard) (mkIdent uid)
      (sugarSuper super) (sugarCard card) InitEmpty (sugarElements elements)


desugarSuper :: Super -> ISuper
desugarSuper x = case x of
  SuperEmpty  -> desugarSuper $ PosSuperEmpty noSpan
  SuperSome superhow setexp -> desugarSuper $ PosSuperSome noSpan superhow setexp
  PosSuperEmpty s ->
      ISuper False [PExp (Just $ TClafer []) (genPExpName s (mkLClaferId baseClafer True)) s $ mkLClaferId baseClafer True]
  PosSuperSome s superhow setexp ->
      ISuper (desugarSuperHow superhow) [desugarSetExp setexp]


desugarSuperHow :: SuperHow -> Bool
desugarSuperHow x = case x of
  SuperColon  -> desugarSuperHow $ PosSuperColon noSpan
  PosSuperColon s -> False
  _  -> True


desugarInit :: PosIdent -> Init -> [IElement]
desugarInit id InitEmpty = desugarInit id $ PosInitEmpty noSpan
desugarInit id (InitSome inithow exp) = desugarInit id $ PosInitSome noSpan inithow exp
desugarInit id (PosInitEmpty _) = []
desugarInit id (PosInitSome s inithow exp) = [IEConstraint (desugarInitHow inithow) 
  (pExpDefPid s (IFunExp "=" [mkPLClaferId (snd $ getIdent id) False, desugarExp exp]))]
  where getIdent (PosIdent y) = y

desugarInitHow :: InitHow -> Bool
desugarInitHow x = case x of
  InitHow_1  -> desugarInitHow $ PosInitHow_1 noSpan
  InitHow_2  -> desugarInitHow $ PosInitHow_2 noSpan
  PosInitHow_1 s -> True
  PosInitHow_2 s -> False


desugarName x = case x of
  Path path -> desugarName $ PosPath noSpan path
  PosPath s path ->
      IClaferId (concatMap ((++ modSep).desugarModId) (init path))
                (desugarModId $ last path) True

desugarModId x = case x of
  ModIdIdent id -> desugarModId $ PosModIdIdent noSpan id
  PosModIdIdent s id -> transIdent id

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
  Constraint exps -> desugarConstraint $ PosConstraint noSpan exps
  PosConstraint s exps -> desugarPath $ desugarExp $
    (if length exps > 1 then foldl1 (PosEAnd noSpan) else head) exps

desugarSoftConstraint :: SoftConstraint -> PExp
desugarSoftConstraint x = case x of
  SoftConstraint exps -> desugarSoftConstraint $ PosSoftConstraint noSpan exps
  PosSoftConstraint s exps -> desugarPath $ desugarExp $
    (if length exps > 1 then foldl1 (PosEAnd noSpan) else head) exps

desugarGoal :: Goal -> PExp
desugarGoal x = case x of
  Goal exps -> desugarGoal $ PosGoal noSpan exps
  PosGoal s exps -> desugarPath $ desugarExp $
    (if length exps > 1 then foldl1 (PosEAnd noSpan) else head) exps

sugarConstraint :: PExp -> Constraint
sugarConstraint pexp = Constraint $ map sugarExp [pexp]

sugarSoftConstraint :: PExp -> SoftConstraint
sugarSoftConstraint pexp = SoftConstraint $ map sugarExp [pexp]

sugarGoal :: PExp -> Goal
sugarGoal pexp = Goal $ map sugarExp [pexp]

desugarAbstract :: Abstract -> Bool
desugarAbstract x = case x of
  AbstractEmpty  -> desugarAbstract $ PosAbstractEmpty noSpan
  Abstract  -> desugarAbstract $ PosAbstract noSpan
  PosAbstractEmpty s  -> False
  PosAbstract s -> True


sugarAbstract :: Bool -> Abstract
sugarAbstract x = case x of
  False -> AbstractEmpty
  True -> Abstract


desugarElements :: Elements -> [IElement]
desugarElements x = case x of
  ElementsEmpty -> desugarElements $ PosElementsEmpty noSpan
  ElementsList elements  -> desugarElements $ PosElementsList noSpan elements
  PosElementsEmpty s -> []
  PosElementsList s elements  -> elements >>= desugarElement


sugarElements :: [IElement] -> Elements
sugarElements x = ElementsList $ map sugarElement x


desugarElement :: Element -> [IElement]
desugarElement x = case x of
  Subclafer clafer  -> desugarElement $ PosSubclafer noSpan clafer
  ClaferUse name card elements  ->
      desugarElement $ PosClaferUse noSpan name card elements
  Subconstraint constraint  -> desugarElement $ PosSubconstraint noSpan constraint
  Subsoftconstraint softconstraint ->
      desugarElement $ PosSubsoftconstraint noSpan softconstraint
  Subgoal goal -> desugarElement $ PosSubgoal noSpan goal
  PosSubclafer s clafer  ->
      (desugarClafer clafer) ++
      (mkArrowConstraint clafer >>= desugarElement)
  PosClaferUse s name card elements  -> desugarClafer $ PosClafer s
      AbstractEmpty GCardEmpty (mkIdent $ sident $ desugarName name)
      (SuperSome SuperColon (PosClaferId noSpan name)) card InitEmpty elements
  PosSubconstraint s constraint  ->
      [IEConstraint True $ desugarConstraint constraint]
  PosSubsoftconstraint s softconstraint ->
      [IEConstraint False $ desugarSoftConstraint softconstraint]
  PosSubgoal s goal -> [IEGoal True $ desugarGoal goal]

sugarElement :: IElement -> Element
sugarElement x = case x of
  IEClafer clafer  -> Subclafer $ sugarClafer clafer
  IEConstraint True constraint -> Subconstraint $ sugarConstraint constraint
  IEConstraint False softconstraint -> Subsoftconstraint $ sugarSoftConstraint softconstraint
  IEGoal _ goal -> Subgoal $ sugarGoal goal


mkArrowConstraint (Clafer abstract gcard id super card init elements) =
    mkArrowConstraint $ PosClafer noSpan abstract gcard id super card init elements
mkArrowConstraint (PosClafer s _ _ ident super _ _ _) = 
  if isSuperSomeArrow super then  [Subconstraint $
       Constraint [PosDeclAllDisj noSpan
       (Decl [LocIdIdent $ mkIdent "x", LocIdIdent $ mkIdent "y"]
             (PosClaferId noSpan  $ Path [ModIdIdent ident]))
       (PosENeq noSpan (PosESetExp noSpan $ Join (PosClaferId noSpan $ Path [ModIdIdent $ mkIdent "x"])
                             (PosClaferId noSpan $ Path [ModIdIdent $ mkIdent "ref"]))
             (PosESetExp noSpan $ Join (PosClaferId noSpan $ Path [ModIdIdent $ mkIdent "y"])
                             (PosClaferId noSpan $ Path [ModIdIdent $ mkIdent "ref"])))]]
  else []


isSuperSomeArrow (SuperSome arrow _) = isSuperArrow arrow
isSuperSomeArrow (PosSuperSome _ arrow _) = isSuperArrow arrow
isSuperSomeArrow _ = False

isSuperArrow SuperArrow = True
isSuperArrow (PosSuperArrow _) = True
isSuperArrow _ = False

desugarGCard :: GCard -> Maybe IGCard
desugarGCard x = case x of
  GCardEmpty  -> desugarGCard $ PosGCardEmpty noSpan
  GCardXor -> desugarGCard $ PosGCardXor noSpan
  GCardOr  -> desugarGCard $ PosGCardOr noSpan
  GCardMux -> desugarGCard $ PosGCardMux noSpan
  GCardOpt -> desugarGCard $ PosGCardOpt noSpan
  GCardInterval card -> desugarGCard $ PosGCardInterval noSpan card
  PosGCardEmpty s  -> Nothing
  PosGCardXor s -> Just $ IGCard True (1, 1)
  PosGCardOr s  -> Just $ IGCard True (1, -1)
  PosGCardMux s -> Just $ IGCard True (0, 1)
  PosGCardOpt s -> Just $ IGCard True (0, -1)
  PosGCardInterval s ncard ->
      Just $ IGCard (isOptionalDef ncard) $ desugarNCard ncard

isOptionalDef (PosNCard s m n) = isOptionalDef $ NCard m n
isOptionalDef (NCard m n) = (0 == mkInteger m) && (not $ isExIntegerAst n)

isExIntegerAst ExIntegerAst = True
isExIntegerAst (PosExIntegerAst _) = True
isExIntegerAst _ = False

sugarGCard :: Maybe IGCard -> GCard
sugarGCard x = case x of
  Nothing -> GCardEmpty
  Just (IGCard _ (i, ex)) -> GCardInterval $ NCard (PosInteger ((0, 0), show i)) (sugarExInteger ex)


desugarCard :: Card -> Maybe Interval
desugarCard x = case x of
  CardEmpty  -> desugarCard $ PosCardEmpty noSpan
  CardLone  ->  desugarCard $ PosCardLone noSpan
  CardSome  ->  desugarCard $ PosCardSome noSpan
  CardAny  -> desugarCard $ PosCardAny noSpan
  CardNum n  -> desugarCard $ PosCardNum noSpan n
  CardInterval card  -> desugarCard $ PosCardInterval noSpan card
  PosCardEmpty s  -> Nothing
  PosCardLone s  ->  Just (0, 1)
  PosCardSome s  ->  Just (1, -1)
  PosCardAny s ->  Just (0, -1)
  PosCardNum s n  -> Just (mkInteger n, mkInteger n)
  PosCardInterval s ncard  -> Just $ desugarNCard ncard


desugarNCard (NCard i ex) = desugarNCard $ PosNCard noSpan i ex
desugarNCard (PosNCard s i ex) = (mkInteger i, desugarExInteger ex)

desugarExInteger ExIntegerAst = -1
desugarExInteger (PosExIntegerAst s) = -1
desugarExInteger (ExIntegerNum n) = mkInteger n
desugarExInteger (PosExIntegerNum s n) = mkInteger n

sugarCard :: Maybe Interval -> Card
sugarCard x = case x of
  Nothing -> CardEmpty
  Just (i, ex) ->
      CardInterval $ NCard (PosInteger ((0, 0), show i)) (sugarExInteger ex)


sugarExInteger n = if n == -1 then ExIntegerAst else (ExIntegerNum $ PosInteger ((0, 0), show n))

desugarExp :: Exp -> PExp
desugarExp x = pExpDefPid (range x) $ desugarExp' x

desugarExp' :: Exp -> IExp
desugarExp' x = case x of
  DeclAllDisj decl exp -> desugarExp' $ PosDeclAllDisj noSpan decl exp
  DeclAll decl exp -> desugarExp' $ PosDeclAll noSpan decl exp
  DeclQuantDisj quant decl exp ->
      desugarExp' $ PosDeclQuantDisj noSpan quant decl exp
  DeclQuant quant decl exp -> desugarExp' $ PosDeclQuant noSpan quant decl exp
  EIff exp0 exp  -> desugarExp' $ PosEIff noSpan exp0 exp
  EImplies exp0 exp  -> desugarExp' $ PosEImplies noSpan exp0 exp
  EImpliesElse exp0 exp1 exp  -> desugarExp' $ PosEImpliesElse noSpan exp0 exp1 exp
  EOr exp0 exp  -> desugarExp' $ PosEOr noSpan exp0 exp
  EXor exp0 exp  -> desugarExp' $ PosEXor noSpan exp0 exp
  EAnd exp0 exp  -> desugarExp' $ PosEAnd noSpan exp0 exp
  ENeg exp -> desugarExp' $ PosENeg noSpan exp
  QuantExp quant exp  -> desugarExp' $ PosQuantExp noSpan quant exp
  ELt  exp0 exp  -> desugarExp' $ PosELt noSpan exp0 exp
  EGt  exp0 exp  -> desugarExp' $ PosEGt noSpan exp0 exp
  EEq  exp0 exp  -> desugarExp' $ PosEEq noSpan exp0 exp
  ELte exp0 exp  -> desugarExp' $ PosELte noSpan exp0 exp
  EGte exp0 exp  -> desugarExp' $ PosEGte noSpan exp0 exp
  ENeq exp0 exp  -> desugarExp' $ PosENeq noSpan exp0 exp
  EIn  exp0 exp  -> desugarExp' $ PosEIn noSpan exp0 exp
  ENin exp0 exp  -> desugarExp' $ PosENin noSpan exp0 exp
  EAdd exp0 exp  -> desugarExp' $ PosEAdd noSpan exp0 exp
  ESub exp0 exp  -> desugarExp' $ PosESub noSpan exp0 exp
  EMul exp0 exp  -> desugarExp' $ PosEMul noSpan exp0 exp
  EDiv exp0 exp  -> desugarExp' $ PosEDiv noSpan exp0 exp
  ECSetExp exp   -> desugarExp' $ PosECSetExp noSpan exp
  ESumSetExp sexp -> desugarExp' $ PosESumSetExp noSpan sexp  
  EMinExp exp    -> desugarExp' $ PosEMinExp noSpan exp
  EGMax exp -> desugarExp' $ PosEGMax noSpan exp
  EGMin exp -> desugarExp' $ PosEGMin noSpan exp
  EInt n -> desugarExp' $ PosEInt noSpan n
  EDouble n -> desugarExp' $ PosEDouble noSpan n
  EStr str  -> desugarExp' $ PosEStr noSpan str
  ESetExp sexp -> desugarExp' $ PosESetExp noSpan sexp    
  PosDeclAllDisj s decl exp ->
      IDeclPExp IAll [desugarDecl True decl] (dpe exp)
  PosDeclAll s decl exp -> IDeclPExp IAll [desugarDecl False decl] (dpe exp)
  PosDeclQuantDisj s quant decl exp ->
      IDeclPExp (desugarQuant quant) [desugarDecl True decl] (dpe exp)
  PosDeclQuant s quant decl exp ->
      IDeclPExp (desugarQuant quant) [desugarDecl False decl] (dpe exp)
  PosEIff s exp0 exp  -> dop iIff [exp0, exp]
  PosEImplies s exp0 exp  -> dop iImpl [exp0, exp]
  PosEImpliesElse s exp0 exp1 exp  -> dop iIfThenElse [exp0, exp1, exp]
  PosEOr s exp0 exp  -> dop iOr   [exp0, exp]
  PosEXor s exp0 exp  -> dop iXor [exp0, exp]
  PosEAnd s exp0 exp  -> dop iAnd [exp0, exp]
  PosENeg s exp  -> dop iNot [exp]
  PosQuantExp s quant exp ->
      IDeclPExp (desugarQuant quant) [] (desugarExp exp)
  PosELt  s exp0 exp  -> dop iLt  [exp0, exp]
  PosEGt  s exp0 exp  -> dop iGt  [exp0, exp]
  PosEEq  s exp0 exp  -> dop iEq  [exp0, exp]
  PosELte s exp0 exp  -> dop iLte [exp0, exp]
  PosEGte s exp0 exp  -> dop iGte [exp0, exp]
  PosENeq s exp0 exp  -> dop iNeq [exp0, exp]
  PosEIn  s exp0 exp  -> dop iIn  [exp0, exp]
  PosENin s exp0 exp  -> dop iNin [exp0, exp]
  PosEAdd s exp0 exp  -> dop iPlus [exp0, exp]
  PosESub s exp0 exp  -> dop iSub [exp0, exp]
  PosEMul s exp0 exp  -> dop iMul [exp0, exp]
  PosEDiv s exp0 exp  -> dop iDiv [exp0, exp]
  PosECSetExp s exp   -> dop iCSet [exp]
  PosESumSetExp s exp -> dop iSumSet [exp]
  PosEMinExp s exp    -> dop iMin [exp]  
  PosEGMax s exp -> dop iGMax [exp]
  PosEGMin s exp -> dop iGMin [exp]  
  PosEInt s n  -> IInt $ mkInteger n
  PosEDouble s (PosDouble n) -> IDouble $ read $ snd n
  PosEStr s (PosString str)  -> IStr $ snd str
  PosESetExp s sexp -> desugarSetExp' sexp
  where
  dop = desugarOp desugarExp
  dpe = desugarPath.desugarExp


desugarOp f op exps = 
    if (op == iIfThenElse)
      then IFunExp op $ (desugarPath $ head mappedList) : (map reducePExp $ tail mappedList)
      else IFunExp op $ map (trans.f) exps
    where
      mappedList = map f exps
      trans = if op `elem` ([iNot, iIfThenElse] ++ logBinOps)
          then desugarPath else id


desugarSetExp :: SetExp -> PExp
desugarSetExp x = pExpDefPid (range x) $ desugarSetExp' x


desugarSetExp' :: SetExp -> IExp
desugarSetExp' x = case x of
  Union exp0 exp        -> desugarSetExp' $ PosUnion noSpan exp0 exp
  UnionCom exp0 exp     -> desugarSetExp' $ PosUnionCom noSpan exp0 exp
  Difference exp0 exp   -> desugarSetExp' $ PosDifference noSpan exp0 exp
  Intersection exp0 exp -> desugarSetExp' $ PosIntersection noSpan exp0 exp
  Domain exp0 exp       -> desugarSetExp' $ PosDomain noSpan exp0 exp
  Range exp0 exp        -> desugarSetExp' $ PosRange noSpan exp0 exp
  Join exp0 exp         -> desugarSetExp' $ PosJoin noSpan exp0 exp
  ClaferId name  -> desugarSetExp' $ PosClaferId noSpan name
  PosUnion s exp0 exp        -> dop iUnion        [exp0, exp]
  PosUnionCom s exp0 exp     -> dop iUnion        [exp0, exp]
  PosDifference s exp0 exp   -> dop iDifference   [exp0, exp]
  PosIntersection s exp0 exp -> dop iIntersection [exp0, exp]
  PosDomain s exp0 exp       -> dop iDomain       [exp0, exp]
  PosRange s exp0 exp        -> dop iRange        [exp0, exp]
  PosJoin s exp0 exp         -> dop iJoin         [exp0, exp]
  PosClaferId s name  -> desugarName name

  where
  dop = desugarOp desugarSetExp


sugarExp :: PExp -> Exp
sugarExp x = sugarExp' $ Language.Clafer.Intermediate.Intclafer.exp x


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
    | op == iSumSet        = ESumSetExp
    | otherwise            = error $ show op ++ "is not an op"
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
    | otherwise            = error $ show op ++ "is not an op"
  sugarTerOp op
    | op == iIfThenElse    = EImpliesElse
    | otherwise            = error $ show op ++ "is not an op"


sugarSetExp :: PExp -> SetExp
sugarSetExp x = sugarSetExp' $ Language.Clafer.Intermediate.Intclafer.exp x


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
    | isSet x     = IDeclPExp ISome [] (pExpDefPid pos x)
    | isNegSome x = IDeclPExp INo   [] $ bpexp $ Language.Clafer.Intermediate.Intclafer.exp $ head $ exps x
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
  then reduceNav $ Language.Clafer.Intermediate.Intclafer.exp pexp0
  else x{exps = (head exps){Language.Clafer.Intermediate.Intclafer.exp = reduceIExp iexp} :
                tail exps}
reduceNav x = x


desugarDecl :: Bool -> Decl -> IDecl
desugarDecl isDisj x = case x of
  Decl locids exp  -> desugarDecl isDisj $ PosDecl noSpan locids exp
  PosDecl s locids exp  ->
    IDecl isDisj (map desugarLocId locids) (desugarSetExp exp)


sugarDecl :: IDecl -> Decl
sugarDecl x = case x of
  IDecl disj locids exp  ->
    Decl (map sugarLocId locids) (sugarSetExp exp)


desugarLocId :: LocId -> String
desugarLocId x = case x of
  LocIdIdent id  -> desugarLocId $ PosLocIdIdent noSpan id
  PosLocIdIdent s id  -> transIdent id


sugarLocId :: String -> LocId
sugarLocId x = LocIdIdent $ mkIdent x


desugarQuant x = case x of
  QuantNo -> desugarQuant $ PosQuantNo noSpan
  QuantLone -> desugarQuant $ PosQuantLone noSpan
  QuantOne -> desugarQuant $ PosQuantOne noSpan
  QuantSome -> desugarQuant $ PosQuantSome noSpan
  PosQuantNo s -> INo
  PosQuantLone s -> ILone
  PosQuantOne s -> IOne
  PosQuantSome s -> ISome


sugarQuant x = case x of
  INo -> QuantNo
  ILone -> QuantLone
  IOne -> QuantOne
  ISome -> QuantSome
