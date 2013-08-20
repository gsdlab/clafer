{-# LANGUAGE RankNTypes #-}
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

import Data.List
import Data.Maybe
import Prelude hiding (exp)
import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Front.Mapper
import Language.Clafer.Intermediate.Intclafer


desugarModule :: Module -> IModule
desugarModule (Module declarations) = desugarModule $ PosModule noSpan declarations
desugarModule (PosModule _ declarations) = IModule "" $
      declarations >>= desugarEnums >>= desugarDeclaration
--      [ImoduleFragment $ declarations >>= desugarEnums >>= desugarDeclaration]

sugarModule :: IModule -> Module
sugarModule x = Module $ map sugarDeclaration $ mDecls x -- (fragments x >>= mDecls)

-- desugars enumeration to abstract and global singleton features
desugarEnums :: Declaration -> [Declaration]
desugarEnums (EnumDecl id' enumids) = desugarEnums $ PosEnumDecl noSpan id' enumids
desugarEnums (PosEnumDecl _ id' enumids) = absEnum : map mkEnum enumids
    where
    oneToOne = (CardInterval $ NCard (PosInteger ((0,0), "1")) (ExIntegerNum $ PosInteger ((0,0), "1")))
    absEnum = ElementDecl $ Subclafer $ Clafer
              Abstract GCardEmpty id' SuperEmpty CardEmpty InitEmpty (ElementsList [])
    mkEnum (PosEnumIdIdent _ eId) = ElementDecl $ Subclafer $ Clafer AbstractEmpty GCardEmpty
                                  eId (SuperSome SuperColon (PosClaferId noSpan $ Path [ModIdIdent id'])) oneToOne InitEmpty (ElementsList [])
    mkEnum (EnumIdIdent eId) = ElementDecl $ Subclafer $ Clafer AbstractEmpty GCardEmpty
                                  eId (SuperSome SuperColon (PosClaferId noSpan $ Path [ModIdIdent id'])) oneToOne InitEmpty (ElementsList [])
desugarEnums x = [x]


desugarDeclaration :: Declaration -> [IElement]
desugarDeclaration (ElementDecl element) = desugarDeclaration $ PosElementDecl noSpan element
desugarDeclaration (PosElementDecl _ element) = desugarElement Nothing element
desugarDeclaration _ = error "desugared"


sugarDeclaration :: IElement -> Declaration
sugarDeclaration (IEClafer clafer) = ElementDecl $ Subclafer $ sugarClafer clafer
sugarDeclaration (IEConstraint _ True constraint) =
      ElementDecl $ Subconstraint $ sugarConstraint constraint
sugarDeclaration  (IEConstraint _ False softconstraint) =
      ElementDecl $ Subsoftconstraint $ sugarSoftConstraint softconstraint
sugarDeclaration  (IEGoal _ _ goal) = ElementDecl $ Subgoal $ sugarGoal goal


desugarClafer :: Maybe IClafer -> Clafer -> [IElement]
desugarClafer par (Clafer abstract gcrd id' super' crd init' es)  = 
    desugarClafer par $ PosClafer noSpan abstract gcrd id' super' crd init' es
desugarClafer par (PosClafer s abstract gcrd id' super' crd init' es)  = 
  (IEClafer ic) : (desugarInit id' init')
  where
    ic = IClafer par s (desugarAbstract abstract) (desugarGCard gcrd) 
      (transIdent id') "" is (desugarCard crd) (0, -1) ies
    is = desugarSuper ic super'
    ies = flip desugarElements es $ Just ic


sugarClafer :: IClafer -> Clafer
sugarClafer (IClafer _ _ abstract gcard' _ uid' super' crd _ es) = 
    Clafer (sugarAbstract abstract) (sugarGCard gcard') (mkIdent uid')
      (sugarSuper super') (sugarCard crd) InitEmpty (sugarElements es)


desugarSuper :: IClafer -> Super -> ISuper
desugarSuper ic' SuperEmpty = desugarSuper ic' $ PosSuperEmpty noSpan
desugarSuper ic' (SuperSome superhow setexp) = desugarSuper ic' $ PosSuperSome noSpan superhow setexp
desugarSuper ic' (PosSuperEmpty s) =
      ISuper ic' False TopLevel [PExp Nothing (Just $ TClafer []) "" s $ mkLClaferId baseClafer True]
desugarSuper ic' (PosSuperSome _ superhow setexp) =
      ISuper ic' (desugarSuperHow superhow) TopLevel [desugarSetExp setexp]


desugarSuperHow :: SuperHow -> Bool
desugarSuperHow SuperColon = desugarSuperHow $ PosSuperColon noSpan
desugarSuperHow (PosSuperColon _) = False
desugarSuperHow _  = True


desugarInit :: PosIdent -> Init -> [IElement]
desugarInit id' InitEmpty = desugarInit id' $ PosInitEmpty noSpan
desugarInit id' (InitSome inithow exp') = desugarInit id' $ PosInitSome noSpan inithow exp'
desugarInit _ (PosInitEmpty _) = []
desugarInit id' (PosInitSome s inithow exp') = [IEConstraint Nothing (desugarInitHow inithow) 
  (pExpDefPid s (IFunExp "=" [mkPLClaferId (snd $ getIdent id') False, desugarExp Nothing exp']))]
  where getIdent (PosIdent y) = y

desugarInitHow :: InitHow -> Bool
desugarInitHow InitHow_1  = desugarInitHow $ PosInitHow_1 noSpan
desugarInitHow InitHow_2  = desugarInitHow $ PosInitHow_2 noSpan
desugarInitHow (PosInitHow_1 _) = True
desugarInitHow (PosInitHow_2 _ )= False


desugarName :: Name -> IExp
desugarName (Path path) = desugarName $ PosPath noSpan path
desugarName (PosPath _ path) =
      IClaferId (concatMap ((++ modSep).desugarModId) (init path))
                (desugarModId $ last path) True

desugarModId :: ModId -> Result
desugarModId (ModIdIdent id') = desugarModId $ PosModIdIdent noSpan id'
desugarModId (PosModIdIdent _ id') = transIdent id'

sugarModId :: String -> ModId
sugarModId modid = ModIdIdent $ mkIdent modid

sugarSuper :: ISuper -> Super
sugarSuper (ISuper _ _ _ []) = SuperEmpty
sugarSuper (ISuper _ isOverlapping' _ [pexp]) = SuperSome (sugarSuperHow isOverlapping') (sugarSetExp pexp)
sugarSuper _ = error "Function sugarSuper from Desugarer expects an ISuper with a list of length one, but it was given one with a list larger than one" -- Should never happen

sugarSuperHow :: Bool -> SuperHow
sugarSuperHow False = SuperColon
sugarSuperHow True  = SuperMArrow


sugarInitHow :: Bool -> InitHow
sugarInitHow True  = InitHow_1
sugarInitHow False = InitHow_2


desugarConstraint :: Constraint -> PExp
desugarConstraint (Constraint exps') = desugarConstraint $ PosConstraint noSpan exps'
desugarConstraint (PosConstraint _ exps') = desugarPath $ desugarExp Nothing $
    (if length exps' > 1 then foldl1 (PosEAnd noSpan) else head) exps'

desugarSoftConstraint :: SoftConstraint -> PExp
desugarSoftConstraint (SoftConstraint exps') = desugarSoftConstraint $ PosSoftConstraint noSpan exps'
desugarSoftConstraint (PosSoftConstraint _ exps') = desugarPath $ desugarExp Nothing $
    (if length exps' > 1 then foldl1 (PosEAnd noSpan) else head) exps'

desugarGoal :: Goal -> PExp
desugarGoal (Goal exps') = desugarGoal $ PosGoal noSpan exps'
desugarGoal (PosGoal _ exps') = desugarPath $ desugarExp Nothing $
    (if length exps' > 1 then foldl1 (PosEAnd noSpan) else head) exps'

sugarConstraint :: PExp -> Constraint
sugarConstraint pexp = Constraint $ map sugarExp [pexp]

sugarSoftConstraint :: PExp -> SoftConstraint
sugarSoftConstraint pexp = SoftConstraint $ map sugarExp [pexp]

sugarGoal :: PExp -> Goal
sugarGoal pexp = Goal $ map sugarExp [pexp]

desugarAbstract :: Abstract -> Bool
desugarAbstract AbstractEmpty = desugarAbstract $ PosAbstractEmpty noSpan
desugarAbstract Abstract = desugarAbstract $ PosAbstract noSpan
desugarAbstract (PosAbstractEmpty _) = False
desugarAbstract (PosAbstract _) = True


sugarAbstract :: Bool -> Abstract
sugarAbstract False = AbstractEmpty
sugarAbstract True = Abstract


desugarElements :: Maybe IClafer -> Elements -> [IElement]
desugarElements ic' (ElementsEmpty) = desugarElements ic' $ PosElementsEmpty noSpan
desugarElements ic' (ElementsList es)  = desugarElements ic' $ PosElementsList noSpan es
desugarElements _ (PosElementsEmpty _) = []
desugarElements ic' (PosElementsList _ es)  = es >>= (desugarElement ic')


sugarElements :: [IElement] -> Elements
sugarElements x = ElementsList $ map sugarElement x


desugarElement :: Maybe IClafer -> Element -> [IElement]
desugarElement ic' x = case x of
  Subclafer claf  -> desugarElement ic' $ PosSubclafer noSpan claf
  ClaferUse name crd es  ->
      desugarElement ic' $ PosClaferUse noSpan name crd es
  Subconstraint constraint  -> desugarElement ic' $ PosSubconstraint noSpan constraint
  Subsoftconstraint softconstraint ->
      desugarElement ic' $ PosSubsoftconstraint noSpan softconstraint
  Subgoal goal -> desugarElement ic' $ PosSubgoal noSpan goal
  PosSubclafer _ claf  ->
      (desugarClafer ic' claf) ++
      (mkArrowConstraint claf >>= desugarElement ic')
  PosClaferUse s name crd es  -> desugarClafer ic' $ PosClafer s
      AbstractEmpty GCardEmpty (mkIdent $ sident $ desugarName name)
      (SuperSome SuperColon (PosClaferId noSpan name)) crd InitEmpty es
  PosSubconstraint _ constraint  ->
      [IEConstraint ic' True $ desugarConstraint constraint]
  PosSubsoftconstraint _ softconstraint ->
      [IEConstraint ic' False $ desugarSoftConstraint softconstraint]
  PosSubgoal _ goal -> [IEGoal ic' True $ desugarGoal goal]

sugarElement :: IElement -> Element
sugarElement x = case x of
  IEClafer claf  -> Subclafer $ sugarClafer claf
  IEConstraint _ True constraint -> Subconstraint $ sugarConstraint constraint
  IEConstraint _ False softconstraint -> Subsoftconstraint $ sugarSoftConstraint softconstraint
  IEGoal _ _ goal -> Subgoal $ sugarGoal goal

mkArrowConstraint :: Clafer -> [Element]
mkArrowConstraint (Clafer abstract gcard' id' super' crd init' es) =
    mkArrowConstraint $ PosClafer noSpan abstract gcard' id' super' crd init' es
mkArrowConstraint (PosClafer _ _ _ ident' super' _ _ _) = 
  if isSuperSomeArrow super' then  [Subconstraint $
       Constraint [PosDeclAllDisj noSpan
       (Decl [LocIdIdent $ mkIdent "x", LocIdIdent $ mkIdent "y"]
             (PosClaferId noSpan  $ Path [ModIdIdent ident']))
       (PosENeq noSpan (PosESetExp noSpan $ Join (PosClaferId noSpan $ Path [ModIdIdent $ mkIdent "x"])
                             (PosClaferId noSpan $ Path [ModIdIdent $ mkIdent "ref"]))
             (PosESetExp noSpan $ Join (PosClaferId noSpan $ Path [ModIdIdent $ mkIdent "y"])
                             (PosClaferId noSpan $ Path [ModIdIdent $ mkIdent "ref"])))]]
  else []

isSuperSomeArrow :: Super -> Bool
isSuperSomeArrow (SuperSome arrow _) = isSuperArrow arrow
isSuperSomeArrow (PosSuperSome _ arrow _) = isSuperArrow arrow
isSuperSomeArrow _ = False

isSuperArrow :: SuperHow -> Bool
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
  GCardInterval crd -> desugarGCard $ PosGCardInterval noSpan crd
  PosGCardEmpty _  -> Nothing
  PosGCardXor _ -> Just $ IGCard True (1, 1)
  PosGCardOr _  -> Just $ IGCard True (1, -1)
  PosGCardMux _ -> Just $ IGCard True (0, 1)
  PosGCardOpt _ -> Just $ IGCard True (0, -1)
  PosGCardInterval _ ncard ->
      Just $ IGCard (isOptionalDef ncard) $ desugarNCard ncard

isOptionalDef :: NCard -> Bool
isOptionalDef (PosNCard _ m n) = isOptionalDef $ NCard m n
isOptionalDef (NCard m n) = ((0::Integer) == mkInteger m) && (not $ isExIntegerAst n)

isExIntegerAst :: ExInteger -> Bool
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
  CardInterval crd  -> desugarCard $ PosCardInterval noSpan crd
  PosCardEmpty _  -> Nothing
  PosCardLone _  ->  Just (0, 1)
  PosCardSome _  ->  Just (1, -1)
  PosCardAny _ ->  Just (0, -1)
  PosCardNum _ n  -> Just (mkInteger n, mkInteger n)
  PosCardInterval _ ncard  -> Just $ desugarNCard ncard

desugarNCard :: NCard -> (Integer, Integer)
desugarNCard (NCard i ex) = desugarNCard $ PosNCard noSpan i ex
desugarNCard (PosNCard _ i ex) = (mkInteger i, desugarExInteger ex)

desugarExInteger :: ExInteger -> Integer
desugarExInteger ExIntegerAst = -1
desugarExInteger (PosExIntegerAst _) = -1
desugarExInteger (ExIntegerNum n) = mkInteger n
desugarExInteger (PosExIntegerNum _ n) = mkInteger n

sugarCard :: Maybe Interval -> Card
sugarCard x = case x of
  Nothing -> CardEmpty
  Just (i, ex) ->
      CardInterval $ NCard (PosInteger ((0, 0), show i)) (sugarExInteger ex)

sugarExInteger :: Integer -> ExInteger
sugarExInteger n = if n == -1 then ExIntegerAst else (ExIntegerNum $ PosInteger ((0, 0), show n))

desugarExp :: Maybe PExp -> Exp -> PExp
desugarExp par x = 
  let pexp = PExp par Nothing "" (range x) iexp
      iexp = flip desugarExp' x $ Just pexp
  in pexp

desugarExp' :: Maybe PExp -> Exp -> IExp
desugarExp' par x = case x of
  DeclAllDisj decl exp' -> desugarExp' par $ PosDeclAllDisj noSpan decl exp'
  DeclAll decl exp' -> desugarExp' par $ PosDeclAll noSpan decl exp'
  DeclQuantDisj quant' decl exp' ->
      desugarExp' par $ PosDeclQuantDisj noSpan quant' decl exp'
  DeclQuant quant' decl exp' -> desugarExp' par $ PosDeclQuant noSpan quant' decl exp'
  EIff exp0 exp'  -> desugarExp' par $ PosEIff noSpan exp0 exp'
  EImplies exp0 exp'  -> desugarExp' par $ PosEImplies noSpan exp0 exp'
  EImpliesElse exp0 exp1 exp'  -> desugarExp' par $ PosEImpliesElse noSpan exp0 exp1 exp'
  EOr exp0 exp'  -> desugarExp' par $ PosEOr noSpan exp0 exp'
  EXor exp0 exp'  -> desugarExp' par $ PosEXor noSpan exp0 exp'
  EAnd exp0 exp'  -> desugarExp' par $ PosEAnd noSpan exp0 exp'
  ENeg exp' -> desugarExp' par $ PosENeg noSpan exp'
  QuantExp quant' exp'  -> desugarExp' par $ PosQuantExp noSpan quant' exp'
  ELt  exp0 exp'  -> desugarExp' par $ PosELt noSpan exp0 exp'
  EGt  exp0 exp'  -> desugarExp' par $ PosEGt noSpan exp0 exp'
  EEq  exp0 exp'  -> desugarExp' par $ PosEEq noSpan exp0 exp'
  ELte exp0 exp'  -> desugarExp' par $ PosELte noSpan exp0 exp'
  EGte exp0 exp'  -> desugarExp' par $ PosEGte noSpan exp0 exp'
  ENeq exp0 exp'  -> desugarExp' par $ PosENeq noSpan exp0 exp'
  EIn  exp0 exp'  -> desugarExp' par $ PosEIn noSpan exp0 exp'
  ENin exp0 exp'  -> desugarExp' par $ PosENin noSpan exp0 exp'
  EAdd exp0 exp'  -> desugarExp' par $ PosEAdd noSpan exp0 exp'
  ESub exp0 exp'  -> desugarExp' par $ PosESub noSpan exp0 exp'
  EMul exp0 exp'  -> desugarExp' par $ PosEMul noSpan exp0 exp'
  EDiv exp0 exp'  -> desugarExp' par $ PosEDiv noSpan exp0 exp'
  ECSetExp exp'   -> desugarExp' par $ PosECSetExp noSpan exp'
  ESumSetExp sexp -> desugarExp' par $ PosESumSetExp noSpan sexp  
  EMinExp exp'    -> desugarExp' par $ PosEMinExp noSpan exp'
  EGMax exp' -> desugarExp' par $ PosEGMax noSpan exp'
  EGMin exp' -> desugarExp' par $ PosEGMin noSpan exp'
  EInt n -> desugarExp' par $ PosEInt noSpan n
  EDouble n -> desugarExp' par $ PosEDouble noSpan n
  EStr str  -> desugarExp' par $ PosEStr noSpan str
  ESetExp sexp -> desugarExp' par $ PosESetExp noSpan sexp    
  PosDeclAllDisj _ decl exp' ->
      IDeclPExp IAll [desugarDecl True decl] (dpe exp')
  PosDeclAll _ decl exp' -> IDeclPExp IAll [desugarDecl False decl] (dpe exp')
  PosDeclQuantDisj _ quant' decl exp' ->
      IDeclPExp (desugarQuant quant') [desugarDecl True decl] (dpe exp')
  PosDeclQuant _ quant' decl exp' ->
      IDeclPExp (desugarQuant quant') [desugarDecl False decl] (dpe exp')
  PosEIff _ exp0 exp'  -> dop iIff [exp0, exp']
  PosEImplies _ exp0 exp'  -> dop iImpl [exp0, exp']
  PosEImpliesElse _ exp0 exp1 exp'  -> dop iIfThenElse [exp0, exp1, exp']
  PosEOr _ exp0 exp'  -> dop iOr   [exp0, exp']
  PosEXor _ exp0 exp'  -> dop iXor [exp0, exp']
  PosEAnd _ exp0 exp'  -> dop iAnd [exp0, exp']
  PosENeg _ exp'  -> dop iNot [exp']
  PosQuantExp _ quant' exp' ->
      IDeclPExp (desugarQuant quant') [] (desugarExp par exp')
  PosELt  _ exp0 exp'  -> dop iLt  [exp0, exp']
  PosEGt  _ exp0 exp'  -> dop iGt  [exp0, exp']
  PosEEq  _ exp0 exp'  -> dop iEq  [exp0, exp']
  PosELte _ exp0 exp'  -> dop iLte [exp0, exp']
  PosEGte _ exp0 exp'  -> dop iGte [exp0, exp']
  PosENeq _ exp0 exp'  -> dop iNeq [exp0, exp']
  PosEIn  _ exp0 exp'  -> dop iIn  [exp0, exp']
  PosENin _ exp0 exp'  -> dop iNin [exp0, exp']
  PosEAdd _ exp0 exp'  -> dop iPlus [exp0, exp']
  PosESub _ exp0 exp'  -> dop iSub [exp0, exp']
  PosEMul _ exp0 exp'  -> dop iMul [exp0, exp']
  PosEDiv _ exp0 exp'  -> dop iDiv [exp0, exp']
  PosECSetExp _ exp'   -> dop iCSet [exp']
  PosESumSetExp _ exp' -> dop iSumSet [exp']
  PosEMinExp s exp'    -> dop iMul [PosEInt s $ PosInteger ((0,0), "-1"), exp']  
  PosEGMax _ exp' -> dop iGMax [exp']
  PosEGMin _ exp' -> dop iGMin [exp']  
  PosEInt _ n  -> IInt $ mkInteger n
  PosEDouble _ (PosDouble n) -> IDouble $ read $ snd n
  PosEStr _ (PosString str)  -> IStr $ snd str
  PosESetExp _ sexp -> desugarSetExp' sexp
  where
  dop = desugarOp (desugarExp par)
  dpe = desugarPath.(desugarExp par)

desugarOp :: (a -> PExp) -> String -> [a] -> IExp
desugarOp f op' exps' = 
    if (op' == iIfThenElse)
      then IFunExp op' $ (desugarPath $ head mappedList) : (map reducePExp $ tail mappedList)
      else IFunExp op' $ map (trans.f) exps'
    where
      mappedList = map f exps'
      trans = if op' `elem` ([iNot, iIfThenElse] ++ logBinOps)
          then desugarPath else id


desugarSetExp :: SetExp -> PExp
desugarSetExp x = pExpDefPid (range x) $ desugarSetExp' x


desugarSetExp' :: SetExp -> IExp
desugarSetExp' x = case x of
  Union exp0 exp'        -> desugarSetExp' $ PosUnion noSpan exp0 exp'
  UnionCom exp0 exp'     -> desugarSetExp' $ PosUnionCom noSpan exp0 exp'
  Difference exp0 exp'   -> desugarSetExp' $ PosDifference noSpan exp0 exp'
  Intersection exp0 exp' -> desugarSetExp' $ PosIntersection noSpan exp0 exp'
  Domain exp0 exp'       -> desugarSetExp' $ PosDomain noSpan exp0 exp'
  Range exp0 exp'        -> desugarSetExp' $ PosRange noSpan exp0 exp'
  Join exp0 exp'         -> desugarSetExp' $ PosJoin noSpan exp0 exp'
  ClaferId name  -> desugarSetExp' $ PosClaferId noSpan name
  PosUnion _ exp0 exp'        -> dop iUnion        [exp0, exp']
  PosUnionCom _ exp0 exp'     -> dop iUnion        [exp0, exp']
  PosDifference _ exp0 exp'   -> dop iDifference   [exp0, exp']
  PosIntersection _ exp0 exp' -> dop iIntersection [exp0, exp']
  PosDomain _ exp0 exp'       -> dop iDomain       [exp0, exp']
  PosRange _ exp0 exp'        -> dop iRange        [exp0, exp']
  PosJoin _ exp0 exp'         -> dop iJoin         [exp0, exp']
  PosClaferId _ name  -> desugarName name

  where
  dop = desugarOp desugarSetExp


sugarExp :: PExp -> Exp
sugarExp x = sugarExp' $ Language.Clafer.Intermediate.Intclafer.exp x


sugarExp' :: IExp -> Exp
sugarExp' x = case x of
  IDeclPExp quant' [] pexp -> QuantExp (sugarQuant quant') (sugarExp pexp)
  IDeclPExp IAll (decl@(IDecl True _ _):[]) pexp ->
    DeclAllDisj   (sugarDecl decl) (sugarExp pexp)
  IDeclPExp IAll  (decl@(IDecl False _ _):[]) pexp ->
    DeclAll       (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant' (decl@(IDecl True _ _):[]) pexp ->
    DeclQuantDisj (sugarQuant quant') (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant' (decl@(IDecl False _ _):[]) pexp ->
    DeclQuant     (sugarQuant quant') (sugarDecl decl) (sugarExp pexp)
  IFunExp op' exps' ->
    if op' `elem` unOps then (sugarUnOp op') (exps''!!0)
    else if op' `elem` setBinOps then (ESetExp $ sugarSetExp' x)
    else if op' `elem` binOps then (sugarOp op') (exps''!!0) (exps''!!1)
    else (sugarTerOp op') (exps''!!0) (exps''!!1) (exps''!!2)
    where
    exps'' = map sugarExp exps'
  IInt n -> EInt $ PosInteger ((0, 0), show n)
  IDouble n -> EDouble $ PosDouble ((0, 0), show n)
  IStr str -> EStr $ PosString ((0, 0), str)
  IClaferId _ _ _ -> ESetExp $ sugarSetExp' x
  _ -> error "Function sugarExp' from Desugarer was given an invalid argument" -- This should never happen
  where
  sugarUnOp op''
    | op'' == iNot           = ENeg
    | op'' == iCSet          = ECSetExp
    | op'' == iMin           = EMinExp
    | op'' == iGMax          = EGMax
    | op'' == iGMin          = EGMin 
    | op'' == iSumSet        = ESumSetExp
    | otherwise            = error $ show op'' ++ "is not an op"
  sugarOp op''
    | op'' == iIff           = EIff
    | op'' == iImpl          = EImplies
    | op'' == iOr            = EOr
    | op'' == iXor           = EXor
    | op'' == iAnd           = EAnd 
    | op'' == iLt            = ELt
    | op'' == iGt            = EGt
    | op'' == iEq            = EEq  
    | op'' == iLte           = ELte
    | op'' == iGte           = EGte
    | op'' == iNeq           = ENeq
    | op'' == iIn            = EIn
    | op'' == iNin           = ENin
    | op'' == iPlus          = EAdd
    | op'' == iSub           = ESub
    | op'' == iMul           = EMul
    | op'' == iDiv           = EDiv
    | otherwise            = error $ show op'' ++ "is not an op"
  sugarTerOp op''
    | op'' == iIfThenElse    = EImpliesElse
    | otherwise            = error $ show op'' ++ "is not an op"


sugarSetExp :: PExp -> SetExp
sugarSetExp x = sugarSetExp' $ Language.Clafer.Intermediate.Intclafer.exp x


sugarSetExp' :: IExp -> SetExp
sugarSetExp' (IFunExp op' exps') = (sugarOp op') (exps''!!0) (exps''!!1)
    where
    exps'' = map sugarSetExp exps'
    sugarOp op''
      | op'' == iUnion         = Union
      | op'' == iDifference    = Difference
      | op'' == iIntersection  = Intersection
      | op'' == iDomain        = Domain
      | op'' == iRange         = Range
      | op'' == iJoin          = Join
      | otherwise              = error "Invalid argument given to function sygarSetExp' in Desugarer"
sugarSetExp' (IClaferId "" id' _) = ClaferId $ Path [ModIdIdent $ mkIdent id']
sugarSetExp' (IClaferId modName' id' _) = ClaferId $ Path $ (sugarModId modName') : [sugarModId id']
sugarSetExp' _ = error "IDecelPexp, IInt, IDobule, and IStr can not be sugared into a setExp!" --This should never happen

desugarPath :: PExp -> PExp
desugarPath (PExp par' iType' pid' pos' x) = reducePExp $ PExp par' iType' pid' pos' result
  where
  result
    | isSet x     = IDeclPExp ISome [] (pExpDefPid pos' x)
    | isNegSome x = IDeclPExp INo   [] $ bpexp $ Language.Clafer.Intermediate.Intclafer.exp $ head $ exps x
    | otherwise   =  x
  isNegSome (IFunExp op' [PExp _ _ _ _ (IDeclPExp ISome [] _)]) = op' == iNot
  isNegSome _ = False


isSet :: IExp -> Bool
isSet (IClaferId _ _ _)  = True
isSet (IFunExp op' _) = op' `elem` setBinOps
isSet _ = False


-- reduce parent
reducePExp :: PExp -> PExp
reducePExp (PExp par' t pid' pos' x) = PExp par' t pid' pos' $ reduceIExp x

reduceIExp :: IExp -> IExp
reduceIExp (IDeclPExp quant' decls' pexp) = IDeclPExp quant' decls' $ reducePExp pexp
reduceIExp (IFunExp op' exps') = redNav $ IFunExp op' $ map redExps exps'
    where
    (redNav, redExps) = if op' == iJoin then (reduceNav, id) else (id, reducePExp) 
reduceIExp x = x

reduceNav :: IExp -> IExp
reduceNav x@(IFunExp op' exps'@((PExp _ _ _ _ iexp@(IFunExp _ (pexp0:pexp:_))):pPexp:_)) = 
  if op' == iJoin && isParent pPexp && isClaferName pexp
  then reduceNav $ Language.Clafer.Intermediate.Intclafer.exp pexp0
  else x{exps = (head exps'){Language.Clafer.Intermediate.Intclafer.exp = reduceIExp iexp} :
                tail exps'}
reduceNav x = x


desugarDecl :: Bool -> Decl -> IDecl
desugarDecl isDisj' (Decl locids exp') = desugarDecl isDisj' $ PosDecl noSpan locids exp'
desugarDecl isDisj' (PosDecl _ locids exp') =
    IDecl isDisj' (map desugarLocId locids) (desugarSetExp exp')


sugarDecl :: IDecl -> Decl
sugarDecl (IDecl _ locids exp') =
    Decl (map sugarLocId locids) (sugarSetExp exp')


desugarLocId :: LocId -> String
desugarLocId (LocIdIdent id') = desugarLocId $ PosLocIdIdent noSpan id'
desugarLocId (PosLocIdIdent _ id') = transIdent id'


sugarLocId :: String -> LocId
sugarLocId x = LocIdIdent $ mkIdent x

desugarQuant :: Quant -> IQuant
desugarQuant QuantNo = desugarQuant $ PosQuantNo noSpan
desugarQuant QuantLone = desugarQuant $ PosQuantLone noSpan
desugarQuant QuantOne = desugarQuant $ PosQuantOne noSpan
desugarQuant QuantSome = desugarQuant $ PosQuantSome noSpan
desugarQuant (PosQuantNo _) = INo
desugarQuant (PosQuantLone _) = ILone
desugarQuant (PosQuantOne _) = IOne
desugarQuant (PosQuantSome _) = ISome

sugarQuant :: IQuant -> Quant
sugarQuant INo = QuantNo
sugarQuant ILone = QuantLone
sugarQuant IOne = QuantOne
sugarQuant ISome = QuantSome
sugarQuant IAll = error "sugarQaunt was called on IAll, this is not allowed!" --Should never happen
