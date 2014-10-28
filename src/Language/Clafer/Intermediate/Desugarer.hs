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
{- | Transforms an Abstract Syntax Tree (AST) from "Language.Clafer.Front.Absclafer"
into Intermediate representation (IR) from "Language.Clafer.Intermediate.Intclafer" of a Clafer model.
-}
module Language.Clafer.Intermediate.Desugarer where

import Data.List

import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer

import Debug.Trace
-- | Transform the AST into the intermediate representation (IR)
desugarModule :: Module -> IModule
desugarModule (Module _ declarations) = IModule "" $
      declarations >>= desugarEnums >>= desugarDeclaration
--      [ImoduleFragment $ declarations >>= desugarEnums >>= desugarDeclaration]

sugarModule :: IModule -> Module
sugarModule x = Module noSpan $ map sugarDeclaration $ _mDecls x -- (fragments x >>= mDecls)

-- | desugars enumeration to abstract and global singleton features
desugarEnums :: Declaration -> [Declaration]
desugarEnums (EnumDecl s id' enumids) = (absEnum s) : map (mkEnum s) enumids
    where
    oneToOne = (CardInterval noSpan $ NCard noSpan (PosInteger ((0,0), "1")) (ExIntegerNum noSpan $ PosInteger ((0,0), "1")))
    absEnum s1 = ElementDecl s1 $ Subclafer s1 $ Clafer s1 (Abstract s1) [] (GCardEmpty s1) id' (SuperEmpty s1) (CardEmpty s1) (InitEmpty s1) (TransitionEmpty s1) (ElementsList s1 [])
    mkEnum s2 (EnumIdIdent _ eId) = ElementDecl s2 $
                                   Subclafer s2 $
                                   Clafer s2 (AbstractEmpty s2) [] (GCardEmpty s2) eId ((SuperSome s2) (SuperColon s2) (ClaferId s2 $ Path s2 [ModIdIdent s2 id'])) oneToOne (InitEmpty s2) (TransitionEmpty s2) (ElementsList s2 [])
desugarEnums x = [x]


desugarDeclaration :: Declaration -> [IElement]
desugarDeclaration (ElementDecl _ element) = desugarElement element
desugarDeclaration _ = error "desugared"


sugarDeclaration :: IElement -> Declaration
sugarDeclaration  (IEClafer clafer) = ElementDecl (_cinPos clafer) $ Subclafer (_cinPos clafer) $ sugarClafer clafer
sugarDeclaration (IEConstraint True constraint) =
      ElementDecl (_inPos constraint) $ Subconstraint (_inPos constraint) $ sugarConstraint constraint
sugarDeclaration  (IEConstraint False softconstraint) =
      ElementDecl (_inPos softconstraint) $ Subsoftconstraint (_inPos softconstraint) $ sugarSoftConstraint softconstraint
sugarDeclaration  (IEGoal _ goal) = ElementDecl (_inPos goal) $ Subgoal (_inPos goal) $ sugarGoal goal


desugarClafer :: Clafer -> [IElement]
desugarClafer clafer@(Clafer s abstract tmods gcrd id' super' crd init' trans es)  =
   preElements ++ [IEClafer $ IClafer s (desugarAbstract abstract) (desugarGCard gcrd) (transIdent id')
            "" (desugarSuper super') (desugarCard crd) (0, -1) (desugarMutability tmods es)
            elements] ++ (desugarInit id' init')
  where
    preElements = desugarInitiallyModifier tmods (transIdent id')
    elements = (desugarClaferTrans clafer) ++ (desugarElements es)

sugarClafer :: IClafer -> Clafer
sugarClafer cl@(IClafer s abstract gcard' _ uid' super' crd _ mut es) =
    Clafer s (sugarAbstract abstract) (sugarModifier cl) (sugarGCard gcard') (mkIdent uid')
      (sugarSuper super') (sugarCard crd) (InitEmpty s) (TransitionEmpty s) (sugarElements mut es)


desugarInitiallyModifier :: [TempModifier] -> String -> [IElement]
desugarInitiallyModifier [] _ = []
desugarInitiallyModifier mods ident = case (find isInitial mods) of
  Just (Initial s) -> [IEConstraint True $ desugarConstraint $ mkExp s ]
  Nothing -> []
  where
    isInitial (Initial _) = True
    isInitial _ = False
    mkExp s = Constraint s [TmpInitially s $ mkClaferIdExp s ident]

sugarModifier :: IClafer -> [TempModifier]
sugarModifier cl = case _mutable cl of
  True -> [] -- In sugared version final is expressed as constraint, but it can be changed -- [Final noSpan]
  False -> []

desugarSuper :: Super -> ISuper
desugarSuper (SuperEmpty s) =
      ISuper False [PExp (Just $ TClafer []) "" s $ mkLClaferId baseClafer True Nothing]
desugarSuper (SuperSome _ superhow setexp) =
      ISuper (desugarSuperHow superhow) [desugarSetExp setexp]


desugarSuperHow :: SuperHow -> Bool
desugarSuperHow (SuperColon _) = False
desugarSuperHow _  = True


desugarInit :: PosIdent -> Init -> [IElement]
desugarInit _ (InitEmpty _) = []
desugarInit id' (InitSome s inithow exp') = [ IEConstraint (desugarInitHow inithow) (pExpDefPid s implIExp) ]
  where
    cId :: PExp
    cId = mkPLClaferId (snd $ getIdent id') False Nothing
    -- <id> = <exp'>
    assignIExp :: IExp
    assignIExp = (IFunExp "=" [cId, desugarExp exp'])
    -- some <id> => <assignIExp>
    implIExp :: IExp
    implIExp = (IFunExp "=>" [ pExpDefPid s $ IDeclPExp ISome [] cId, pExpDefPid s assignIExp ])
    getIdent (PosIdent y) = y

desugarInitHow :: InitHow -> Bool
desugarInitHow (InitHow_1 _) = True
desugarInitHow (InitHow_2 _ )= False


desugarClaferTrans :: Clafer -> [IElement]
desugarClaferTrans (Clafer _ _ _ _ name _ _ _ trans es) =
  case trans of
      TransitionEmpty _ -> []
      Transition s arrow e -> [IEConstraint True (desugarTrans s (mkClaferIdExp s $ transIdent name) arrow e)]

desugarTrans :: Span -> Exp -> TransArrow -> Exp -> PExp
desugarTrans s e1 arrow e2 = desugarExp $ desugarTrans' s e1 arrow e2

desugarTrans' :: Span -> Exp -> TransArrow -> Exp -> Exp
desugarTrans' s e1 arrow e2 =  case arrow of
      AsyncTransArrow _ -> LtlW s e1 e2
      GuardedAsyncTransArrow _ (TransGuard _ guardExp) -> EImplies s guardExp (LtlW s e1 e2)
      SyncTransArrow _ -> LtlU s e1 e2
      GuardedSyncTransArrow _ (TransGuard _ guardExp) -> EImplies s guardExp (LtlW s e1 e2)
      NextTransArrow _ -> EAnd s e1 (LtlX s e2)
      GuardedNextTransArrow _ (TransGuard _ guardExp) -> EImplies s guardExp (EAnd s e1 (LtlX s e2))


desugarMutability :: [TempModifier] -> Elements -> Mutability
desugarMutability mods es = not ( containsFinal || (containsFinalConstr es) )
  where
    containsFinal = any isFinalMod mods
    containsFinalConstr (ElementsEmpty _) = False
    containsFinalConstr (ElementsList _ es) = any isFinalEl es
    isFinalEl :: Element -> Bool
    isFinalEl (Subconstraint _ (FinalConstraint _ )) = True
    isFinalEl _ = False
    isFinalMod (Final _) = True
    isFinalMod _ = False

desugarName :: Name -> IExp
desugarName (Path _ path) =
      IClaferId (concatMap ((++ modSep).desugarModId) (init path))
                (desugarModId $ last path) True Nothing

desugarModId :: ModId -> Result
desugarModId (ModIdIdent _ id') = transIdent id'

sugarModId :: String -> ModId
sugarModId modid = ModIdIdent noSpan $ mkIdent modid

sugarSuper :: ISuper -> Super
sugarSuper (ISuper _ []) = SuperEmpty noSpan
sugarSuper (ISuper isOverlapping' [pexp]) = SuperSome noSpan (sugarSuperHow isOverlapping') (sugarSetExp pexp)
sugarSuper _ = error "Function sugarSuper from Desugarer expects an ISuper with a list of length one, but it was given one with a list larger than one" -- Should never happen

sugarSuperHow :: Bool -> SuperHow
sugarSuperHow False = SuperColon noSpan
sugarSuperHow True  = SuperMArrow noSpan


sugarInitHow :: Bool -> InitHow
sugarInitHow True  = InitHow_1 noSpan
sugarInitHow False = InitHow_2 noSpan


desugarConstraint :: Constraint -> PExp
desugarConstraint (Constraint _ exps') = desugarPath $ desugarExp $
    (if length exps' > 1 then foldl1 (EAnd noSpan) else head) exps'

desugarSoftConstraint :: SoftConstraint -> PExp
desugarSoftConstraint (SoftConstraint _ exps') = desugarPath $ desugarExp $
    (if length exps' > 1 then foldl1 (EAnd noSpan) else head) exps'

desugarGoal :: Goal -> PExp
desugarGoal (Goal s exps') = desugarPath $ desugarExp $
    (if length exps' > 1 then foldl1 (EAnd s) else head) exps'

sugarConstraint :: PExp -> Constraint
sugarConstraint pexp = Constraint (_inPos pexp)  $ map sugarExp [pexp]

sugarSoftConstraint :: PExp -> SoftConstraint
sugarSoftConstraint pexp = SoftConstraint (_inPos pexp) $ map sugarExp [pexp]

sugarGoal :: PExp -> Goal
sugarGoal pexp = Goal (_inPos pexp) $ map sugarExp [pexp]

desugarAbstract :: Abstract -> Bool
desugarAbstract (AbstractEmpty _) = False
desugarAbstract (Abstract _) = True


sugarAbstract :: Bool -> Abstract
sugarAbstract False = AbstractEmpty noSpan
sugarAbstract True = Abstract noSpan


desugarElements :: Elements -> [IElement]
desugarElements (ElementsEmpty _) = []
desugarElements (ElementsList _ es)  = es >>= desugarElement


sugarElements :: Mutability -> [IElement] -> Elements
sugarElements mut x = ElementsList noSpan $ mutConstraint ++ (map sugarElement x)
  where
    mutConstraint = case mut of
      True -> [Subconstraint noSpan $ FinalConstraint noSpan]
      False -> []


      {-(let desugared = desugarClafer claf  in trace ("desugarClafer; desugared:\n" ++ show desugared ++"\nsugared:\n"++show claf) desugared) ++-}
desugarElement :: Element -> [IElement]
desugarElement x = case x of
  Subclafer _ claf  -> desugarClafer claf ++
      (mkArrowConstraint claf >>= desugarElement)
  ClaferUse s name crd es  -> desugarClafer $ Clafer s
      (AbstractEmpty s) [] (GCardEmpty s) (mkIdent $ _sident $ desugarName name)
      ((SuperSome s) (SuperColon s) (ClaferId s name)) crd (InitEmpty s) (TransitionEmpty s) es
  Subconstraint _ constraint  ->
      case constraint of
          FinalConstraint _ -> []
          Constraint _ _ -> [IEConstraint True $ desugarConstraint constraint]
  Subsoftconstraint _ softconstraint ->
      [IEConstraint False $ desugarSoftConstraint softconstraint]
  Subgoal _ goal -> [IEGoal True $ desugarGoal goal]

sugarElement :: IElement -> Element
sugarElement x = case x of
  IEClafer claf  -> Subclafer noSpan $ sugarClafer claf
  IEConstraint True constraint -> Subconstraint noSpan $ sugarConstraint constraint
  IEConstraint False softconstraint -> Subsoftconstraint noSpan $ sugarSoftConstraint softconstraint
  IEGoal _ goal -> Subgoal noSpan $ sugarGoal goal

mkArrowConstraint :: Clafer -> [Element]
mkArrowConstraint (Clafer s _ _ _ ident' super' _ _ _ _) =
  if isSuperSomeArrow super' then  [Subconstraint s $
       Constraint s [DeclAllDisj s
       (Decl s [LocIdIdent s $ mkIdent "x", LocIdIdent s $ mkIdent "y"]
             (ClaferId s $ Path s [ModIdIdent s ident']))
       (ENeq s (ESetExp s $ Join s (ClaferId s $ Path s [ModIdIdent s $ mkIdent "x"])
                             (ClaferId s $ Path s [ModIdIdent s $ mkIdent "ref"]))
             (ESetExp s $ Join s (ClaferId s $ Path s [ModIdIdent s $ mkIdent "y"])
                             (ClaferId s $ Path s [ModIdIdent s $ mkIdent "ref"])))]]
  else []

isSuperSomeArrow :: Super -> Bool
isSuperSomeArrow (SuperSome _ arrow _) = isSuperArrow arrow
isSuperSomeArrow _ = False

isSuperArrow :: SuperHow -> Bool
isSuperArrow (SuperArrow _) = True
isSuperArrow _ = False

desugarGCard :: GCard -> Maybe IGCard
desugarGCard x = case x of
  GCardEmpty _  -> Nothing
  GCardXor _ -> Just $ IGCard True (1, 1)
  GCardOr _  -> Just $ IGCard True (1, -1)
  GCardMux _ -> Just $ IGCard True (0, 1)
  GCardOpt _ -> Just $ IGCard True (0, -1)
  GCardInterval _ ncard ->
      Just $ IGCard (isOptionalDef ncard) $ desugarNCard ncard

isOptionalDef :: NCard -> Bool
isOptionalDef (NCard _ m n) = ((0::Integer) == mkInteger m) && (not $ isExIntegerAst n)

isExIntegerAst :: ExInteger -> Bool
isExIntegerAst (ExIntegerAst _) = True
isExIntegerAst _ = False

sugarGCard :: Maybe IGCard -> GCard
sugarGCard x = case x of
  Nothing -> GCardEmpty noSpan
  Just (IGCard _ (i, ex)) -> GCardInterval noSpan $ NCard noSpan (PosInteger ((0, 0), show i)) (sugarExInteger ex)


desugarCard :: Card -> Maybe Interval
desugarCard x = case x of
  CardEmpty _  -> Nothing
  CardLone _  ->  Just (0, 1)
  CardSome _  ->  Just (1, -1)
  CardAny _ ->  Just (0, -1)
  CardNum _ n  -> Just (mkInteger n, mkInteger n)
  CardInterval _ ncard  -> Just $ desugarNCard ncard

desugarNCard :: NCard -> (Integer, Integer)
desugarNCard (NCard _ i ex) = (mkInteger i, desugarExInteger ex)

desugarExInteger :: ExInteger -> Integer
desugarExInteger (ExIntegerAst _) = -1
desugarExInteger (ExIntegerNum _ n) = mkInteger n

sugarCard :: Maybe Interval -> Card
sugarCard x = case x of
  Nothing -> CardEmpty noSpan
  Just (i, ex) ->
      CardInterval noSpan $ NCard noSpan (PosInteger ((0, 0), show i)) (sugarExInteger ex)

sugarExInteger :: Integer -> ExInteger
sugarExInteger n = if n == -1 then ExIntegerAst noSpan else (ExIntegerNum noSpan $ PosInteger ((0, 0), show n))

desugarExp :: Exp -> PExp
desugarExp x = pExpDefPid (getSpan x) $ desugarExp' x


translateTmpPatterns :: Exp -> Exp
translateTmpPatterns e = case e of
  TmpPatJustScope span p scope -> case scope of
    -- []((Q & !R & <>R) -> (P U R))
    PatScopeBetween _ q r ->
      let anti = EAnd span (EAnd span q (ENeg span r)) $ LtlF span r
          cons = LtlU span p r
      in LtlG span $ EImplies span anti cons
    -- [](Q & !R -> (P W R))
    PatScopeUntil _ q r ->
      let anti = EAnd span q (ENeg span r)
          cons = LtlW span p r
      in LtlG span $ EImplies span anti cons
      -- Before is same as PRECEDENCE pattern group
  TmpPatBeforeNoScope span s p -> LtlW span (ENeg span p) s
  TmpPatBefore span s p scope -> case scope of
    --[]((Q & !R & <>R) -> (!P U (S | R)))
    PatScopeBetween _ q r ->
      let anti = EAnd span (EAnd span q (ENeg span r)) $ LtlF span r
          cons = LtlU span (ENeg span p) (EOr span s r)
      in LtlG span $ EImplies span anti cons
    --[](Q & !R -> (!P W (S | R)))
    PatScopeUntil _ q r ->
      let anti = EAnd span q (ENeg span r)
          cons = LtlW span (ENeg span p) (EOr span s r)
      in LtlG span $ EImplies span anti cons
      -- After is equavalent to RESPONSE pattern group
  TmpPatAfterNoScope span s p -> LtlG span $ EImplies span p (LtlF span s)
  TmpPatAfter span s p scope -> case scope of
    --[]((Q & !R & <>R) -> (P -> (!R U (S & !R))) U R)
    PatScopeBetween _ q r ->
      let anti = EAnd span (EAnd span q (ENeg span r)) $ LtlF span r
          intImpl = EImplies span p $ LtlU span (ENeg span r) (EAnd span s (ENeg span r))
          cons = LtlU span intImpl r
      in LtlG span $ EImplies span anti cons
    --[](Q & !R -> ((P -> (!R U (S & !R))) W R))
    PatScopeUntil _ q r ->
      let anti = EAnd span q (ENeg span r)
          intImpl = EImplies span p $ LtlU span (ENeg span r) (EAnd span s (ENeg span r))
          cons = LtlW span intImpl r
      in LtlG span $ EImplies span anti cons
  TmpInitially s exp ->
    let oper1 =  ENeg s $ mkClaferIdExp s "this"
        oper2 = LtlX s $ mkClaferIdExp s "this"
    in EImplies s (EAnd s oper1 oper2) $ LtlX s exp
  TmpFinally s exp ->
    let oper1 =  mkClaferIdExp s "this"
        oper2 = LtlX s $ ENeg s $ mkClaferIdExp s "this"
    in EImplies s (EAnd s oper1 oper2) exp
  TmpEventually s exp -> LtlF s exp
  TmpWUntil s exp0 exp1 -> LtlW s exp0 exp1
  TmpUntil s exp0 exp1 -> LtlU s exp0 exp1
  TmpGlobally s exp -> LtlG s exp
  TmpNext s exp -> LtlX s exp
  TransitionExp s exp0 arrow exp1 -> desugarTrans' s exp0 arrow exp1
  _ -> e



desugarExp' :: Exp -> IExp
desugarExp' x = let x' =  translateTmpPatterns x in case x' of
  DeclAllDisj _ decl exp' ->
      IDeclPExp IAll [desugarDecl True decl] (dpe exp')
  DeclAll _ decl exp' -> IDeclPExp IAll [desugarDecl False decl] (dpe exp')
  DeclQuantDisj _ quant' decl exp' ->
      IDeclPExp (desugarQuant quant') [desugarDecl True decl] (dpe exp')
  DeclQuant _ quant' decl exp' ->
      IDeclPExp (desugarQuant quant') [desugarDecl False decl] (dpe exp')
  EIff _ exp0 exp'  -> dop iIff [exp0, exp']
  EImplies _ exp0 exp'  -> dop iImpl [exp0, exp']
  EImpliesElse _ exp0 exp1 exp'  -> dop iIfThenElse [exp0, exp1, exp']
  EOr _ exp0 exp'  -> dop iOr   [exp0, exp']
  EXor _ exp0 exp'  -> dop iXor [exp0, exp']
  EAnd _ exp0 exp'  -> dop iAnd [exp0, exp']
  ENeg _ exp'  -> dop iNot [exp']
  LtlU  _ exp0 exp'  -> dop iU  [exp0, exp']
  LtlW  _ exp0 exp'  -> dop iW  [exp0, exp']
  LtlF  _ exp'  -> dop iF  [exp']
  LtlG  _ exp'  -> dop iG  [exp']
  LtlX  _ exp'  -> dop iX  [exp']
  QuantExp _ quant' exp' ->
      IDeclPExp (desugarQuant quant') [] (desugarExp exp')
  ELt  _ exp0 exp'  -> dop iLt  [exp0, exp']
  EGt  _ exp0 exp'  -> dop iGt  [exp0, exp']
  EEq  _ exp0 exp'  -> dop iEq  [exp0, exp']
  ELte _ exp0 exp'  -> dop iLte [exp0, exp']
  EGte _ exp0 exp'  -> dop iGte [exp0, exp']
  ENeq _ exp0 exp'  -> dop iNeq [exp0, exp']
  EIn  _ exp0 exp'  -> dop iIn  [exp0, exp']
  ENin _ exp0 exp'  -> dop iNin [exp0, exp']
  EAdd _ exp0 exp'  -> dop iPlus [exp0, exp']
  ESub _ exp0 exp'  -> dop iSub [exp0, exp']
  EMul _ exp0 exp'  -> dop iMul [exp0, exp']
  EDiv _ exp0 exp'  -> dop iDiv [exp0, exp']
  ECSetExp _ exp'   -> dop iCSet [exp']
  ESumSetExp _ exp' -> dop iSumSet [exp']
  EMinExp _ exp'    -> dop iMin [exp']
  EGMax _ exp' -> dop iGMax [exp']
  EGMin _ exp' -> dop iGMin [exp']
  EInt _ n  -> IInt $ mkInteger n
  EDouble _ (PosDouble n) -> IDouble $ read $ snd n
  EStr _ (PosString str)  -> IStr $ snd str
  ESetExp _ sexp -> desugarSetExp' sexp
  _ -> error (show x)
  where
  dop = desugarOp desugarExp
  dpe = desugarPath.desugarExp

desugarOp :: (a -> PExp) -> String -> [a] -> IExp
desugarOp f op' exps' =
    if (op' == iIfThenElse)
      then IFunExp op' $ (desugarPath $ head mappedList) : (map reducePExp $ tail mappedList)
      else IFunExp op' $ map (trans.f) exps'
    where
      mappedList = map f exps'
      trans = if op' `elem` ([iNot, iIfThenElse] ++ logBinOps ++ ltlUnOps)
          then desugarPath else id


desugarSetExp :: SetExp -> PExp
desugarSetExp x = pExpDefPid (getSpan x) $ desugarSetExp' x


desugarSetExp' :: SetExp -> IExp
desugarSetExp' x = case x of
  Union _ exp0 exp'        -> dop iUnion        [exp0, exp']
  UnionCom _ exp0 exp'     -> dop iUnion        [exp0, exp']
  Difference _ exp0 exp'   -> dop iDifference   [exp0, exp']
  Intersection _ exp0 exp' -> dop iIntersection [exp0, exp']
  Domain _ exp0 exp'       -> dop iDomain       [exp0, exp']
  Range _ exp0 exp'        -> dop iRange        [exp0, exp']
  Join _ exp0 exp'         -> dop iJoin         [exp0, exp']
  ClaferId _ name  -> desugarName name

  where
  dop = desugarOp desugarSetExp


sugarExp :: PExp -> Exp
sugarExp x = sugarExp' $ Language.Clafer.Intermediate.Intclafer._exp x


sugarExp' :: IExp -> Exp
sugarExp' x = case x of
  IDeclPExp quant' [] pexp -> QuantExp noSpan (sugarQuant quant') (sugarExp pexp)
  IDeclPExp IAll (decl@(IDecl True _ _):[]) pexp ->
    DeclAllDisj noSpan (sugarDecl decl) (sugarExp pexp)
  IDeclPExp IAll  (decl@(IDecl False _ _):[]) pexp ->
    DeclAll noSpan (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant' (decl@(IDecl True _ _):[]) pexp ->
    DeclQuantDisj noSpan (sugarQuant quant') (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant' (decl@(IDecl False _ _):[]) pexp ->
    DeclQuant noSpan (sugarQuant quant') (sugarDecl decl) (sugarExp pexp)
  IFunExp op' exps' ->
    if op' `elem` unOps then (sugarUnOp op') (exps''!!0)
    else if op' `elem` setBinOps then (ESetExp noSpan $ sugarSetExp' x)
    else if op' `elem` binOps then (sugarOp op') (exps''!!0) (exps''!!1)
    else (sugarTerOp op') (exps''!!0) (exps''!!1) (exps''!!2)
    where
    exps'' = map sugarExp exps'
  IInt n -> EInt noSpan $ PosInteger ((0, 0), show n)
  IDouble n -> EDouble noSpan $ PosDouble ((0, 0), show n)
  IStr str -> EStr noSpan $ PosString ((0, 0), str)
  IClaferId _ _ _ _ -> ESetExp noSpan $ sugarSetExp' x
  _ -> error "Function sugarExp' from Desugarer was given an invalid argument" -- This should never happen
  where
  sugarUnOp op''
    | op'' == iNot           = ENeg noSpan
    | op'' == iCSet          = ECSetExp noSpan
    | op'' == iMin           = EMinExp noSpan
    | op'' == iGMax          = EGMax noSpan
    | op'' == iGMin          = EGMin noSpan
    | op'' == iSumSet        = ESumSetExp noSpan
    | op'' == iF             = LtlF noSpan
    | op'' == iG             = LtlG noSpan
    | op'' == iX             = LtlX noSpan
    | otherwise            = error $ show op'' ++ "is not an op"
  sugarOp op''
    | op'' == iIff           = EIff noSpan
    | op'' == iImpl          = EImplies noSpan
    | op'' == iOr            = EOr noSpan
    | op'' == iXor           = EXor noSpan
    | op'' == iAnd           = EAnd noSpan
    | op'' == iLt            = ELt noSpan
    | op'' == iGt            = EGt noSpan
    | op'' == iEq            = EEq noSpan
    | op'' == iLte           = ELte noSpan
    | op'' == iGte           = EGte noSpan
    | op'' == iNeq           = ENeq noSpan
    | op'' == iIn            = EIn noSpan
    | op'' == iNin           = ENin noSpan
    | op'' == iPlus          = EAdd noSpan
    | op'' == iSub           = ESub noSpan
    | op'' == iMul           = EMul noSpan
    | op'' == iDiv           = EDiv noSpan
    | op'' == iU             = LtlU noSpan
    | op'' == iW             = LtlW noSpan
    | otherwise            = error $ show op'' ++ "is not an op"
  sugarTerOp op''
    | op'' == iIfThenElse    = EImpliesElse noSpan
    | otherwise            = error $ show op'' ++ "is not an op"


sugarSetExp :: PExp -> SetExp
sugarSetExp x = sugarSetExp' $ _exp x


sugarSetExp' :: IExp -> SetExp
sugarSetExp' (IFunExp op' exps') = (sugarOp op') (exps''!!0) (exps''!!1)
    where
    exps'' = map sugarSetExp exps'
    sugarOp op''
      | op'' == iUnion         = Union noSpan
      | op'' == iDifference    = Difference noSpan
      | op'' == iIntersection  = Intersection noSpan
      | op'' == iDomain        = Domain noSpan
      | op'' == iRange         = Range noSpan
      | op'' == iJoin          = Join noSpan
      | otherwise              = error "Invalid argument given to function sygarSetExp' in Desugarer"
sugarSetExp' (IClaferId "" id' _ _) = ClaferId noSpan $ Path noSpan [ModIdIdent noSpan $ mkIdent id']
sugarSetExp' (IClaferId modName' id' _ _) = ClaferId noSpan $ Path noSpan $ (sugarModId modName') : [sugarModId id']
sugarSetExp' _ = error "IDecelPexp, IInt, IDobule, and IStr can not be sugared into a setExp!" --This should never happen

desugarPath :: PExp -> PExp
desugarPath (PExp iType' pid' pos' x) = reducePExp $ PExp iType' pid' pos' result
  where
  result
    | isSet x     = IDeclPExp ISome [] (pExpDefPid pos' x)
    | isNegSome x = IDeclPExp INo   [] $ _bpexp $ Language.Clafer.Intermediate.Intclafer._exp $ head $ _exps x
    | otherwise   =  x
  isNegSome (IFunExp op' [PExp _ _ _ (IDeclPExp ISome [] _)]) = op' == iNot
  isNegSome _ = False


isSet :: IExp -> Bool
isSet (IClaferId _ _ _ _)  = True
isSet (IFunExp op' _) = op' `elem` setBinOps
isSet _ = False


-- reduce parent
reducePExp :: PExp -> PExp
reducePExp (PExp t pid' pos' x) = PExp t pid' pos' $ reduceIExp x

reduceIExp :: IExp -> IExp
reduceIExp (IDeclPExp quant' decls' pexp) = IDeclPExp quant' decls' $ reducePExp pexp
reduceIExp (IFunExp op' exps') = redNav $ IFunExp op' $ map redExps exps'
    where
    (redNav, redExps) = if op' == iJoin then (reduceNav, id) else (id, reducePExp)
reduceIExp x = x

reduceNav :: IExp -> IExp
reduceNav x@(IFunExp op' exps'@((PExp _ _ _ iexp@(IFunExp _ (pexp0:pexp:_))):pPexp:_)) =
  if op' == iJoin && isParent pPexp && isClaferName pexp
  then reduceNav $ Language.Clafer.Intermediate.Intclafer._exp pexp0
  else x{_exps = (head exps'){Language.Clafer.Intermediate.Intclafer._exp = reduceIExp iexp} :
                tail exps'}
reduceNav x = x


desugarDecl :: Bool -> Decl -> IDecl
desugarDecl isDisj' (Decl _ locids exp') =
    IDecl isDisj' (map desugarLocId locids) (desugarSetExp exp')


sugarDecl :: IDecl -> Decl
sugarDecl (IDecl _ locids exp') =
    Decl noSpan (map sugarLocId locids) (sugarSetExp exp')


desugarLocId :: LocId -> String
desugarLocId (LocIdIdent _ id') = transIdent id'


sugarLocId :: String -> LocId
sugarLocId x = LocIdIdent noSpan $ mkIdent x

desugarQuant :: Quant -> IQuant
desugarQuant (QuantNo _) = INo
desugarQuant (QuantNot _) = INo
desugarQuant (QuantLone _) = ILone
desugarQuant (QuantOne _) = IOne
desugarQuant (QuantSome _) = ISome

sugarQuant :: IQuant -> Quant
sugarQuant INo = QuantNo noSpan  -- will never sugar to QuantNOT
sugarQuant ILone = QuantLone noSpan
sugarQuant IOne = QuantOne noSpan
sugarQuant ISome = QuantSome noSpan
sugarQuant IAll = error "sugarQaunt was called on IAll, this is not allowed!" --Should never happen

mkClaferIdExp :: Span -> String -> Exp
mkClaferIdExp s name = ESetExp s $ mkClaferId s name

mkClaferId :: Span -> String -> SetExp
mkClaferId s name = ClaferId s $ Path s [ModIdIdent s $ mkIdent name]
