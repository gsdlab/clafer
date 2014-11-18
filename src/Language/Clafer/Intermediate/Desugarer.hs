{-# LANGUAGE TemplateHaskell #-}
{-
 Copyright (C) 2012-2014 Kacper Bak, Jimmy Liang, Michal Antkiewicz, Paulius Juodisius <http://gsd.uwaterloo.ca>

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
into Intermediate representation (IR) from "Language.Clafer.Intermediate.Intclafer" 
of a Clafer model. Collects the information stored in DesugarerState.
-}
module Language.Clafer.Intermediate.Desugarer 
  ( desugar
  , sugarModule
  , sugarExp
  , sugarInitHow
  , desugarPath
  ) where

import Control.Applicative ((<$>))
import Control.Monad.State
import Control.Lens
import Data.List (sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Ord

import Language.ClaferT 
import Language.Clafer.Common
import Data.Maybe (fromMaybe)
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer

-- | Information collected during desugaring
data DesugarerState = DesugarerState 
  { _astElementsMap :: Map Span [Ast] -- ^ collected Ast elements 
  , _irElements :: [ (MUID, Ir) ] -- ^ collected Ir elements (in inverse order, IModule last)
  , _irParents :: [ (MUID, MUID) ] -- ^ parent MUIDs (in inverse order, IModule last)
  , _irSpans :: [ (MUID, Span) ]  -- ^ Spans of the original AST node for Ir elements (in reverse order, IModule last)
  , _irCounter :: MUID -- ^ counter for generating MUIDs of IR elements
  , _naClafers :: Int -- ^ number of abstract clafers
  , _nrClafers :: Int -- ^ number of reference clafers
  , _ncClafers :: Int -- ^ number of concrete clafers 
  , _nConstrs :: Int -- ^ number of constraints
  , _ngoals :: Int -- ^ number of goals (objectives)
  , _sglCard :: Interval -- ^ global cardinality
  , _clafersWithKeywords :: [String] -- ^ list of error messages about clafers whose names are keywords
  , _multipleClafers :: [String] -- ^ list of messages about clafers whose cardinality is greater than 1
  }

makeLenses ''DesugarerState

-- | New MUIDs should be generated for each element being processed
genNewMUID :: State DesugarerState MUID
genNewMUID  = do
  muid <- use irCounter
  irCounter += 1
  return muid -- MUIDs are 0 numbered, so we need to return the previous one

addAstElement :: Ast -> Span -> State DesugarerState ()
addAstElement    ast'   span' = astElementsMap %= (Map.insertWith (++) span' [ast'])

-- | Collect new elements in maps
--   The MUID of the added element must be recorded in the pair becuase the order of adding the elements may, 
--   in general, not follow the order of the element processing.
addIrElement :: MUID -> Ir       -> MUID       -> Span  -> State DesugarerState ()
addIrElement    muid    irElement   parentsMUID    irSpan = do
  irElements %= ((muid, irElement) :)
  irParents  %= ((muid, parentsMUID) :)
  irSpans    %= ((muid, irSpan) :)

-- | Transform the AST into the intermediate representation (IR)
desugar :: Monad m => Maybe URL -> ClaferT m (IModule, [String], [String])
desugar               mURL       = do
  ast <- getAst
  let 
    (iModule, dState) = runState
      (desugarModule mURL ast) 
      (DesugarerState Map.empty [] [] [] 0 0 0 0 0 0 (1, 1) [] [])
  env <- getEnv
  putEnv env
    { astModuleTrace = _astElementsMap dState
    , irModuleMap = newIRModuleMap $ prepareList $ _irElements dState
    , irParentMap = newIRParentMap $ prepareList $ _irParents dState
    , muidSpanMap = newMUIDSpanMap $ prepareList $ _irSpans dState
    , nAbstractClafers = _naClafers dState
    , nReferenceClafers = _nrClafers dState
    , nConcreteClafers = _ncClafers dState
    , nConstraints = _nConstrs dState
    , nGoals = _ngoals dState
    , globalCard = _sglCard dState      
    }
  return (iModule, reverse $ _clafersWithKeywords dState, reverse $ _multipleClafers dState)
  where
    prepareList :: [(MUID, a)] -> [a]
    prepareList    xs           = map snd $ sortBy (comparing fst) $ filter (\(m, _) -> m >= 0) xs

desugarModule :: Maybe String -> Module -> State DesugarerState IModule
desugarModule mURL aModule@(Module span' declarations') = do
  muid <- genNewMUID   -- will always return 0 for the module
  let 
    parentsMUID = muid -- the module is its own parent
  iDeclarations <- concat <$> mapM (desugarDeclaration muid) (declarations' >>= desugarEnums)
  let
    iModule = IModule (fromMaybe "" mURL) iDeclarations
  addIrElement muid (IRIModule iModule) parentsMUID span'
  addAstElement (AstModule aModule) span'
  return iModule      

sugarModule :: IModule -> Module
sugarModule x = Module noSpan $ map sugarDeclaration $ _mDecls x -- (fragments x >>= mDecls)

-- | desugars enumeration to abstract and top-level singleton clafers
desugarEnums :: Declaration -> [Declaration]
desugarEnums (EnumDecl (Span p1 p2) id' enumids) = absEnum : (map mkEnum enumids)
    where
    p2' = case enumids of
        -- the abstract enum clafer should end before the first literal begins
        ((EnumIdIdent (Span (Pos y' x') _) _):_) -> Pos y' (x'-3)  -- cutting the ' = '
        [] -> p2   -- should never happen - cannot have enum without any literals. Return the original end pos.
    oneToOne pos' = (CardInterval noSpan $ 
                  NCard noSpan (PosInteger (pos', "1")) (ExIntegerNum noSpan $ PosInteger (pos', "1")))
    absEnum = let 
        s1 = Span p1 p2' 
      in 
        ElementDecl s1 $ 
           Subclafer s1 $ 
             Clafer s1 (Abstract s1) (GCardEmpty s1) id' (SuperEmpty s1) (CardEmpty s1) (InitEmpty s1) (ElementsList s1 [])
    mkEnum (EnumIdIdent s2 eId) = -- each concrete clafer must fit within the original span of the literal
      ElementDecl s2 $ 
        Subclafer s2 $ 
          Clafer s2 (AbstractEmpty s2) (GCardEmpty s2) eId ((SuperSome s2) (SuperColon s2) (ClaferId s2 $ Path s2 [ModIdIdent s2 id'])) (oneToOne (0, 0)) (InitEmpty s2) (ElementsList s2 [])
desugarEnums x = [x]


desugarDeclaration :: MUID -> Declaration            -> State DesugarerState [IElement]
desugarDeclaration parentsMUID (ElementDecl _ element') = desugarElement parentsMUID element'
desugarDeclaration _          _                        = error "Desugarer.desugarDeclaration: enum declarations should have already been converted to clafers. BUG."

sugarDeclaration :: IElement -> Declaration
sugarDeclaration (IEClafer clafer) = ElementDecl (_cinPos clafer) $ Subclafer (_cinPos clafer) $ sugarClafer clafer
sugarDeclaration (IEConstraint (IConstraint _ True constraint)) =
      ElementDecl (_inPos constraint) $ Subconstraint (_inPos constraint) $ sugarConstraint constraint
sugarDeclaration  (IEConstraint (IConstraint _ False softconstraint)) =
      ElementDecl (_inPos softconstraint) $ Subsoftconstraint (_inPos softconstraint) $ sugarSoftConstraint softconstraint
sugarDeclaration  (IEGoal (IGoal _ _ goal)) = ElementDecl (_inPos goal) $ Subgoal (_inPos goal) $ sugarGoal goal


desugarClafer :: MUID -> Clafer                                                                -> State DesugarerState [IElement]
desugarClafer parentsMUID aClafer@(Clafer span' abstract' gcrd' id' super' crd' init' elements') = do
  muid <- genNewMUID
  ielements <- desugarElements muid elements'
  isuper <- desugarSuper muid super'
  iinit <- desugarInit muid id' init'
  let
    iident' = transIdent id'
    isAbstract' = desugarAbstract abstract'
    iCard' = desugarCard crd'
    ieClafer@(IEClafer iClafer') = IEClafer $ IClafer muid span' isAbstract' (desugarGCard gcrd') iident'
          isuper iCard' (0, -1) (ielements ++ iinit)
  addIrElement muid (IRIClafer iClafer') parentsMUID span'
  addAstElement (AstClafer aClafer) span'
  sglCard %= statsCard (_glCard iClafer')
  if iClafer' ^. isAbstract
  then naClafers += 1
  else
    if iClafer' ^. super . isOverlapping 
      then nrClafers += 1
      else ncClafers += 1
  let
    (Span (Pos l c) _) = span'
    (_, m) = fromMaybe (0, 0) iCard'
  -- check whether a name is a keyword
  when (iident' `elem` keywordIdents) $
    clafersWithKeywords %= ( ("'" ++ iident' ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n") : )
  -- check whether the clafer is multiple
  when (isAbstract' && (m > 1 || m < 0)) $
    multipleClafers %= ( ("'" ++ iident' ++ "' on line " ++ show l ++ " column " ++ show c ++ "\n") : )
  return [ieClafer]
  where
    statsCard :: Interval -> Interval -> Interval
    statsCard (m1, n1) (m2, n2) = (max m1 m2, maxEx n1 n2)
      where
      maxEx m' n' = if m' == -1 || n' == -1 then -1 else max m' n'

sugarClafer :: IClafer -> Clafer
sugarClafer (IClafer _ s abstract gcard' uid' super' crd _ es) = 
    Clafer s (sugarAbstract abstract) (sugarGCard gcard') (mkIdent uid')
      (sugarSuper super') (sugarCard crd) (InitEmpty s) (sugarElements es)

desugarSuper :: MUID -> Super             -> State DesugarerState ISuper
desugarSuper parentsMUID aSuper@(SuperEmpty span') = do
  muid <- genNewMUID
  let 
    pexp' = PExp muid (Just $ TClafer []) span' $ mkLClaferId baseClafer baseClaferMUID True
  addIrElement muid (IRPExp pexp') parentsMUID span'
  addAstElement (AstSuper aSuper) span'
  return $ ISuper False [ pexp' ]
desugarSuper parentsMUID aSuper@(SuperSome span' superhow setexp) = do
  muid <- genNewMUID
  pexp' <- desugarSetExp parentsMUID setexp
  addIrElement muid (IRPExp pexp') parentsMUID span'
  addAstElement (AstSuper aSuper) span'
  return $ ISuper (desugarSuperHow superhow $ isPrim setexp) [pexp']
  where
    isPrim (ClaferId _ (Path _ [(ModIdIdent _ (PosIdent (_,ident')))])) = isPrimitive ident'
    isPrim _  = False 


desugarSuperHow :: SuperHow -> Bool       -> Bool
desugarSuperHow (SuperColon _) isPrimitive = if isPrimitive then True else False  -- need to have reference for primitive
desugarSuperHow _              _           = True                                 -- otherwise reference


desugarInit :: MUID    -> PosIdent -> Init                          -> State DesugarerState [IElement]
desugarInit    _          _           (InitEmpty _)                  = return []
desugarInit    parentsMUID id'         aInit@(InitSome span' inithow' exp') = do
  constraintMuid <- genNewMUID
  pExpMuid <- genNewMUID
  pexp' <- desugarExp parentsMUID exp'
  let
    cId :: PExp
    cId = mkPLClaferId (snd $ getIdent id') (pseudoMUID-5) False
    -- <id> = <exp'>
    assignIExp :: IExp
    assignIExp = (IFunExp "=" [cId, pexp'])
    -- some <id> => <assignIExp>
    implIExp :: IExp
    implIExp = (IFunExp "=>" [ pExpDefPid pseudoMUID span' $ IDeclPExp ISome [] cId, pExpDefPid pseudoMUID span' assignIExp ])
    iConstraint' = IConstraint constraintMuid (desugarInitHow inithow') (PExp pExpMuid Nothing span' implIExp)
  addIrElement constraintMuid (IRIConstraint iConstraint') parentsMUID span'
  addAstElement (AstInit aInit) span'
  nConstrs += 1
  return [ IEConstraint iConstraint' ]
  where 
    getIdent (PosIdent y) = y

desugarInitHow :: InitHow -> Bool
desugarInitHow (InitHow_1 _) = True
desugarInitHow (InitHow_2 _ )= False

desugarName :: Name -> State DesugarerState IExp
desugarName aName@(Path span' path) = do
  addAstElement (AstName aName) span'
  return $ IClaferId (concatMap ((++ modSep).desugarModId) (init path))
                (desugarModId $ last path) unresolvedMUID True

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


desugarConstraint :: MUID -> Constraint -> State DesugarerState PExp
desugarConstraint parentsMUID (Constraint _ exps') = do
  pexp' <- desugarExp parentsMUID $ (if length exps' > 1 then foldl1 (EAnd noSpan) else head) exps'
  return $ desugarPath pexp'

desugarSoftConstraint :: MUID -> SoftConstraint -> State DesugarerState PExp
desugarSoftConstraint parentsMUID (SoftConstraint _ exps') = do
  pexp' <- desugarExp parentsMUID $ (if length exps' > 1 then foldl1 (EAnd noSpan) else head) exps'
  return $ desugarPath pexp'

desugarGoal :: MUID -> Goal -> State DesugarerState IElement
desugarGoal parentsMUID aGoal@(Goal span' (minMaxExp:[])) = do
  muid <- genNewMUID
  let 
    (isMax, exp'') = case minMaxExp of
      (EGMax _ exp') -> (True, exp')
      (EGMin _ exp') -> (False, exp')
      _              -> error "Desugarer.desugarGoal: goal should only have min and max expressions"
  iexp' <- desugarExp parentsMUID exp''
  let
    iGoal' = IGoal muid isMax $ desugarPath iexp'
  addIrElement muid (IRIGoal iGoal') parentsMUID span'
  addAstElement (AstGoal aGoal) span'
  ngoals += 1
  return $ IEGoal iGoal'
desugarGoal _ _ = error "Desugarer: An objective must have exactly one of min or max expressions."

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

desugarElements :: MUID -> Elements           -> State DesugarerState [IElement]
desugarElements _          (ElementsEmpty _)   = return $ []
desugarElements parentsMUID (ElementsList _ es) = concat <$> mapM (desugarElement parentsMUID) es

sugarElements :: [IElement] -> Elements
sugarElements x = ElementsList noSpan $ map sugarElement x

desugarElement :: MUID -> Element -> State DesugarerState [IElement]
desugarElement parentsMUID x  = case x of
  Subclafer _ claf  -> do
      claf' <- desugarClafer parentsMUID claf
      arrConstr <- concat <$> mapM (desugarElement parentsMUID) (mkArrowConstraint claf)
      return $ claf' ++ arrConstr
  -- replace `X with X : X and desugar
  ClaferUse s name crd es  -> do
      iName' <- desugarName name
      let iClafer' = Clafer s (AbstractEmpty s) (GCardEmpty s) (mkIdent $ _sident iName') ((SuperSome s) (SuperColon s) (ClaferId s name)) crd (InitEmpty s) es
      desugarClafer parentsMUID iClafer' 
  Subconstraint span' constraint' -> do
    muid <- genNewMUID
    pexp' <- desugarConstraint parentsMUID constraint'
    let iConstraint' = IConstraint muid True $ pexp'
    addIrElement muid (IRIConstraint iConstraint') parentsMUID span'
    addAstElement (AstConstraint constraint') span'
    nConstrs += 1
    return [IEConstraint $ iConstraint']
  Subsoftconstraint span' softconstraint' -> do
    muid <- genNewMUID
    pexp' <- desugarSoftConstraint parentsMUID softconstraint'
    let iConstraint' = IConstraint muid False $ pexp'
    addIrElement muid (IRIConstraint iConstraint') parentsMUID span'
    addAstElement (AstSoftConstraint softconstraint') span'
    nConstrs += 1
    return [IEConstraint $ iConstraint']
  Subgoal _ goal -> do
    goal' <- desugarGoal parentsMUID goal
    return [goal']

sugarElement :: IElement -> Element
sugarElement x = case x of
  IEClafer claf  -> Subclafer noSpan $ sugarClafer claf
  IEConstraint (IConstraint _ True constraint) -> Subconstraint noSpan $ sugarConstraint constraint
  IEConstraint (IConstraint _ False softconstraint) -> Subsoftconstraint noSpan $ sugarSoftConstraint softconstraint
  IEGoal (IGoal _ _ goal) -> Subgoal noSpan $ sugarGoal goal

mkArrowConstraint :: Clafer -> [Element]
mkArrowConstraint (Clafer s _ _ ident' super' _ _ _) = 
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

desugarExp :: MUID -> Exp -> State DesugarerState PExp
desugarExp parentsMUID x    = do
  muid <- genNewMUID
  exp' <- desugarExp' muid x
  let 
    span' = (getSpan x)
    pexp' = PExp muid Nothing span' exp'
  addIrElement muid (IRPExp pexp') parentsMUID span'
  addAstElement (AstExp x) span'
  return pexp'

desugarExp' :: MUID -> Exp -> State DesugarerState IExp
desugarExp' parentsMUID x    = case x of
  DeclAllDisj _ decl exp' -> do
      decl' <- desugarDecl parentsMUID True decl
      iexp' <- dpe parentsMUID exp'
      return $ IDeclPExp IAll [decl'] iexp'
  DeclAll _ decl exp' -> do
      decl' <- desugarDecl parentsMUID False decl
      iexp' <- dpe parentsMUID exp'
      return $ IDeclPExp IAll [decl'] (iexp')
  DeclQuantDisj _ quant' decl exp' -> do
      decl' <- desugarDecl parentsMUID True decl
      iexp' <- dpe parentsMUID exp'
      return $ IDeclPExp (desugarQuant quant') [decl'] (iexp')
  DeclQuant _ quant' decl exp' -> do
      decl' <- desugarDecl parentsMUID False decl
      iexp' <- dpe parentsMUID exp'
      return $ IDeclPExp (desugarQuant quant') [decl'] (iexp')
  EIff _ exp0 exp'  -> dop parentsMUID iIff [exp0, exp']
  EImplies _ exp0 exp'  -> dop parentsMUID iImpl [exp0, exp']
  EImpliesElse _ exp0 exp1 exp'  -> dop parentsMUID iIfThenElse [exp0, exp1, exp']
  EOr _ exp0 exp'  -> dop parentsMUID iOr   [exp0, exp']
  EXor _ exp0 exp'  -> dop parentsMUID iXor [exp0, exp']
  EAnd _ exp0 exp'  -> dop parentsMUID iAnd [exp0, exp']
  ENeg _ exp'  -> dop parentsMUID iNot [exp']
  QuantExp _ quant' exp' -> do
      pexp' <- desugarExp parentsMUID exp'
      return $ IDeclPExp (desugarQuant quant') [] (pexp')
  ELt  _ exp0 exp'  -> dop parentsMUID iLt  [exp0, exp']
  EGt  _ exp0 exp'  -> dop parentsMUID iGt  [exp0, exp']
  EEq  _ exp0 exp'  -> dop parentsMUID iEq  [exp0, exp']
  ELte _ exp0 exp'  -> dop parentsMUID iLte [exp0, exp']
  EGte _ exp0 exp'  -> dop parentsMUID iGte [exp0, exp']
  ENeq _ exp0 exp'  -> dop parentsMUID iNeq [exp0, exp']
  EIn  _ exp0 exp'  -> dop parentsMUID iIn  [exp0, exp']
  ENin _ exp0 exp'  -> dop parentsMUID iNin [exp0, exp']
  EAdd _ exp0 exp'  -> dop parentsMUID iPlus [exp0, exp']
  ESub _ exp0 exp'  -> dop parentsMUID iSub [exp0, exp']
  EMul _ exp0 exp'  -> dop parentsMUID iMul [exp0, exp']
  EDiv _ exp0 exp'  -> dop parentsMUID iDiv [exp0, exp']
  ECSetExp _ exp'   -> dop parentsMUID iCSet [exp']
  ESumSetExp _ exp' -> dop parentsMUID iSumSet [exp']
  EMinExp _ exp'    -> dop parentsMUID iMin [exp']  
  EGMax _ exp' -> dop parentsMUID iGMax [exp']
  EGMin _ exp' -> dop parentsMUID iGMin [exp']  
  EInt _ n  -> return $ IInt $ mkInteger n
  EDouble _ (PosDouble n) -> return $ IDouble $ read $ snd n
  EStr _ (PosString str)  -> return $ IStr $ snd str
  ESetExp _ sexp -> desugarSetExp' parentsMUID sexp
  where
    dop :: MUID -> String -> [Exp] -> State DesugarerState IExp
    dop parentsMUID' op'       exps'  = desugarOp (desugarExp parentsMUID') op' exps'
    dpe :: MUID -> Exp -> State DesugarerState PExp
    dpe parentsMUID' exp' = liftM desugarPath $ desugarExp parentsMUID' exp'

desugarOp :: (a -> State DesugarerState PExp) -> String -> [a]  -> State DesugarerState IExp
desugarOp    desugaringFunction                  op'       exps' = 
    if (op' == iIfThenElse)
      then do
        headPExp <- head <$> pExpList
        tailPExps <- tail <$> pExpList
        return $ IFunExp op' $ (desugarPath headPExp) : (map reducePExp tailPExps)
      else do
        exps'' <- mapM desugaringFunction exps'
        return $ IFunExp op' $ map trans exps''
    where
      pExpList :: State DesugarerState [ PExp ]
      pExpList = mapM desugaringFunction exps'
      trans :: PExp -> PExp
      trans = if op' `elem` ([iNot, iIfThenElse] ++ logBinOps)
          then desugarPath else id


desugarSetExp :: MUID -> SetExp -> State DesugarerState PExp
desugarSetExp parentsMUID x = do
  pexpMUID' <- genNewMUID
  setExp' <- desugarSetExp' parentsMUID  x
  let 
    span' = (getSpan x)
    pexp' = pExpDefPid pexpMUID' span' setExp'
  addIrElement pexpMUID' (IRPExp pexp') parentsMUID span'
  addAstElement (AstSetExp x) span'
  return pexp'

desugarSetExp' :: MUID -> SetExp -> State DesugarerState IExp
desugarSetExp' parentsMUID x = case x of
  Union _ exp0 exp'        -> dop parentsMUID iUnion        [exp0, exp']
  UnionCom _ exp0 exp'     -> dop parentsMUID iUnion        [exp0, exp']
  Difference _ exp0 exp'   -> dop parentsMUID iDifference   [exp0, exp']
  Intersection _ exp0 exp' -> dop parentsMUID iIntersection [exp0, exp']
  Domain _ exp0 exp'       -> dop parentsMUID iDomain       [exp0, exp']
  Range _ exp0 exp'        -> dop parentsMUID iRange        [exp0, exp']
  Join _ exp0 exp'         -> dop parentsMUID iJoin         [exp0, exp']
  ClaferId _ name  -> desugarName name
  where
    dop :: MUID -> String -> [SetExp] -> State DesugarerState IExp
    dop parentsMUID' op'       exps'  = desugarOp (desugarSetExp parentsMUID') op' exps'

sugarExp :: PExp -> Exp
sugarExp x = sugarExp' $ _exp x

sugarExp' :: IExp -> Exp
sugarExp' x = case x of
  IDeclPExp quant' [] pexp -> QuantExp noSpan (sugarQuant quant') (sugarExp pexp)
  IDeclPExp IAll (decl@(IDecl _ True _ _):[]) pexp ->
    DeclAllDisj noSpan (sugarDecl decl) (sugarExp pexp)
  IDeclPExp IAll  (decl@(IDecl _ False _ _):[]) pexp ->
    DeclAll noSpan (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant' (decl@(IDecl _ True _ _):[]) pexp ->
    DeclQuantDisj noSpan (sugarQuant quant') (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant' (decl@(IDecl _ False _ _):[]) pexp ->
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
desugarPath (PExp muid' iType' pos' x) = reducePExp $ PExp muid' iType' pos' result
  where
  result
    | isSet x     = IDeclPExp ISome [] (pExpDefPid pseudoMUID pos' x)
    | isNegSome x = IDeclPExp INo   [] $ _bpexp $ _exp $ head $ _exps x
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
  then reduceNav $ _exp pexp0
  else x{_exps = (head exps'){_exp = reduceIExp iexp} :
                tail exps'}
reduceNav x = x

desugarDecl :: MUID    -> Bool -> Decl                          -> State DesugarerState IDecl
desugarDecl    parentsMUID isDisj' aDecl@(Decl span' locids exp') = do
  muid <- genNewMUID
  setExp' <- desugarSetExp parentsMUID exp'
  desugaredLocIds <- mapM (desugarLocId muid) locids
  let
    iDecl = IDecl muid isDisj' desugaredLocIds setExp'
  addIrElement muid (IRIDecl iDecl) parentsMUID span'
  addAstElement (AstDecl aDecl) span'
  return iDecl

sugarDecl :: IDecl -> Decl
sugarDecl (IDecl _ _ locids exp') =
    Decl noSpan (map (sugarLocId.fst) locids) (sugarSetExp exp')

desugarLocId :: MUID     -> LocId -> State DesugarerState (CName, MUID)
desugarLocId    parentsMUID aLocId@(LocIdIdent span' id') = do
  muid' <- genNewMUID
  let ident' = transIdent id'
  addIrElement muid' (IRILocId ident') parentsMUID span'
  addAstElement (AstLocId aLocId) span'
  return (ident', muid')


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
sugarQuant IAll = error "sugarQuant was called on IAll, this is not allowed!" --Should never happen
