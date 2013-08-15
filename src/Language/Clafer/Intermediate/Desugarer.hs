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

import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Data.Function (on)
import Prelude hiding (exp)
import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Front.Mapper
import Language.Clafer.Intermediate.Intclafer


desugarModule :: Module -> (IModule, Map.Map Span IClafer)
desugarModule (Module declarations) = desugarModule $ PosModule noSpan declarations
desugarModule (PosModule _ declarations) = 
  let iMod = IModule "" $ 
        declarations >>= desugarEnums >>= desugarDeclaration
          --[ImoduleFragment $ declarations >>= desugarEnums >>= desugarDeclaration]
      pMap = foldMapIR makeMap iMod
      clafers = bfsClafers $ toClafers $ mDecls iMod
  --in (iMod, pMap)
  in (flip mapIR iMod $ reDefAdd clafers pMap, pMap)
  where
    {-reDefAdd :: [IClafer] -> [IClafer] -> Map.Map Span IClafer -> Ir -> Ir
    reDefAdd clafers' (c:cs) parMap i@(IRClafer clafer) =
      if ((not $ istop $ cinPos clafer) && isRefDef parMap clafers' c clafer) then (if (isSpecified c clafer) then
        IRClafer $ clafer{super = ISuper Redefinition [PExp (Just $ TClafer []) "" noSpan (IClaferId "" (ident c) $ istop $ cinPos c)]}
          else error $ "Incorrect redefinition, Clafer:\n" ++ show clafer ++ "\nis an improper redefinition of Clafer:\n" ++ show c)
      else reDefAdd clafers' cs parMap i
      where
        isRefDef :: Map.Map Span IClafer -> [IClafer] -> IClafer -> IClafer -> Bool
        isRefDef pareMap clafs claf1 claf2 = 
          let p1 = flip Map.lookup pareMap $ cinPos claf1
              p2 = flip Map.lookup pareMap $ cinPos claf2
          in if (p1==Nothing && p2==Nothing) then (recursiveCheck clafs claf1 claf2)
            else if (p1==Nothing || p2==Nothing) then False
              else if (ident claf1 == ident claf2) then isRefDef pareMap clafs (fromJust p1) $ fromJust p2
                else False
          where
            recursiveCheck :: [IClafer] -> IClafer -> IClafer -> Bool
            recursiveCheck clafs' c1 c2 = 
              let match = flip find clafs' $ (== getSuper c2) . ident
              in if (ident c1 == getSuper c2) then True
                else if (match == Nothing) then False
                  else recursiveCheck clafs' c1 $ fromJust match-}
    reDefAdd :: [IClafer] -> Map.Map Span IClafer -> Ir -> Ir
    reDefAdd clafs parMap i@(IRClafer clafer) = 
      let ranks = filter (\(_,n) -> n/=0) $ flip map clafs $ \x -> if (istop $ cinPos clafer) then (x,0) else getReDefRank x 1 x clafer
      in if (ranks==[]) then i else 
        let c = fst $ minimumBy (compare `on` snd) ranks
        in if (isSpecified c clafer) then 
          IRClafer $ clafer{super = ISuper Redefinition [PExp (Just $ TClafer []) "" noSpan (IClaferId "" (ident c) $ istop $ cinPos c)]}
            else error $ "Incorrect redefinition, Clafer:\n" ++ show clafer ++ "\nis an improper redefinition of Clafer:\n" ++ show c
      where
        getReDefRank :: IClafer -> Integer -> IClafer -> IClafer -> (IClafer, Integer)
        getReDefRank oClaf acc claf1 claf2 =
          let par1 = flip Map.lookup parMap $ cinPos claf1
              par2 = flip Map.lookup parMap $ cinPos claf2
          in if (par1==Nothing && par2==Nothing && recursiveCheck claf1 claf2) 
            then (oClaf, acc) else if (par1==Nothing || par2==Nothing) 
              then (oClaf, 0) else if (ident claf1 == ident claf2) 
                then getReDefRank oClaf (acc+1) (fromJust par1) $ fromJust par2
                  else (oClaf, 0)
          where
          recursiveCheck :: IClafer -> IClafer -> Bool
          recursiveCheck c1 c2 = 
            let match = flip find clafs $ (== getSuper c2) . ident
            in if (ident c1 == getSuper c2) then True
              else if (match == Nothing) then False
                else recursiveCheck c1 $ fromJust match
            
        isSpecified :: IClafer -> IClafer -> Bool
        isSpecified claf1 claf2 = 
          (card claf2 `withinCard` card claf1) && (gcard claf2 `withinGRCard` gcard claf1)
            && (glCard claf2 `withinGLCard` glCard claf1)
          where
            withinCard (Just (x2,y2)) (Just (x1,y1)) = x1 `lt` x2 && y1 `gt` y2
            withinCard Nothing (Just (x1,y1)) = x1 `lt` 1 && y1 `gt` 1
            withinCard (Just (x2,y2)) Nothing = 1 `lt` x2 && 1 `gt` y2
            withinCard _ _ = True
            withinGRCard (Just (IGCard _ (x2,y2))) (Just (IGCard _ (x1,y1))) = x1 `lt` x2 && y1 `gt` y2
            withinGRCard Nothing (Just (IGCard _ (x1,y1))) = x1 `lt` 0 && y1 `gt` (-1)
            withinGRCard (Just (IGCard _ (x2,y2))) Nothing = 0 `lt` x2 && (-1) `gt` y2
            withinGRCard _ _ = True
            withinGLCard (x2,y2) (x1,y1) = x1 `lt` x2 && y1 `gt` y2
            lt x y = if (x == -1) then (y == -1) else if (y == -1) then True else x <= y
            gt x y = (not $ x `lt` y) || x==y
    reDefAdd _ _ i = i


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
desugarDeclaration (PosElementDecl _ element) = desugarElement element
desugarDeclaration _ = error "desugared"


sugarDeclaration :: IElement -> Declaration
sugarDeclaration (IEClafer clafer) = ElementDecl $ Subclafer $ sugarClafer clafer
sugarDeclaration (IEConstraint True constraint) =
      ElementDecl $ Subconstraint $ sugarConstraint constraint
sugarDeclaration  (IEConstraint False softconstraint) =
      ElementDecl $ Subsoftconstraint $ sugarSoftConstraint softconstraint
sugarDeclaration  (IEGoal _ goal) = ElementDecl $ Subgoal $ sugarGoal goal


desugarClafer :: Clafer -> [IElement]
desugarClafer (Clafer abstract gcrd id' super' crd init' es)  = 
    desugarClafer $ PosClafer noSpan abstract gcrd id' super' crd init' es
desugarClafer (PosClafer s abstract gcrd id' super' crd init' es)  = 
    (IEClafer $ IClafer s (desugarAbstract abstract) (desugarGCard gcrd) (transIdent id')
            "" (desugarSuper super') (desugarRefrence super') (desugarCard crd) (0, -1)
            (desugarElements es)) : (desugarInit id' init')

sugarClafer :: IClafer -> Clafer
sugarClafer (IClafer _ abstract gcard' _ uid' super' ref' crd _ es) = 
    Clafer (sugarAbstract abstract) (sugarGCard gcard') (mkIdent uid')
      (sugarSuper super' ref') (sugarCard crd) InitEmpty (sugarElements es)


desugarSuper :: Super -> ISuper
desugarSuper SuperEmpty = desugarSuper $ PosSuperEmpty noSpan
desugarSuper (SuperSome superhow setexp) = desugarSuper $ PosSuperSome noSpan superhow setexp
desugarSuper (PosSuperEmpty s) =
      ISuper TopLevel [PExp (Just $ TClafer []) "" s $ mkLClaferId baseClafer True]
desugarSuper (PosSuperSome _ superhow setexp) =
      ISuper TopLevel $ if (desugarSuperHowS superhow) then [desugarSetExp setexp] else []

desugarSuperHowS :: SuperHow -> Bool
desugarSuperHowS SuperColon = desugarSuperHowS $ PosSuperColon noSpan
desugarSuperHowS (PosSuperColon _) = True
desugarSuperHowS _ = False


desugarRefrence :: Super -> IReference
desugarRefrence (SuperSome superhow setexp) = desugarRefrence $ PosSuperSome noSpan superhow setexp
desugarRefrence (PosSuperSome _ superhow setexp) = case superhow of
  SuperColon -> emptyIReference 
  (PosSuperColon _) -> emptyIReference
  _ -> IReference (desugarSuperHowR superhow) [desugarSetExp setexp]
desugarRefrence _ = emptyIReference

desugarSuperHowR :: SuperHow -> Bool
desugarSuperHowR SuperArrow = desugarSuperHowR $ PosSuperArrow noSpan
desugarSuperHowR SuperMArrow = desugarSuperHowR $ PosSuperMArrow noSpan
desugarSuperHowR (PosSuperArrow _) = True
desugarSuperHowR (PosSuperMArrow _) = False
desugarSuperHowR _  = error "desugarSuperHowR function from desugarer did not work properly" --Should never happen


desugarInit :: PosIdent -> Init -> [IElement]
desugarInit id' InitEmpty = desugarInit id' $ PosInitEmpty noSpan
desugarInit id' (InitSome inithow exp') = desugarInit id' $ PosInitSome noSpan inithow exp'
desugarInit _ (PosInitEmpty _) = []
desugarInit id' (PosInitSome s inithow exp') = [IEConstraint (desugarInitHow inithow) 
  (pExpDefPid s (IFunExp "=" [mkPLClaferId (snd $ getIdent id') False, desugarExp exp']))]
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

sugarSuper :: ISuper -> IReference -> Super
sugarSuper (ISuper _ []) (IReference _ []) = SuperEmpty
sugarSuper (ISuper _ [pexp]) (IReference _ []) = SuperSome SuperColon (sugarSetExp pexp)
sugarSuper (ISuper _ []) (IReference i [pexp]) = SuperSome (if i then SuperArrow else SuperMArrow) (sugarSetExp pexp)
sugarSuper _ _ = error "Function sugarSuper from Desugarer expects an ISuper and IReference with a lists of length one or less, but it was given one with a list larger than one" -- Should never happen


sugarInitHow :: Bool -> InitHow
sugarInitHow True  = InitHow_1
sugarInitHow False = InitHow_2


desugarConstraint :: Constraint -> PExp
desugarConstraint (Constraint exps') = desugarConstraint $ PosConstraint noSpan exps'
desugarConstraint (PosConstraint _ exps') = desugarPath $ desugarExp $
    (if length exps' > 1 then foldl1 (PosEAnd noSpan) else head) exps'

desugarSoftConstraint :: SoftConstraint -> PExp
desugarSoftConstraint (SoftConstraint exps') = desugarSoftConstraint $ PosSoftConstraint noSpan exps'
desugarSoftConstraint (PosSoftConstraint _ exps') = desugarPath $ desugarExp $
    (if length exps' > 1 then foldl1 (PosEAnd noSpan) else head) exps'

desugarGoal :: Goal -> PExp
desugarGoal (Goal exps') = desugarGoal $ PosGoal noSpan exps'
desugarGoal (PosGoal _ exps') = desugarPath $ desugarExp $
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


desugarElements :: Elements -> [IElement]
desugarElements (ElementsEmpty) = desugarElements $ PosElementsEmpty noSpan
desugarElements (ElementsList es)  = desugarElements $ PosElementsList noSpan es
desugarElements (PosElementsEmpty _) = []
desugarElements (PosElementsList _ es)  = es >>= desugarElement


sugarElements :: [IElement] -> Elements
sugarElements x = ElementsList $ map sugarElement x


desugarElement :: Element -> [IElement]
desugarElement x = case x of
  Subclafer claf  -> desugarElement $ PosSubclafer noSpan claf
  ClaferUse name crd es  ->
      desugarElement $ PosClaferUse noSpan name crd es
  Subconstraint constraint  -> desugarElement $ PosSubconstraint noSpan constraint
  Subsoftconstraint softconstraint ->
      desugarElement $ PosSubsoftconstraint noSpan softconstraint
  Subgoal goal -> desugarElement $ PosSubgoal noSpan goal
  PosSubclafer _ claf  ->
      (desugarClafer claf) ++
      (mkArrowConstraint claf >>= desugarElement)
  PosClaferUse s name crd es  -> desugarClafer $ PosClafer s
      AbstractEmpty GCardEmpty (mkIdent $ sident $ desugarName name)
      (SuperSome SuperColon (PosClaferId noSpan name)) crd InitEmpty es
  PosSubconstraint _ constraint  ->
      [IEConstraint True $ desugarConstraint constraint]
  PosSubsoftconstraint _ softconstraint ->
      [IEConstraint False $ desugarSoftConstraint softconstraint]
  PosSubgoal _ goal -> [IEGoal True $ desugarGoal goal]

sugarElement :: IElement -> Element
sugarElement x = case x of
  IEClafer claf  -> Subclafer $ sugarClafer claf
  IEConstraint True constraint -> Subconstraint $ sugarConstraint constraint
  IEConstraint False softconstraint -> Subsoftconstraint $ sugarSoftConstraint softconstraint
  IEGoal _ goal -> Subgoal $ sugarGoal goal

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

desugarExp :: Exp -> PExp
desugarExp x = pExpDefPid (range x) $ desugarExp' x

desugarExp' :: Exp -> IExp
desugarExp' x = case x of
  DeclAllDisj decl exp' -> desugarExp' $ PosDeclAllDisj noSpan decl exp'
  DeclAll decl exp' -> desugarExp' $ PosDeclAll noSpan decl exp'
  DeclQuantDisj quant' decl exp' ->
      desugarExp' $ PosDeclQuantDisj noSpan quant' decl exp'
  DeclQuant quant' decl exp' -> desugarExp' $ PosDeclQuant noSpan quant' decl exp'
  EIff exp0 exp'  -> desugarExp' $ PosEIff noSpan exp0 exp'
  EImplies exp0 exp'  -> desugarExp' $ PosEImplies noSpan exp0 exp'
  EImpliesElse exp0 exp1 exp'  -> desugarExp' $ PosEImpliesElse noSpan exp0 exp1 exp'
  EOr exp0 exp'  -> desugarExp' $ PosEOr noSpan exp0 exp'
  EXor exp0 exp'  -> desugarExp' $ PosEXor noSpan exp0 exp'
  EAnd exp0 exp'  -> desugarExp' $ PosEAnd noSpan exp0 exp'
  ENeg exp' -> desugarExp' $ PosENeg noSpan exp'
  QuantExp quant' exp'  -> desugarExp' $ PosQuantExp noSpan quant' exp'
  ELt  exp0 exp'  -> desugarExp' $ PosELt noSpan exp0 exp'
  EGt  exp0 exp'  -> desugarExp' $ PosEGt noSpan exp0 exp'
  EEq  exp0 exp'  -> desugarExp' $ PosEEq noSpan exp0 exp'
  ELte exp0 exp'  -> desugarExp' $ PosELte noSpan exp0 exp'
  EGte exp0 exp'  -> desugarExp' $ PosEGte noSpan exp0 exp'
  ENeq exp0 exp'  -> desugarExp' $ PosENeq noSpan exp0 exp'
  EIn  exp0 exp'  -> desugarExp' $ PosEIn noSpan exp0 exp'
  ENin exp0 exp'  -> desugarExp' $ PosENin noSpan exp0 exp'
  EAdd exp0 exp'  -> desugarExp' $ PosEAdd noSpan exp0 exp'
  ESub exp0 exp'  -> desugarExp' $ PosESub noSpan exp0 exp'
  EMul exp0 exp'  -> desugarExp' $ PosEMul noSpan exp0 exp'
  EDiv exp0 exp'  -> desugarExp' $ PosEDiv noSpan exp0 exp'
  ECSetExp exp'   -> desugarExp' $ PosECSetExp noSpan exp'
  ESumSetExp sexp -> desugarExp' $ PosESumSetExp noSpan sexp  
  EMinExp exp'    -> desugarExp' $ PosEMinExp noSpan exp'
  EGMax exp' -> desugarExp' $ PosEGMax noSpan exp'
  EGMin exp' -> desugarExp' $ PosEGMin noSpan exp'
  EInt n -> desugarExp' $ PosEInt noSpan n
  EDouble n -> desugarExp' $ PosEDouble noSpan n
  EStr str  -> desugarExp' $ PosEStr noSpan str
  ESetExp sexp -> desugarExp' $ PosESetExp noSpan sexp    
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
      IDeclPExp (desugarQuant quant') [] (desugarExp exp')
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
  dop = desugarOp desugarExp
  dpe = desugarPath.desugarExp

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
desugarPath (PExp iType' pid' pos' x) = reducePExp $ PExp iType' pid' pos' result
  where
  result
    | isset x     = IDeclPExp ISome [] (pExpDefPid pos' x)
    | isNegSome x = IDeclPExp INo   [] $ bpexp $ Language.Clafer.Intermediate.Intclafer.exp $ head $ exps x
    | otherwise   =  x
  isNegSome (IFunExp op' [PExp _ _ _ (IDeclPExp ISome [] _)]) = op' == iNot
  isNegSome _ = False


isset :: IExp -> Bool
isset (IClaferId _ _ _)  = True
isset (IFunExp op' _) = op' `elem` setBinOps
isset _ = False


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

emptyIReference :: IReference
emptyIReference = IReference False []

makeMap :: Ir -> Map.Map Span IClafer
makeMap (IRClafer c) = Map.fromList $ zip (concat $ map getPos $ elements c) (repeat c)
makeMap _ = Map.empty

getPos :: IElement -> [Span]
getPos (IEClafer c) = [cinPos c]
getPos e = iFoldMap getPExpPos $ IRIElement e
  where
    getPExpPos (IRPExp p) = [inPos p]
    getPExpPos _ = []

{-addrSpan :: Map.Map Span IClafer -> [IClafer] -> [IClafer] -> [IClafer] -> Ir -> Ir -- The three IClafer lists are as follows 1. The list we are mapping through
addrSpan _ [] _ [] i = i                                                            --                                        2. A list of all clafers
addrSpan _ [] _ acc _ =                                                             --                                        3. An accumlator gathering all posibilities
  (IRClafer (maximumBy (compare `on` (depth . fst . fromJust . rInfo . super)) acc)) 
  where
    depth (Span (Pos _ c) _) = c
    depth (PosSpan _ (Pos _ c) _) = c
    depth (Span (PosPos _ _ c) _) = c
    depth (PosSpan _ (PosPos _ _ c) _) = c
addrSpan parMap (c:cs) clafers acc irclaf@(IRClafer claf)  = flip (addrSpan parMap cs clafers) irclaf $
  if (((getSuper claf) == ident c || ident claf == ident c) && (cinPos claf /= cinPos c) && commonNesting claf c parMap clafers) 
    then (:acc) $ claf{super = (super claf){rInfo = Just $ (cinPos c,"")}} 
      else acc 
addrSpan _ _ _ _ i =  i 

addrUid :: Map.Map Span IClafer -> [IClafer] -> Ir -> Ir
addrUid parMap (c:cs) irclaf@(IRClafer claf) = 
  if (((rInfo $ super claf) /= Nothing) && ((fst $ fromJust $ rInfo $ super claf) == (cinPos c)))
    then IRClafer $ claf{super = (super claf){rInfo = Just $ (fst $ fromJust $ rInfo $ super claf ,uid c)}} 
      else addrUid parMap cs irclaf 
addrUid _ _ i = i -}

