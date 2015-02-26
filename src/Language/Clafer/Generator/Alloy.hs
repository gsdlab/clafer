{-# LANGUAGE RankNTypes, FlexibleContexts #-}
{-
 Copyright (C) 2012-2013 Kacper Bak, Jimmy Liang, Rafael Olaechea <http://gsd.uwaterloo.ca>

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
-- | Generates Alloy4.1 or 4.2 code for a Clafer model
module Language.Clafer.Generator.Alloy (genModule) where

import Control.Applicative ((<$>))
import Control.Lens hiding (elements, mapping)
import Control.Monad.State
import Data.List
import Data.Maybe

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.AbsClafer
import Language.Clafer.Generator.Concat
import Language.Clafer.Intermediate.Intclafer hiding (exp)


data GenEnv = GenEnv
  { claferargs :: ClaferArgs
  , uidIClaferMap :: UIDIClaferMap
  , forScopes :: String
  }  deriving (Show)


-- | Alloy code generation
-- 07th Mayo 2012 Rafael Olaechea
--      Added Logic to print a goal block in case there is at least one goal.
genModule :: ClaferArgs -> (IModule, GEnv) -> [(UID, Integer)] -> (Result, [(Span, IrTrace)])
genModule    claferargs'   (imodule, genv)    scopes            = (flatten output, filter ((/= NoTrace) . snd) $ mapLineCol output)
  where

  genScopes :: [(UID, Integer)] -> String
  genScopes    []                = ""
  genScopes    scopes'           = " but " ++ intercalate ", " (map (\ (uid', scope)  -> show scope ++ " " ++ uid') scopes')

  forScopes' = "for 1" ++ genScopes scopes
  genEnv = GenEnv claferargs' (uidClaferMap genv) forScopes'
  output = header genEnv +++ (cconcat $ map (genDeclaration genEnv) (_mDecls imodule)) +++
       if ((not $ skip_goals claferargs') && length goals_list > 0) then
                CString "objectives o_global {\n" +++   (cintercalate (CString ",\n") goals_list) +++   CString "\n}"
       else
                CString ""
       where
                goals_list = filterNull (map (genDeclarationGoalsOnly genEnv) (_mDecls imodule))

header :: GenEnv -> Concat
header    genEnv  = CString $ unlines
    [ "open util/integer"
    , "pred show {}"
    , if (validate $ claferargs genEnv) ||  (noalloyruncommand $ claferargs genEnv)
      then ""
      else "run show " ++ forScopes genEnv
    , ""]


-- 07th Mayo 2012 Rafael Olaechea
-- Modified so that we can collect all goals into a single block as required per the way goals are handled in modified alloy.
genDeclarationGoalsOnly :: GenEnv -> IElement -> Concat
genDeclarationGoalsOnly    genEnv    x         = case x of
  IEClafer _  -> CString ""
  IEConstraint _ _  -> CString ""
  IEGoal _ (PExp _ _ _ innerexp) -> case innerexp of
        IFunExp op'  exps' ->  if  op' == iGMax || op' == iGMin then
                        mkMetric op' $ genPExp genEnv [] (head exps')
                else
                        error "unary operator  distinct from (min/max) at the topmost level of a goal element"
        _ ->  error "no unary operator (min/max) at the topmost level of a goal element."

-- 07th Mayo 2012 Rafael Olaechea
-- Removed goal from this function as they will now  all be collected into a single block.
genDeclaration :: GenEnv -> IElement -> Concat
genDeclaration genEnv x = case x of
  IEClafer clafer'  -> (genClafer genEnv [] clafer') +++ (mkFact $ cconcat $ genSetUniquenessConstraint clafer')
  IEConstraint True pexp  -> mkFact $ genPExp genEnv [] pexp
  IEConstraint False pexp  -> mkAssert genEnv (genAssertName pexp) $ genPExp genEnv [] pexp
  IEGoal _ (PExp _ _ _ innerexp) -> case innerexp of
        IFunExp op'  _ ->  if  op' == iGMax || op' == iGMin then
                       CString ""
                else
                        error "unary operator  distinct from (min/max) at the topmost level of a goal element"
        _ ->  error "no unary operator (min/max) at the topmost level of a goal element."

mkFact :: Concat -> Concat
mkFact x@(CString "") = x
mkFact xs = cconcat [CString "fact ", mkSet xs, CString "\n"]

genAssertName :: PExp -> Concat
genAssertName    PExp{_inPos=(Span _ (Pos line _))} = CString $ "assertOnLine_" ++ show line

mkAssert :: GenEnv -> Concat -> Concat        -> Concat
mkAssert    _         _         x@(CString "") = x
mkAssert    genEnv    name      xs = cconcat
  [ CString "assert ", name, CString " "
  , mkSet xs
  , CString "\n"
  , CString "check ", name, CString " "
  , CString $ forScopes genEnv
  , CString "\n\n"
  ]

mkMetric :: String -> Concat -> Concat
mkMetric goalopname xs = cconcat [ if goalopname == iGMax then CString "maximize" else  CString "minimize", CString " ", xs, CString " "]

mkSet :: Concat -> Concat
mkSet xs = cconcat [CString "{ ", xs, CString " }"]

showSet :: Concat -> [Concat] -> Concat
showSet delim xs = showSet' delim $ filterNull xs
  where
  showSet' _ []     = CString "{}"
  showSet' delim' xs' = mkSet $ cintercalate delim' xs'

optShowSet :: [Concat] -> Concat
optShowSet [] = CString ""
optShowSet xs = CString "\n" +++ showSet (CString "\n  ") xs

-- optimization: top level cardinalities
-- optimization: if only boolean parents, then set card is known
genClafer :: GenEnv -> [String] -> IClafer -> Concat
genClafer genEnv resPath clafer'
  = (cunlines $ filterNull
      [   cardFact
      +++ claferDecl clafer' (
          (showSet (CString "\n, ") $ genRelations genEnv clafer')
          +++ (optShowSet $ filterNull $ genConstraints genEnv resPath clafer')
        )
      ]
    )
  +++ CString "\n"
  +++ children'
  where
  children' = cconcat $ filterNull $ map
             (genClafer genEnv ((_uid clafer') : resPath)) $
             getSubclafers $ _elements clafer'
  cardFact
    | null resPath && (null $ flatten $ genOptCard clafer') =
        case genCard (_uid clafer') $ _card clafer' of
          CString "set" -> CString ""
          c -> mkFact c
    | otherwise = CString ""

claferDecl :: IClafer -> Concat -> Concat
claferDecl    c     rest    = cconcat
  [ genOptCard c
  , CString $ genAbstract $ _isAbstract c
  , CString "sig "
  , Concat NoTrace [CString $ _uid c, genExtends $ _super c, CString "\n", rest]
  ]
  where
  genAbstract isAbs = if isAbs then "abstract " else ""
  genExtends Nothing = CString ""
  genExtends (Just (PExp _ _ _ (IClaferId _ i _ _))) = CString " " +++ Concat NoTrace [CString $ "extends " ++ i]
  -- todo: handle multiple inheritance
  genExtends _ = CString ""

genOptCard :: IClafer -> Concat
genOptCard    c
  | glCard' `elem` ["lone", "one", "some"] = cardConcat (_uid c) False [CString glCard'] +++ (CString " ")
  | otherwise                              = CString ""
  where
  glCard' = genIntervalCrude $ _glCard c


-- -----------------------------------------------------------------------------
-- overlapping inheritance is a new clafer with val (unlike only relation)
-- relations: overlapping inheritance (val rel), children
-- adds parent relation
-- 29/March/2012  Rafael Olaechea: ref is now prepended with clafer name to be able to refer to it from partial instances.
genRelations :: GenEnv -> IClafer -> [Concat]
genRelations genEnv c = maybeToList r ++ (map mkRel $ getSubclafers $ _elements c)
  where
  r = if isJust $ _reference c
                then
                        Just $ Concat NoTrace [CString $ genRel (if (noalloyruncommand $ claferargs genEnv) then  (_uid c ++ "_ref") else "ref")
                         c {_card = Just (1, 1)} $
                         flatten $ refType genEnv c]
                else
                        Nothing
  mkRel c' = Concat NoTrace [CString $ genRel (genRelName $ _uid c') c' $ _uid c']

genRelName :: String -> String
genRelName name = "r_" ++ name

genRel :: String -> IClafer -> String -> String
genRel name c rType = genAlloyRel name (genCardCrude $ _card c) rType'
  where
  rType' = if isPrimitive rType then "Int" else rType

genAlloyRel :: String -> String -> String -> String
genAlloyRel name card' rType = concat [name, " : ", card', " ", rType]

refType :: GenEnv -> IClafer -> Concat
refType    genEnv c = fromMaybe (CString "") $ fmap ((genType genEnv).getTarget) $ _ref <$> _reference c


getTarget :: PExp -> PExp
getTarget    x     = case x of
  PExp _ _ _ (IFunExp op' (_:pexp:_))  -> if op' == iJoin then pexp else x
  _ -> x

genType :: GenEnv -> PExp                              -> Concat
genType    genEnv    x@(PExp _ _ _ y@(IClaferId _ _ _ _)) = genPExp genEnv []
  x{_exp = y{_isTop = True}}
genType m x = genPExp m [] x


-- -----------------------------------------------------------------------------
-- constraints
-- parent + group constraints + reference + user constraints
-- a = NUMBER do all x : a | x = NUMBER (otherwise alloy sums a set)
genConstraints :: GenEnv -> [String]      -> IClafer -> [Concat]
genConstraints    genEnv    resPath c
  = (genParentConst resPath c)
  : (genGroupConst genEnv c)
{- genPathConst produces incorrect code for top-level clafers

abstract System
    abstract Connection
    connections -> Connection *

sig c0_connections
{ ref : one c0_Connection }
{ one @r_c0_connections.this
  ref = (@r_c0_System.@r_c0_Connection) }

r_c0_System does not exist because System is top-level. The constraint is useless anyway, since all instances
of Connection are nested under all Systems anyway.
  disabled code:
  : genPathConst genEnv  (if (noalloyruncommand $ claferargs genEnv) then  (_uid c ++ "_ref") else "ref") resPath c
-}
  : constraints
  where
  constraints = concat $ map genConst $ _elements c
  genConst x = case x of
    IEConstraint True pexp  -> [ genPExp genEnv ((_uid c) : resPath) pexp ]
    IEConstraint False pexp  -> [ CString "// Assertion " +++ (genAssertName pexp) +++ CString " ignored since nested assertions are not supported in Alloy.\n"]
    IEClafer c' ->
        (if genCardCrude (_card c') `elem` ["one", "lone", "some"]
         then CString ""
         else mkCard ({- do not use the genRelName as the constraint name -} _uid c') False (genRelName $ _uid c') $ fromJust (_card c')
        )
        : (genParentSubrelationConstriant (uidIClaferMap genEnv) c')
        : (genSetUniquenessConstraint c')
    IEGoal _ _ -> error "getConst function from Alloy generator was given a Goal, this function should only be given a Constrain or Clafer" -- This should never happen


genSetUniquenessConstraint :: IClafer -> [Concat]
genSetUniquenessConstraint c =
    (case _reference c of
      Just (IReference True _) ->
        (case _card c of
            Just (lb,  ub) -> if (lb > 1 || ub > 1 || ub == -1)
              then [ CString $ (
                        (case isTopLevel c of
                          False -> "all disj x, y : this.@" ++ (genRelName $ _uid c)
                          True  -> " all disj x, y : "       ++ (_uid c)))
                      ++ " | (x.@ref) != (y.@ref) "
                   ]
              else []
            _ -> [])
      _ -> []
    )

genParentSubrelationConstriant :: UIDIClaferMap -> IClafer   -> Concat
genParentSubrelationConstriant    uidIClaferMap'        headClafer =
  case match of
    Nothing -> CString ""
    Just NestedInheritanceMatch {
           _superClafer = superClafer
         }  -> if (isProperNesting uidIClaferMap' match) && (not $ isTopLevel superClafer)
               then CString $ concat
                [ genRelName $ _uid headClafer
                , " in "
                , genRelName $ _uid superClafer
                ]
               else CString ""
  where
    match = matchNestedInheritance uidIClaferMap' headClafer

-- optimization: if only boolean features then the parent is unique
genParentConst :: [String] -> IClafer -> Concat
genParentConst [] _     = CString ""
genParentConst _ c =  genOptParentConst c

genOptParentConst :: IClafer -> Concat
genOptParentConst    c
  | glCard' == "one"  = CString ""
  | glCard' == "lone" = Concat NoTrace [CString $ "one " ++ rel]
  | otherwise         = Concat NoTrace [CString $ "one @" ++ rel ++ ".this"]
  -- eliminating problems with cyclic containment;
  -- should be added to cases when cyclic containment occurs
  --                    , " && no iden & @", rel, " && no ~@", rel, " & @", rel]
  where
  rel = genRelName $ _uid c
  glCard' = genIntervalCrude $ _glCard c

genGroupConst :: GenEnv -> IClafer -> Concat
genGroupConst    genEnv    clafer'
  | _isAbstract clafer' || null children' || flatten card' == "" = CString ""
  | otherwise = cconcat [CString "let children = ", brArg id $ CString children', CString" | ", card']
  where
  superHierarchy :: [IClafer]
  superHierarchy = findHierarchy getSuper (uidIClaferMap genEnv) clafer'
  children' = intercalate " + " $ map (genRelName._uid) $
             getSubclafers $ concatMap _elements superHierarchy
  card'     = mkCard (_uid clafer') True "children" $ _interval $ fromJust $ _gcard $ clafer'

mkCard :: String -> Bool -> String -> (Integer, Integer) -> Concat
mkCard constraintName group' element' crd
  | crd' == "set" || crd' == ""        = CString ""
  | crd' `elem` ["one", "lone", "some"] = CString $ crd' ++ " " ++ element'
  | otherwise                            = interval'
  where
  interval' = genInterval constraintName group' element' crd
  crd'  = flatten $ interval'

-- generates expression for references that point to expressions (not single clafers)
genPathConst :: GenEnv -> String -> [String] -> IClafer -> Concat
genPathConst    genEnv    name      resPath     c
  | isRefPath (c ^. reference) = cconcat [CString name, CString " = ",
                                fromMaybe (error "genPathConst: impossible.") $
                                fmap ((brArg id).(genPExp genEnv resPath)) $
                                _ref <$> _reference c]
  | otherwise        = CString ""

isRefPath :: Maybe IReference -> Bool
isRefPath    Nothing = False
isRefPath    (Just IReference{_ref=s}) = not $ isSimplePath s

isSimplePath :: PExp -> Bool
isSimplePath    (PExp _ _ _ (IClaferId _ _ _ _)) = True
isSimplePath    (PExp _ _ _ (IFunExp op' _)) = op'  == iUnion
isSimplePath    _ = False

-- -----------------------------------------------------------------------------
-- Not used?
-- genGCard element gcard = genInterval element  $ interval $ fromJust gcard


genCard :: String -> Maybe Interval -> Concat
genCard    element'   crd            = genInterval element' False element' $ fromJust crd

genCardCrude :: Maybe Interval -> String
genCardCrude crd = genIntervalCrude $ fromJust crd

genIntervalCrude :: Interval -> String
genIntervalCrude x = case x of
  (1, 1)  -> "one"
  (0, 1)  -> "lone"
  (1, -1) -> "some"
  _       -> "set"


genInterval :: String      -> Bool -> String -> Interval -> Concat
genInterval    constraintName group'   element'   x         = case x of
  (1, 1) -> cardConcat constraintName group' [CString "one"]
  (0, 1) -> cardConcat constraintName group' [CString "lone"]
  (1, -1)   -> cardConcat constraintName group' [CString "some"]
  (0, -1)   -> CString "set" -- "set"
  (n, exinteger)  ->
    case (s1, s2) of
      (Just c1, Just c2) -> cconcat [c1, CString " and ", c2]
      (Just c1, Nothing) -> c1
      (Nothing, Just c2) -> c2
      (Nothing, Nothing) -> undefined
    where
    s1 = if n == 0
         then Nothing
         else Just $ cardLowerConcat constraintName group' [CString $ concat [show n, " <= #",  element']]
    s2 =
        do
            result <- genExInteger element' x exinteger
            return $ cardUpperConcat constraintName group' [CString result]


cardConcat :: String        -> Bool -> [Concat] -> Concat
cardConcat    constraintName = Concat . ExactCard constraintName


cardLowerConcat :: String        -> Bool -> [Concat] -> Concat
cardLowerConcat    constraintName = Concat . LowerCard constraintName


cardUpperConcat :: String        -> Bool -> [Concat] -> Concat
cardUpperConcat    constraintName = Concat . UpperCard constraintName


genExInteger :: String -> Interval -> Integer -> Maybe Result
genExInteger    element'  (y,z) x  =
  if (y==0 && z==0) then Just $ concat ["#", element', " = ", "0"] else
    if x == -1 then Nothing else Just $ concat ["#", element', " <= ", show x]


-- -----------------------------------------------------------------------------
-- Generate code for logical expressions

genPExp :: GenEnv -> [String] -> PExp -> Concat
genPExp    genEnv    resPath     x     = genPExp' genEnv resPath $ adjustPExp resPath x

genPExp' :: GenEnv -> [String] -> PExp                      -> Concat
genPExp'    genEnv    resPath     (PExp iType' pid' pos exp') = case exp' of
  IDeclPExp q d pexp -> Concat (IrPExp pid') $
    [ CString $ genQuant q, CString " "
    , cintercalate (CString ", ") $ map ((genDecl genEnv resPath)) d
    , CString $ optBar d, genPExp' genEnv resPath pexp]
    where
    optBar [] = ""
    optBar _  = " | "
  IClaferId _ "ref" _ _ -> CString "@ref"
  IClaferId _ sid istop _ -> CString $
      if head sid == '~' then sid else
      if isNothing iType' then sid' else case fromJust $ iType' of
    TInteger -> vsident
    TReal -> vsident
    TString -> vsident
    _ -> sid'
    where
    sid' = (if istop then "" else '@' : genRelName "") ++ sid
    -- 29/March/2012  Rafael Olaechea: ref is now prepended with clafer name to be able to refer to it from partial instances.
    -- 30/March/2012 Rafael Olaechea added referredClaferUniqeuid to fix problems when having this.x > number  (e.g test/positive/i10.cfr )
    vsident = if (noalloyruncommand $ claferargs genEnv) then sid' ++  ".@"  ++ referredClaferUniqeuid ++ "_ref"  else  sid'  ++ ".@ref"
        where referredClaferUniqeuid = if sid == "this" then (head resPath) else sid
  IFunExp _ _ -> case exp'' of
    IFunExp _ _ -> genIFunExp pid' genEnv resPath exp''
    _ -> genPExp' genEnv resPath $ PExp iType' pid' pos exp''
    where
    exp'' = transformExp exp'
  IInt n -> CString $ show n
  IDouble _ -> error "no real numbers allowed"
  IStr _ -> error "no strings allowed"



-- 3-May-2012 Rafael Olaechea.
-- Removed transfromation from x = -2 to x = (0-2) as this creates problem with  partial instances.
-- See http://gsd.uwaterloo.ca:8888/question/461/new-translation-of-negative-number-x-into-0-x-is.
transformExp :: IExp -> IExp
transformExp (IFunExp op' (e1:_))
  | op' == iMin = IFunExp iMul [PExp (_iType e1) "" noSpan $ IInt (-1), e1]
transformExp    x@(IFunExp op' exps'@(e1:e2:_))
  | op' == iXor = IFunExp iNot [PExp (Just TBoolean) "" noSpan (IFunExp iIff exps')]
  | op' == iJoin && isClaferName' e1 && isClaferName' e2 &&
    getClaferName e1 == thisIdent && head (getClaferName e2) == '~' =
        IFunExp op' [e1{_iType = Just $ TClafer []}, e2]
  | otherwise  = x
transformExp x = x

genIFunExp :: String -> GenEnv -> [String] -> IExp             -> Concat
genIFunExp    pid'      genEnv    resPath     (IFunExp op' exps') =
  if (op' == iSumSet)
    then genIFunExp pid' genEnv resPath (IFunExp iSumSet' [(removeright (head exps')), (getRight $ head exps')])
    else if (op' == iSumSet')
      then Concat (IrPExp pid') $ intl exps'' (map CString $ genOp (Alloy42 `elem` (mode $ claferargs genEnv)) iSumSet)
      else Concat (IrPExp pid') $ intl exps'' (map CString $ genOp (Alloy42 `elem` (mode $ claferargs genEnv)) op')
  where
  intl
    | op' == iSumSet' = flip $ interleave
    | op' `elem` arithBinOps && length exps' == 2 = interleave
    | otherwise = \xs ys -> reverse $ interleave (reverse xs) (reverse ys)
  exps'' = map (optBrArg genEnv resPath) exps'
genIFunExp _ _ _ _ = error "Function genIFunExp from Alloy Generator expected a IFunExp as an argument but was given something else" --This should never happen


optBrArg :: GenEnv -> [String] -> PExp -> Concat
optBrArg    genEnv    resPath     x     = brFun (genPExp' genEnv resPath) x
  where
  brFun = case x of
    PExp _ _ _ (IClaferId _ _ _ _) -> ($)
    PExp _ _ _ (IInt _) -> ($)
    _  -> brArg

interleave :: [Concat] -> [Concat] -> [Concat]
interleave [] [] = []
interleave (x:xs) [] = x:xs
interleave [] (x:xs) = x:xs
interleave (x:xs) ys = x : interleave ys xs

brArg :: (a -> Concat) -> a -> Concat
brArg f arg = cconcat [CString "(", f arg, CString ")"]

--     isAlloy42
genOp :: Bool -> String -> [String]
genOp    True       op'
  | op' == iPlus = [".plus[", "]"]
  | op' == iSub  = [".minus[", "]"]
  | otherwise   = genOp False op'
genOp    _             op'
  | op' == iSumSet = ["sum temp : "," | temp."]
  | op' == iProdSet = ["prod temp : "," | temp."]
  | op' `elem` unOps  = [op']
  | op' == iPlus = [".add[", "]"]
  | op' == iSub  = [".sub[", "]"]
  | op' == iMul = [".mul[", "]"]
  | op' == iDiv = [".div[", "]"]
  | op' `elem` logBinOps ++ relBinOps ++ arithBinOps = [" " ++ op' ++ " "]
  | op' == iUnion = [" + "]
  | op' == iDifference = [" - "]
  | op' == iIntersection = [" & "]
  | op' == iDomain = [" <: "]
  | op' == iRange = [" :> "]
  | op' == iJoin = ["."]
  | op' == iIfThenElse = [" => ", " else "]
genOp _ _ = error "This should never happen"

-- adjust parent
adjustPExp :: [String] -> PExp -> PExp
adjustPExp resPath (PExp t pid' pos x) = PExp t pid' pos $ adjustIExp resPath x

adjustIExp :: [String] -> IExp -> IExp
adjustIExp resPath x = case x of
  IDeclPExp q d pexp -> IDeclPExp q d $ adjustPExp resPath pexp
  IFunExp op' exps' -> adjNav $ IFunExp op' $ map adjExps exps'
    where
    (adjNav, adjExps) = if op' == iJoin then (aNav, id)
                        else (id, adjustPExp resPath)
  IClaferId _ _ _ _ -> aNav x
  _  -> x
  where
  aNav = fst.(adjustNav resPath)

adjustNav :: [String] -> IExp -> (IExp, [String])
adjustNav resPath x@(IFunExp op' (pexp0:pexp:_))
  | op' == iJoin = (IFunExp iJoin
                   [pexp0{_exp = iexp0},
                    pexp{_exp = iexp}], path')
  | otherwise   = (x, resPath)
  where
  (iexp0, path) = adjustNav resPath (_exp pexp0)
  (iexp, path') = adjustNav path    (_exp pexp)
adjustNav resPath x@(IClaferId _ id' _ _)
  | id' == parentIdent = (x{_sident = "~@" ++ (genRelName $ head resPath)}, tail resPath)
  | otherwise    = (x, resPath)
adjustNav _ _ = error "Function adjustNav Expect a IFunExp or IClaferID as one of it's argument but it was given a differnt IExp" --This should never happen

genQuant :: IQuant -> String
genQuant    x       = case x of
  INo   -> "no"
  ILone -> "lone"
  IOne  -> "one"
  ISome -> "some"
  IAll -> "all"


genDecl :: GenEnv -> [String] -> IDecl -> Concat
genDecl    genEnv    resPath     x      = case x of
  IDecl disj locids pexp -> cconcat [CString $ genDisj disj, CString " ",
    CString $ intercalate ", " locids, CString " : ", genPExp genEnv resPath pexp]


genDisj :: Bool -> String
genDisj    x     = case x of
  False -> ""
  True  -> "disj"

-- mapping line/columns between Clafer and Alloy code

data AlloyEnv = AlloyEnv {
  lineCol :: (LineNo, ColNo),
  mapping :: [(Span, IrTrace)]
  } deriving (Eq,Show)

mapLineCol :: Concat -> [(Span, IrTrace)]
mapLineCol code = mapping $ execState (mapLineCol' code) (AlloyEnv (firstLine, firstCol) [])

addCode :: MonadState AlloyEnv m => String -> m ()
addCode str = modify (\s -> s {lineCol = lineno (lineCol s) str})

mapLineCol' :: MonadState AlloyEnv m => Concat -> m ()
mapLineCol' (CString str) = addCode str
mapLineCol' c@(Concat srcPos' n) = do
  posStart <- gets lineCol
  _ <- mapM mapLineCol' n
  posEnd   <- gets lineCol

  {-
   - Alloy only counts inner parenthesis as part of the constraint, but not outer parenthesis.
   - ex1. the constraint looks like this in the file
   -    (constraint a) <=> (constraint b)
   - But the actual constraint in the API is
   -    constraint a) <=> (constraint b
   -
   - ex2. the constraint looks like this in the file
   -    (((#((this.@r_c2_Finger).@r_c3_Pinky)).add[(#((this.@r_c2_Finger).@r_c4_Index))]).add[(#((this.@r_c2_Finger).@r_c5_Middle))]) = 0
   - But the actual constraint in the API is
   -    #((this.@r_c2_Finger).@r_c3_Pinky)).add[(#((this.@r_c2_Finger).@r_c4_Index))]).add[(#((this.@r_c2_Finger).@r_c5_Middle))]) = 0
   -
   - Seems unintuitive since the brackets are now unbalanced but that's how they work in Alloy. The next
   - few lines of code is counting the beginning and ending parenthesis's and subtracting them from the
   - positions in the map file.
   - Same is true for square brackets.
   - This next little snippet is rather inefficient since we are retraversing the Concat's to flatten.
   - But it's the simplest and correct solution I can think of right now.
   -}
  let flat = flatten c
      raiseStart = countLeading "([" flat
      deductEnd = -(countTrailing ")]" flat)
  modify (\s -> s {mapping = (Span (uncurry Pos $ posStart `addColumn` raiseStart) (uncurry Pos $ posEnd `addColumn` deductEnd), srcPos') : (mapping s)})

addColumn :: Interval -> Integer -> Interval
addColumn (x, y) c = (x, y + c)
countLeading :: String -> String -> Integer
countLeading c xs = toInteger $ length $ takeWhile (`elem` c) xs
countTrailing :: String -> String -> Integer
countTrailing c xs = countLeading c (reverse xs)

lineno :: (Integer, ColNo) -> String -> (Integer, ColNo)
lineno (l, c) str = (l + newLines, (if newLines > 0 then firstCol else c) + newCol)
  where
  newLines = toInteger $ length $ filter (== '\n') str
  newCol   = toInteger $ length $ takeWhile (/= '\n') $ reverse str

firstCol :: ColNo
firstCol  = 1 :: ColNo
firstLine :: LineNo
firstLine = 1 :: LineNo

removeright :: PExp -> PExp
removeright (PExp _ _ _ (IFunExp _ (x : (PExp _ _ _ (IClaferId _ _ _ _)) : _))) = x
removeright (PExp t id' pos (IFunExp o (x1:x2:xs))) = (PExp t id' pos (IFunExp o (x1:(removeright x2):xs)))
removeright (PExp _ _ _ _) = error "Function removeright from the AlloyGenerator expects a PExp with a IFunExp inside, was given something else" --This should never happen

getRight :: PExp -> PExp
getRight (PExp _ _ _ (IFunExp _ (_:x:_))) = getRight x
getRight p = p
