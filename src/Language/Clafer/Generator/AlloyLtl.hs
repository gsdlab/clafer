{-# LANGUAGE RankNTypes, FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-
 Copyright (C) 2012-2015 Kacper Bak, Jimmy Liang, Michal Antkiewicz, Rafael Olaechea <http://gsd.uwaterloo.ca>

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
-- | Generates Alloy4.2 code for a Clafer model
module Language.Clafer.Generator.AlloyLtl (genAlloyLtlModule) where

import Control.Applicative
import Control.Conditional
import Control.Lens hiding (elements, mapping, op)
import Control.Monad.State
import Data.FileEmbed
import Data.List hiding (and)
import Data.Maybe
import Data.StringMap (keys, elems, toList)
import Debug.Trace
import Prelude

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.AbsClafer
import Language.Clafer.Front.LexClafer
import Language.Clafer.Generator.Concat
import Language.Clafer.Intermediate.Intclafer hiding (exp)

data GenCtx = GenCtx {
    ctxClafer :: IClafer,
    resPath::[String],
    time :: Maybe String
  } deriving (Show)

emptyCtx :: IClafer -> GenCtx
emptyCtx c = GenCtx c [] Nothing

data GenEnv = GenEnv
  { claferargs :: ClaferArgs
  , uidIClaferMap :: UIDIClaferMap
  , forScopes :: String
  }  deriving (Show)

stateSig :: String
stateSig = "State"

anyTrue :: [Bool] -> Bool
anyTrue = any (\x -> x)

-- Alloy code generation
genAlloyLtlModule :: ClaferArgs -> (IModule, GEnv) -> [(UID, Integer)] -> [Token]   -> (Result, [(Span, IrTrace)])
genAlloyLtlModule    claferargs'   (imodule, genv)       scopes         otherTokens' = (flatten output, filter ((/= NoTrace) . snd) $ mapLineCol output)
  where
  tl = trace_len claferargs'
  uidIClaferMap' = uidClaferMap genv
  genEnv = GenEnv claferargs' uidIClaferMap' forScopes'
  rootClafer = findIClafer uidIClaferMap' rootIdent
  clafer' = case rootClafer of
                          Just c' -> c'
                          _ -> error "Missing root clafer" -- should never happen


  -- multiply the scope by trace length for mutable clafers
  adjustScope :: (UID, Integer) -> (UID, Integer)
  adjustScope s@(uid', scope')   = case findIClafer uidIClaferMap' uid' of
    Just claf -> if isMutable claf then (uid', tl * scope') else s
    Nothing   -> s

  genScopes :: [(UID, Integer)] -> String
  genScopes [] = ""
  genScopes scopes' = " but " ++ intercalate ", " (map (\ (uid', scope)  -> show scope ++ " " ++ uid') scopes')

  forScopes' = "for " ++ show tl ++ (genScopes $ map adjustScope scopes)
  -- output = header claferargs scopes +++ (cconcat $ map (genDeclaration genEnv) (_mDecls imodule)) +++
  outputBody = genRootClafer genEnv clafer'
  output = header genEnv otherTokens' +++ outputBody

header :: GenEnv -> [Token]    -> Concat
header    genEnv   otherTokens' = CString $ unlines $ catMaybes
    [ (Alloy  `notElem` (mode args)) ?<> Just "open util/integer"
    , Just $ genAlloyEscapes otherTokens'
    , (AlloyLtl `elem` (mode args))    ?<> Just traceModuleSource
    , (not (validate args)) ?<>
      Just ("run show " ++ forScopes genEnv)
    , Just "pred show {}"
    , Just ""
    , Just "/* Clafer specifications (input dependent) */"
    , Just ""
    ]
    where args = claferargs genEnv

genAlloyEscapes :: [Token]  -> String
genAlloyEscapes otherTokens' = concat $ map printAlloyEscape otherTokens'
    where
      printAlloyEscape (PT _ (T_PosAlloy code)) =  let
          code' = fromJust $ stripPrefix "[alloy|" code
        in
          take ((length code') - 2) code'

      printAlloyEscape _                        = ""

traceModuleSource :: String
traceModuleSource =  $(embedStringFile  "src/Language/Clafer/Generator/stateTrace.als")

genRootClafer :: GenEnv -> IClafer -> Concat
genRootClafer genEnv clafer'  =
  (cunlines $ filterNull
          [   claferDecl clafer' (
              (showSet (CString "\n, ") $ genRootRelations genEnv ctx)
              +++ (optShowSet $ filterNull $ genConstraints genEnv ctx)
            )
          ]
        )
      +++ CString "\n" +++ children'
      +++ CString "\n" +++ assertions
  where
  ctx = GenCtx clafer' [] Nothing
  children' = cconcat $ filterNull $ map
             (genClafer genEnv [_uid clafer']) $
             getSubclafers $ _elements clafer'
  assertions = cconcat $ map mkSingleAssert $ getAssertions clafer'
  mkSingleAssert pexp = mkAssert genEnv (genAssertName pexp) $
    genAssertBody genEnv (GenCtx clafer' [_uid clafer'] Nothing) pexp clafer'

getAssertions :: IClafer -> [PExp]
getAssertions clafer' = concat $ map pullAssert $ _elements clafer'
  where pullAssert (IEConstraint False pexp) = [pexp]
        pullAssert _ = []

{- Unused since the introduction of root Clafer
genDeclaration :: GenEnv -> IElement -> Concat
genDeclaration genEnv x = case x of
  IEClafer clafer'  -> genRootClafer genEnv clafer'
  IEConstraint True pexp  -> mkFact $ genPExp genEnv (GenCtx [] Nothing) pexp
  IEConstraint False pexp  -> mkAssert genEnv (genAssertName pexp) $ genPExp genEnv (GenCtx [] Nothing) pexp
  IEGoal _ (PExp _ _ _ innerexp) -> CString ""
-}

mkFact :: Concat -> Concat
mkFact x@(CString "") = x
mkFact xs = cconcat [CString "fact ", mkSet xs, CString "\n"]

genAssertName :: PExp -> Concat
genAssertName    PExp{_inPos=(Span _ (Pos line _))} = CString $ "assertOnLine_" ++ show line

genAssertBody :: GenEnv -> GenCtx -> PExp -> IClafer -> Concat
genAssertBody genEnv ctx pexp clafer' = cconcat $
    if containsStatefulExp genEnv pexp
    then [genTimeDecl "t" [] clafer', genPExp genEnv ctx {time = Just "t"} pexp]
    else [genPExp genEnv ctx {time = Nothing} pexp]

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
genClafer genEnv resPath' clafer'
  = (cunlines $ filterNull
      [   cardFact
      +++ claferDecl clafer' (
          (showSet (CString "\n, ") $ genRelations genEnv ctx)
          +++ (optShowSet $ filterNull $ genConstraints genEnv ctx)
        )
      ]
    )
  +++ CString "\n" +++ children'
  +++ CString "\n" +++ assertions
  where
  ctx = GenCtx clafer' resPath' Nothing
  children' = cconcat $ filterNull $ map
             (genClafer genEnv ((_uid clafer') : resPath')) $
             getSubclafers $ _elements clafer'
  cardFact
    | null resPath' && (null $ flatten $ genOptCard clafer') =
        case genCard (_uid clafer') $ _card clafer' of
          CString "set" -> CString ""
          c -> mkFact c
    | otherwise = CString ""
  assertions = cconcat $ map mkSingleAssert $ getAssertions clafer'
  mkSingleAssert pexp = mkAssert genEnv (genAssertName pexp) $
    genAssertBody genEnv ctx pexp clafer'

claferDecl :: IClafer -> Concat -> Concat
claferDecl    c     rest    = cconcat
  [ genSigCard
  , CString $ if _isAbstract c then "abstract " else ""
  , CString "sig "
  , Concat NoTrace [CString $ _uid c, genExtends $ _super c, CString "\n", rest]
  ]
  where
  genSigCard = if not (isMutable c) then genOptCard c else CString ""
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


genRootRelations :: GenEnv -> GenCtx -> [Concat]
genRootRelations    genEnv    ctx        = maybeToList references ++ (map mkRel $ getSubclafers $ _elements c)
  where
  c = ctxClafer ctx
  references = if isJust $ _reference c
                then
                        Just $ Concat NoTrace [CString $ genRel (genRefName $ _uid c)
                         c {_card = Just (1, 1)} rType]
                else
                        Nothing
  rType = flatten $ refType genEnv c
  mkRel c' = Concat NoTrace [CString $ genRel (genRelName $ _uid c') c' $ _uid c']


genRelations :: GenEnv -> GenCtx -> [Concat]
genRelations    genEnv    ctx        = maybeToList r ++ (map mkRel $ getSubclafers $ _elements c)
  where
  c = ctxClafer ctx
  r = if isJust $ _reference c
                then
                        Just $ Concat NoTrace [CString $ genRel (genRefName $ _uid c)
                         c {_card = Just (1, 1)} rType]
                else
                        Nothing
  rType = flatten $ refType genEnv c
  mkRel c' = Concat NoTrace [CString $ genRel (genRelName $ _uid c') c' $ _uid c']

genRelName :: String -> String
genRelName name = "r_" ++ name

genRefName :: String -> String
genRefName name = name ++ "_ref"

genRel :: String -> IClafer -> String -> String
genRel name c rType = if isMutable c
  then genMutAlloyRel name rType'
  else genAlloyRel name (genCardCrude $ _card c) rType'
  where
  rType' = if isPrimitive rType then "Int" else rType


genAlloyRel :: String -> String -> String -> String
genAlloyRel name card' rType = concat [name, " : ", card', " ", rType]

genMutAlloyRel :: String -> String -> String
genMutAlloyRel name rType = concat [name, " : ", rType, " -> ", stateSig]

refType :: GenEnv -> IClafer -> Concat
refType    genEnv c = fromMaybe (CString "") (((genType genEnv c).getTarget) <$> (_ref <$> _reference c))

getTarget :: PExp -> PExp
getTarget    x     = case x of
  PExp _ _ _ (IFunExp op' (_:pexp:_))  -> if op' == iJoin then pexp else x
  _ -> x

genType :: GenEnv -> IClafer -> PExp                                -> Concat
genType    _         c       x@(PExp _ _ _ y@(IClaferId _ sid _ _)) = CString sid
genType    genEnv    c       x                                      = genPExp genEnv (emptyCtx c) x


-- -----------------------------------------------------------------------------
-- constraints
-- user constraints + parent + group constraints + reference
-- a = NUMBER do all x : a | x = NUMBER (otherwise alloy sums a set)

containsStatefulExp :: GenEnv ->  PExp -> Bool
containsStatefulExp    genEnv     (PExp iType' _ _ exp') =  case exp' of
  IFunExp op _ | op == iInitially || op == iFinally -> False
  IFunExp _ exps' -> anyTrue $ map (containsStatefulExp genEnv) exps'
  IClaferId _ sident' _ (GlobalBind claferUid) -> timedIClaferId
    where
    boundIClafer = fromJust $ findIClafer (uidIClaferMap genEnv) claferUid
    mutable' = isMutable boundIClafer
    timedIClaferId
      | sident' == "ref" = mutable'
      | head sident' == '~' = False
      | isNothing iType' = mutable'
      | otherwise = case fromJust $ iType' of
        TInteger -> False
        TReal -> False
        TString -> False
        _ -> mutable'
  IDeclPExp _ decls' e -> anyTrue (map (containsMut genEnv) decls') || containsStatefulExp genEnv e
  _ -> False
  where
  containsMut genEnv' (IDecl _ _ body') = containsStatefulExp genEnv' body'

genConstraints :: GenEnv -> GenCtx -> [Concat]
genConstraints    genEnv    ctx
  = (genParentConst (resPath ctx) c)
  : (genMutClaferConst ctx c)
  : (genMutSubClafersConst genEnv c)
  : (genGroupConst genEnv c)
  : (genRefSubrelationConstriant (uidIClaferMap genEnv) c)
  : (genInitialSubClafersConst genEnv ctx)
-- Disabled because genPathConst is disabled in the static alloy generator.
-- TODO: remove it if not needed
--  : (genPathConst genEnv ctx  (if (noalloyruncommand (claferargs genEnv)) then  (_uid c ++ "_ref") else "ref") c)
  : constraints
  where
  c = ctxClafer ctx
  constraints = concatMap genConst $ _elements c
  genConst :: IElement -> [ Concat ]
  genConst    x = case x of
    IEConstraint True pexp  -> -- genPExp cargs ((_uid c) : resPath) pexp
        if containsStatefulExp genEnv pexp
        then [genTimeDecl "t" (resPath ctx) c, genPExp genEnv ctx { time = Just "t", resPath = ((_uid c) : (resPath ctx))} pexp]
        else [genPExp genEnv ctx { time = Nothing, resPath = ((_uid c) : (resPath ctx))} pexp]
    IEConstraint False pexp ->
        if _ident c == rootIdent
        then []  -- has already been generated in genRootClafer
        else [ CString "// Assertion " +++ (genAssertName pexp) +++ CString " ignored since nested assertions are not supported in Alloy.\n" ]
    IEClafer c' ->
        (if genCardCrude (_card c') `elem` ["one", "lone", "some"]
         then CString ""
         else mkCard ({- do not use the genRelName as the constraint name -} _uid c') False (genRelName $ _uid c') $ fromJust (_card c')
        )
        : (genParentSubrelationConstriant (uidIClaferMap genEnv) c')
        : (genSetUniquenessConstraint c')

    IEGoal _ _ -> error "[bug] Alloy.getConst: should not be given a goal." -- This should never happen


-- generates time variable binding declaration which appears as a first expression in mutable constraints
-- it references all time moments when context clafer instance is active
-- typical binding form is: this.(ParentSig.ContextClaferRelation)
-- Template uses localFirst function:
-- let t = localFirst[rel, parentSig, this]
-- if defined under root clafer:
-- let t = first |
genTimeDecl :: String -> [String] -> IClafer -> Concat
genTimeDecl tvar rPath c | isMutable c = CString $ case rPath of
                                           par:_ -> genLocalFirst tvar par c
                                           [] -> globalFirstDecl -- For top level constraint
                         | otherwise = CString globalFirstDecl
  where
    globalFirstDecl = "let " ++ tvar ++ " = first | "

genLocalFirst :: String -> String -> IClafer -> String
genLocalFirst tvar parent c = "one " ++ tvar ++ " : localFirst[" ++
                                             genRelName (_uid c) ++
                                             "," ++ parent ++
                                             ", this] | "

-- if clafer is mutable, generates fact that prevents instance from disapearing for one or more snapshot
-- and then reapearing and says that  only subclafer may only have one parent.
-- typically:
-- lone localFirst [rel, parent_sig, this] && lone r_c0_a.Time.this
genMutClaferConst :: GenCtx -> IClafer -> Concat
genMutClaferConst ctx c
  | isMutable c = CString $ "lone localFirst["
                        ++ genRelName (_uid c) ++ ", " ++ parentSig ++ ", this] && " ++ "lone "
                        ++ genRelName (_uid c) ++ "." ++ stateSig ++ ".this"
  | otherwise = CString ""
  where parentSig = case resPath ctx of
              x:_ -> x
              [] -> error "genMutClaferConst:: can not make parent"

genInitialSubClafersConst :: GenEnv -> GenCtx -> Concat
genInitialSubClafersConst genEnv ctx =
  let initialSubClafers = filter _isInitial $ getSubclafers $ _elements $ ctxClafer ctx in
  case initialSubClafers of
    x:_ -> genTimeDecl time' (resPath ctx) (ctxClafer ctx) +++
      cintercalate (CString " && \n\t") (map genInitialConst initialSubClafers)
    [] -> CString ""
  where
    makeSomeExp c = pExpDefPid noSpan $ IDeclPExp ISome [] $ cId c
    cId c = mkPLClaferId noSpan (_uid c) False $ GlobalBind (_uid c)
    genInitialConst c = cconcat [ CString "("
               , genPExp' genEnv (ctx {time = Just time'}) $ makeSomeExp c
               , CString ")"]
    time' =  "t"


-- generates cardinality and parent dependency constraints for mutable subclafers
-- typically all t: Time | lone r_field.t && lone r_field2.t &&
--                         no (parent_rel.t.this) => (no r_field[this].t && no r_field2[this].t)
-- Michal: TODO: revise because now a clafer can have both super and reference at the same time
-- Paulius: TODO: check if cardinality constraints are correct
genMutSubClafersConst :: GenEnv -> IClafer -> Concat
genMutSubClafersConst    genEnv c = genTimeQuant allSubExp +++ (cintercalate (CString " && \n\t") allSubExp)
  where
  allSubExp = cardConsts ++ refCardConst ++ (genReqParentConstBody "t" c mutClafers)
  cardConsts = map genCardConstBody $ filter (\c' -> cardStr c' /= "set") mutClafers
  refCardConst
    | (isMutable c) && (isJust $ _reference c) = [CString $ "one this.@" ++ genRefName (_uid c) ++ ".t"]
    | otherwise = []
  mutClafers = filter isMutable $ getSubclafers $ _elements c
  cardStr c' = genCardCrude $ _card c'
  genTimeQuant [] = CString ""
  genTimeQuant _ = genTimeAllQuant "t"
  genCardConstBody c' = CString $ (cardStr c') ++ " " ++ (genRelName $ _uid c') ++ ".t"

-- Generates constraints that prevents instance subgraphs that are not connected to the root
-- Constraints says that if at some time moment t there is no connection to the parent then that clafer can not have any subchildren
-- Typically:
-- all t:Time | no rel_parent.t.this => no rel_child[this].t && no rel_child2
-- Func does not generate "all t:Time |" part.
-- TODO needs to be tested
genReqParentConstBody :: String -> IClafer -> [IClafer] -> [Concat]
genReqParentConstBody time' c mutSubClafers =
  if not (isMutable c) then []
                      else case mutSubClafers of
                                [] -> []
                                _  -> [CString ("(" ++ genAnticedent ++ " => " ++ intercalate " && " genConsequent ++ ")")]
  where
    genAnticedent = "no " ++ genRelName (_uid c) ++ "." ++ time' ++ ".this"
    genConsequent = map genSubClaferConst mutSubClafers
    genSubClaferConst subC = "no " ++ genRelName (_uid subC) ++ "." ++ time'

genSetUniquenessConstraint :: IClafer -> [Concat]
genSetUniquenessConstraint c =
    (case _reference c of
      Just (IReference True _ _) ->
        (case _card c of
            Just (lb,  ub) -> if (lb > 1 || ub > 1 || ub == -1)
              then [ CString $ (
                        (case isTopLevel c of
                          False -> "all disj x, y : this.@" ++ (genRelName $ _uid c)
                          True  -> " all disj x, y : "       ++ (_uid c)))
                     ++ " | (x.@" ++ genRefName (_uid c) ++ ") != (y.@" ++ genRefName (_uid c) ++ ") "
                   ]
              else []
            _ -> [])
      _ -> []
    )

-- TODO: need to include time stamps
genParentSubrelationConstriant :: UIDIClaferMap -> IClafer   -> Concat
genParentSubrelationConstriant    uidIClaferMap'   headClafer =
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

-- See Common.NestedInheritanceMatch
genRefSubrelationConstriant :: UIDIClaferMap -> IClafer   -> Concat
genRefSubrelationConstriant    uidIClaferMap'   headClafer =
  if isJust $ _reference headClafer
  then
    case match of
      Nothing -> CString ""
      Just NestedInheritanceMatch
        { _superClafer = superClafer
        ,  _superClafersTarget = superClafersTarget
        }  -> case (isProperRefinement uidIClaferMap' match, not $ null superClafersTarget) of
                 ((True, True, True), True) -> CString $ concat
                  [ genRefName $ _uid headClafer
                  , " in "
                  , genRefName $ _uid superClafer
                  ]
                 _ -> CString ""
  else CString ""
  where
    match = matchNestedInheritance uidIClaferMap' headClafer


-- optimization: if only boolean features then the parent is unique
-- if child type is mutable then parenting constraints are expressed through genMutSubClafersConst
genParentConst :: [String] -> IClafer -> Concat
genParentConst [] _     = CString ""
genParentConst _ c
  | isMutable c = CString ""
  | otherwise  = genOptParentConst c

genOptParentConst :: IClafer -> Concat
genOptParentConst    c
  | glCard' == "one"         = CString ""
  | glCard' == "lone"        = Concat NoTrace [CString $ "one " ++ rel]
  | otherwise                = Concat NoTrace [CString $ "one @" ++ rel ++ ".this"]
  -- eliminating problems with cyclic containment;
  -- should be added to cases when cyclic containment occurs
  --                    , " && no iden & @", rel, " && no ~@", rel, " & @", rel]
  where
  rel = genRelName $ _uid c
  glCard' = genIntervalCrude $ _glCard c

genGroupConst :: GenEnv -> IClafer -> Concat
genGroupConst    genEnv    clafer'
  | _isAbstract clafer' || null children' || flatten card' == "" = CString ""
  | otherwise = cconcat [genTimeQuant, CString "let children = ", brArg id $ CString children', CString " | ", card']
  where
  superHierarchy :: [IClafer]
  superHierarchy = findHierarchy getSuper (uidIClaferMap genEnv) clafer'
  subclafers = getSubclafers $ concatMap _elements superHierarchy
  children' = intercalate " + " $ map childRel subclafers
  childRel :: IClafer -> String
  childRel subc = (genRelName._uid) subc ++ (if isMutable subc then ".t" else "")
  card'     = mkCard (_uid clafer') True "children" $ _interval $ fromJust $ _gcard $ clafer'
  genTimeQuant = if any isMutable subclafers then genTimeAllQuant "t" else CString ""

mkCard :: String -> Bool -> String -> (Integer, Integer) -> Concat
mkCard constraintName group' element' crd
  | crd' == "set" || crd' == ""        = CString ""
  | crd' `elem` ["one", "lone", "some"] = CString $ crd' ++ " " ++ element'
  | otherwise                            = interval'
  where
  interval' = genInterval constraintName group' element' crd
  crd'  = flatten $ interval'


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
    s1 = if n == 0 then Nothing else Just $ cardLowerConcat constraintName group' [CString $ concat [show n, " <= #",  element']]
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
genClaferIdSuffix :: GenEnv -> GenCtx -> ClaferBinding -> String
genClaferIdSuffix genEnv GenCtx{time=Just t} (GlobalBind claferUid) =
  case findIClafer (uidIClaferMap genEnv) claferUid of
    Just c' | isMutable c' -> "." ++ t
            | otherwise -> ""
genClaferIdSuffix _ _ _ = ""

getClaferIdWithState :: GenCtx -> String -> Bool -> String
getClaferIdWithState GenCtx{time=Just t} ident' True = ident' ++ "." ++ t
getClaferIdWithState _ ident' _ = ident'


genPExp :: GenEnv -> GenCtx -> PExp -> Concat
genPExp    genEnv    ctx       x     = genPExp' genEnv ctx $ adjustPExp ctx x

genPExp' :: GenEnv -> GenCtx -> PExp                       -> Concat
genPExp'    genEnv    ctx       (PExp iType' pid' pos exp') = case exp' of
  IDeclPExp q d pexp -> Concat (IrPExp pid') $
    [ CString $ genQuant q, CString " "
    , cintercalate (CString ", ") $ map (genDecl genEnv ctx) d
    , CString $ optBar d, genPExp' genEnv ctx pexp]
    where
    optBar [] = ""
    optBar _  = " | "
  IClaferId _ "integer" _ _ -> CString "Int"
  IClaferId _ "int" _ _ -> CString "Int"
  IClaferId _ "string" _ _ -> CString "Int"
  IClaferId _ "dref" _ _ -> CString $ getClaferIdWithState ctx ("@"  ++ getTClaferUID iType' ++ "_ref")
          (isNothing (boundIClafer >>= _reference >>= _refModifier))
    where
      boundIClafer = findIClafer (uidIClaferMap genEnv) (getTClaferUID iType')
      getTClaferUID (Just TMap{_so = TClafer{_hi = [u]}}) = u
      getTClaferUID (Just TMap{_so = TClafer{_hi = (u:_)}}) = u
      getTClaferUID t = error $ "[bug] Alloy.genPExp'.getTClaferUID: unknown type: " ++ show t
  IClaferId _ sid isTop bind@(GlobalBind claferUid) -> CString $
      if head sid == '~'
      then if bound
           then "~(" ++ tail sid ++ (if isMutable boundClafer then ".t" else "") ++ ")"
           else error "AlloyLtl.genPExp' Unbounded parent expression" -- should never happen
      else if isBuiltInExpr then vsident else sid'
    where
    (bound, boundClafer) = case findIClafer (uidIClaferMap genEnv) claferUid of
                             Just c' -> (True, c')
                             _ -> (False, undefined)
    isBuiltInExpr = isPrimitive sid ||
      case iType' of
           Just TInteger -> True
           Just TReal -> True
           Just TString -> True
           _ -> False
    sid' = if isBuiltInExpr || sid == "this" || isTop && bound && (not $ isMutable boundClafer)
              then sid else ('@' : genRelName "" ++ sid ++ genClaferIdSuffix genEnv ctx bind)
    vsident = sid' ++  ".@"  ++ genRefName (if sid == "this" then head $ resPath ctx else sid)
  IClaferId _ sid _ (LocalBind _) -> CString sid  -- this is the case for local declarations in quantifiers
  IClaferId _ sid _ NoBind -> CString sid  -- this is the case for local declarations in quantifiers
  IFunExp _ _ -> case exp'' of
    IFunExp _ _ -> genIFunExp genEnv pid' ctx exp''
    _ -> genPExp' genEnv ctx $ PExp iType' pid' pos exp''
    where
    exp'' = transformExp exp' $ ctxClafer ctx
  IInt n -> CString $ show n
  IDouble _ -> error "no double numbers allowed"
  IReal _ -> error "no real numbers allowed"
  IStr _ -> error "no strings allowed"
  x -> error $ "AlloyLtl.genPExp': No pattern match for " ++ show x


-- 3-May-2012 Rafael Olaechea.
-- Removed transfromation from x = -2 to x = (0-2) as this creates problem with  partial instances.
-- See http://gsd.uwaterloo.ca:8888/question/461/new-translation-of-negative-number-x-into-0-x-is.
-- Encoding of Weak Until expression is done by translating to equivalent Until expression
-- a W b === G a || a U b
transformExp :: IExp -> IClafer -> IExp
transformExp (IFunExp op' (e1:_)) c'
  | op' == iMin = IFunExp iMul [PExp (_iType e1) "" noSpan $ IInt (-1), e1]
{-  | op' == iInitially && isMutable c' = -- transforms to: (no this && X this) => X e1
        let thisExpr = PExp (Just TBoolean) "" noSpan (IClaferId "" "this" False (GlobalBind (_uid c')))
            oper1 =  PExp (Just TBoolean) "" noSpan (IFunExp iNot [ thisExpr ])
            oper2 = PExp (Just TBoolean) "" noSpan (IFunExp iX [thisExpr])
            and' = PExp (Just TBoolean) "" noSpan (IFunExp iAnd [oper1, oper2] )
            xExpr = PExp (Just TBoolean) "" noSpan (IFunExp iX [e1])
        in  IFunExp iImpl [and', xExpr]
  | op' == iInitially  = _exp e1 -}
transformExp    x@(IFunExp op' exps'@(e1:e2:_)) _
  | op' == iXor = IFunExp iNot [PExp (Just TBoolean) "" noSpan (IFunExp iIff exps')]
  | op' == iW = let p1 = PExp (Just TBoolean) "" noSpan $ IFunExp iG [e1] -- G e1
                    p2 = PExp (Just TBoolean) "" noSpan x{_op=iU} -- e1 U e2
                in IFunExp iOr [p1, p2] -- G e1 || e1 U e2
  | op' == iJoin && isClaferName' e1 && isClaferName' e2 &&
    getClaferName e1 == thisIdent && head (getClaferName e2) == '~' =
        IFunExp op' [e1{_iType = Just $ TClafer []}, e2]
  | otherwise  = x
transformExp x _ = x

genIFunExp :: GenEnv -> String -> GenCtx -> IExp             -> Concat
genIFunExp    genEnv    pid'      ctx       (IFunExp op' exps') =
  if (op' `elem` ltlOps)
  then Concat (IrPExp pid') $ surroundPar $ genLtlExp genEnv ctx op' exps'
  else if (op' == iSumSet)
    then genIFunExp genEnv pid' ctx (IFunExp iSumSet' [removeright firstExp, getRight firstExp])
    else if (op' == iSumSet')
      then Concat (IrPExp pid') $ intl exps'' (map CString $ genOp iSumSet)
      else Concat (IrPExp pid') $ intl exps'' (map CString $ genOp op')
  where
    iSumSet' = "sum'"
    firstExp = case exps' of
                      x:_ -> x
                      [] -> error "genIFunExp"
    surroundPar [] = []
    surroundPar xs = CString "(" : (xs ++ [CString ")"])
    intl
      | op' == iSumSet' = flip interleave
      | op' `elem` arithBinOps && length exps' == 2 = interleave
      | otherwise = \xs ys -> reverse $ interleave (reverse xs) (reverse ys)
    exps'' = map (optBrArg genEnv ctx) exps'
genIFunExp _ _ _ x = error $ "[bug] Alloy.genIFunExp: expecting a IFunExp, instead got: " ++ show x--This should never happen

genLtlExp :: GenEnv -> GenCtx -> String -> [PExp] -> [Concat]
genLtlExp    genEnv    ctx       op'        exps' = dispatcher exps'
  where
  dispatcher
    | op' == iF = genF
    | op' == iX = genX
    | op' == iG = genG
    | op' == iU = genU
    | op' == iInitially = genInitially -- error $ "AlloyLtl.genLtlExp: Initially should have been translated in transformExp"
    | op' == iFinally = genFinally -- error $ "AlloyLtl.genLtlExp: Initially should have been translated in transformExp"
    | op' == iW = error $ "AlloyLtl.genLtlExp: W should have been translated in transformExp"
    | otherwise = error $ "AlloyLtl.genLtlExp: unsupported temporal operator: " ++ op' -- should never happen
  genF [e1]
    | containsStatefulExp genEnv e1 = mapToCStr ["some ", t', ":", t, ".*next | "] ++ [genPExp' genEnv (ctx {time = Just t'}) e1]
    | otherwise = [genPExp' genEnv (ctx {time = Just t'}) e1]
  genF _ = error "AlloyLtl.genLtlExp: F modality requires one argument" -- should never happen
  genX [e1]
    | containsStatefulExp genEnv e1 = mapToCStr ["some ", t, ".next and let ", t', " = ", t, ".next | "] ++ [genPExp' genEnv (ctx {time = Just t'}) e1]
    | otherwise = [genPExp' genEnv (ctx {time = Just t'}) e1]
  genX _ = error "AlloyLtl.genLtlExp: X modality requires one argument" -- should never happen
  genG [e1]
    | containsStatefulExp genEnv e1 = mapToCStr ["infinite and all ", t', ":", t, ".*next | "] ++ [genPExp' genEnv (ctx {time = Just t'}) e1]
    | otherwise = [genPExp' genEnv (ctx {time = Just t'}) e1]
  genG _ = error "AlloyLtl.genLtlExp: G modality requires one argument" -- should never happen
  genU (e1:e2:_) = mapToCStr ["some ", t', ":", t, ".future | "] ++ [genPExp' genEnv (ctx {time = Just t'}) e2] ++
    mapToCStr [" and ( all ", t'', ": upto[", t, ", ", t', "] | "] ++ [genPExp' genEnv (ctx {time = Just t''}) e1, CString ")"]
  genU _ = error "AlloyLtl.genLtlExp: U modality requires two arguments" -- should never happen
  genInitially [e1] = [CString "("
               , genTimeDecl newTime (resPath ctx) (ctxClafer ctx)
               , genPExp' genEnv (ctx {time = Just newTime}) e1
               , CString ")"]
  genInitially _ = error "AlloyLtl.genLtlExp: initially requires one argument"
  genFinally _ = error "AlloyLtl.genFinally: TODO"
  newTime = (fromMaybe "t" $ time ctx) ++ "0"
  t = fromMaybe "t" $ time ctx
  t' = t ++ "'"
  t'' = t' ++ "'"


optBrArg :: GenEnv  -> GenCtx -> PExp -> Concat
optBrArg    genEnv     ctx       x     = brFun (genPExp' genEnv ctx) x
  where
  brFun = case x of
    PExp _ _ _ (IClaferId{}) -> ($)
    PExp _ _ _ (IInt _) -> ($)
    _  -> brArg

interleave :: [Concat] -> [Concat] -> [Concat]
interleave [] [] = []
interleave (x:xs) [] = x:xs
interleave [] (x:xs) = x:xs
interleave (x:xs) ys = x : interleave ys xs

brArg :: (a -> Concat) -> a -> Concat
brArg f arg = cconcat [CString "(", f arg, CString ")"]

genOp :: String -> [String]
genOp    op'
  | op' == iPlus = [".plus[", "]"]
  | op' == iSub  = [".minus[", "]"]
  | op' == iSumSet = ["sum temp : "," | temp."]
  | op' `elem` unOps  = [op']
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
genOp op' = error $ "[bug] Alloy.genOp: Unmatched operator: " ++ op'

-- adjust parent
adjustPExp :: GenCtx -> PExp -> PExp
adjustPExp ctx (PExp t pid' pos x) = PExp t pid' pos $ adjustIExp ctx x

adjustIExp :: GenCtx -> IExp -> IExp
adjustIExp ctx x = case x of
  IDeclPExp q d pexp -> IDeclPExp q d $ adjustPExp ctx pexp
  IFunExp op' exps' -> adjNav $ IFunExp op' $ map adjExps exps'
    where
    (adjNav, adjExps) = if op' == iJoin then (aNav, id)
                        else (id, adjustPExp ctx)
  IClaferId _ _ _  _-> aNav x
  _  -> x
  where
  aNav = fst.(adjustNav $ resPath ctx)

-- Essentially replaces IClaferId "parent" with appropriate relation name
-- Example "this.parent" becomes "this.~@r_parent"
adjustNav :: [String] -> IExp -> (IExp, [String])
adjustNav resPath' x@(IFunExp op' (pexp0:pexp:_))
  | op' == iJoin = (IFunExp iJoin
                   [pexp0{_exp = iexp0},
                    pexp{_exp = iexp}], path')
  | otherwise   = (x, resPath')
  where
  (iexp0, path) = adjustNav resPath' (_exp pexp0)
  (iexp, path') = adjustNav path    (_exp pexp)
adjustNav resPath' x@(IClaferId _ id' _ _)
  | id' == parentIdent = (x{_sident = "~@" ++ (genRelName topPath)}, tail resPath')
  | otherwise    = (x, resPath')
    where
      topPath = case resPath' of
                     r:_ -> r
                     [] -> error "AlloyLtl.adjustNav: resPath is empty"
adjustNav _ _ = error "Function adjustNav Expect a IFunExp or IClaferID as one of it's argument but it was given a differnt IExp" --This should never happen

genQuant :: IQuant -> String
genQuant    x       = case x of
  INo   -> "no"
  ILone -> "lone"
  IOne  -> "one"
  ISome -> "some"
  IAll -> "all"


genDecl :: GenEnv -> GenCtx -> IDecl -> Concat
genDecl    genEnv    ctx       x      = case x of
  IDecl disj locids pexp -> cconcat [CString $ genDisj disj, CString " ",
    CString $ intercalate ", " locids, CString " : ", genPExp genEnv ctx pexp]


genDisj :: Bool -> String
genDisj    True = "disj"
genDisj    False = ""

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
removeright (PExp _ _ _ (IFunExp _ (x : (PExp _ _ _ IClaferId{}) : _))) = x
removeright (PExp _ _ _ (IFunExp _ (x : (PExp _ _ _ (IInt _ )) : _))) = x
removeright (PExp _ _ _ (IFunExp _ (x : (PExp _ _ _ (IStr _ )) : _))) = x
removeright (PExp _ _ _ (IFunExp _ (x : (PExp _ _ _ (IDouble _ )) : _))) = x
removeright (PExp t id' pos (IFunExp o (x1:x2:xs))) = PExp t id' pos (IFunExp o (x1:(removeright x2):xs))
removeright x@PExp{} = error $ "[bug] AlloyGenerator.removeright: expects a PExp with a IFunExp inside but was given: " ++ show x --This should never happen

getRight :: PExp -> PExp
getRight (PExp _ _ _ (IFunExp _ (_:x:_))) = getRight x
getRight p = p

genTimeAllQuant :: String -> Concat
genTimeAllQuant tvar = CString $ "all " ++ tvar ++ " : " ++ stateSig ++ " | "

-- :vim:expandtabs
