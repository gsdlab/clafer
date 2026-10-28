{-# LANGUAGE RankNTypes, FlexibleContexts #-}
{-
 Copyright (C) 2012-2026 Kacper Bak, Jimmy Liang, Michal Antkiewicz, Rafael Olaechea <http://gsd.uwaterloo.ca>

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
{- | Generates Alloy 6 code with its native temporal logic for a dynamic Clafer model, one
     with temporal operators or modifiers. The semantics follows Juodisius et al., Clafer:
     Lightweight Modeling of Structure, Behaviour, and Variability (2019), section 5, with
     two changes (an errata to the paper, which was never implemented):

     * A trace is an infinite sequence of snapshots (Alloy's lasso traces).
     * The signature of a clafer is the pool of all its instances over the trace. An instance
       exists in a snapshot when its parent links it through the containment relation
       @r_c@, which is @var@ unless the clafer is static (see 'isStatic'); @alive_c@ is the
       set of the existing instances of @c@.
     * An instance does not change its parent (the static field @p_c@), and nothing outlives
       its parent.
     * Change: an instance may reappear. The paper forbids it, but then a cyclic behaviour,
       e.g., green, yellow, red, green, ..., needs infinitely many instances, which no lasso
       trace over finitely many atoms has.
     * The multiplicities, group cardinalities and constraints of a clafer hold in every
       snapshot, for every existing instance; the top-level ones hold in every snapshot.
     * Change: the temporal obligations of a constraint (X, F, G and U, Alloy's @after@,
       @eventually@, @always@ and @until@) hold while the context instance exists; the
       constraint disappears together with it. A modeller extends the timeline of a
       constraint by placing it higher in the hierarchy, or at the top level. A transition
       of a clafer, e.g., @on --> off@, is a constraint of its parent, so the transition of
       a nested state disappears when its enclosing state is left.
     * @initial@ children exist whenever their parent appears; the instances of a @final@
       clafer do not change while their parent exists.
     * @initially@ and @finally@ refer to the first and the last snapshot of the context
       instance's lifetime.
-}
module Language.Clafer.Generator.AlloyLtl (genAlloyLtlModule) where

import Control.Monad.State
import Data.List
import Data.Maybe
import Prelude

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.AbsClafer
import Language.Clafer.Front.LexClafer
import Language.Clafer.Generator.Concat
import Language.Clafer.Intermediate.Intclafer hiding (exp)

data GenEnv = GenEnv
  { claferargs :: ClaferArgs
  , uidIClaferMap :: UIDIClaferMap
  , allClafers :: [IClafer]   -- ^ the clafers of the model, without the root
  , forScopes :: String
  }

-- | Alloy 6 code generation
genAlloyLtlModule :: ClaferArgs -> (IModule, GEnv) -> [(UID, Integer)] -> [Token]     -> (Result, [(Span, IrTrace)])
genAlloyLtlModule    claferargs'   (_      , genv)    scopes              otherTokens' = (flatten output, filter ((/= NoTrace) . snd) $ mapLineCol output)
  where
  uidIClaferMap' = uidClaferMap genv
  root = fromMaybe (error "AlloyLtl: missing root clafer") $ findIClafer uidIClaferMap' rootIdent
  clafers' = tail $ nestedClafers root
  tl = trace_len claferargs'
  genEnv = GenEnv claferargs' uidIClaferMap' clafers' forScopes'

  -- a disappeared instance may reappear, so a scope bounds the instances in a snapshot
  forScopes' = "for 1 but " ++ intercalate ", " (map (\(uid', scope') -> show scope' ++ " " ++ uid') scopes ++ [show tl ++ " steps"])
  output = header genEnv otherTokens' +++ cconcat (map (genClafer genEnv) $ root : clafers')

nestedClafers :: IClafer -> [IClafer]
nestedClafers c = c : concatMap nestedClafers (getSubclafers $ _elements c)

header :: GenEnv -> [Token]     -> Concat
header    genEnv    otherTokens' = CString $ unlines
    [ "open util/integer"
    , genAlloyEscapes otherTokens' ++ "pred show {}"
    , if validate $ claferargs genEnv
      then ""
      else "run show " ++ forScopes genEnv
    , ""]

genAlloyEscapes :: [Token]  -> String
genAlloyEscapes otherTokens' = concatMap printAlloyEscape otherTokens'
    where
      printAlloyEscape (PT _ (T_PosAlloy code)) =  let
          code' = fromJust $ stripPrefix "[alloy|" code
        in
          take (length code' - 2) code' ++ "\n"
      printAlloyEscape _                        = ""

-- -----------------------------------------------------------------------------
-- the structure of the model

isRoot :: IClafer -> Bool
isRoot c = _uid c == rootIdent

-- | The parent of the clafer, the root for the top-level ones.
parentOf :: GenEnv -> IClafer -> Maybe IClafer
parentOf genEnv c
  | isRoot c     = Nothing
  | isTopLevel c = findIClafer (uidIClaferMap genEnv) rootIdent
  | otherwise    = findIClafer (uidIClaferMap genEnv) $ _parentUID c

-- | A top-level abstract clafer has no containment relation; its instances are those of its subclafers.
hasContainment :: IClafer -> Bool
hasContainment c = not (isRoot c) && not (_isAbstract c && isTopLevel c)

-- | The children that the clafer contains through a containment relation.
containedClafers :: IClafer -> [IClafer]
containedClafers = filter hasContainment . getSubclafers . _elements

-- | Whether the containment relation of the clafer is static: the clafer is final and so
--   are its ancestors, so its instances exist in the whole trace (Juodisius et al., 6.2).
isStatic :: GenEnv -> IClafer -> Bool
isStatic genEnv c
  | isRoot c  = True
  | otherwise = _isFinal c && maybe True (isStatic genEnv) (parentOf genEnv c)

-- | The direct subclafers of the clafer.
subsOf :: GenEnv -> IClafer -> [IClafer]
subsOf genEnv c = [ c' | c' <- allClafers genEnv, getSuper c' == [_uid c] ]

-- | The concrete clafers that are or extend the clafer.
concreteSubs :: GenEnv -> IClafer -> [IClafer]
concreteSubs genEnv c
  | _isAbstract c = concatMap (concreteSubs genEnv) $ subsOf genEnv c
  | otherwise     = [c]

aliveName :: UID -> String
aliveName uid'
  | uid' == rootIdent = rootIdent
  | otherwise         = "alive_" ++ uid'

genRelName :: String -> String
genRelName name = "r_" ++ name

genRefName :: String -> String
genRefName name = name ++ "_ref"

genParentName :: String -> String
genParentName name = "p_" ++ name

-- | The relation from the instances of the clafer to their existing parents. The parent of an
--   instance does not change, so the navigation also works after the instance disappeared.
parentRel :: GenEnv -> UID -> String
parentRel genEnv uid' = case findIClafer (uidIClaferMap genEnv) uid' of
  Just c -> "(" ++ rels c ++ " :> " ++ maybe rootIdent (aliveName . _uid) (parentOf genEnv c) ++ ")"
  Nothing -> error $ "AlloyLtl.parentRel: clafer not found: " ++ uid'
  where
  rels c
    | _isAbstract c = case map (('@' :) . genParentName . _uid) $ concreteSubs genEnv c of
        []    -> "none->none"
        rels' -> "(" ++ intercalate " + " rels' ++ ")"
    | otherwise = '@' : genParentName (_uid c)

mkFact :: Concat -> Concat
mkFact x@(CString "") = x
mkFact xs = cconcat [CString "fact ", mkSet xs, CString "\n"]

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

genClafer :: GenEnv -> IClafer -> Concat
genClafer genEnv c = cunlines (filterNull
  [ claferDecl c (showSet (CString "\n, ") (genRelations genEnv c) +++ optShowSet (filterNull $ genConstraints genEnv c))
  , if isRoot c then CString "" else aliveFun
  , mkFact $ cintercalate (CString "\n  ") $ filterNull $ genStructure genEnv c
  , cconcat $ map (mkAssert genEnv) $ getAssertions c
  ]) +++ CString "\n"
  where
  aliveFun = CString $ "fun " ++ aliveName (_uid c) ++ " : set " ++ _uid c ++ " { " ++ aliveBody ++ " }"
  aliveBody
    | hasContainment c = sigOf (fromJust $ parentOf genEnv c) ++ ".@" ++ genRelName (_uid c)
    | otherwise        = case map (aliveName . _uid) $ subsOf genEnv c of
        []    -> "none"
        alive -> intercalate " + " alive
  sigOf p = if isRoot p then rootIdent else _uid p

claferDecl :: IClafer -> Concat -> Concat
claferDecl    c     rest    = cconcat
  [ CString $ if isRoot c then "one " else ""
  , CString $ if _isAbstract c then "abstract " else ""
  , CString "sig "
  , Concat NoTrace [CString $ _uid c, genExtends $ _super c, CString "\n", rest]
  ]
  where
  genExtends (Just (PExp _ _ _ (IClaferId _ i _ _))) = CString " " +++ Concat NoTrace [CString $ "extends " ++ i]
  genExtends _ = CString ""

-- | The parent, reference and containment fields of the clafer.
genRelations :: GenEnv -> IClafer -> [Concat]
genRelations genEnv c = parent' ++ reference' ++ map mkRel (containedClafers c)
  where
  parent'
    | hasContainment c && not (_isAbstract c) =
        [CString $ genParentName (_uid c) ++ " : lone " ++ maybe rootIdent sigName (parentOf genEnv c)]
    | otherwise = []
  sigName p = if isRoot p then rootIdent else _uid p
  reference' = case _reference c of
    Just r  -> [CString $ var' (isStatic genEnv c && isJust (_refModifier r)) ++ genRefName (_uid c) ++ " : set " ++ refType genEnv c]
    Nothing -> []
  mkRel c' = Concat NoTrace [CString $ var' (isStatic genEnv c') ++ genRelName (_uid c') ++ " : set " ++ _uid c']
  var' static = if static then "" else "var "

refType :: GenEnv -> IClafer -> String
refType genEnv c = case _ref <$> _reference c of
  Just pexp -> case getTarget pexp of
    PExp _ _ _ (IClaferId _ sid _ _) | isPrimitive sid -> "Int"
                                     | otherwise       -> sid
    target -> flatten $ genPExp genEnv [_uid c] target
  Nothing -> ""

getTarget :: PExp -> PExp
getTarget    x     = case x of
  PExp _ _ _ (IFunExp op' (_:pexp:_))  -> if op' == iJoin then pexp else x
  _ -> x

-- | The facts about the instances of the clafer: a fixed parent, which exists; for a nested
--   abstract clafer, its instances are those of its subclafers.
genStructure :: GenEnv -> IClafer -> [Concat]
genStructure genEnv c
  | not (hasContainment c) = []
  | _isAbstract c =
      [ CString $ "always @" ++ rel ++ " = " ++ case map (('@' :) . genRelName . _uid) $ subsOf genEnv c of
          []   -> "none->none"
          rels -> "(" ++ intercalate " + " rels ++ ")" ]
  | otherwise =
      [ CString $ "always ~@" ++ rel ++ " in @" ++ genParentName (_uid c)
      , if isRoot parent' then CString "" else CString $ "always @" ++ rel ++ ".univ in " ++ aliveName (_uid parent')
      ]
  where
  rel = genRelName $ _uid c
  parent' = fromJust $ parentOf genEnv c

-- | The constraints in the signature fact of the clafer, which hold for every existing instance.
genConstraints :: GenEnv -> IClafer -> [Concat]
genConstraints genEnv c = map always' (filterNull $ refConsts ++ groupConst ++ childConsts ++ userConsts) ++ initialConsts ++ finalConsts
  where
  uid' = _uid c
  alive = aliveName uid'
  -- in every snapshot in which this instance exists
  always' x
    | isRoot c  = cconcat [CString "always (", x, CString ")"]
    | otherwise = cconcat [CString "always (this in ", CString alive, CString " implies (", x, CString "))"]
  -- an instance refers to one existing target
  refConsts = case _reference c of
    Just _ ->
      [ CString $ "one this.@" ++ genRefName uid' ] ++
      [ CString $ "this.@" ++ genRefName uid' ++ " in " ++ aliveName target
      | let target = refType genEnv c, target /= "Int", isJust (findIClafer (uidIClaferMap genEnv) target) ]
    Nothing -> []
  groupConst = [ genGroupConst genEnv c ]
  childConsts = concatMap childConst $ containedClafers c
  childConst c' =
    [ mkCard (_uid c') False ("this.@" ++ genRelName (_uid c')) $ fromJust $ _card c'
    , genParentSubrelationConstraint (uidIClaferMap genEnv) c'
    ] ++ genSetUniquenessConstraint c'
  userConsts = [ genPExp genEnv [uid'] pexp | IEConstraint True pexp <- _elements c ]
  -- whenever this instance appears
  initialConsts =
    [ appears $ CString $ "some this.@" ++ genRelName (_uid c') | c' <- containedClafers c, _isInitial c' ]
  appears x
    | isRoot c  = x
    | otherwise = cconcat [CString "always (this in ", CString alive, CString " and not before this in ", CString alive, CString " implies (", x, CString "))"]
  -- the instances of a final child do not change while this instance exists
  finalConsts =
    [ CString $ "always (this in " ++ alive ++ " and after this in " ++ alive ++ " implies (this.@" ++ rel ++ ")' = this.@" ++ rel ++ ")"
    | c' <- containedClafers c, _isFinal c', not (isStatic genEnv c'), let rel = genRelName (_uid c') ] ++
    [ CString $ "always (this in " ++ alive ++ " and after this in " ++ alive ++ " implies (this.@" ++ refRel ++ ")' = this.@" ++ refRel ++ ")"
    | Just r <- [_reference c], isJust (_refModifier r), not (isStatic genEnv c), let refRel = genRefName uid' ]

getAssertions :: IClafer -> [PExp]
getAssertions c = [ pexp | isRoot c, IEConstraint False pexp <- _elements c ]

mkAssert :: GenEnv -> PExp -> Concat
mkAssert genEnv pexp = cconcat
  [ CString "assert ", name, CString " { always (", genPExp genEnv [rootIdent] pexp, CString ") }\n"
  , CString "check ", name, CString " ", CString $ forScopes genEnv, CString "\n\n"
  ]
  where
  name = CString $ "assertOnLine_" ++ show line
  Span (Pos line _) _ = _inPos pexp

genSetUniquenessConstraint :: IClafer -> [Concat]
genSetUniquenessConstraint c = case (_reference c, _card c) of
  (Just (IReference True _ _), Just (lb, ub)) | lb > 1 || ub > 1 || ub == -1 ->
    [ CString $ "all disj x, y : this.@" ++ genRelName (_uid c) ++ " | (x.@" ++ genRefName (_uid c) ++ ") != (y.@" ++ genRefName (_uid c) ++ ")" ]
  _ -> []

genParentSubrelationConstraint :: UIDIClaferMap -> IClafer -> Concat
genParentSubrelationConstraint uidIClaferMap' headClafer = case matchNestedInheritance uidIClaferMap' headClafer of
  Just match@NestedInheritanceMatch{ _superClafer = superClafer }
    | isProperNesting uidIClaferMap' (Just match) && not (isTopLevel superClafer) ->
        CString $ "this.@" ++ genRelName (_uid headClafer) ++ " in this.@" ++ genRelName (_uid superClafer)
  _ -> CString ""

genGroupConst :: GenEnv -> IClafer -> Concat
genGroupConst genEnv clafer'
  | _isAbstract clafer' || null children' || flatten card' == "" = CString ""
  | otherwise = cconcat [CString "let children = ", brArg id $ CString children', CString " | ", card']
  where
  superHierarchy = findHierarchy getSuper (uidIClaferMap genEnv) clafer'
  children' = intercalate " + " $ map (("this.@" ++) . genRelName . _uid) $ getSubclafers $ concatMap _elements superHierarchy
  card' = mkCard (_uid clafer') True "children" $ _interval $ fromJust $ _gcard clafer'

mkCard :: String -> Bool -> String -> (Integer, Integer) -> Concat
mkCard constraintName group' element' crd
  | crd' == "set" || crd' == ""        = CString ""
  | crd' `elem` ["one", "lone", "some"] = CString $ crd' ++ " " ++ element'
  | otherwise                            = interval'
  where
  interval' = genInterval constraintName group' element' crd
  crd'  = flatten interval'

genInterval :: String -> Bool -> String -> Interval -> Concat
genInterval constraintName group' element' x = case x of
  (1, 1)  -> cardConcat constraintName group' [CString "one"]
  (0, 1)  -> cardConcat constraintName group' [CString "lone"]
  (1, -1) -> cardConcat constraintName group' [CString "some"]
  (0, -1) -> CString "set"
  (n, exinteger) ->
    case (s1, s2) of
      (Just c1, Just c2) -> cconcat [c1, CString " and ", c2]
      (Just c1, Nothing) -> c1
      (Nothing, Just c2) -> c2
      (Nothing, Nothing) -> undefined
    where
    element'' = "(" ++ element' ++ ")"
    s1 = if n == 0 then Nothing else Just $ cardLowerConcat constraintName group' [CString $ show n ++ " <= #" ++ element'']
    s2 = cardUpperConcat constraintName group' . (: []) . CString <$> genExInteger element'' x exinteger

cardConcat :: String -> Bool -> [Concat] -> Concat
cardConcat constraintName = Concat . ExactCard constraintName

cardLowerConcat :: String -> Bool -> [Concat] -> Concat
cardLowerConcat constraintName = Concat . LowerCard constraintName

cardUpperConcat :: String -> Bool -> [Concat] -> Concat
cardUpperConcat constraintName = Concat . UpperCard constraintName

genExInteger :: String -> Interval -> Integer -> Maybe Result
genExInteger element' (y, z) x
  | y == 0 && z == 0 = Just $ "#" ++ element' ++ " = 0"
  | x == -1          = Nothing
  | otherwise        = Just $ "#" ++ element' ++ " <= " ++ show x

-- -----------------------------------------------------------------------------
-- expressions; the head of the path is the UID of the context clafer

genPExp :: GenEnv -> [String] -> PExp -> Concat
genPExp genEnv resPath x = genPExp' genEnv resPath $ adjustPExp genEnv resPath x

genPExp' :: GenEnv -> [String] -> PExp                      -> Concat
genPExp'    genEnv    resPath     (PExp iType' pid' pos exp') = case exp' of
  IDeclPExp q d pexp -> Concat (IrPExp pid')
    [ CString $ genQuant q, CString " "
    , cintercalate (CString ", ") $ map (genDecl genEnv resPath) d
    , CString $ optBar d, genPExp' genEnv resPath pexp]
    where
    optBar [] = ""
    optBar _  = " | "
  IClaferId _ "integer" _ _ -> CString "Int"
  IClaferId _ "int" _ _ -> CString "Int"
  IClaferId _ "string" _ _ -> CString "Int"
  IClaferId _ "dref" _ _ -> CString $ "@" ++ genRefName (getTClaferUID iType')
    where
      getTClaferUID (Just TMap{_so = TClafer{_hi = (u:_)}}) = u
      getTClaferUID t = error $ "[bug] AlloyLtl.genPExp'.getTClaferUID: unknown type: " ++ show t
  -- a variable of a quantifier
  IClaferId _ sid _ (LocalBind _) -> CString sid
  IClaferId _ sid istop _ -> CString $
      if head sid `elem` "~@("
        then sid
        else case iType' of
          Just TInteger -> vsident
          Just TDecimal -> vsident
          Just TDouble -> vsident
          Just TReal -> vsident
          Just TString -> vsident
          _ -> sid'
    where
    sid'
      | sid == thisIdent = thisAlive resPath
      | sid == rootIdent = rootIdent
      | istop            = aliveName sid
      | otherwise        = '@' : genRelName sid
    vsident = sid' ++ ".@" ++ genRefName (if sid == thisIdent then head resPath else sid)
  IFunExp _ _ -> case exp'' of
    IFunExp _ _ -> genIFunExp pid' genEnv resPath exp''
    _ -> genPExp' genEnv resPath $ PExp iType' pid' pos exp''
    where
    exp'' = transformExp exp'
  IInt n -> CString $ show n
  IDouble _ -> error "no double numbers allowed"
  IDecimal _ -> error "no decimal numbers allowed"
  IReal _ -> error "no real numbers allowed"
  IStr _ -> error "no strings allowed"

-- | The context instance, as long as it exists.
thisAlive :: [String] -> String
thisAlive (ctx:_) | ctx /= rootIdent = "(this & " ++ aliveName ctx ++ ")"
thisAlive _ = rootIdent

-- | Whether the context instance exists, unless the context is the root, which always exists.
contextExists :: [String] -> Maybe String
contextExists resPath@(ctx:_) | ctx /= rootIdent = Just $ "some " ++ thisAlive resPath
contextExists _ = Nothing

-- | Whether the context instance appears now (its first snapshot), or the trace begins.
appearsNow :: [String] -> String
appearsNow (ctx:_) | ctx /= rootIdent = "not before this in " ++ aliveName ctx
appearsNow _ = "not before some " ++ rootIdent

-- 3-May-2012 Rafael Olaechea.
-- Removed transfromation from x = -2 to x = (0-2) as this creates problem with  partial instances.
-- See http://gsd.uwaterloo.ca:8888/question/461/new-translation-of-negative-number-x-into-0-x-is.
-- Weak until: a W b === G a || a U b
transformExp :: IExp -> IExp
transformExp (IFunExp op' [e1])
  | op' == iMin = IFunExp iMul [PExp (_iType e1) "" noSpan $ IInt (-1), e1]
transformExp    x@(IFunExp op' exps'@(e1:e2:_))
  | op' == iXor = IFunExp iNot [PExp (Just TBoolean) "" noSpan (IFunExp iIff exps')]
  | op' == iW = IFunExp iOr [PExp (Just TBoolean) "" noSpan $ IFunExp iG [e1], PExp (Just TBoolean) "" noSpan x{_op = iU}]
  | op' == iJoin && isClaferName' e1 && isClaferName' e2 &&
    getClaferName e1 == thisIdent && head (getClaferName e2) == '~' =
        IFunExp op' [e1{_iType = Just $ TClafer []}, e2]
  | otherwise  = x
transformExp x = x

genIFunExp :: String -> GenEnv -> [String] -> IExp                  -> Concat
genIFunExp    pid'      genEnv    resPath     (IFunExp "min" [exp']) = Concat (IrPExp pid') [CString "min[", genPExp' genEnv resPath exp', CString "]"]
genIFunExp    pid'      genEnv    resPath     (IFunExp "max" [exp']) = Concat (IrPExp pid') [CString "max[", genPExp' genEnv resPath exp', CString "]"]
-- the navigation starts from the context instance, also after it has disappeared
genIFunExp    pid'      genEnv    resPath     (IFunExp op' [PExp{_exp=IClaferId{_sident=sid}}, exp2])
  | op' == iJoin && sid == thisIdent = Concat (IrPExp pid') [CString "this.", optBrArg genEnv resPath exp2]
  | op' == iJoin && sid == rootIdent = genPExp' genEnv resPath exp2
genIFunExp    pid'      genEnv    resPath     (IFunExp op' [exp'])
  | op' == iInitially = Concat (IrPExp pid') [CString $ "(" ++ appearsNow resPath ++ ") implies ", brArg (genPExp' genEnv resPath) exp']
  | op' == iFinally   = Concat (IrPExp pid') [CString $ "(some " ++ thisAlive resPath ++ " and after no " ++ thisAlive resPath ++ ") implies ", brArg (genPExp' genEnv resPath) exp']
  -- the obligations hold while the context instance exists
  | Just p <- contextExists resPath, op' == iX =
      Concat (IrPExp pid') [CString $ "after (not " ++ p ++ " or ", e, CString ")"]
  | Just p <- contextExists resPath, op' == iF =
      Concat (IrPExp pid') [CString $ "eventually (not " ++ p ++ " or ", e, CString ")"]
  | Just p <- contextExists resPath, op' == iG =
      Concat (IrPExp pid') [CString $ "(not " ++ p ++ ") releases (not " ++ p ++ " or ", e, CString ")"]
  where
  e = brArg (genPExp' genEnv resPath) exp'
genIFunExp    pid'      genEnv    resPath     (IFunExp op' [exp1, exp2])
  | Just p <- contextExists resPath, op' == iU =
      Concat (IrPExp pid') [CString $ "(" ++ p ++ " and ", brArg (genPExp' genEnv resPath) exp1,
                             CString $ ") until (not " ++ p ++ " or ", brArg (genPExp' genEnv resPath) exp2, CString ")"]
genIFunExp    pid'      genEnv    resPath     (IFunExp op' exps')
  | op' == iSumSet = genIFunExp pid' genEnv resPath (IFunExp iSumSet' [removeright (head exps'), getRight $ head exps'])
  | op' == iSumSet' = Concat (IrPExp pid') $ intl exps'' (map CString $ genOp iSumSet)
  | otherwise       = Concat (IrPExp pid') $ intl exps'' (map CString $ genOp op')
  where
      iSumSet' = "sum'"
      intl
        | op' == iSumSet' = flip interleave
        | op' `elem` arithBinOps && length exps' == 2 = interleave
        | otherwise = \xs ys -> reverse $ interleave (reverse xs) (reverse ys)
      exps'' = map (optBrArg genEnv resPath) exps'
genIFunExp _ _ _ x = error $ "[bug] AlloyLtl.genIFunExp: expecting a IFunExp, instead got: " ++ show x

optBrArg :: GenEnv -> [String] -> PExp -> Concat
optBrArg    genEnv    resPath     x     = brFun (genPExp' genEnv resPath) x
  where
  brFun = case x of
    PExp _ _ _ IClaferId{} -> ($)
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
  | op' == iX = ["after "]
  | op' == iF = ["eventually "]
  | op' == iG = ["always "]
  | op' == iU = [" until "]
  | op' == iPlus = [".plus[", "]"]
  | op' == iSub  = [".minus[", "]"]
  | op' == iSumSet = ["sum temp : "," | temp."]
  | op' == iProdSet = ["prod temp : "," | temp."]
  | op' `elem` unOps  = [op']
  | op' == iMul = [".mul[", "]"]
  | op' == iDiv = [".div[", "]"]
  | op' == iRem = [".rem[", "]"]
  | op' `elem` logBinOps ++ relBinOps ++ arithBinOps = [" " ++ op' ++ " "]
  | op' == iUnion = [" + "]
  | op' == iDifference = [" - "]
  | op' == iIntersection = [" & "]
  | op' == iDomain = [" <: "]
  | op' == iRange = [" :> "]
  | op' == iJoin = ["."]
  | op' == iIfThenElse = [" => ", " else "]
genOp op' = error $ "[bug] AlloyLtl.genOp: Unmatched operator: " ++ op'

-- | Replaces the navigation to the parent with the relation to the parent.
adjustPExp :: GenEnv -> [String] -> PExp -> PExp
adjustPExp genEnv resPath (PExp t pid' pos x) = PExp t pid' pos $ adjustIExp genEnv resPath x

adjustIExp :: GenEnv -> [String] -> IExp -> IExp
adjustIExp genEnv resPath x = case x of
  IDeclPExp q d pexp -> IDeclPExp q d $ adjustPExp genEnv resPath pexp
  IFunExp op' exps' -> adjNav $ IFunExp op' $ map adjExps exps'
    where
    (adjNav, adjExps) = if op' == iJoin then (aNav, id)
                        else (id, adjustPExp genEnv resPath)
  IClaferId{} -> aNav x
  _  -> x
  where
  aNav = fst . adjustNav genEnv resPath

adjustNav :: GenEnv -> [String] -> IExp -> (IExp, [String])
adjustNav genEnv resPath x@(IFunExp op' (pexp0:pexp:_))
  | op' == iJoin = (IFunExp iJoin [pexp0{_exp = iexp0}, pexp{_exp = iexp}], path')
  | otherwise   = (x, resPath)
  where
  (iexp0, path) = adjustNav genEnv resPath (_exp pexp0)
  (iexp, path') = adjustNav genEnv (typePath path) (_exp pexp)
  -- the right operand navigates from the clafer of the left one, e.g., a variable @b1@ in @b1.parent@
  typePath p = case _iType pexp0 of
    Just (TClafer (uid':_)) | isJust (findIClafer (uidIClaferMap genEnv) uid') -> uid' : drop 1 p
    _ -> p
adjustNav genEnv resPath x@(IClaferId _ id' _ _)
  | id' == parentIdent = (x{_sident = parentRel genEnv $ head resPath}, parentPath)
  | otherwise          = (x, resPath)
  where
  -- the path continues with the parent of the context clafer
  parentPath = case findIClafer (uidIClaferMap genEnv) (head resPath) >>= parentOf genEnv of
    Just p  -> _uid p : tail resPath
    Nothing -> tail resPath
adjustNav _ _ _ = error "AlloyLtl.adjustNav: expects a IFunExp or IClaferId"

genQuant :: IQuant -> String
genQuant    x       = case x of
  INo   -> "no"
  ILone -> "lone"
  IOne  -> "one"
  ISome -> "some"
  IAll -> "all"

genDecl :: GenEnv -> [String] -> IDecl -> Concat
genDecl    genEnv    resPath     x      = case x of
  IDecl disj locids pexp -> cconcat [CString $ if disj then "disj" else "", CString " ",
    CString $ intercalate ", " locids, CString " : ", genPExp genEnv resPath pexp]

removeright :: PExp -> PExp
removeright (PExp _ _ _ (IFunExp _ (x : PExp _ _ _ IClaferId{} : _))) = x
removeright (PExp _ _ _ (IFunExp _ (x : PExp _ _ _ (IInt _ ) : _))) = x
removeright (PExp _ _ _ (IFunExp _ (x : PExp _ _ _ (IStr _ ) : _))) = x
removeright (PExp _ _ _ (IFunExp _ (x : PExp _ _ _ (IDouble _ ) : _))) = x
removeright (PExp t id' pos (IFunExp o (x1:x2:xs))) = PExp t id' pos (IFunExp o (x1:removeright x2:xs))
removeright x@PExp{} = error $ "[bug] AlloyLtl.removeright: expects a PExp with a IFunExp inside but was given: " ++ show x

getRight :: PExp -> PExp
getRight (PExp _ _ _ (IFunExp _ (_:x:_))) = getRight x
getRight p = p

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
  mapM_ mapLineCol' n
  posEnd   <- gets lineCol
  -- Alloy counts the inner parentheses as part of a constraint, but not the outer ones
  let flat = flatten c
      raiseStart = countLeading "([" flat
      deductEnd = -(countTrailing ")]" flat)
  modify (\s -> s {mapping = (Span (uncurry Pos $ posStart `addColumn` raiseStart) (uncurry Pos $ posEnd `addColumn` deductEnd), srcPos') : mapping s})

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
