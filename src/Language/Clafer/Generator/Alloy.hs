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
module Language.Clafer.Generator.Alloy where
import Data.Char
import Data.List
import Data.Maybe
import Data.Function
import Control.Monad.State

import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ScopeAnalysis

-- representation of strings in chunks (for line/column numbering)
data Concat = CString String | Concat {
  srcPos :: IrTrace,
  nodes  :: [Concat]
  } deriving (Eq, Show)
type Position = ((LineNo, ColNo), (LineNo, ColNo))

data IrTrace =
    IrPExp {pUid::String} |
    LowerCard {pUid::String, isGroup::Bool} |
    UpperCard {pUid::String, isGroup::Bool} |
    ExactCard {pUid::String, isGroup::Bool} |
    NoTrace
    deriving (Eq, Show)


mkConcat pos str = Concat pos [CString str]

iscPrimitive x = isPrimitive $ flatten x

flatten :: Concat -> String
flatten (CString x)      = x
flatten (Concat _ nodes) = nodes >>= flatten

(+++) (CString x)     (CString y)     = CString $ x ++ y
(+++) (CString "")    y@Concat{}      = y
(+++) x               y@(Concat src ys)
    | src == NoTrace = Concat NoTrace $ x : ys
    | otherwise      = Concat NoTrace $ [x, y]
(+++) x@Concat{}      (CString "")     = x
(+++) x@(Concat src xs)  y
    | src == NoTrace = Concat NoTrace $ xs ++ [y]
    | otherwise      = Concat NoTrace $ [x, y]
  
  
cconcat = foldr (+++) (CString "")

cintercalate xs xss = cconcat (intersperse xs xss)

filterNull = filter (not.isNull)

isNull (CString "")  = True
isNull (Concat _ []) = True
isNull _ = False

cunlines xs = cconcat $ map (+++ (CString "\n")) xs

-- Alloy code generation
-- 07th Mayo 2012 Rafael Olaechea 
--      Added Logic to print a goal block in case there is at least one goal.
genModule :: ClaferArgs -> (IModule, GEnv) -> (Result, [(Span, IrTrace)])
genModule    claferargs    (imodule, _)     = (flatten output, filter ((/= NoTrace) . snd) $ mapLineCol output)
  where
  output = header claferargs imodule +++ (cconcat $ map (genDeclaration claferargs) (mDecls imodule)) +++ 
       if length goals_list > 0 then 
                CString "objectives o_global {\n" +++   (cintercalate (CString ",\n") goals_list) +++   CString "\n}" 
       else  
                CString "" 
       where 
                goals_list = filterNull (map (genDeclarationGoalsOnly claferargs) (mDecls imodule))

header :: ClaferArgs -> IModule -> Concat
header    args          imodule  = CString $ unlines
    [ if (fromJust $ mode args) == Alloy42 then "" else "open util/integer"
    , "pred show {}"
    , if (fromJust $ validate args) ||  (fromJust $ noalloyruncommand args)  
      then "" 
      else "run show for 1" ++ genScopes (getScopeStrategy (scope_strategy args) imodule)
    , ""]
    where
    genScopes [] = ""
    genScopes scopes = " but " ++ intercalate ", " (map genScope scopes)
    
genScope :: (String, Integer) -> String
genScope    (uid, scope)       = show scope ++ " " ++ uid


-- 07th Mayo 2012 Rafael Olaechea
-- Modified so that we can collect all goals into a single block as required per the way goals are handled in modified alloy.
genDeclarationGoalsOnly :: ClaferArgs -> IElement -> Concat
genDeclarationGoalsOnly    claferargs    x         = case x of
  IEClafer clafer  -> CString ""
  IEConstraint _ pexp  -> CString ""
  IEGoal _ pexp@(PExp iType pid pos innerexp) -> case innerexp of 
        IFunExp op  exps ->  if  op == iGMax || op == iGMin then  
                        mkMetric op $ genPExp claferargs [] (head exps) 
                else 
                        error "unary operator  distinct from (min/max) at the topmost level of a goal element"
        other ->  error "no unary operator (min/max) at the topmost level of a goal element."

-- 07th Mayo 2012 Rafael Olaechea
-- Removed goal from this function as they will now  all be collected into a single block.       
genDeclaration :: ClaferArgs -> IElement -> Concat
genDeclaration claferargs x = case x of
  IEClafer clafer  -> genClafer claferargs [] clafer
  IEConstraint _ pexp  -> mkFact $ genPExp claferargs [] pexp
  IEGoal _ pexp@(PExp iType pid pos innerexp) -> case innerexp of 
        IFunExp op  exps ->  if  op == iGMax || op == iGMin then  
                       CString ""
                else 
                        error "unary operator  distinct from (min/max) at the topmost level of a goal element"
        other ->  error "no unary operator (min/max) at the topmost level of a goal element."

mkFact  xs = cconcat [CString "fact ", mkSet xs, CString "\n"]

mkMetric goalopname xs = cconcat [ if goalopname == iGMax then CString "maximize" else  CString "minimize", CString " ", xs, CString " "]

                                                    
mkSet xs = cconcat [CString "{ ", xs, CString " }"]

showSet delim xs = showSet' delim $ filterNull xs
  where
  showSet' _ []     = CString "{}"
  showSet' delim xs = mkSet $ cintercalate delim xs

optShowSet [] = CString ""
optShowSet xs = CString "\n" +++ showSet (CString "\n  ") xs

-- optimization: top level cardinalities
-- optimization: if only boolean parents, then set card is known
genClafer :: ClaferArgs -> [String] -> IClafer -> Concat
genClafer claferargs resPath oClafer = (cunlines $ filterNull
  [ cardFact +++ claferDecl clafer
        ((showSet (CString "\n, ") $ genRelations claferargs clafer) +++
        (optShowSet $ filterNull $ genConstraints claferargs resPath clafer))
  ]) +++ CString "\n" +++ children
  where
  clafer = transPrimitive oClafer
  children = cconcat $ filterNull $ map
             (genClafer claferargs ((uid clafer) : resPath)) $
             getSubclafers $ elements clafer
  cardFact
    | null resPath && (null $ flatten $ genOptCard clafer) =
        case genCard (uid clafer) $ card clafer of
          CString "set" -> CString ""
          c -> mkFact c
    | otherwise = CString ""

transPrimitive :: IClafer -> IClafer
transPrimitive    clafer   = clafer{super = toOverlapping $ super clafer}
  where
  toOverlapping x@(ISuper _ [PExp _ _ _ (IClaferId _ id _)])
    | isPrimitive id = x{isOverlapping = True}
    | otherwise      = x
  toOverlapping x = x

claferDecl :: IClafer -> Concat -> Concat
claferDecl    clafer     rest    = cconcat [genOptCard clafer,
  CString $ genAbstract $ isAbstract clafer, CString "sig ",
  Concat NoTrace [CString $ uid clafer, genExtends $ super clafer, CString "\n", rest]]
  where
  genAbstract isAbstract = if isAbstract then "abstract " else ""
  genExtends (ISuper False [PExp _ _ _ (IClaferId _ "clafer" _)]) = CString ""
  genExtends (ISuper False [PExp _ _ _ (IClaferId _ id _)]) = CString " " +++ Concat NoTrace [CString $ "extends " ++ id]
  -- todo: handle multiple inheritance
  genExtends _ = CString ""

genOptCard :: IClafer -> Concat
genOptCard    clafer
  | glCard' `elem` ["lone", "one", "some"] = cardConcat (uid clafer) False [CString glCard'] +++ (CString " ")
  | otherwise                              = CString ""
  where
  glCard' = genIntervalCrude $ glCard clafer
    

-- -----------------------------------------------------------------------------
-- overlapping inheritance is a new clafer with val (unlike only relation)
-- relations: overlapping inheritance (val rel), children
-- adds parent relation
-- 29/March/2012  Rafael Olaechea: ref is now prepended with clafer name to be able to refer to it from partial instances.
genRelations claferargs clafer = maybeToList ref ++ (map mkRel $ getSubclafers $ elements clafer)
  where
  ref = if isOverlapping $ super clafer 
                then
                        Just $ Concat NoTrace [CString $ genRel (if (fromJust $ noalloyruncommand claferargs) then  (uid clafer ++ "_ref") else "ref")
                         clafer {card = Just (1, 1)} $ 
                         flatten $ refType claferargs clafer] 
                else 
                        Nothing
  mkRel c = Concat NoTrace [CString $ genRel (genRelName $ uid c) c $ uid c]


genRelName name = "r_" ++ name


genRel name clafer rType = genAlloyRel name (genCardCrude $ card clafer) rType'
  where
  rType' = if isPrimitive rType then "Int" else rType

genAlloyRel name card rType = concat [name, " : ", card, " ", rType]


refType claferargs c = cintercalate (CString " + ") $ map ((genType claferargs).getTarget) $ supers $ super c


getTarget :: PExp -> PExp
getTarget    x     = case x of
  PExp _ _ _ (IFunExp op (pexp0:pexp:_))  -> if op == iJoin then pexp else x
  _ -> x

genType :: ClaferArgs -> PExp                              -> Concat
genType    claferargs    x@(PExp _ _ _ y@(IClaferId _ _ _)) = genPExp claferargs []
  x{Language.Clafer.Intermediate.Intclafer.exp = y{isTop = True}}
genType mode x = genPExp mode [] x


-- -----------------------------------------------------------------------------
-- constraints
-- user constraints + parent + group constraints + reference
-- a = NUMBER do all x : a | x = NUMBER (otherwise alloy sums a set)
genConstraints :: ClaferArgs -> [String]      -> IClafer -> [Concat]
genConstraints    claferargs    resPath clafer = (genParentConst resPath clafer) :
  (genGroupConst clafer) : genPathConst claferargs  (if (fromJust $ noalloyruncommand claferargs) then  (uid clafer ++ "_ref") else "ref") resPath clafer : constraints 
  where
  constraints = map genConst $ elements clafer
  genConst x = case x of
    IEConstraint _ pexp  -> genPExp claferargs ((uid clafer) : resPath) pexp
    IEClafer clafer ->
        if genCardCrude crd `elem` ["one", "lone", "some"]
        then CString "" else mkCard ({- do not use the genRelName as the constraint name -} uid clafer) False (genRelName $ uid clafer) $ fromJust crd
      where
      crd = card clafer

-- optimization: if only boolean features then the parent is unique
genParentConst [] _     = CString ""
genParentConst _ clafer =  genOptParentConst clafer

genOptParentConst :: IClafer -> Concat
genOptParentConst    clafer
  | glCard' == "one"  = CString ""
  | glCard' == "lone" = Concat NoTrace [CString $ "one " ++ rel]
  | otherwise         = Concat NoTrace [CString $ "one @" ++ rel ++ ".this"]
  -- eliminating problems with cyclic containment;
  -- should be added to cases when cyclic containment occurs
  --                    , " && no iden & @", rel, " && no ~@", rel, " & @", rel]
  where
  rel = genRelName $ uid clafer
  glCard' = genIntervalCrude $ glCard clafer

genGroupConst :: IClafer -> Concat
genGroupConst    clafer
  | null children || flatten card == "" = CString ""
  | otherwise = cconcat [CString "let children = ", brArg id $ CString children, CString" | ", card]
  where
  children = intercalate " + " $ map (genRelName.uid) $
             getSubclafers $ elements clafer
  card     = mkCard (uid clafer) True "children" $ interval $ fromJust $ gcard $ clafer


mkCard constraintName group element card
  | card' == "set" || card' == ""        = CString ""
  | card' `elem` ["one", "lone", "some"] = CString $ card' ++ " " ++ element
  | otherwise                            = interval'
  where
  interval' = genInterval constraintName group element card
  card'  = flatten $ interval'

-- generates expression for references that point to expressions (not single clafers)
genPathConst :: ClaferArgs -> String -> [String] -> IClafer -> Concat
genPathConst    claferargs    name      resPath     clafer
  | isRefPath clafer = cconcat [CString name, CString " = ",
                                cintercalate (CString " + ") $
                                map ((brArg id).(genPExp claferargs resPath)) $
                                supers $ super clafer]
  | otherwise        = CString ""
 
isRefPath clafer = (isOverlapping $ super clafer) &&
                   ((length s > 1) || (not $ isSimplePath s))
  where
  s = supers $ super clafer

isSimplePath :: [PExp] -> Bool
isSimplePath    [PExp _ _ _ (IClaferId _ _ _)] = True
isSimplePath    [PExp _ _ _ (IFunExp op _)] = op == iUnion
isSimplePath    _ = False

-- -----------------------------------------------------------------------------
-- Not used?
-- genGCard element gcard = genInterval element  $ interval $ fromJust gcard


genCard :: String -> Maybe Interval -> Concat
genCard    element   card            = genInterval element False element $ fromJust card


genCardCrude card = genIntervalCrude $ fromJust card


genIntervalCrude x = case x of
  (1, 1) -> "one"
  (0, 1) -> "lone"
  (1, -1) -> "some"
  _                   -> "set"


genInterval :: String      -> Bool -> String -> Interval -> Concat
genInterval    constraintName group   element   x         = case x of
  (1, 1) -> cardConcat constraintName group [CString "one"]
  (0, 1) -> cardConcat constraintName group [CString "lone"]
  (1, -1)   -> cardConcat constraintName group [CString "some"]
  (0, -1)   -> CString "set" -- "set"
  (n, exinteger)  ->
    case (s1, s2) of
      (Just c1, Just c2) -> cconcat [c1, CString " and ", c2]
      (Just c1, Nothing) -> c1
      (Nothing, Just c2) -> c2
      (Nothing, Nothing) -> undefined
    where
    s1 = if n == 0 then Nothing else Just $ cardLowerConcat constraintName group [CString $ concat [show n, " <= #",  element]]
    s2 =
        do
            result <- genExInteger element exinteger
            return $ cardUpperConcat constraintName group [CString result]


cardConcat :: String        -> Bool -> [Concat] -> Concat
cardConcat    constraintName = Concat . ExactCard constraintName


cardLowerConcat :: String        -> Bool -> [Concat] -> Concat
cardLowerConcat    constraintName = Concat . LowerCard constraintName


cardUpperConcat :: String        -> Bool -> [Concat] -> Concat
cardUpperConcat    constraintName = Concat . UpperCard constraintName


genExInteger :: String -> Integer -> Maybe Result
genExInteger    element   x        =
  if x == -1 then Nothing else Just $ concat ["#", element, " <= ", show x]


-- -----------------------------------------------------------------------------
-- Generate code for logical expressions

genPExp :: ClaferArgs -> [String] -> PExp -> Concat
genPExp    claferargs    resPath     x     = genPExp' claferargs resPath $ adjustPExp resPath x

genPExp' :: ClaferArgs -> [String] -> PExp                      -> Concat
genPExp'    claferargs    resPath     x@(PExp iType pid pos exp) = case exp of
  IDeclPExp quant decls pexp -> Concat (IrPExp pid) $
    [ CString $ genQuant quant, CString " "
    , cintercalate (CString ", ") $ map ((genDecl claferargs resPath)) decls
    , CString $ optBar decls, genPExp' claferargs resPath pexp]
    where
    optBar [] = ""
    optBar _  = " | "
  IClaferId _ "ref" _ -> CString "@ref"
  IClaferId _ sident isTop -> CString $
      if head sident == '~' then sident else
      if isNothing iType then sident' else case fromJust $ iType of
    TInteger -> vsident
    TReal -> vsident
    TString -> vsident
    _ -> sident'
    where
    sident' = (if isTop then "" else '@' : genRelName "") ++ sident
    -- 29/March/2012  Rafael Olaechea: ref is now prepended with clafer name to be able to refer to it from partial instances.
    -- 30/March/2012 Rafael Olaechea added referredClaferUniqeuid to fix problems when having this.x > number  (e.g test/positive/i10.cfr )     
    vsident = if (fromJust $ noalloyruncommand claferargs) then sident' ++  ".@"  ++ referredClaferUniqeuid ++ "_ref"  else  sident'  ++ ".@ref"
        where referredClaferUniqeuid = if sident == "this" then (head resPath) else sident
  IFunExp _ _ -> case exp' of
    IFunExp op exps -> genIFunExp pid claferargs resPath exp'
    _ -> genPExp' claferargs resPath $ PExp iType pid pos exp'
    where
    exp' = transformExp exp
  IInt n -> CString $ show n
  IDouble n -> error "no real numbers allowed"
  IStr str -> error "no strings allowed"



-- 3-May-2012 Rafael Olaechea.
-- Removed transfromation from x = -2 to x = (0-2) as this creates problem with  partial instances.
-- See http://gsd.uwaterloo.ca:8888/question/461/new-translation-of-negative-number-x-into-0-x-is.
transformExp :: IExp -> IExp
transformExp    x@(IFunExp op exps@(e1:e2:_))
  | op == iXor = IFunExp iNot [PExp (Just TBoolean) (genPExpName noSpan (IFunExp iIff exps)) noSpan (IFunExp iIff exps)]
  | op == iJoin && isClaferName' e1 && isClaferName' e2 &&
    getClaferName e1 == this && head (getClaferName e2) == '~' =
        IFunExp op [e1{iType = Just $ TClafer []}, e2]
  | otherwise  = x
transformExp x = x

genIFunExp :: String -> ClaferArgs -> [String] -> IExp             -> Concat
genIFunExp    pid       claferargs    resPath     (IFunExp op exps) = Concat (IrPExp pid) $ intl exps' (map CString $ genOp (fromJust $ mode (claferargs :: ClaferArgs)) op)
  where
  intl
    | op `elem` arithBinOps && length exps == 2 = interleave
    | otherwise = \xs ys -> reverse $ interleave (reverse xs) (reverse ys)
  exps' = map (optBrArg claferargs resPath) exps


optBrArg :: ClaferArgs -> [String] -> PExp -> Concat
optBrArg    claferargs    resPath     x     = brFun (genPExp' claferargs resPath) x
  where
  brFun = case x of
    PExp _ _ _ (IClaferId _ _ _) -> ($)
    PExp _ _ _ (IInt _) -> ($)
    _  -> brArg
    

interleave [] [] = []
interleave (x:xs) [] = x:xs
interleave [] (x:xs) = x:xs
interleave (x:xs) ys = x : interleave ys xs


brArg f arg = cconcat [CString "(", f arg, CString ")"]

genOp :: ClaferMode -> [Char] -> [[Char]]
genOp    Alloy42       op
  | op == iPlus = [".plus[", "]"]
  | op == iSub  = [".minus[", "]"]
  | otherwise   = genOp Alloy op
genOp    _             op
  | op `elem` unOps = [op]
  | op == iPlus = [".add[", "]"]
  | op == iSub  = [".sub[", "]"]
  | op == iMul = [".mul[", "]"]
  | op == iDiv = [".div[", "]"]
  | op `elem` logBinOps ++ relBinOps ++ arithBinOps = [" " ++ op ++ " "]
  | op == iUnion = [" + "]
  | op == iDifference = [" - "]
  | op == iIntersection = [" & "]
  | op == iDomain = [" <: "]
  | op == iRange = [" :> "]
  | op == iJoin = ["."]
  | op == iIfThenElse = [" => ", " else "]

-- adjust parent
adjustPExp :: [String] -> PExp -> PExp
adjustPExp resPath (PExp t pid pos x) = PExp t pid pos $ adjustIExp resPath x

adjustIExp resPath x = case x of
  IDeclPExp quant decls pexp -> IDeclPExp quant decls $ adjustPExp resPath pexp
  IFunExp op exps -> adjNav $ IFunExp op $ map adjExps exps
    where
    (adjNav, adjExps) = if op == iJoin then (aNav, id)
                        else (id, adjustPExp resPath)
  IClaferId _ _ _ -> aNav x
  _  -> x
  where
  aNav = fst.(adjustNav resPath)

adjustNav resPath x@(IFunExp op (pexp0:pexp:_))
  | op == iJoin = (IFunExp iJoin
                   [pexp0{Language.Clafer.Intermediate.Intclafer.exp = iexp0},
                    pexp{Language.Clafer.Intermediate.Intclafer.exp = iexp}], path')
  | otherwise   = (x, resPath)
  where
  (iexp0, path) = adjustNav resPath (Language.Clafer.Intermediate.Intclafer.exp pexp0)
  (iexp, path') = adjustNav path    (Language.Clafer.Intermediate.Intclafer.exp pexp)
adjustNav resPath x@(IClaferId _ id _)
  | id == parent = (x{sident = "~@" ++ (genRelName $ head resPath)}, tail resPath)
  | otherwise    = (x, resPath)

genQuant :: IQuant -> String
genQuant    x       = case x of
  INo   -> "no"
  ILone -> "lone"
  IOne  -> "one"
  ISome -> "some"
  IAll -> "all"


genDecl :: ClaferArgs -> [String] -> IDecl -> Concat
genDecl    claferargs    resPath     x      = case x of
  IDecl disj locids pexp -> cconcat [CString $ genDisj disj, CString " ",
    CString $ intercalate ", " locids, CString " : ", genPExp claferargs resPath pexp]


genDisj :: Bool -> String
genDisj    x     = case x of
  False -> ""
  True  -> "disj"

-- mapping line/columns between Clafer and Alloy code

data AlloyEnv = AlloyEnv {
  lineCol :: (LineNo, ColNo),
  mapping :: [(Span, IrTrace)]
  } deriving (Eq,Show)

mapLineCol code = mapping $ execState (mapLineCol' code) (AlloyEnv (firstLine, firstCol) [])

addCode str = modify (\s -> s {lineCol = lineno (lineCol s) str})

mapLineCol' (CString str) = addCode str
mapLineCol' c@(Concat srcPos nodes) = do
  posStart <- gets lineCol
  mapM mapLineCol' nodes
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
  modify (\s -> s {mapping = (Span (uncurry Pos $ posStart `addColumn` raiseStart) (uncurry Pos $ posEnd `addColumn` deductEnd), srcPos) : (mapping s)})


addColumn (x, y) c = (x, y + c)
countLeading c xs = toInteger $ length $ takeWhile (`elem` c) xs
countTrailing c xs = countLeading c (reverse xs)

lineno (l, c) str = (l + newLines, (if newLines > 0 then firstCol else c) + newCol)
  where
  newLines = toInteger $ length $ filter (== '\n') str
  newCol   = toInteger $ length $ takeWhile (/= '\n') $ reverse str

firstCol  = 1 :: ColNo
firstLine = 1 :: LineNo
