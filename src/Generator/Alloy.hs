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
module Generator.Alloy where
import Data.Char
import Data.List
import Data.Maybe
import Data.Function
import Control.Monad.State

import Common
import ClaferArgs
import Front.Absclafer
import Intermediate.Intclafer
import Intermediate.ResolverType
import Intermediate.ScopeAnalyzer

{-
 - What should Concat srcPos be? Consider the following Alloy snippet
 - 
 -   sig c2_D extends c1_B
 -   { r_c3_C : set c3_C }
 -
 -   sig c3_C
 -   {}
 -   { one @r_c3_C.this }
 -
 -   fact { 6 <= #c13_G and #c13_G <= 7 }
 -   sig c13_G in c1_B
 - 
 -
 -
 - "Sig"
 -   extends c1_B
 -   { r_c3_C : set c3_C }
 -
 - "SubSig"
 -   r_c3_C : set c3_C
 -
 - "Extends"
 -   extends c1_B
 -
 - "In"
 -   in c1_B
 - 
 - "Parent"
 -   one @r_c3_C.this
 -
 - "Cardinality lower c13_G"
 -   6 <= #c13_G
 -
 - "Cardinality upper c13_G"
 -   #c13_G <= 7
 -
 - TODO: examples of the other possible srcPos
 -}

-- representation of strings in chunks (for line/column numbering)
data Concat = CString String | Concat {
  srcPos :: String,
  nodes  :: [Concat]
  } deriving (Eq, Show)

mkConc pos str = Concat pos [CString str]

iscPrimitive x = isPrimitive $ flatten x

flatten :: Concat -> String
flatten (CString x)      = x
flatten (Concat _ nodes) = nodes >>= flatten

(+++) (CString x)     (CString y)      = CString $ x ++ y
(+++) (CString "")    y@Concat{}       = y
(+++) x               (Concat "" ys)   = Concat "" $ x : ys
(+++) x@CString{}     y@Concat{}       = Concat "" $ [x, y]
(+++) x@Concat{}      (CString "")     = x
(+++) (Concat "" xs)  y                = Concat "" $ xs ++ [y]
(+++) x@Concat{}      y@CString{}      = Concat "" $ [x, y]
(+++) x@(Concat p xs) y@(Concat p' ys)
  | p == p'                            = Concat p $ xs ++ ys
  | otherwise                          = Concat "" [x, y]
  
  
cconcat = foldr (+++) (CString "")

cintercalate xs xss = cconcat (intersperse xs xss)

filterNull = filter (not.isNull)

isNull (CString "")  = True
isNull (Concat _ []) = True
isNull _ = False

cunlines xs = cconcat $ map (+++ (CString "\n")) xs

-- Alloy code generation
genModule :: ClaferArgs -> (IModule, GEnv) -> (Result, [(String, Position)])
genModule args (imodule, _) = (flatten output, mapLineCol output)
  where
  output = header args imodule +++ (cconcat $ map (genDeclaration
           (fromJust $ mode args)) (mDecls imodule))


header args imodule = CString $ unlines
    [ if (fromJust $ mode args) == Alloy42 then "" else "open util/integer"
    , "pred show {}"
    , if (fromJust $ validate args) then "" else "run  show for 1" ++ genScopes (scopeAnalysis imodule)
    , ""]
    where
    genScopes scopes = " but " ++ intercalate ", " (map genScope scopes)
    
genScope :: (String, Integer) -> String
genScope (uid, scope) = show scope ++ " " ++ uid


genDeclaration :: ClaferMode -> IElement -> Concat
genDeclaration mode x = case x of
  IEClafer clafer  -> genClafer mode [] clafer
  IEConstraint _ pexp  -> mkFact $ genPExp mode [] pexp
  IEGoal _ pexp@(PExp iType pid pos innerexp) -> case innerexp of 
        IFunExp op  exps ->  if  op == iGMax || op == iGMin then  
                        mkMetric op $ genPExp mode [] (head exps) 
                else 
                        error "unary operator  distinct from (min/max) at the topmost level of a goal element"
        other ->  error "no unary operator (min/max) at the topmost level of a goal element."

mkFact  xs = cconcat [CString "fact ", mkSet xs, CString "\n"]

mkMetric goalopname xs = cconcat [CString "objectives o_global {", if goalopname == iGMax then CString "maximize" else  CString "minimize", CString " [", xs, CString " ]",  CString " }" , CString "\n"]

                                                    
mkSet xs = cconcat [CString "{ ", xs, CString " }"]

showSet delim xs = showSet' delim $ filterNull xs
  where
  showSet' _ []     = CString "{}"
  showSet' delim xs = mkSet $ cintercalate delim xs

optShowSet [] = CString ""
optShowSet xs = CString "\n" +++ showSet (CString "\n  ") xs

-- optimization: top level cardinalities
-- optimization: if only boolean parents, then set card is known
genClafer :: ClaferMode -> [String] -> IClafer -> Concat
genClafer mode resPath oClafer = (cunlines $ filterNull
  [ cardFact +++ claferDecl clafer
        ((showSet (CString "\n, ") $ genRelations mode clafer) +++
        (optShowSet $ filterNull $ genConstraints mode resPath clafer))
  ]) +++ CString "\n" +++ children
  where
  clafer = transPrimitive oClafer
  children = cconcat $ filterNull $ map
             (genClafer mode ((uid clafer) : resPath)) $
             getSubclafers $ elements clafer
  cardFact
    | null resPath && (null $ flatten $ genOptCard clafer) =
        case genCard (uid clafer) $ card clafer of
          CString "set" -> CString ""
          c -> mkFact c
    | otherwise = CString ""


transPrimitive clafer = clafer{super = toOverlapping $ super clafer}
  where
  toOverlapping x@(ISuper _ [PExp _ _ _ (IClaferId _ id _)])
    | isPrimitive id = x{isOverlapping = True}
    | otherwise      = x
  toOverlapping x = x

claferDecl clafer rest = cconcat [genOptCard clafer,
  CString $ genAbstract $ isAbstract clafer, CString "sig ",
  Concat "Sig" [CString $ uid clafer, genExtends $ super clafer, CString "\n", rest]]
  where
  genAbstract isAbstract = if isAbstract then "abstract " else ""
  genExtends (ISuper False [PExp _ _ _ (IClaferId _ "clafer" _)]) = CString ""
  genExtends (ISuper False [PExp _ _ _ (IClaferId _ id _)]) = CString " " +++ Concat "Extends" [CString $ "extends " ++ id]
  -- todo: handle multiple inheritance
  genExtends _ = CString ""


genOptCard clafer
  | glCard' `elem` ["lone", "one", "some"] = cardConcat (uid clafer) [CString glCard'] +++ (CString " ")
  | otherwise                              = CString ""
  where
  glCard' = genIntervalCrude $ glCard clafer
    

-- -----------------------------------------------------------------------------
-- overlapping inheritance is a new clafer with val (unlike only relation)
-- relations: overlapping inheritance (val rel), children
-- adds parent relation
-- 29/March/2012  Rafael Olaechea: ref is now prepended with clafer name to be able to refer to it from partial instances.
genRelations mode clafer = maybeToList ref ++ (map mkRel $ getSubclafers $ elements clafer)
  where
  ref = if isOverlapping $ super clafer then
        Just $ Concat "SubSig" [CString $ genRel (uid  clafer ++ "_ref")  
                                clafer {card = Just (1, ExIntegerNum 1)} $
                                flatten $ refType mode clafer] else Nothing
  mkRel c = Concat "SubSig" [CString $ genRel (genRelName $ uid c) c $ uid c]


genRelName name = "r_" ++ name


genRel name clafer rType = genAlloyRel name (genCardCrude $ card clafer) rType'
  where
  rType' = if isPrimitive rType then "Int" else rType

genAlloyRel name card rType = concat [name, " : ", card, " ", rType]


refType mode c = cintercalate (CString " + ") $ map ((genType mode).getTarget) $ supers $ super c


getTarget :: PExp -> PExp
getTarget x = case x of
  PExp _ _ _ (IFunExp op (pexp0:pexp:_))  -> if op == iJoin then pexp else x
  _ -> x


genType mode x@(PExp _ _ _ y@(IClaferId _ _ _)) = genPExp mode []
  x{Intermediate.Intclafer.exp = y{isTop = True}}
genType mode x = genPExp mode [] x


-- -----------------------------------------------------------------------------
-- constraints
-- user constraints + parent + group constraints + reference
-- a = NUMBER do all x : a | x = NUMBER (otherwise alloy sums a set)
genConstraints mode resPath clafer = (genParentConst resPath clafer) :
  (genGroupConst clafer) : genPathConst mode  (uid clafer ++ "_ref") resPath clafer : constraints 
  where
  constraints = map genConst $ elements clafer
  genConst x = case x of
    IEConstraint _ pexp  -> genPExp mode ((uid clafer) : resPath) pexp
    IEClafer clafer ->
        if genCardCrude crd `elem` ["one", "lone", "some"]
        then CString "" else mkCard ({- do not use the genRelName as the constraint name -} uid clafer) (genRelName $ uid clafer) $ fromJust crd
      where
      crd = card clafer

-- optimization: if only boolean features then the parent is unique
genParentConst [] _     = CString ""
genParentConst _ clafer =  genOptParentConst clafer

genOptParentConst :: IClafer -> Concat
genOptParentConst clafer
  | glCard' == "one"  = CString ""
  | glCard' == "lone" = Concat "Parent-relationship" [CString $ "one " ++ rel]
  | otherwise         = Concat "Parent-relationship" [CString $ "one @" ++ rel ++ ".this"]
  -- eliminating problems with cyclic containment;
  -- should be added to cases when cyclic containment occurs
  --                    , " && no iden & @", rel, " && no ~@", rel, " & @", rel]
  where
  rel = genRelName $ uid clafer
  glCard' = genIntervalCrude $ glCard clafer


genGroupConst clafer
  | null children || flatten card == "" = CString ""
  | otherwise = cconcat [CString "let children = ", brArg id $ CString children, CString" | ", card]
  where
  children = intercalate " + " $ map (genRelName.uid) $
             getSubclafers $ elements clafer
  card     = mkCard ("group " ++ uid clafer) "children" $ interval $ fromJust $ gcard $ clafer


mkCard constraintName element card
  | card' == "set" || card' == ""        = CString ""
  | card' `elem` ["one", "lone", "some"] = CString $ card' ++ " " ++ element
  | otherwise                            = interval'
  where
  interval' = genInterval constraintName element card
  card'  = flatten $ interval'

-- generates expression for references that point to expressions (not single clafers)
genPathConst mode name resPath clafer
  | isRefPath clafer = cconcat [CString name, CString " = ",
                                cintercalate (CString " + ") $
                                map ((brArg id).(genPExp mode resPath)) $
                                supers $ super clafer]
  | otherwise        = CString ""
 
isRefPath clafer = (isOverlapping $ super clafer) &&
                   ((length s > 1) || (not $ isSimplePath s))
  where
  s = supers $ super clafer

isSimplePath :: [PExp] -> Bool
isSimplePath [PExp _ _ _ (IClaferId _ _ _)] = True
isSimplePath [PExp _ _ _ (IFunExp op _)] = op == iUnion
isSimplePath _ = False

-- -----------------------------------------------------------------------------
-- Not used?
-- genGCard element gcard = genInterval element  $ interval $ fromJust gcard


genCard :: String -> Maybe Interval -> Concat
genCard element card = genInterval element element $ fromJust card


genCardCrude card = genIntervalCrude $ fromJust card


genIntervalCrude x = case x of
  (1, ExIntegerNum 1) -> "one"
  (0, ExIntegerNum 1) -> "lone"
  (1, ExIntegerAst)   -> "some"
  _                   -> "set"


genInterval :: String -> String -> Interval -> Concat
genInterval constraintName element x = case x of
  (1, ExIntegerNum 1) -> cardConcat constraintName [CString "one"]
  (0, ExIntegerNum 1) -> cardConcat constraintName [CString "lone"]
  (1, ExIntegerAst)   -> cardConcat constraintName [CString "some"]
  (0, ExIntegerAst)   -> CString "set" -- "set"
  (n, exinteger)  ->
    case (s1, s2) of
      (Just c1, Just c2) -> cconcat [c1, CString " and ", c2]
      (Just c1, Nothing) -> c1
      (Nothing, Just c2) -> c2
      (Nothing, Nothing) -> undefined
    where
    s1 = if n == 0 then Nothing else Just $ cardLowerConcat constraintName [CString $ concat [show n, " <= #",  element]]
    s2 =
        do
            result <- genExInteger element exinteger
            return $ cardUpperConcat constraintName [CString result]


cardConcat :: String -> [Concat] -> Concat
cardConcat constraintName = Concat ("Cardinality exact " ++ constraintName)


cardLowerConcat :: String -> [Concat] -> Concat
cardLowerConcat constraintName = Concat ("Cardinality lower " ++ constraintName)


cardUpperConcat :: String -> [Concat] -> Concat
cardUpperConcat constraintName = Concat ("Cardinality upper " ++ constraintName)


genExInteger :: String -> ExInteger -> Maybe Result
genExInteger element x = case x of
  ExIntegerAst   -> Nothing
  ExIntegerNum n -> Just $ concat ["#", element, " <= ", show n]


-- -----------------------------------------------------------------------------
-- Generate code for logical expressions

genPExp :: ClaferMode -> [String] -> PExp -> Concat
genPExp mode resPath x = genPExp' mode resPath $ adjustPExp resPath x

genPExp' mode resPath x@(PExp iType pid pos exp) = case exp of
  IDeclPExp quant decls pexp -> Concat pid $
    [ CString $ genQuant quant, CString " "
    , cintercalate (CString ", ") $ map ((genDecl mode resPath)) decls
    , CString $ optBar decls, genPExp' mode resPath pexp]
    where
    optBar [] = ""
    optBar _  = " | "
  IClaferId _ sident isTop -> CString $
      if head sident == '~' then sident else
      if isNothing iType then sident' else case fromJust $ iType of
    TInteger -> vsident
    TReal -> vsident
    TString -> vsident
    TRef _ -> vsident
    _ -> sident'
    where
    sident' = (if isTop then "" else '@' : genRelName "") ++ sident
    -- 29/March/2012  Rafael Olaechea: ref is now prepended with clafer name to be able to refer to it from partial instances.
    -- 30/March/2012 Rafael Olaechea added referredClaferUniqeuid to fix problems when having this.x > number  (e.g test/positive/i10.cfr )     
    vsident = sident' ++  ".@"  ++ referredClaferUniqeuid ++ "_ref"
        where referredClaferUniqeuid = if sident == "this" then (head resPath) else sident
  IFunExp _ _ -> case exp' of
    IFunExp op exps -> genIFunExp pid mode resPath exp'
    _ -> genPExp' mode resPath $ PExp iType pid pos exp'
    where
    exp' = transformExp exp
  IInt n -> CString $ show n
  IDouble n -> error "no real numbers allowed"
  IStr str -> error "no strings allowed"


transformExp x@(IFunExp op exps@(e1:e2:_))
  | op == iXor = IFunExp iNot [PExp (Just TBoolean) "" noPos (IFunExp iIff exps)]
  | op == iJoin && isClaferName' e1 && isClaferName' e2 &&
    getClaferName e1 == this && head (getClaferName e2) == '~' =
        IFunExp op [e1{iType = Just TClafer}, e2]
  | otherwise  = x
transformExp x = x

genIFunExp pid mode resPath (IFunExp op exps) = Concat pid $ intl exps' (map CString $ genOp mode op)
  where
  intl
    | op `elem` arithBinOps && length exps == 2 = interleave
    | otherwise = \xs ys -> reverse $ interleave (reverse xs) (reverse ys)
  exps' = map (optBrArg mode resPath) exps


optBrArg mode resPath x = brFun (genPExp' mode resPath) x
  where
  brFun = case x of
    PExp _ _ _ (IClaferId _ _ _) -> ($)
    PExp _ _ _ (IInt _) -> ($)
    _  -> brArg
    

interleave [] [] = []
interleave (x:[]) [] = [x]
interleave [] (x:[]) = [x]
interleave (x:xs) ys = x : interleave ys xs


brArg f arg = cconcat [CString "(", f arg, CString ")"]


genOp Alloy42 op
  | op == iPlus = [".plus[", "]"]
  | op == iSub  = [".minus[", "]"]
  | otherwise   = genOp Alloy op
genOp _ op
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
                   [pexp0{Intermediate.Intclafer.exp = iexp0},
                    pexp{Intermediate.Intclafer.exp = iexp}], path')
  | otherwise   = (x, resPath)
  where
  (iexp0, path) = adjustNav resPath (Intermediate.Intclafer.exp pexp0)
  (iexp, path') = adjustNav path    (Intermediate.Intclafer.exp pexp)
adjustNav resPath x@(IClaferId _ id _)
  | id == parent = (x{sident = "~@" ++ (genRelName $ head resPath)}, tail resPath)
  | otherwise    = (x, resPath)

genQuant :: IQuant -> String
genQuant x = case x of
  INo   -> "no"
  ILone -> "lone"
  IOne  -> "one"
  ISome -> "some"
  IAll -> "all"


genDecl :: ClaferMode -> [String] -> IDecl -> Concat
genDecl mode resPath x = case x of
  IDecl disj locids pexp -> cconcat [CString $ genDisj disj, CString " ",
    CString $ intercalate ", " locids, CString " : ", genPExp mode resPath pexp]


genDisj :: Bool -> String
genDisj x = case x of
  False -> ""
  True  -> "disj"

-- mapping line/columns between Clafer and Alloy code

data AlloyEnv = AlloyEnv {
  lineCol :: (LineNo, ColNo),
  mapping :: [(String, Position)]
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
   - This next little snippet is rather inefficient since we are retraversing the Concat's to flatten.
   - But it's the simplest and correct solution I can think of right now.
   -}
  let flat = flatten c
      raiseStart = countLeading '(' flat
      deductEnd = -(countTrailing ')' flat)
  modify (\s -> s {mapping = (srcPos, (posStart `addColumn` raiseStart, posEnd `addColumn` deductEnd)) : (mapping s)})

addColumn (x, y) c = (x, y + c)
countLeading c xs = length $ takeWhile (== c) xs
countTrailing c xs = countLeading c (reverse xs)

lineno (l, c) str = (l + newLines, (if newLines > 0 then firstCol else c) + newCol)
  where
  newLines = length $ filter (== '\n') str
  newCol   = length $ takeWhile (/= '\n') $ reverse str

firstCol  = 1 :: ColNo
firstLine = 1 :: LineNo
