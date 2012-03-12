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

(+++) (CString x) (CString y)          = CString $ x ++ y
(+++) x@(CString _) (Concat srcPos xs) = Concat srcPos (x:xs)
(+++) (Concat srcPos xs) x@(CString _) = Concat srcPos (xs ++ [x])
(+++) x@(Concat p xs) y@(Concat p' ys) 
  | p <= p'                            = concatPos (srcPos x)
  | otherwise                          = concatPos (srcPos y)
  where
  concatPos sp = Concat sp [x, y]


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
  output = header args +++ (cconcat $ map (genDeclaration
           (fromJust $ mode args)) (mDecls imodule))


header args = CString $ unlines
    [ if (fromJust $ mode args) == Alloy42 then "" else "open util/integer"
    , "pred show {}"
    , if (fromJust $ validate args) then "" else "run  show for 1"
    , ""]


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

mkMetric goalopname xs = cconcat [CString "metrics ", CString "{ ", if goalopname == iGMax then CString "max" else  CString "min", CString " [", xs, CString " ]",  CString " }" , CString "\n"]

                                                    
mkSet xs = cconcat [CString "{ ", xs, CString " }"]

showSet delim xs = showSet' delim $ filterNull xs
  where
  showSet' _ []     = CString "{}"
  showSet' delim xs = mkSet $ cintercalate delim xs

optShowSet [] = CString ""
optShowSet xs = showSet (CString "\n  ") xs

-- optimization: top level cardinalities
-- optimization: if only boolean parents, then set card is known
genClafer :: ClaferMode -> [String] -> IClafer -> Concat
genClafer mode resPath oClafer = (cunlines $ filterNull
  [ cardFact +++ claferDecl clafer
  , showSet (CString "\n, ") $ genRelations mode clafer
  , optShowSet $ filterNull $ genConstraints mode resPath clafer
  ]) +++ children
  where
  clafer = transPrimitive oClafer
  children = cconcat $ filterNull $ map
             (genClafer mode ((uid clafer) : resPath)) $
             getSubclafers $ elements clafer
  cardFact
    | null resPath && (null $ flatten $ genOptCard clafer) =
        case genCard (uid clafer) $ card clafer of
          "set" -> CString ""
          c -> mkFact $ CString c
    | otherwise = CString ""


transPrimitive clafer = clafer{super = toOverlapping $ super clafer}
  where
  toOverlapping x@(ISuper _ [PExp _ _ _ (IClaferId _ id _)])
    | isPrimitive id = x{isOverlapping = True}
    | otherwise      = x
  toOverlapping x = x

claferDecl clafer = cconcat [genOptCard clafer,
  CString $ genAbstract $ isAbstract clafer, CString "sig ",
  CString $ uid clafer, CString $ genExtends $ super clafer]
  where
  genAbstract isAbstract = if isAbstract then "abstract " else ""
  genExtends (ISuper False [PExp _ _ _ (IClaferId _ "clafer" _)]) = ""
  genExtends (ISuper False [PExp _ _ _ (IClaferId _ id _)]) = " extends " ++ id
  -- todo: handle multiple inheritance
  genExtends (ISuper True  [PExp _ _ _ (IClaferId _ id _)]) = if isPrimitive id then "" else " in " ++ id
  genExtends _ = ""


genOptCard clafer
  | glCard' `elem` ["lone", "one", "some"] = (CString glCard') +++ (CString " ")
  | otherwise                              = CString ""
  where
  glCard' = genIntervalCrude $ glCard clafer
    

isPrimitiveClafer clafer = case super clafer of
  ISuper _ [PExp _ _ _ (IClaferId _ id _)] -> isPrimitive id && (null $ elements clafer)
  _ -> False

-- -----------------------------------------------------------------------------
-- overlapping inheritance is a new clafer with val (unlike only relation)
-- relations: overlapping inheritance (val rel), children
-- adds parent relation
genRelations mode clafer = ref : (map (CString . mkRel) $ getSubclafers $ elements clafer)
  where
  ref = CString $ if isPrimitive $ flatten $ refType mode clafer then
            genRel "ref" clafer {card = Just (1, ExIntegerNum 1)} $
            flatten $ refType mode clafer else ""
  mkRel c = genRel (genRelName $ uid c) c $ uid c


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
genConstraints mode resPath clafer = (CString $ genParentConst resPath clafer) :
  (genGroupConst clafer) : constraints 
  where
  constraints = map genConst $ elements clafer
  genConst x = case x of
    IEConstraint _ pexp  -> genPExp mode ((uid clafer) : resPath) pexp
    IEClafer clafer -> CString $
        if genCardCrude crd `elem` ["one", "lone", "some"]
        then "" else mkCard (genRelName $ uid clafer) $ fromJust crd
      where
      crd = card clafer

-- optimization: if only boolean features then the parent is unique
genParentConst [] _     = ""
genParentConst _ clafer = concat $ genOptParentConst clafer


genOptParentConst clafer
  | glCard' == "one"  = [""]
  | glCard' == "lone" = ["one ", rel]
  | otherwise         = [ "one @", rel, ".this"]
  -- eliminating problems with cyclic containment;
  -- should be added to cases when cyclic containment occurs
  --                    , " && no iden & @", rel, " && no ~@", rel, " & @", rel]
  where
  rel = genRelName $ uid clafer
  glCard' = genIntervalCrude $ glCard clafer


genGroupConst clafer
  | null children || card == "" = CString ""
  | otherwise = cconcat [CString "let children = ", brArg id $ CString children, CString" | ", CString card]
  where
  children = intercalate " + " $ map (genRelName.uid) $
             getSubclafers $ elements clafer
  card     = mkCard "children" $ interval $ fromJust $ gcard $ clafer


mkCard element card
  | card' == "set" || card' == ""        = ""
  | card' `elem` ["one", "lone", "some"] = card' ++ " " ++ element
  | otherwise                            = card'
  where
  card'  = genInterval element card

-- -----------------------------------------------------------------------------
genGCard element gcard = genInterval element  $ interval $ fromJust gcard


genCard element card = genInterval element $ fromJust card


genCardCrude card = genIntervalCrude $ fromJust card


genIntervalCrude x = case x of
  (1, ExIntegerNum 1) -> "one"
  (0, ExIntegerNum 1) -> "lone"
  (1, ExIntegerAst)   -> "some"
  _                   -> "set"


genInterval element x = case x of
  (1, ExIntegerNum 1) -> "one"
  (0, ExIntegerNum 1) -> "lone"
  (1, ExIntegerAst)   -> "some"
  (0, ExIntegerAst)   -> "set"
  (n, exinteger)  ->
    s1 ++ (if null s1 || null s2 then "" else " and") ++ s2
    where
    s1 = if n == 0 then "" else concat [show n, " <= #",  element]
    s2 = genExInteger element exinteger


genExInteger :: String -> ExInteger -> Result
genExInteger element x = case x of
  ExIntegerAst  -> ""
  ExIntegerNum n  -> concat [" #", element, " <= ", show n]


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
{-  IClaferId _ "parent" _  -> Concat pid $
    [brArg id $ (CString $ genRelName $ head resPath) +++ CString ".this"] -}
  IClaferId _ sident isTop -> CString $
      if head sident == '~' then sident else
      if isNothing iType then sident' else case fromJust $ iType of
    TInteger -> vsident
    TReal -> vsident
    TString -> vsident
    _ -> sident'
    where
    sident' = (if isTop then "" else '@' : genRelName "") ++ sident
    vsident = sident' ++ ".@ref"
  IFunExp _ _ -> case exp' of
    IFunExp op exps -> Concat pid $ [genIFunExp mode resPath exp']
    _ -> genPExp' mode resPath $ PExp iType pid pos exp'
    where
    exp' = transformExp exp
  IInt n -> CString $ show n
  IDouble n -> error "no real numbers allowed"
  IStr str -> error "no strings allowed"


transformExp x@(IFunExp op exps@(e1:e2:_))
  | op == iXor = IFunExp iNot [PExp (Just TBoolean) "" noPos (IFunExp iIff exps)]
  | otherwise  = x
transformExp x = x

genIFunExp mode resPath (IFunExp op exps) = cconcat $ intl exps' (map CString $ genOp mode op)
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
mapLineCol' (Concat srcPos nodes) = do
  posStart <- gets lineCol
  mapM mapLineCol' nodes
  posEnd   <- gets lineCol
  modify (\s -> s {mapping = (srcPos, (posStart, posEnd)) : (mapping s)})

lineno (l, c) str = (l + newLines, (if newLines > 0 then firstCol else c) + newCol)
  where
  newLines = length $ filter (== '\n') str
  newCol   = length $ takeWhile (/= '\n') $ reverse str

firstCol  = 1 :: ColNo
firstLine = 1 :: LineNo
