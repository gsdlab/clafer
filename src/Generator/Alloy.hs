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

import Common
import ClaferArgs
import Front.Absclafer
import Intermediate.Intclafer
import Intermediate.ResolverType

genModule :: ClaferArgs -> (IModule, GEnv) -> Result
genModule args (imodule, _) =
  header args ++ ((mDecls imodule) >>= (genDeclaration (fromJust $ mode args)))


header args = unlines
    [ if (fromJust $ mode args) == Alloy42 then "" else "open util/integer"
    , "pred show {}"
    , if (fromJust $ validate args) then "" else "run  show for 1"
    , ""]


valField = "val"


genDeclaration :: ClaferMode -> IElement -> Result
genDeclaration mode x = case x of
  IEClafer clafer  -> genClafer mode Nothing clafer
  IEConstraint _ pexp  -> mkFact $ genPExp mode Nothing pexp


mkFact xs = concat ["fact ", mkSet xs, "\n"]

mkSet xs = concat ["{ ", xs, " }"]

showSet delim xs = showSet' delim $ filterNull xs
  where
  showSet' _ []     = "{}"
  showSet' delim xs = mkSet $ intercalate delim xs

-- optimization: top level cardinalities
-- optimization: if only boolean parents, then set card is known
genClafer :: ClaferMode -> Maybe IClafer -> IClafer -> Result
genClafer mode parent oClafer
--  | isJust parent && isRef clafer && (not $ isPrimitiveClafer clafer) {- ||
--    (isPrimitiveClafer clafer && isJust parent) -} = ""
{-  | otherwise -}   = (unlines $ filterNull
                   [cardFact ++ claferDecl clafer
                   , showSet "\n, " $ genRelations mode clafer
                   , optShowSet $ filterNull $ genConstraints mode parent clafer
                   ]) ++ children
  where
  clafer = transPrimitive oClafer
  children = concat $ filterNull $ map (genClafer mode $ Just clafer) $
             getSubclafers $ elements clafer
  cardFact
    | isNothing parent && (null $ genOptCard clafer) =
        case genCard (uid clafer) $ card clafer of
          "set" -> ""
          c -> mkFact c
    | otherwise = ""


optShowSet [] = ""
optShowSet xs = showSet "\n  " xs

transPrimitive clafer = clafer{super = toOverlapping $ super clafer}
  where
  toOverlapping x@(ISuper _ [PExp _ _ (IClaferId _ id _)])
    | isPrimitive id = x{isOverlapping = True}
    | otherwise      = x
  toOverlapping x = x

claferDecl clafer = concat [genOptCard clafer,
  genAbstract $ isAbstract clafer, "sig ",
  uid clafer, genExtends $ super clafer]
  where
  genAbstract isAbstract = if isAbstract then "abstract " else ""
  genExtends (ISuper False [PExp _ _ (IClaferId _ "clafer" _)]) = ""
  genExtends (ISuper False [PExp _ _ (IClaferId _ id _)]) = " extends " ++ id
  -- todo: handle multiple inheritance
  genExtends (ISuper True  [PExp _ _ (IClaferId _ id _)]) = if isPrimitive id then "" else " in " ++ id
  genExtends _ = ""


genOptCard clafer
  | glCard' `elem` ["lone", "one", "some"] = glCard' ++ " "
  | otherwise                              = ""
  where
  glCard' = genIntervalCrude $ glCard clafer
    

isPrimitiveClafer clafer = case super clafer of
  ISuper _ [PExp _ _ (IClaferId _ id _)] -> isPrimitive id && (null $ elements clafer)
  _ -> False

-- -----------------------------------------------------------------------------
-- overlapping inheritance is a new clafer with val (unlike only relation)
-- relations: overlapping inheritance (val rel), children
-- adds parent relation
genRelations mode clafer = ref : (map mkRel $ getSubclafers $ elements clafer)
  where
  ref = if isPrimitive $ refType mode clafer then
            genRel "ref" clafer {card = Just (1, ExIntegerNum 1)} $
            refType mode clafer else ""
  mkRel c = genRel (genRelName $ uid c) c $ uid c


genRelName name = "r_" ++ name


genRel name clafer rType = genAlloyRel name (genCardCrude $ card clafer) rType'
  where
  rType' = if isPrimitive rType then "Int" else rType

genAlloyRel name card rType = concat [name, " : ", card, " ", rType]


refType mode c = intercalate " + " $ map ((genType mode).getTarget) $ supers $ super c


getTarget :: PExp -> PExp
getTarget x = case x of
  PExp _ _ (IFunExp op (pexp0:pexp:_))  -> if op == iJoin then pexp else x
  _ -> x


genType mode x@(PExp _ _ y@(IClaferId _ _ _)) = genPExp mode Nothing
  x{Intermediate.Intclafer.exp = y{isTop = True}}
genType mode x = genPExp mode Nothing x


-- -----------------------------------------------------------------------------
-- constraints
-- user constraints + parent + group constraints + reference
-- a = NUMBER do all x : a | x = NUMBER (otherwise alloy sums a set)
genConstraints mode parent clafer = genParentConst parent clafer :
  genGroupConst clafer : constraints 
  where
  constraints = map genConst $ elements clafer
  genConst x = case x of
    IEConstraint _ pexp  -> genPExp mode (Just clafer) pexp
    IEClafer clafer -> if genCardCrude crd `elem` ["one", "lone", "some"]
                         then "" else mkCard (genRelName $ uid clafer) $
                           fromJust crd
      where
      crd = card clafer

-- optimization: if only boolean features then the parent is unique
genParentConst pClafer clafer = maybe ""
                                (const $ concat $ genOptParentConst clafer)
                                pClafer


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


genGroupConst :: IClafer -> Result
genGroupConst clafer
  | null children || card == "" = ""
  | otherwise = "let children = " ++ (brArg id $ children) ++ " | " ++ card
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


genInterval :: String -> Interval -> Result
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

genPExp :: ClaferMode -> Maybe IClafer -> PExp -> Result
genPExp mode clafer x@(PExp iType pid exp) = case exp of
  IDeclPExp quant decls pexp -> concat
    [genQuant quant, " ", intercalate ", " $ map (genDecl mode clafer) decls,
     optBar decls, genPExp mode clafer pexp]
    where
    optBar [] = ""
    optBar _  = " | "
  IClaferId _ "parent" _  ->
    brArg id $ (genRelName $ uid $ fromJust clafer) ++ ".this"
  IClaferId _ sident isTop -> if isNothing iType then sident' else case fromJust $ iType of
    TInteger -> vsident
    TReal -> vsident
    TString -> vsident
    _ -> sident'
    where
    sident' = (if isTop then "" else '@' : genRelName "") ++ sident
    vsident = sident' ++ ".@ref"
  IFunExp _ _ -> case exp' of
    IFunExp op exps -> genIFunExp mode clafer exp'
    _ -> genPExp mode clafer $ PExp iType pid exp'
    where
    exp' = transformExp exp
  IInt n -> show n
  IDouble n -> error "no real numbers allowed"
  IStr str -> error "no strings allowed"


transformExp x@(IFunExp op exps@(e1:e2:_))
  | op == iXor = IFunExp iNot [PExp (Just TBoolean) "" (IFunExp iIff exps)]
  | otherwise  = x
transformExp x = x


genIFunExp mode clafer (IFunExp op exps) = concat $ intl exps' (genOp mode op)
  where
  intl
    | op `elem` arithBinOps && length exps == 2 = interleave
    | otherwise = \xs ys -> reverse $ interleave (reverse xs) (reverse ys)
  exps' = map (optBrArg mode clafer) exps


optBrArg mode clafer x = brFun (genPExp mode clafer) x
  where
  brFun = case x of
    PExp _ _ (IClaferId _ _ _) -> ($)
    PExp _ _ (IInt _) -> ($)
    _  -> brArg


interleave [] [] = []
interleave (x:[]) [] = [x]
interleave [] (x:[]) = [x]
interleave (x:xs) ys = x : interleave ys xs


brArg f arg = "(" ++ f arg ++ ")"


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

genQuant :: IQuant -> Result
genQuant x = case x of
  INo   -> "no"
  ILone -> "lone"
  IOne  -> "one"
  ISome -> "some"
  IAll -> "all"


genDecl :: ClaferMode -> Maybe IClafer -> IDecl -> Result
genDecl mode clafer x = case x of
  IDecl disj locids pexp -> concat [genDisj disj, " ",
    intercalate ", " locids, " : ", genPExp mode clafer pexp]


genDisj :: Bool -> Result
genDisj x = case x of
  False -> ""
  True  -> "disj"
