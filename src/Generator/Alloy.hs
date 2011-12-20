{-
 This file is part of the Clafer Translator (clafer).

 Copyright (C) 2010 Kacper Bak <http://gsd.uwaterloo.ca/kbak>

 clafer is free software: you can redistribute it and/or modify
 it under the terms of the GNU Lesser General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 clafer is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Lesser General Public License for more details.

 You should have received a copy of the GNU Lesser General Public License
 along with clafer. (See files COPYING and COPYING.LESSER.)  If not,
 see <http://www.gnu.org/licenses/>.
-}
module Generator.Alloy where

import Data.Char
import Data.List
import Data.Maybe
import Data.Function

import Common
import Front.Absclafer
import Intermediate.Intclafer
import Intermediate.ResolverType

genModule :: ClaferMode -> (IModule, GEnv) -> Result
genModule mode (imodule, _) =
  header ++ ((mDecls imodule) >>= (genDeclaration mode))


header = unlines
    [ "pred show {}"
    , "run  show for 1"
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
  | isJust parent && isRef clafer && (not $ isPrimitiveClafer clafer) {- ||
    (isPrimitiveClafer clafer && isJust parent) -} = ""
  | otherwise    = (unlines $ filterNull
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

claferDecl clafer = concat [genOptCard clafer,
  genAbstract $ isAbstract clafer, "sig ",
  uid clafer, genExtends $ super clafer]
  where
  genAbstract isAbstract = if isAbstract then "abstract " else ""
  genExtends (ISuper False [PExp _ _ (IClaferId _ "clafer" _)]) = ""
  genExtends (ISuper False [PExp _ _ (IClaferId _ id _)]) = " extends " ++ id
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
  ref = if isOverlapping $ super clafer then
          genRel "ref" clafer {card = Just (1, ExIntegerNum 1)} $
                 refType mode clafer
        else ""
  mkRel c = genRel (genRelName $ uid c) c $
            (if isRef c {- || isPrimitiveClafer c-} then (refType mode) else uid) c


genRelName name = "r_" ++ name


genRel name clafer rType = genAlloyRel name (genCardCrude $ card clafer) rType'
  where
  rType' = if isPrimitive rType then "Int" else rType

-- optimization: direct ref to Int attribute (no new clafer)
-- reference clafers as relations


isRef clafer = (null $ elements clafer) && (isOverlapping $ super clafer)


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
  genGroupConst clafer : genPathConst mode "ref" clafer : refs ++ constraints 
  where
  constraints = map genConst $ elements clafer
  genConst x = case x of
    IEConstraint _ pexp  -> genPExp mode (Just clafer) pexp
    IEClafer clafer -> if genCardCrude crd `elem` ["one", "lone", "some"]
                         then "" else mkCard (genRelName $ uid clafer) $
                           fromJust crd
      where
      crd = card clafer
  refs = map (\c -> genPathConst mode (genRelName $ uid c) c) $
         filter isRefPath $ filter isRef $ getSubclafers $ elements clafer

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


genPathConst mode name clafer
  | isRefPath clafer = name ++ " = " ++ (intercalate " + " $
                       map ((brArg id).(genPExp mode $ Just clafer)) $
                       supers $ super clafer)
  | otherwise        = ""


isRefPath clafer = (isOverlapping $ super clafer) &&
                   ((length s > 1) || (not $ isSimplePath s))
  where
  s = supers $ super clafer


isSimplePath :: [PExp] -> Bool
isSimplePath [PExp _ _ (IClaferId _ _ _)] = True
isSimplePath [PExp _ _ (IFunExp op _)] = op == iUnion
isSimplePath _ = False

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
  IClaferId _ sident isTop -> if isNothing iType then error sident else case fromJust $ iType of
    INumeric _ -> vsident
    IString  _ -> vsident
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
  | op == iXor = IFunExp iNot [PExp (Just IBoolean) "" (IFunExp iIff exps)]
  | op `elem` relGenBinOps && not (isSpecialExp e1 || isSpecialExp e2) =
    case (fromJust $ iType e1, fromJust $ iType e2) of
      (ISet, INumeric (Just IInteger)) -> if e1 == (locCl' locRef) then x else
                                             mkNumExp locId op e1 (locCl' locRef) e2
      (INumeric (Just IInteger), ISet) -> if e2 == (locCl' locRef) then x else
                                             mkNumExp locId op e1 e2 (locCl' locRef)
      (INumeric (Just ISetInteger), INumeric (Just ISetInteger)) ->
        if e1 == locCl' locRef then x else mkNumExps
        [("cl0", e1), ("cl1", e2)] op (locCl' "cl0.@ref") (locCl' "cl1.@ref")
      (INumeric (Just ISetReal), INumeric (Just ISetReal)) ->
        if e1 == locCl' locRef then x else mkNumExps
        [("cl0", e1), ("cl1", e2)] op (locCl' "cl0.@ref") (locCl' "cl1.@ref")
      _ -> x
  | otherwise = x
  where
  locId = "cl0"
  locRef = locId ++ ".@ref"
  locCl = locCl' locId
  locCl' locId = PExp (Just ISet) "" (IClaferId "" locId True)
transformExp x = x


isSpecialExp (PExp _ _ (IClaferId _ id _)) = id `elem` [this, parent]
isSpecialExp _ = False

mkNumExp locId op e1 e2 e3 = mkNumExps [(locId, e1)] op e2 e3

mkNumExps locExps op e2 e3 = IDeclPExp IAll decls $
                  PExp (Just IBoolean) "" (IFunExp op [e2, e3])
  where
  decls = map (\(locId, e) -> IDecl False [locId] e) locExps

genIFunExp mode clafer (IFunExp op exps) = concat $ intl exps' (genOp mode op)
  where
  intl
    | mode == Alloy42 && op `elem` [iPlus, iSub] = interleave
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
genOp _ op
  | op `elem` unOps = [op]
  | op `elem` [iMul, iDiv] = error $ "no " ++ op ++ " allowed"
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
