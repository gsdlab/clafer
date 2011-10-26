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
genModule mode (declarations, _) = header ++ (declarations >>= (genDeclaration mode))


header = unlines
    [ "pred show {}"
    , "run  show for 1"
    , ""]


valField = "val"


genDeclaration :: ClaferMode -> IDeclaration -> Result
genDeclaration mode x = case x of
  IClaferDecl clafer  -> genClafer mode Nothing clafer
  IConstDecl lexp  -> mkFact $ genLExp mode Nothing lexp


mkFact xs = concat ["fact ", mkSet xs, "\n"]

mkSet xs = concat ["{ ", xs, " }"]

showSet delim xs = showSet' delim $ filterNull xs
  where
  showSet' _ []     = "{}"
  showSet' delim xs = mkSet $ intercalate delim xs

-- optimization: top level cardinalities
-- optimization: if only boolean parents, then set card is known
genClafer :: ClaferMode -> Maybe IClafer -> IClafer -> Result
genClafer mode parent clafer
  | isJust parent && isRef clafer || isPrimitiveClafer clafer = ""
  | otherwise    = (unlines $ filterNull
                   [cardFact ++ claferDecl clafer
                   , showSet "\n, " $ genRelations clafer
                   , showSet "\n  " $ genConstraints mode parent clafer
                   ]) ++ children
  where
  children = concat $ filterNull $ map (genClafer mode $ Just clafer) $
             getSubclafers $ elements clafer
  cardFact
    | isNothing parent && (null $ genOptCard clafer) =
        case genCard (uid clafer) $ card clafer of
          "set" -> ""
          c -> mkFact c
    | otherwise = ""

claferDecl clafer = concat [genOptCard clafer,
  genAbstract $ isAbstract clafer, "sig ",
  uid clafer, genExtends $ super clafer]
  where
  genAbstract isAbstract = if isAbstract then "abstract " else ""
  genExtends (ISuper False [ISExpIdent "clafer" _]) = ""
  genExtends (ISuper False [ISExpIdent id _])       = " extends " ++ id
  genExtends _ = ""


genOptCard clafer
  | glCard' `elem` ["lone", "one", "some"] = glCard' ++ " "
  | otherwise                              = ""
  where
  glCard' = genIntervalCrude $ glCard clafer
    

isPrimitiveClafer clafer = case super clafer of
  ISuper _ [ISExpIdent id _] -> isPrimitive id && (null $ elements clafer)
  _ -> False

-- -----------------------------------------------------------------------------
-- overlapping inheritance is a new clafer with val (unlike only relation)
-- relations: overlapping inheritance (val rel), children
-- adds parent relation
genRelations clafer = ref : (map mkRel $ getSubclafers $ elements clafer)
  where
  ref = if isOverlapping $ super clafer then
          genRel "ref" clafer $ refType clafer
        else ""
  mkRel c = genRel (genRelName $ uid c) c $
            (if isRef c || isPrimitiveClafer c then refType else uid) c


genRelName name = "r_" ++ name


genRel name clafer rType = genAlloyRel name (genCardCrude $ card clafer) rType'
  where
  rType' = if isPrimitive rType then "Int" else rType

-- optimization: direct ref to Int attribute (no new clafer)
-- reference clafers as relations


isRef clafer = (null $ elements clafer) && (isOverlapping $ super clafer)


genAlloyRel name card rType = concat [name, " : ", card, " ", rType]


refType c = intercalate " + " $ map (genType.getTarget) $ supers $ super c


getTarget :: ISExp -> ISExp
getTarget x = case x of
  ISExpJoin sexp0 sexp  -> sexp
  _ -> x


genType x@(ISExpIdent _ _) = genSExp Nothing x{isTop = True} TSExp
genType x = genSExp Nothing x TSExp


-- -----------------------------------------------------------------------------
-- constraints
-- user constraints + parent + group constraints + reference
-- a = NUMBER do all x : a | x = NUMBER (otherwise alloy sums a set)
genConstraints mode parent clafer = genParentConst parent clafer :
  genGroupConst clafer : genPathConst "ref" clafer : refs ++ constraints 
  where
  constraints = map genConst $ elements clafer
  genConst x = case x of
    ISubconstraint lexp  -> genLExp mode (Just clafer) lexp
    ISubclafer clafer -> if genCardCrude crd `elem` ["one", "lone", "some"]
                         then "" else mkCard (genRelName $ uid clafer) $
                           fromJust crd
      where
      crd = card clafer
  refs = map (\c -> genPathConst (genRelName $ uid c) c) $
         filter isRefPath $ filter isRef $ getSubclafers $ elements clafer

-- optimization: if only boolean features then the parent is unique
genParentConst pClafer clafer = maybe ""
                                (const $ concat $ genOptParentConst clafer)
                                pClafer


genOptParentConst clafer
  | glCard' == "one"  = [""]
  | glCard' == "lone" = ["one ", rel]
  | otherwise         = ["one ", rel, ".this"]
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


genPathConst name clafer
  | isRefPath clafer = name ++ " = " ++ (intercalate " + " $
                       map ((brArg id).(flip (genSExp $ Just clafer) TSExp)) $
                       supers $ super clafer)
  | otherwise        = ""


isRefPath clafer = (isOverlapping $ super clafer) &&
                   ((length s > 1) || (not $ isSimplePath s))
  where
  s = supers $ super clafer


isSimplePath :: [ISExp] -> Bool
isSimplePath [(ISExpIdent _ _)] = True
isSimplePath [(ISExpUnion _ _)] = True
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

genLExp :: ClaferMode -> Maybe IClafer -> ILExp -> Result
genLExp mode clafer x = case x of
  IEIff lexp0 lexp  -> genL lexp0 " <=> " lexp
  IEImpliesElse lexp0 lexp Nothing  -> genL lexp0 " => " lexp
  IEImpliesElse lexp0 lexp1 (Just lexp)  -> concat 
    [genLExp mode clafer (IEImpliesElse lexp0 lexp1 Nothing),
     " else (", genLExp mode clafer lexp, ")"]
  IEOr lexp0 lexp  -> genL lexp0 " or " lexp
  IEXor lexp0 lexp  -> genLExp mode clafer $ IENeg $ IEIff lexp0 lexp
  IEAnd lexp0 lexp  -> genL lexp0 " && " lexp
  IENeg lexp  -> "not ("  ++ genLExp mode clafer lexp ++ ")"
  IETerm term  -> genTerm mode clafer term
  where
  genL = genBinOp (genLExp mode clafer)


genTerm :: ClaferMode -> Maybe IClafer -> ITerm -> Result
genTerm mode clafer x = case x of
  ITermCmpExp cmpexp t -> genCmpExp mode clafer cmpexp $ fromJust t
  ITermQuantSet quant sexp -> genQuant quant ++ " "  ++ (genSExp clafer) sexp TSExp
  ITermQuantDeclExp decls lexp -> concat
    [intercalate "| " $ map (genDecl clafer) decls, " | ",  genLExp mode clafer lexp]


genCmpExp :: ClaferMode -> Maybe IClafer -> ICmpExp -> EType -> Result
genCmpExp mode clafer x t = case x of
  IELt exp0 exp  -> genCmp exp0 " < " exp
  IEGt exp0 exp  -> genCmp exp0 " > " exp
  IEEq exp0 exp  -> genCmp exp0 " = " exp
  IEREq exp0 exp  -> genCmp exp0 " = " exp
  IELte exp0 exp  -> genCmp exp0 " =< " exp
  IEGte exp0 exp  -> genCmp exp0 " >= " exp
  IENeq exp0 exp  -> genCmp exp0 " != " exp
  IERNeq exp0 exp  -> genCmp exp0 " != " exp
  IEIn exp0 exp  -> genBinOp (flip (genExp mode clafer) t) exp0 " in " exp
  IENin exp0 exp  -> genBinOp (flip (genExp mode clafer) t) exp0 " not in " exp
  where
  genCmp x op y = on (genNumExp (t, resolveTExp x, resolveTExp y) op)
                  (flip (genExp mode clafer) t) x y


genNumExp :: (EType, EType, EType) -> Result -> Result -> Result -> Result
genNumExp (TSExp, _, _) op x y = x ++ " = " ++ y
genNumExp (TSAExp, TSExp, _) op x y = "all cl0 : " ++ x ++ " | cl0" ++ op ++ y
genNumExp (TSAExp, _, TSExp) op x y = "all cl0 : " ++ y ++ " | " ++ x ++ op ++ "cl0"
-- BUG: it doesn't work if set/arithemetic expressions are more complex
genNumExp _ op x y = x ++ op ++ y


genSExp :: Maybe IClafer -> ISExp -> EType -> Result
genSExp _ (ISExpIdent "this" _) TSAExp = "this.@ref"
genSExp clafer x@(ISExpIdent id True) TSAExp = id ++ ".@ref"
genSExp clafer x t = genSExp' clafer x True


genSExp' :: Maybe IClafer -> ISExp -> Bool -> Result
genSExp' clafer x isFirst = case x of
  ISExpUnion sexp0 sexp -> genS sexp0 "+" sexp
  ISExpIntersection sexp0 sexp  -> genS sexp0 "&" sexp
  ISExpDomain sexp0 sexp  -> genS sexp0 "<:" sexp
  ISExpRange sexp0 sexp  -> genS sexp0 ":>" sexp
  ISExpJoin sexp0 sexp  -> intercalate "."
    [brArg (flip (genSExp' clafer) isFirst) sexp0,
     brArg (flip (genSExp' clafer) False) sexp]
  ISExpIdent "parent" _  ->
    brArg id $ (genRelName $ uid $ fromJust clafer) ++ ".this"
  ISExpIdent ident isTop -> 
    (if isFirst && isTop then "" else '@' : genRelName "") ++ ident
  where
  genS = genBinOp (flip (genSExp' clafer) isFirst)


genBinOp f x op y = ((lurry (intercalate op)) `on` (brArg f)) x y


brArg f arg = "(" ++ f arg ++ ")"


genExp :: ClaferMode -> Maybe IClafer -> IExp -> EType -> Result
genExp mode clafer x t = case x of
  IENumExp aexp -> genAExp mode clafer aexp t
  IEStrExp strexp -> error $ "analyzed: " ++ show strexp


genQuant :: Quant -> Result
genQuant x = case x of
  QuantNo   -> "no"
  QuantLone -> "lone"
  QuantOne  -> "one"
  QuantSome -> "some"


genExQuant :: ExQuant -> Result
genExQuant x = case x of
  ExQuantAll -> "all"
  ExQuantQuant quant -> genQuant quant


genDecl :: Maybe IClafer -> IDecl -> Result
genDecl clafer x = case x of
  IDecl exquant disj locids sexp -> concat [genExQuant exquant, " ",
    genDisj disj, " ",
    intercalate ", " locids, " : ", genSExp clafer sexp TSExp]


genDisj :: Bool -> Result
genDisj x = case x of
  False -> ""
  True  -> "disj"


genAExp :: ClaferMode -> Maybe IClafer -> IAExp -> EType -> Result
genAExp mode clafer x t = case x of
  IEAdd aexp0 aexp -> genArith aexp0 op aexp ++ br
    where
    (op, br) = case mode of 
           Alloy -> ("+", "")
           Alloy42 -> (".plus[", "]")
  IESub aexp0 aexp -> genArith aexp0 op aexp ++ br
    where
    (op, br) = case mode of 
           Alloy -> ("-", "")
           Alloy42 -> (".minus[", "]")
  IEMul aexp0 aexp -> genArith aexp0 "*" aexp
  IECSetExp sexp -> "#" ++ brArg (flip (genSExp clafer) TSExp) sexp
  IEASetExp sexp -> genSExp clafer sexp t
  IEInt n    -> show n
  where
  genArith = genBinOp (flip (genAExp mode clafer) t)
  