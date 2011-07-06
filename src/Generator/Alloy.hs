module Generator.Alloy where

import Data.Char
import Data.List
import Data.Maybe
import Data.Function

import Common
import Front.Absclafer
import Intermediate.Intclafer
import Intermediate.ResolverType

genModule :: (IModule, GEnv) -> Result
genModule (declarations, _) = header ++ (declarations >>= genDeclaration)


header = unlines
    [ "pred show {}"
    , "run  show for 1"
    , ""]


valField = "val"


genDeclaration :: IDeclaration -> Result
genDeclaration x = case x of
  IClaferDecl clafer  -> genClafer Nothing clafer
  IConstDecl lexp  -> mkFact $ genLExp Nothing lexp


mkFact xs = concat ["fact ", mkSet xs, "\n"]

mkSet xs = concat ["{ ", xs, " }"]

showSet delim xs = showSet' delim $ filterNull xs
  where
  showSet' _ []     = "{}"
  showSet' delim xs = mkSet $ intercalate delim xs

-- optimization: top level cardinalities
-- optimization: if only boolean parents, then set card is known
genClafer :: Maybe IClafer -> IClafer -> Result
genClafer parent clafer
  | isRef clafer = ""
  | otherwise    = (unlines $ filterNull
                   [cardFact ++ claferDecl clafer
                   , showSet "\n, " $ genRelations clafer
                   , showSet "\n  " $ genConstraints parent clafer
                   ]) ++ children
  where
  children = concat $ filterNull $ map (genClafer $ Just clafer) $
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
  genExtends (ISuper False [ISExpIdent id _]) = " extends " ++ id
  genExtends _ = ""


genOptCard clafer
  | glCard' `elem` ["lone", "one", "some"] = glCard' ++ " "
  | otherwise                              = ""
  where
  glCard' = genIntervalCrude $ glCard clafer
    

-- -----------------------------------------------------------------------------
-- overlapping inheritance is a new clafer with val (unlike only relation)
-- relations: overlapping inheritance (val rel), children
-- adds parent relation
genRelations clafer = ref : (map mkRel $ getSubclafers $ elements clafer)
  where
  ref = if isOverlapping $ super clafer then
          genRel "ref" clafer $ refType clafer
        else ""
  mkRel c = genRel (genRelName $ uid c) c $ (if isRef c then refType else uid) c


genRelName name = "r_" ++ name


genRel name clafer rType = genAlloyRel name (genCardCrude $ card clafer) rType'
  where
  rType' = if rType `elem` [intType, integerType, strType] then "Int" else rType

-- optimization: direct ref to Int attribute (no new clafer)
-- reference clafers as relations


isRef clafer = (null $ elements clafer) && (isOverlapping $ super clafer)


genAlloyRel name card rType = concat [name, " : ", card, " ", rType]


refType c = intercalate " + " $ map (genType.getTarget) $ supers $ super c


getTarget :: ISExp -> ISExp
getTarget x = case x of
  ISExpJoin sexp0 sexp  -> sexp
  _ -> x


genType x = genSExp Nothing x TSExp

-- -----------------------------------------------------------------------------
-- constraints
-- user constraints + parent + group constraints + reference
-- a = NUMBER do all x : a | x = NUMBER (otherwise alloy sums a set)
genConstraints parent clafer = genParentConst parent clafer :
  genGroupConst clafer : genPathConst "ref" clafer : refs ++ constraints 
  where
  constraints = mapMaybe genConst $ elements clafer
  genConst x = case x of
    ISubconstraint lexp  -> Just $ genLExp (Just clafer) lexp
    _ -> Nothing
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

genLExp :: Maybe IClafer -> ILExp -> Result
genLExp clafer x = case x of
  IEIff lexp0 lexp  -> genL lexp0 " <=> " lexp
  IEImpliesElse lexp0 lexp Nothing  -> genL lexp0 " => " lexp
  IEImpliesElse lexp0 lexp1 (Just lexp)  -> concat 
    [genLExp clafer (IEImpliesElse lexp0 lexp1 Nothing),
     " else (", genLExp clafer lexp, ")"]
  IEOr lexp0 lexp  -> genL lexp0 " or " lexp
  IEXor lexp0 lexp  -> genLExp clafer $ IENeg $ IEIff lexp0 lexp
  IEAnd lexp0 lexp  -> genL lexp0 " && " lexp
  IENeg lexp  -> "not ("  ++ genLExp clafer lexp ++ ")"
  IETerm term  -> genTerm clafer term
  where
  genL = genBinOp (genLExp clafer)


genTerm :: Maybe IClafer -> ITerm -> Result
genTerm clafer x = case x of
  ITermCmpExp cmpexp t -> genCmpExp clafer cmpexp $ fromJust t
  ITermQuantSet quant sexp -> genQuant quant ++ " "  ++ (genSExp clafer) sexp TSExp
  ITermQuantDeclExp decls lexp -> concat
    [intercalate "| " $ map (genDecl clafer) decls, " | ",  genLExp clafer lexp]


genCmpExp :: Maybe IClafer -> ICmpExp -> EType -> Result
genCmpExp clafer x t = case x of
  IELt exp0 exp  -> genCmp exp0 " < " exp
  IEGt exp0 exp  -> genCmp exp0 " > " exp
  IEEq exp0 exp  -> genCmp exp0 " = " exp
  IEREq exp0 exp  -> genCmp exp0 " = " exp
  IELte exp0 exp  -> genCmp exp0 " =< " exp
  IEGte exp0 exp  -> genCmp exp0 " >= " exp
  IENeq exp0 exp  -> genCmp exp0 " != " exp
  IERNeq exp0 exp  -> genCmp exp0 " != " exp
  IEIn exp0 exp  -> genBinOp (flip (genExp clafer) t) exp0 " in " exp
  IENin exp0 exp  -> genBinOp (flip (genExp clafer) t) exp0 " not in " exp
  where
  genCmp x op y = on (genNumExp (t, resolveTExp x, resolveTExp y) op)
                  (flip (genExp clafer) t) x y


genNumExp :: (EType, EType, EType) -> Result -> Result -> Result -> Result
genNumExp (TSExp, _, _) " = " x y = x ++ " = " ++ y
genNumExp (TSExp, _, _) op x y =
  "all cl0 : " ++ x ++ ", cl1 : " ++ y ++ " | cl0" ++ op ++ "cl1"
genNumExp (TSAExp, t0, t) op x y
  | t0 == TSExp = "all cl0 : " ++ x ++ " | cl0" ++ op ++ y
  | otherwise   = "all cl0 : " ++ y ++ " | " ++ x ++ op ++ "cl0"
genNumExp _ op x y = x ++ op ++ y


genSExp :: Maybe IClafer -> ISExp -> EType -> Result
genSExp _ (ISExpIdent "this" _) TSAExp = "this.@ref"
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


genExp :: Maybe IClafer -> IExp -> EType -> Result
genExp clafer x t = case x of
  IESetExp sexp  -> genSExp clafer sexp t
  IENumExp aexp -> genAExp clafer aexp
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
  ExQuant quant -> genQuant quant


genDecl :: Maybe IClafer -> IDecl -> Result
genDecl clafer x = case x of
  IDecl exquant disj locids sexp -> concat [genExQuant exquant, " ",
    genDisj disj, " ",
    intercalate ", " locids, " : ", genSExp clafer sexp TSExp]


genDisj :: Bool -> Result
genDisj x = case x of
  False -> ""
  True  -> "disj"


genAExp :: Maybe IClafer -> IAExp -> Result
genAExp clafer x = case x of
  IEAdd aexp0 aexp -> genArith aexp0 "+" aexp
  IESub aexp0 aexp -> genArith aexp0 "-" aexp
  IEMul aexp0 aexp -> genArith aexp0 "*" aexp
  IEUmn aexp -> "-" ++ brArg (genAExp clafer) aexp
  IECSetExp sexp -> "#" ++ brArg (flip (genSExp clafer) TSExp) sexp
  IEInt n    -> show n
  where
  genArith = genBinOp (genAExp clafer)
