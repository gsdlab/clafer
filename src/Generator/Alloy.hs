module Generator.Alloy where

import Data.Char
import Data.List
import Data.Maybe
import Data.Function

import Common
import Front.Absclafer
import Intermediate.Intclafer

genModule :: IModule -> Result
genModule declarations = header ++ ([genDeclaration] >>= (declarations >>=))

-- TODO: header depends on the use of ints/strings
header = unlines
    [ "pred show {}"
    , "run  show for 1"
    , ""
    , concat [ "one sig string {", valField, " : Int}"]
    , concat [ "one sig integer {", valField, " : Int}"] 
{-    , concat ["fun ", children, "(p : ",  baseClafer, ") : set ", baseClafer,
              "{p.~", parent, " - p}"] -}
    , ""]


valField = "val"


genDeclaration :: IDeclaration -> Result
genDeclaration x = case x of
  IClaferDecl clafer  -> genClafer clafer
  IConstDecl lexp  -> mkFact $ genLExp lexp


mkFact xs = concat ["fact ", mkSet xs, "\n"]

mkSet xs = concat ["{ ", xs, " }"]


genClafer :: IClafer -> Result
genClafer x = undefined


-- -----------------------------------------------------------------------------
-- Generate code for logical expressions
genLExp :: ILExp -> Result
genLExp x = case x of
  IEIff lexp0 lexp  -> genL lexp0 " <=> " lexp
  IEImpliesElse lexp0 lexp Nothing  -> genL lexp0 " => " lexp
  IEImpliesElse lexp0 lexp1 (Just lexp)  -> concat 
    [genLExp (IEImpliesElse lexp0 lexp1 Nothing), " else (", genLExp lexp, ")"]
  IEOr lexp0 lexp  -> genL lexp0 " or " lexp
  IEXor lexp0 lexp  -> genLExp $ IENeg $ IEIff lexp0 lexp
  IEAnd lexp0 lexp  -> genL lexp0 " && " lexp
  IENeg lexp  -> "not ("  ++ genLExp lexp ++ ")"
  IETerm term  -> genTerm term
  where
  genL = genBinOp genLExp


genTerm :: ITerm -> Result
genTerm x = case x of
  ITermCmpExp cmpexp  -> genCmpExp cmpexp
  ITermQuantSet quant sexp -> genQuant quant ++ " "  ++ genSExp sexp
  ITermQuantDeclExp decls lexp -> concat
    [intercalate "| " $ map genDecl decls, " | ",  genLExp lexp]


genCmpExp :: CmpExp -> Result
genCmpExp x = case x of
  ELt exp0 exp  -> genCmp exp0 " < " exp
  EGt exp0 exp  -> genCmp exp0 " > " exp
  EEq exp0 exp  -> genCmp exp0 " = " exp
  EREq exp0 exp  -> genCmp exp0 " = " exp
  ELte exp0 exp  -> genCmp exp0 " =< " exp
  EGte exp0 exp  -> genCmp exp0 " >= " exp
  ENeq exp0 exp  -> genCmp exp0 " != " exp
  ERNeq exp0 exp  -> genCmp exp0 " != " exp
  EIn exp0 exp  -> genCmp exp0 " in " exp
  ENin exp0 exp  -> genCmp exp0 " not in " exp
  where
  genCmp = genBinOp genExp



genSExp :: SExp -> Result
genSExp x = case x of
  SExpUnion sexp0 sexp -> genS sexp0 "+" sexp
  SExpIntersection sexp0 sexp  -> genS sexp0 "&" sexp
  SExpDomain sexp0 sexp  -> genS sexp0 "<:" sexp
  SExpRange sexp0 sexp  -> genS sexp0 ":>" sexp
  SExpJoin sexp0 sexp  -> genS sexp0 "." sexp
  SExpIdent ident -> transIdent ident
  where
  genS = genBinOp genSExp


genBinOp f x op y = ((\x' y' -> intercalate op [x',y']) `on` (brArg f)) x y


brArg f arg = "(" ++ f arg ++ ")"


genExp :: Exp -> Result
genExp x = case x of
  ESetExp sexp  -> genSExp sexp
  ENumExp aexp -> genAExp aexp
  EStrExp strexp -> error "analyzed"


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


genDecl :: Decl -> Result
genDecl x = case x of
  Decl exquant disj locids sexp -> concat [genExQuant exquant, " ",
    genDisj disj, " ",
    intercalate ", " $ map genLocId locids, " : ", genSExp sexp]


genDisj :: Disj -> Result
genDisj x = case x of
  DisjEmpty -> ""
  Disj -> "disj"


genLocId :: LocId -> Result
genLocId x = case x of
   LocIdIdent ident -> transIdent ident


genAExp :: AExp -> Result
genAExp x = case x of
  EAdd aexp0 aexp -> genArith aexp0 "+" aexp
  ESub aexp0 aexp -> genArith aexp0 "-" aexp
  EMul aexp0 aexp -> genArith aexp0 "*" aexp
  EUmn aexp -> "-" ++ brArg genAExp aexp
  ECSetExp sexp -> "#" ++ brArg genSExp sexp
  EInt n    -> show n
  where
  genArith = genBinOp genAExp
