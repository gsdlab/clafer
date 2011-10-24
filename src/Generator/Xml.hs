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
module Generator.Xml where

-- import Text.XML.HaXml.XmlContent.Haskell hiding (Result)

import Common
import Front.Absclafer
import Intermediate.Intclafer
-- import Generator.XmlHelp

tag name exp = concat ["<", name, ">", exp, "</", name, ">"]

optTag elem f = maybe "" f elem

tagType name typename exp = opening ++ rest
  where
  opening = concat ["<", name, " xsi:type=\"cl:", typename, "\""]
  rest
    | null exp  = " />"
    | otherwise = concat [">", exp, "</", name, ">"]

genXmlInteger n = tag "IntLiteral" $ show n

genXmlModule :: IModule -> Result
genXmlModule decls = concat
  [ "<Module xmlns=\"http://gsd.uwaterloo.ca/clafer\""
  , " xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""
  , " xmlns:cl=\"http://gsd.uwaterloo.ca/clafer\">"
  ,  concatMap genXmlDeclaration decls
  , "</Module>"]

genXmlDeclaration :: IDeclaration -> Result
genXmlDeclaration x = case x of
  IClaferDecl clafer  -> tagType "Declaration" "IClaferDecl" $ genXmlClafer clafer
  IConstDecl lexp  -> tagType "Declaration" "IConstraintDecl" $ genXmlLExp lexp

genXmlClafer :: IClafer -> Result
genXmlClafer x = case x of
  IClafer abstract gcard id uid super card glcard elements  ->
    tag "Clafer" $ concat [ genXmlAbstract abstract
                          , optTag gcard genXmlGCard
                          , genXmlId id
                          , genXmlUid uid
                          , genXmlSuper super
                          , optTag card genXmlCard
                          , genXmlGlCard glcard
                          , concatMap genXmlElement elements]

genXmlAbstract isAbstract = tag "IsAbstract" $ show isAbstract

genXmlGCard (IGCard isKeyword interval) = tag "GroupCard" $ concat
  [ tag "IsKeyword" $ show isKeyword
  , genXmlInterval interval]

genXmlInterval (nMin, nMax) = tag "Interval" $ concat
  [ tag "Min" $ genXmlInteger nMin
  , genXmlExInteger nMax]

genXmlExInteger x = case x of
  ExIntegerAst -> tagType "Max" "ExIntegerAst" ""
  ExIntegerNum n -> tagType "Max" "ExIntegerNum" $ genXmlInteger n

genXmlId ident = tag "Id" ident

genXmlUid uid = tag "UniqueId" uid

genXmlSuper x = case x of
  ISuper isOverlapping sexps -> tag "Super" $ concat
    [ tag "IsOverlapping" $ show isOverlapping
    , concatMap genXmlSuperSet sexps]

genXmlSuperSet sexp = tagType "SuperSet" (genXmlSExpType sexp) $ genXmlSExp sexp

genXmlCard interval = tag "Card" $ genXmlInterval interval

genXmlGlCard interval = tag "GlobalCard" $ genXmlInterval interval

genXmlElement x = case x of
  ISubclafer clafer  -> tagType "Element" "ISubclafer" $ genXmlClafer clafer
  ISubconstraint lexp  -> tagType "Element" "ISubconstraint" $
                          tagType "Exp" (genXmlLExpType lexp) $ genXmlLExp lexp

genXmlAnyOp ft f xs = concatMap
  (\(tname, texp) -> tagType tname (ft texp) $ f texp) xs

genXmlBinOp ft f exp0 exp1 = genXmlAnyOp ft f [("Exp1", exp0), ("Exp2", exp1)]

genXmlLExpType x = case x of
  IEIff lexp0 lexp  -> "IEIff"
  IEImpliesElse lexp0 lexp _  -> "IEImpliesElse"
  IEOr lexp0 lexp  -> "IEOr"
  IEXor lexp0 lexp  -> "IEXor"
  IEAnd lexp0 lexp  -> "IEAnd"
  IENeg lexp  -> "IENeg"
  IETerm term  -> "IETerm"

genXmlLExp x = case x of
  IEIff lexp0 lexp  -> genE lexp0 lexp
  IEImpliesElse lexp0 lexp1 lexp2  -> genXmlAnyOp genXmlLExpType genXmlLExp $
    [("Condition", lexp0), ("Pass", lexp1)] ++ lexp2'
    where
    lexp2' = maybe [] (\l -> [("Fail", l)]) lexp2
  IEOr lexp0 lexp  -> genE lexp0 lexp
  IEXor lexp0 lexp  -> genE lexp0 lexp
  IEAnd lexp0 lexp  -> genE lexp0 lexp
  IENeg lexp  -> tagType "Exp" (genXmlLExpType lexp) $ genXmlLExp lexp
  IETerm term  -> tagType "Exp" (genXmlTermType term) $ genXmlTerm term
  where
  genE = genXmlBinOp genXmlLExpType genXmlLExp

genXmlTermType x = case x of
  ITermCmpExp cmpexp t -> "ITermCmpExp"
  ITermQuantSet quant sexp -> "ITermQuantSet"
  ITermQuantDeclExp decls lexp -> "ITermQuantDeclExp"

genXmlTerm x = case x of
  ITermCmpExp cmpexp t -> concat
    [ tagType "Exp" (genXmlCmpExpType cmpexp) $ genXmlCmpExp cmpexp
    , optTag t $ genXmlEType]
  ITermQuantSet quant sexp -> concat
    [ tagType "Quant" (genXmlQuantType quant) ""
    , tagType "Exp" (genXmlSExpType sexp) $ genXmlSExp sexp]
  ITermQuantDeclExp decls lexp -> concat
    [ concatMap genXmlDecl decls
    , tagType "Exp" (genXmlLExpType lexp) $ genXmlLExp lexp]

genXmlEType x = tagType "ExpType" (genXmlETypeType x) ""

genXmlETypeType x = case x of
  TAExp -> "TAExp"
  TSExp -> "TSExp"
  TSAExp -> "TSAExp"

genXmlCmpExpType :: ICmpExp -> Result
genXmlCmpExpType x = case x of
  IELt exp0 exp  -> "IELt"
  IEGt exp0 exp  -> "IEGt"
  IEEq exp0 exp  -> "IEEq"
  IEREq exp0 exp  -> "IEREq"
  IELte exp0 exp  -> "IELte"
  IEGte exp0 exp  -> "IEGte"
  IENeq exp0 exp  -> "IENeq"
  IERNeq exp0 exp  -> "IERNeq"
  IEIn exp0 exp  -> "IEIn"
  IENin exp0 exp  -> "IENin"

genXmlCmpExp :: ICmpExp -> Result
genXmlCmpExp x = case x of
  IELt exp0 exp  -> genE exp0 exp
  IEGt exp0 exp  -> genE exp0 exp
  IEEq exp0 exp  -> genE exp0 exp
  IEREq exp0 exp  -> genE exp0 exp
  IELte exp0 exp  -> genE exp0 exp
  IEGte exp0 exp  -> genE exp0 exp
  IENeq exp0 exp  -> genE exp0 exp
  IERNeq exp0 exp  -> genE exp0 exp
  IEIn exp0 exp  -> genE exp0 exp
  IENin exp0 exp  -> genE exp0 exp
  where
  genE = genXmlBinOp genXmlExpType genXmlExp

genXmlExpType x = case x of
  IENumExp aexp -> "IENumExp"
  IEStrExp strexp -> "IEStrExp"

genXmlExp x = case x of
  IENumExp aexp -> tagType "Exp" (genXmlAExpType aexp) $ genXmlAExp aexp
  IEStrExp strexp -> tagType "Exp" (genXmlStrExpType strexp) $ genXmlStrExp strexp

genXmlSExpType x = case x of
  ISExpUnion sexp0 sexp -> "ISExpUnion"
  ISExpIntersection sexp0 sexp  -> "ISExpIntersection"
  ISExpDomain sexp0 sexp  -> "ISExpDomain"
  ISExpRange sexp0 sexp  -> "ISExpRange"
  ISExpJoin sexp0 sexp  -> "ISExpJoin"
  ISExpIdent ident isTop -> "ISExpIdent"

genXmlSExp x = case x of
  ISExpUnion sexp0 sexp -> genE sexp0 sexp
  ISExpIntersection sexp0 sexp  -> genE sexp0 sexp
  ISExpDomain sexp0 sexp  -> genE sexp0 sexp
  ISExpRange sexp0 sexp  -> genE sexp0 sexp
  ISExpJoin sexp0 sexp  -> genE sexp0 sexp
  ISExpIdent ident isTop -> concat [genXmlId ident, tag "IsTop" $ show isTop]
  where
  genE = genXmlBinOp genXmlSExpType genXmlSExp

genXmlDecl (IDecl exquant disj locids sexp) = tag "Declaration" $ concat
  [ tagType "ExQuant" (genXmlExQuantType exquant) $ genXmlExQuant exquant
  , tag "IsDisjoint" $ show disj
  , concatMap (tag "Declarations") locids
  , genXmlSExp sexp]

genXmlAExpType x = case x of
  IEAdd aexp0 aexp -> "IEAdd"
  IESub aexp0 aexp -> "IESub"
  IEMul aexp0 aexp -> "IEMul"
  IECSetExp sexp -> "IECSetExp"
  IEASetExp sexp -> "IEASetExp"
  IEInt n    -> "IEInt"

genXmlAExp x = case x of
  IEAdd aexp0 aexp -> genE aexp0 aexp
  IESub aexp0 aexp -> genE aexp0 aexp
  IEMul aexp0 aexp -> genE aexp0 aexp
  IECSetExp sexp -> tagType "Exp" (genXmlSExpType sexp) $ genXmlSExp sexp
  IEASetExp sexp -> tagType "Exp" (genXmlSExpType sexp) $ genXmlSExp sexp
  IEInt n    -> genXmlInteger n
  where
  genE = genXmlBinOp genXmlAExpType genXmlAExp

genXmlQuantType x = case x of
  QuantNo   -> "QuantNo"
  QuantLone -> "QuantLone"
  QuantOne  -> "QuantOne"
  QuantSome -> "QuantSome"

genXmlStrExpType x = case x of
  EConc strexp0 strexp -> "EConc"
  EStr string -> "EStr"

genXmlStrExp x = case x of
  EConc strexp0 strexp -> genXmlBinOp genXmlStrExpType genXmlStrExp strexp0 strexp
  EStr strexp -> tag "StrLiteral" strexp

genXmlExQuantType x = case x of
  ExQuantAll -> "ExQuantAll"
  ExQuantQuant quant -> "ExQuantQuant"

genXmlExQuant x = case x of
  ExQuantAll -> ""
  ExQuantQuant quant -> tagType "Quant" (genXmlQuantType quant) ""
