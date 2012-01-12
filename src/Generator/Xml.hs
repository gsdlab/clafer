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

genXmlBoolean label b = tag label $ toLowerS $ show b

genXmlString str = tag "StrLiteral" str

genXmlModule :: IModule -> Result
genXmlModule imodule = concat
  [ "<?xml version=\"1.0\"?>"
  , "<Module xmlns=\"http://gsd.uwaterloo.ca/clafer\""
  , " xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""
  , " xmlns:cl=\"http://gsd.uwaterloo.ca/clafer\""
  , " xsi:schemaLocation=\"http://gsd.uwaterloo.ca/clafer"
  , " http://gsd.uwaterloo.ca/ClaferIR.xsd\">"
  , tag "Name" $ mName imodule
  , concatMap genXmlElement $ mDecls imodule
  , "</Module>"]


genXmlClafer :: IClafer -> Result
genXmlClafer x = case x of
  IClafer abstract gcard id uid super card glcard elements  ->
    concat [ genXmlAbstract abstract
           , optTag gcard genXmlGCard
           , genXmlId id
           , genXmlUid uid
           , genXmlSuper super
           , optTag card genXmlCard
           , genXmlGlCard glcard
           , concatMap genXmlElement elements]

genXmlAbstract isAbstract = genXmlBoolean "IsAbstract" isAbstract

genXmlGCard (IGCard isKeyword interval) = tag "GroupCard" $ concat
  [ genXmlBoolean "IsKeyword" isKeyword
  , tag "Interval" $ genXmlInterval interval]

genXmlInterval (nMin, nMax) = concat
  [ tag "Min" $ genXmlInteger nMin
  , genXmlExInteger nMax]

genXmlExInteger x = case x of
  ExIntegerAst -> tagType "Max" "ExIntegerAst" ""
  ExIntegerNum n -> tagType "Max" "ExIntegerNum" $ genXmlInteger n

genXmlId ident = tag "Id" ident

genXmlUid uid = tag "UniqueId" uid

genXmlSuper x = case x of
  ISuper isOverlapping pexps -> tag "Supers" $ concat
    [ genXmlBoolean "IsOverlapping" isOverlapping
    , concatMap (genXmlPExp "Super") pexps]


genXmlCard interval = tag "Card" $ genXmlInterval interval

genXmlGlCard interval = tag "GlobalCard" $ genXmlInterval interval

genXmlElement x = case x of
  IEClafer clafer  -> tagType "Declaration" "IClafer" $ genXmlClafer clafer
  IEConstraint isHard pexp  -> tagType "Declaration" "IConstraint" $ concat
                         [ genXmlBoolean "IsHard" isHard
                         , genXmlPExp "ParentExp" pexp]
                                                          
genXmlAnyOp ft f xs = concatMap
  (\(tname, texp) -> tagType tname (ft texp) $ f texp) xs

genXmlPExp tagName (PExp iType pid iexp) = tag tagName $ concat
  [ optTag iType genXmlIType
  , tag "ParentId" pid
  , tagType "Exp" (genXmlIExpType iexp) $ genXmlIExp iexp]

genXmlIExpType x = case x of
  IDeclPExp _ _ _ -> "IDeclarationParentExp"
  IFunExp _ _ -> "IFunctionExp"
  IInt n -> "IIntExp"
  IDouble n -> "IDoubleExp"
  IStr str -> "IStringExp"
  IClaferId _ _ _ -> "IClaferId"


genXmlIExp x = case x of
  IDeclPExp quant decls pexp -> concat
    [ tagType "Quantifier" (genXmlQuantType quant) ""
    , concatMap genXmlDecl decls
    , genXmlPExp "BodyParentExp" pexp]
  IFunExp op exps -> concat
    [ tag "Operation" $ concatMap escape op
    , concatMap (genXmlPExp "Argument") exps]
    where
    escape '\"' = "&quot;"
    escape '\'' = "&apos;"
    escape '<'  = "&lt;"
    escape '>'  = "&gt;"
    escape '&'  = "&amp;"
    escape x    = [x]
  IInt n -> genXmlInteger n
  IDouble n -> tag "DoubleLiteral" $ show n
  IStr str -> genXmlString str  
  IClaferId modName sident isTop -> concat
    [ tag "ModuleName" modName
    , tag "Id" sident
    , genXmlBoolean "IsTop" isTop]


genXmlDecl (IDecl disj locids pexp) = tag "Declaration" $ concat
  [ genXmlBoolean "IsDisjunct" disj
  , concatMap (tag "LocalDeclaration") locids
  , genXmlPExp "Body" pexp]


genXmlQuantType x = case x of
  INo   -> "INo"
  ILone -> "ILone"
  IOne  -> "IOne"
  ISome -> "ISome"
  IAll  -> "IAll"

genXmlITypeType x = case x of
  IBoolean -> "IBoolean"
  IString  str -> "IString"
  INumeric n   -> "INumeric"
  ISet -> "ISet"

genXmlIType x = tagType "Type" (genXmlITypeType x) $ case x of
  IString  str -> optTag str (\x -> tagType "StringSubtype" (show x) "")
  INumeric n   -> optTag n (\x -> tagType "NumericSubtype" (show x) "")
  _ -> ""
