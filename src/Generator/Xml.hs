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
genXmlModule imodule = concat
  [ "<?xml version=\"1.0\"?>"
  , "<Module xmlns=\"http://gsd.uwaterloo.ca/clafer\""
  , " xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""
  , " xmlns:cl=\"http://gsd.uwaterloo.ca/clafer\""
  , " xsi:schemaLocation=\"http://gsd.uwaterloo.ca/clafer"
  , "                      http://gsd.uwaterloo.ca/Clafer.xsd\">"
  , tag "Name" $ mName imodule
  , concatMap genXmlElement $ mDecls imodule
  , "</Module>"]


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
  ISuper isOverlapping pexps -> tag "Super" $ concat
    [ tag "IsOverlapping" $ show isOverlapping
    , concatMap genXmlSuperSet pexps]

genXmlSuperSet pexp = tag "SuperSet" $ genXmlPExp pexp

genXmlCard interval = tag "Card" $ genXmlInterval interval

genXmlGlCard interval = tag "GlobalCard" $ genXmlInterval interval

genXmlElement x = case x of
  IEClafer clafer  -> tagType "Element" "IEClafer" $ genXmlClafer clafer
  IEConstraint _ pexp  -> tagType "Element" "IEConstraint" $
                        tag "Exp" $ genXmlPExp pexp

genXmlAnyOp ft f xs = concatMap
  (\(tname, texp) -> tagType tname (ft texp) $ f texp) xs

genXmlPExp (PExp iType pid iexp) = concat
  [ tag "IType" $ optTag iType genXmlIType
  , tag "PId" pid
  , tagType "IExp" (genXmlIExpType iexp) $ genXmlIExp iexp]

genXmlIExpType x = takeWhile (/= ' ') $ show x

genXmlIExp x = case x of
  IDeclPExp quant decls pexp -> concat
    [ tagType "Quant" (genXmlQuantType quant) ""
    , concatMap genXmlDecl decls
    , tag "Exp" $ genXmlPExp pexp]
  IFunExp op exps -> concat
    [ tag "Op" $ show op
    , concatMap (\(tname, texp) -> tag tname $ genXmlPExp texp) $
      zip (map (\x -> "Exp" ++ show x) [1..]) exps]
  IInt n -> genXmlInteger n
  IDouble n -> tag "DoubleLiteral" $ show n
  IStr str -> tag "StrLiteral" str  
  IClaferId modName sident isTop -> concat
    [ tag "ModName" modName
    , tag "Sident" $ tag "StrLiteral" sident
    , tag "IsTop" $ show isTop]


genXmlDecl (IDecl disj locids pexp) = tag "Declaration" $ concat
  [ tag "IsDisjoint" $ show disj
  , concatMap (tag "Declarations") locids
  , genXmlPExp pexp]


genXmlQuantType x = case x of
  INo   -> "INo"
  ILone -> "ILone"
  IOne  -> "IOne"
  ISome -> "ISome"
  IAll  -> "IAll"

genXmlIType x = case x of
  IBoolean -> "IBoolean"
  IString  str -> tag "IString" $ optTag str show
  INumeric n   -> tag "INumeric" $ optTag n show
  ISet -> "ISet"