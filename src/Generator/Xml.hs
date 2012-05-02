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
module Generator.Xml where

-- import Text.XML.HaXml.XmlContent.Haskell hiding (Result)

import Common
import Front.Absclafer
import Intermediate.Intclafer
import Generator.Schema

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

genXmlString str = tag "StringLiteral" str

genXmlIntPair (x, y) = concat
  [ genXmlInteger x
  , genXmlInteger y]

genXmlModule :: IModule -> Result
genXmlModule imodule = concat
  [ "<?xml version=\"1.0\"?>"
  , "<Module xmlns=\"http://clafer.org/ir\""
  , " xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""
  , " xmlns:cl=\"http://clafer.org/ir\""
  , " xsi:schemaLocation=\"https://github.com/gsdlab/clafer/blob/master/src/ClaferIR.xsd\">"
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
  IEGoal isMaximize pexp -> tagType "Declaration" "IGoal" $ concat 
                         [ genXmlBoolean "IsMaximize" isMaximize
                         , genXmlPExp "ParentExp" pexp]
                         
                                                          
genXmlAnyOp ft f xs = concatMap
  (\(tname, texp) -> tagType tname (ft texp) $ f texp) xs

genXmlPExp tagName (PExp iType pid pos iexp) = tag tagName $ concat
  [ optTag iType genXmlIType
  , tag "ParentId" pid
  , tag "Position" $ genXmlPosition pos
  , tagType "Exp" (genXmlIExpType iexp) $ genXmlIExp iexp]

genXmlPosition (start, end) = concat
  [ tag "Start" $ genXmlIntPair start
  , tag "End"   $ genXmlIntPair end]

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
  TBoolean -> "IBoolean"
  TString -> "IString"
  TInteger -> "IInteger"
  TReal -> "IReal"
  TClafer -> "ISet"
  -- In the future, TRef might be needed in the Xml IR.
  -- For now, keep it simple.
  TRef t -> genXmlITypeType t

genXmlIType x = tagType "Type" (genXmlITypeType x) ""
