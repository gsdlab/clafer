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
-- | Generates Python representation of IR for the <https://github.com/gsdlab/ClaferZ3 ClaferZ3>.
module Language.Clafer.Generator.Python where

import Data.Char
import Data.Maybe (fromMaybe)

import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer

tag:: String -> String -> String
tag name exp' = concat ["<", name, ">", exp', "</", name, ">\n"]

--Maybe a -> (a -> [Char]) -> [Char]
--optTag elem f = maybe "" f elem

tagType :: String -> String -> String -> String
tagType name typename exp' = opening ++ rest
  where
  opening = concat ["<", name, " xsi:type=\"cl:", typename, "\""]
  rest
    | null exp' =" />"
    | otherwise = concat [">", exp', "</", name, ">"]

genPythonInteger :: Integer -> String
genPythonInteger n = concat ["IntegerLiteral.IntegerLiteral(", show n, ")" ] -- might need to include IntegerLiteral

isNull :: String -> String
isNull [] = "\"\""
isNull x = x

boolHelper:: String -> String
boolHelper (x:xs) = toUpper x : xs
boolHelper [] = []

genPythonBoolean :: String -> Bool -> String
genPythonBoolean label b = concat [label, "=", boolHelper $ toLowerS $ show b]

genPythonString :: String -> String
genPythonString str = concat [ "StringLiteral.StringLiteral(", show str, ")"] -- might need to include StringLiteral

genPythonIntPair :: (Integer, Integer) -> String
genPythonIntPair (x, y) = concat
  [ "(", genPythonInteger x
  , ","
  , genPythonInteger y, ")"]

-- | Generate an API for the IR in Python
genPythonModule :: IModule -> Result
genPythonModule imodule = concat
  [ "from ast import Module\n"
  , "from ast import GCard\n"
  , "from ast import Supers\n"
  , "from ast import Clafer\n"
  , "from ast import Exp\n"
  , "from ast import Declaration\n"
  , "from ast import LocalDeclaration\n"
  , "from ast import IRConstraint\n"
  , "from ast import FunExp\n"
  , "from ast import ClaferId\n"
  , "from ast import DeclPExp\n"
  , "from ast import Goal\n\n"
  , "from ast import IntegerLiteral\n"
  , "from ast import DoubleLiteral\n"
  , "from ast import StringLiteral\n"
  , "def getModule():\n"
  , "\tstack = []\n"
  , "\tmodule = Module.Module(\"\")\n"
  , "\tstack.append(module)\n"
  , concatMap genPythonElement $ _mDecls imodule
  , "\treturn module"
  ]


genPythonClafer :: IClafer -> Result
genPythonClafer x = case x of
  IClafer pos' modifiers' gcard' id' uid' puid' super' card' glcard' _ elements'  ->
    concat [ "\t", genPythonPosition pos', "\n"
           , "\t", genPythonAbstract $ _abstract modifiers', "\n"
           , "\t", maybe "" genPythonGCard gcard', "\n"
           , "\t", genPythonId id', "\n"
           , "\t", genPythonUid uid', "\n"
           , "\t", genPythonParentUid puid', "\n"
           , "\t", genPythonSuper super', "\n"
           , "\t", maybe "" genPythonCard card', "\n"
           , "\t", genPythonGlCard glcard', "\n"
           , "\tcurrClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)\n"
           , "\tstack[-1].addElement(currClafer)\n"
           , "\tstack.append(currClafer)\n"
           , concatMap genPythonElement elements'
           , "\tstack.pop()\n"]

genPythonAbstract :: Bool -> String
genPythonAbstract isAbstract' = concat [ genPythonBoolean "isAbstract" isAbstract']

genPythonGCard :: IGCard -> String
genPythonGCard (IGCard isKeyword' interval') = concat
		[ "groupCard = GCard.GCard(", genPythonBoolean "isKeyword" isKeyword', ", "
    	, "interval=" , genPythonInterval interval' , ")"]

genPythonInterval :: (Integer, Integer) -> String
genPythonInterval (nMin, nMax) = concat
  [ "(", genPythonInteger nMin
  , ",", genPythonInteger nMax
  , ")"]

genPythonId :: String -> String
genPythonId ident' = concat[ "id=\"", ident', "\""]

genPythonUid :: String -> String
genPythonUid uid' = concat [ "uid=\"", uid', "\""]

genPythonParentUid :: String -> String
genPythonParentUid uid' = concat [ "parentUid=\"", uid', "\""]

genPythonSuper :: ISuper -> String
genPythonSuper x = case x of
  ISuper isOverlapping' pexps' -> concat
    [ "my_supers = Supers.Supers(", genPythonBoolean "isOverlapping" isOverlapping', ", elements=["
    , concatMap (genPythonPExp "Super") pexps' , "])"]

genPythonCard :: (Integer, Integer) -> String
genPythonCard interval' = concat [ "card=" , genPythonInterval interval']

genPythonGlCard :: (Integer, Integer) -> String
genPythonGlCard interval' = concat ["globalCard=", genPythonInterval interval']

genPythonElement :: IElement -> String
genPythonElement x = case x of
  IEClafer clafer'  -> concat ["##### clafer #####\n" ,genPythonClafer clafer']
  IEConstraint isHard' pexp'  -> concat
                         [ "##### constraint #####\n", "\tconstraint = IRConstraint.IRConstraint(" , genPythonBoolean "isHard" isHard' , " ,"
                         , " exp=", genPythonPExp "ParentExp" pexp' , ")\n"
                         , "\tstack[-1].addElement(constraint)\n"]
  IEGoal isMaximize' pexp' -> concat
                         [ "##### goal #####\n" ,"\tgoal = Goal.Goal(" , genPythonBoolean "isMaximize" isMaximize'
                         , ", exp=", genPythonPExp "ParentExp" pexp' , ")\n"
                         , "\tstack[-1].addElement(goal)\n"]


{-genPythonAnyOp ft f xs = concatMap
  (\(tname, texp) -> tagType tname (ft texp) $ f texp) xs -}


genPythonPExp :: String -> PExp -> String
genPythonPExp tagName (PExp iType' pid' pos' iexp') = concat
  [ "\n\t\tExp.Exp","(expType=\"", tagName, "\", ", maybe "exptype=\"\"" genPythonIType iType'
  , ", parentId=\"", pid', "\""
  , ", " , genPythonPosition pos'
  , ", iExpType=\"" , genPythonIExpType iexp' , "\""
  , ", iExp=[" , genPythonIExp iexp' ,"])"]

genPythonPosition :: Span -> String
genPythonPosition (Span (Pos s1 s2) (Pos e1 e2)) = concat
  [ "pos=(", genPythonIntPair (s1, s2), ", ", genPythonIntPair (e1, e2), ")"]

genPythonIExpType :: IExp -> String
genPythonIExpType x = case x of
  IDeclPExp _ _ _ -> "IDeclarationParentExp"
  IFunExp _ _ -> "IFunctionExp"
  IInt _ -> "IIntExp"
  IDouble _ -> "IDoubleExp"
  IStr _ -> "IStringExp"
  IClaferId _ _ _ _ -> "IClaferId"


declHelper :: [IDecl] -> String
declHelper [] = "None, "
declHelper x = concatMap genPythonDecl x

genPythonIExp :: IExp -> String
genPythonIExp x = case x of
  IDeclPExp quant' decls' pexp' -> concat
    [ "DeclPExp.DeclPExp(" , "quantifier=\"", (genPythonQuantType quant'), "\", "
    , "declaration=", declHelper decls'
    , "bodyParentExp=" , genPythonPExp "BodyParentExp" pexp', ")"]
  IFunExp op' exps' -> concat
    [ "FunExp.FunExp(operation=\"" , (if op' == "-" && length exps' == 1 then "UNARY_MINUS" else op') , "\", elements="
    , "[", concatMap (\y -> genPythonPExp "Argument" y ++",") (init exps') , genPythonPExp "Argument" (last exps') ,"])" ]
{-    where
    escape '\"'="&quot;"
    escape '\''="&apos;"
    escape '<' ="&lt;"
    escape '>' ="&gt;"
    escape '&' ="&amp;"
    escape x    = [x] -}
  IInt n -> genPythonInteger n
  IDouble n ->  concat [ "DoubleLiteral.DoubleLiteral(", show n, ")"] --DoubleLiteral
  IStr str -> genPythonString str
  IClaferId modName' sident' isTop' bind' -> concat
    [ "ClaferId.ClaferId(moduleName=\"", modName' , "\", "
    , "my_id=\"", sident' , "\", "
    , genPythonBoolean "isTop" isTop'
    , "my_bind=\"", fromMaybe "" bind' , "\", ", ")"]


genPythonDecl :: IDecl -> String
genPythonDecl (IDecl disj locids pexp) = concat
  [ "\n\t\tDeclaration.Declaration(" , genPythonBoolean "isDisjunct" disj, ", localDeclarations=["
  , concatMap (\x -> "LocalDeclaration.LocalDeclaration(\"" ++ x ++ "\"), ") (init locids), "LocalDeclaration.LocalDeclaration(\"" , (last locids), "\")], "
  , " body=", genPythonPExp "Body" pexp , "),"]


genPythonQuantType :: IQuant -> String
genPythonQuantType x = case x of
  INo   -> "No"
  ILone -> "Lone"
  IOne  -> "One"
  ISome -> "Some"
  IAll  -> "All"

genPythonITypeType :: IType -> String
genPythonITypeType x = case x of
  TBoolean -> "Boolean"
  TString -> "String"
  TInteger -> "Integer"
  TReal -> "Real"
  TClafer _-> "Set"
  -- In the future, TRef might be needed in the Python IR.
  -- For now, keep it simple.
  --TRef t -> genPythonITypeType t

genPythonIType :: IType -> String
genPythonIType x = concat [ "exptype=\"", (genPythonITypeType x), "\"" ]
