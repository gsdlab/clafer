{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang, Luke Brown <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Generator.Xml where

-- import Text.XML.HaXml.XmlContent.Haskell hiding (Result)

import Data.Maybe (fromJust)
import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer

tag :: String -> String -> String
tag name exp' = concat ["<", name, ">", exp', "</", name, ">\n"]

optTag :: Maybe a -> (a -> String) -> String
optTag ele f = maybe "" f ele

tagType :: String -> String -> String -> String
tagType name typename exp' = opening ++ rest
  where
  opening = concat ["<", name, " xsi:type=\"cl:", typename, "\""]
  rest
    | null exp'  = " />"
    | otherwise = concat [">", exp', "</", name, ">"]

genXmlInteger :: Integer -> String
genXmlInteger n = tag "IntLiteral" $ show n

genXmlBoolean :: String -> Bool -> String
genXmlBoolean label b = tag label $ toLowerS $ show b

genXmlString :: String -> String
genXmlString str = tag "StringLiteral" str

genXmlIntPair :: (Integer, Integer) -> String
genXmlIntPair (x, y) = concat
  [ genXmlInteger x
  , genXmlInteger y]

genXmlModule :: IModule -> Result
genXmlModule imodule = concat
  [ "<?xml version=\"1.0\"?>"
  , "<Module xmlns=\"http://clafer.org/ir\""
  , " xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""
  , " xmlns:cl=\"http://clafer.org/ir\""
  , " xsi:schemaLocation=\"http://clafer.org/ir https://github.com/gsdlab/clafer/blob/master/src/ClaferIR.xsd\">"
  , tag "Name" $ mName imodule
  , concatMap genXmlElement $ mDecls imodule
  , "</Module>"]


genXmlClafer :: IClafer -> Result
genXmlClafer x = case x of
  IClafer _ pos abstract gcrd id' uid' super' ref' crd glcard es ->
    concat [ tag "Position" $ genXmlPosition pos
           , genXmlAbstract abstract
           , optTag gcrd genXmlGCard
           , genXmlId id'
           , genXmlUid uid'
           , flip genXmlSuper super' $ IEClafer x
           , flip genXmlRef ref' $ IEClafer x
           , optTag crd genXmlCard
           , genXmlGlCard glcard
           , concatMap genXmlElement es] 


genXmlAbstract :: Bool -> String
genXmlAbstract isAbs = genXmlBoolean "IsAbstract" isAbs

genXmlGCard :: IGCard -> String
genXmlGCard (IGCard isKeyword' interval') = tag "GroupCard" $ concat
  [ genXmlBoolean "IsKeyword" isKeyword'
  , tag "Interval" $ genXmlInterval interval']

genXmlInterval :: (Integer, Integer) -> String
genXmlInterval (nMin, nMax) = concat
  [ tag "Min" $ genXmlInteger nMin
  , tag "Max" $ genXmlInteger nMax]

genXmlId :: String -> String
genXmlId ident' = tag "Id" ident'

genXmlUid :: String -> String
genXmlUid uid' = tag "UniqueId" uid'

genXmlSuper :: IElement -> ISuper -> String
genXmlSuper e (ISuper _ sk pexps) = 
  tag "Supers" $ concat $
    (tag "SuperKind" $ show $ sk) :
      [concatMap (genXmlPExp "Super" e) pexps]

genXmlRef :: IElement -> IReference -> String
genXmlRef e (IReference _ s pexps) =
  tag "Refs" $ concat $
    (genXmlBoolean "IsSet" s) :
      [concatMap (genXmlPExp "Ref" e) pexps]

genXmlCard :: (Integer, Integer) -> String
genXmlCard interval' = tag "Card" $ genXmlInterval interval'

genXmlGlCard :: (Integer, Integer) -> String
genXmlGlCard interval' = tag "GlobalCard" $ genXmlInterval interval'

genXmlElement :: IElement -> String
genXmlElement x = case x of
  IEClafer clafer  -> tagType "Declaration" "IClafer" $ genXmlClafer clafer
  IEConstraint _ isHard' pexp  -> tagType "Declaration" "IConstraint" $ concat
                         [ genXmlBoolean "IsHard" isHard'
                         , genXmlPExp "ParentExp" x pexp]
  IEGoal _ isMaximize' pexp -> tagType "Declaration" "IGoal" $ concat 
                         [ genXmlBoolean "IsMaximize" isMaximize'
                         , genXmlPExp "ParentExp" x pexp]
                         

genXmlAnyOp :: (a -> String) -> (a -> String) -> [(String, a)] -> String                                                    
genXmlAnyOp ft f xs = concatMap
  (\(tname, texp) -> tagType tname (ft texp) $ f texp) xs

genXmlPExp :: String -> IElement -> PExp -> String
genXmlPExp tagName e (PExp _ iType' pid' pos' iexp) = 
  let parentID = case e of
        (IEClafer c) -> claferParent c
        (IEConstraint p _ _) -> p
        (IEGoal p _ _) -> p
      parentParentID = if parentID == Nothing then Nothing 
        else claferParent $ fromJust parentID
  in tag tagName $ concat
  [ optTag iType' genXmlIType
  , tag "ParentId" pid'
  , tag "Position" $ genXmlPosition pos'
  , tagType "Exp" (genXmlIExpType iexp) $ genXmlIExp iexp e parentID parentParentID]

genXmlPosition :: Span -> String
genXmlPosition (Span (Pos s1 s2) (Pos e1 e2)) = concat
  [ tag "Start" $ genXmlIntPair (s1, s2)
  , tag "End"   $ genXmlIntPair (e1, e2)]
genXmlPosition (PosSpan _ s e) = genXmlPosition (Span s e)
genXmlPosition (Span (PosPos _ s1 s2) e) = genXmlPosition (Span (Pos s1 s2) e)
genXmlPosition (Span s (PosPos _ e1 e2)) = genXmlPosition (Span s (Pos e1 e2))

genXmlIExpType :: IExp -> String
genXmlIExpType x = case x of
  IDeclPExp _ _ _ -> "IDeclarationParentExp"
  IFunExp _ _ -> "IFunctionExp"
  IInt _ -> "IIntExp"
  IDouble _ -> "IDoubleExp"
  IStr _ -> "IStringExp"
  IClaferId _ _ _ -> "IClaferId"

genXmlIExp :: IExp -> IElement -> Maybe IClafer -> Maybe IClafer -> String
genXmlIExp x e pid' ppid' = case x of
  IDeclPExp quant' decls' pexp -> concat
    [ tagType "Quantifier" (genXmlQuantType quant') ""
    , concatMap (genXmlDecl e) decls'
    , genXmlPExp "BodyParentExp" e pexp]
  IFunExp op' exps' -> concat
    [ tag "Operation" $ concatMap escape op'
    , concatMap (genXmlPExp "Argument" e) exps']
    where
    escape '\"' = "&quot;"
    escape '\'' = "&apos;"
    escape '<'  = "&lt;"
    escape '>'  = "&gt;"
    escape '&'  = "&amp;"
    escape y    = [y]
  IInt n -> genXmlInteger n
  IDouble n -> tag "DoubleLiteral" $ show n
  IStr str -> genXmlString str  
  IClaferId modName' sident' isTop' -> concat
    [ tag "ModuleName" modName'
    , tag "Id" (if (sident'=="this" && pid'/=Nothing) then (uid $ fromJust pid') 
        else if (sident'=="parent" && ppid'/=Nothing) then (uid $ fromJust ppid') 
          else sident')
    , genXmlBoolean "IsTop" isTop'
--    , tag "kind" $ if (sident' `elem` ["this","parent"]) then sident' else "clafer"
--  this is not in IR and it's not clear how the users of XML need that. Not in ClaferIR.xsd either
    ]

genXmlDecl :: IElement -> IDecl -> String
genXmlDecl e (IDecl disj locids pexp) = tag "Declaration" $ concat
  [ genXmlBoolean "IsDisjunct" disj
  , concatMap (tag "LocalDeclaration") locids
  , genXmlPExp "Body" e pexp]

genXmlQuantType :: IQuant -> String
genXmlQuantType x = case x of
  INo   -> "INo"
  ILone -> "ILone"
  IOne  -> "IOne"
  ISome -> "ISome"
  IAll  -> "IAll"

genXmlITypeType :: IType -> String
genXmlITypeType x = case x of
  TBoolean -> "IBoolean"
  TString -> "IString"
  TInteger -> "IInteger"
  TReal -> "IReal"
  TClafer _ -> "ISet"

genXmlIType :: IType -> String
genXmlIType x = tagType "Type" (genXmlITypeType x) ""
