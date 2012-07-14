{-
 Copyright (C) 2012 Christopher Walker <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Generator.Graph (genGraph, traceAstModule, traceIrModule) where

import Language.Clafer.Common(fst3,snd3,trd3)
import Language.Clafer.Front.Absclafer
import Language.Clafer.Front.LayoutResolver(revertLayout)
import Language.Clafer.Front.Mapper(range)
import Language.Clafer.Intermediate.Tracing
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Generator.Html(genHtml, genText, genTooltip, printModule)
import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Maybe
import Prelude hiding (exp)


genGraph m ir name = cleanOutput $ "digraph " ++ name ++ "\n{\nrankdir=BT;\nnode [shape=box];\n" ++ body ++ "}"
                       where body = graphModule m $ traceIrModule ir

graphModule (Module [])     irMap = ""
graphModule (Module (x:xs)) irMap = graphDeclaration x (True, Nothing, Nothing) irMap ++ graphModule (Module xs) irMap
graphModule (PosModule _ declarations) irMap = graphModule (Module declarations) irMap

graphDeclaration (ElementDecl element)      topLevel irMap = graphElement element topLevel irMap
graphDeclaration (PosElementDecl _ element) topLevel irMap = graphDeclaration (ElementDecl element) topLevel irMap
graphDeclaration _                          _        _     = ""

graphElement (Subclafer clafer)  topLevel irMap = graphClafer clafer topLevel irMap
graphElement (PosSubclafer _ subclafer) topLevel irMap = graphElement (Subclafer subclafer) topLevel irMap
graphElement (ClaferUse name card elements) topLevel irMap = if snd3 topLevel == Nothing then "" else fromJust (snd3 topLevel) ++ " -> " ++ graphName name topLevel irMap ++ " [arrowhead = onormal style = dashed constraint = false];\n"
graphElement (PosClaferUse span name card elements) topLevel irMap = if snd3 topLevel == Nothing then "" else fromJust (snd3 topLevel) ++ " -> " ++ getUseId span irMap ++ " [arrowhead = onormal style = dashed constraint = false];\n"
graphElement _ _ _ = ""

graphElements ElementsEmpty topLevel irMap = ""
graphElements (PosElementsEmpty _) topLevel irMap = graphElements ElementsEmpty topLevel irMap
graphElements (ElementsList elements) topLevel irMap = concatMap (\x -> graphElement x topLevel irMap  ++ "\n") elements
graphElements (PosElementsList _ elements) topLevel irMap = graphElements (ElementsList elements) topLevel irMap 

graphClafer (Clafer abstract gCard id super card init elements) topLevel irMap = ""
graphClafer (PosClafer span abstract gCard id super card init elements) topLevel irMap
  | fst3 topLevel == True = let {tooltip = genTooltip (Module [ElementDecl (Subclafer (Clafer abstract gCard id super card init elements))]) irMap;
                               uid = getDivId span irMap} in
                             uid ++ " [label=\"" ++ (head $ lines tooltip) ++ "\" URL=\"#" ++ uid ++ "\" tooltip=\"" ++ htmlNewlines tooltip ++ "\"];\n"
                             ++ graphSuper super (True, Just uid, Just uid) irMap ++ graphElements elements (False, Just uid, Just uid) irMap
  | otherwise             = let (PosIdent (_,ident)) = id in
                             graphSuper super (fst3 topLevel, snd3 topLevel, Just ident) irMap ++ graphElements elements (fst3 topLevel, snd3 topLevel, Just ident) irMap

graphSuper SuperEmpty topLevel irMap = ""
graphSuper (PosSuperEmpty _) topLevel irMap = graphSuper SuperEmpty topLevel irMap
graphSuper (SuperSome superHow setExp) topLevel irMap = let {parent [] = "error";
                                                            parent (uid@('c':xs):xss) = if '_' `elem` xs then uid else parent xss;
                                                            parent (xs:xss) = parent xss;
                                                            super = parent $ graphSetExp setExp topLevel irMap} in
                                                            if super == "error" then "" else fromJust (snd3 topLevel) ++ " -> " ++ parent (graphSetExp setExp topLevel irMap) ++ graphSuperHow superHow topLevel irMap
graphSuper (PosSuperSome _ superHow setExp) topLevel irMap = graphSuper (SuperSome superHow setExp) topLevel irMap

graphSuperHow SuperColon  topLevel irMap = " [arrowhead = onormal " ++ if fst3 topLevel == True then "constraint = true];\n" else "style = dashed constraint = false];\n"
graphSuperHow (PosSuperColon _) topLevel irMap = graphSuperHow SuperColon topLevel irMap
graphSuperHow SuperArrow  topLevel irMap = " [arrowhead = vee constraint = false" ++ (if fst3 topLevel == True then "" else " label=" ++ (fromJust $ trd3 topLevel)) ++ "];\n"
graphSuperHow (PosSuperArrow _) topLevel irMap = graphSuperHow SuperArrow topLevel irMap
graphSuperHow SuperMArrow topLevel irMap = " [arrowhead = veevee constraint = false" ++ (if fst3 topLevel == True then "" else " label=" ++ (fromJust $ trd3 topLevel)) ++ "];\n"
graphSuperHow (PosSuperMArrow _) topLevel irMap = graphSuperHow SuperMArrow topLevel irMap     

graphName (Path modids) topLevel irMap = unwords $ map (\x -> graphModId x topLevel irMap) modids
graphName (PosPath _ modids) topLevel irMap = graphName (Path modids) topLevel irMap

graphModId (ModIdIdent posident) topLevel irMap = graphPosIdent posident topLevel irMap
graphModId (PosModIdIdent _ posident) topLevel irMap = graphModId (ModIdIdent posident) topLevel irMap

graphPosIdent (PosIdent (pos, id)) topLevel irMap = getUid (PosIdent (pos, id)) irMap

graphCard _ _ _ = ""
graphConstraint _ _ _ = ""
graphDecl _ _ _ = ""
graphInit _ _ _ = ""
graphInitHow _ _ _ = ""
graphExp _ _ _ = ""
graphQuant _ _ _ = ""
graphGoal _ _ _ = ""
graphSoftConstraint _ _ _ = ""
graphAbstract _ _ _ = ""
graphGCard _ _ _ = ""
graphNCard _ _ _ = ""
graphExInteger _ _ _ = ""

graphSetExp (ClaferId name) topLevel irMap = [graphName name topLevel irMap]
graphSetExp (PosClaferId _ name) topLevel irMap = graphSetExp (ClaferId name) topLevel irMap
graphSetExp (Union set1 set2) topLevel irMap = graphSetExp set1 topLevel irMap ++ graphSetExp set2 topLevel irMap
graphSetExp (PosUnion _ set1 set2) topLevel irMap = graphSetExp (Union set1 set2) topLevel irMap
graphSetExp (UnionCom set1 set2) topLevel irMap = graphSetExp set1 topLevel irMap ++ graphSetExp set2 topLevel irMap
graphSetExp (PosUnionCom _ set1 set2) topLevel irMap = graphSetExp (UnionCom set1 set2) topLevel irMap
graphSetExp (Difference set1 set2) topLevel irMap = graphSetExp set1 topLevel irMap ++ graphSetExp set2 topLevel irMap
graphSetExp (PosDifference _ set1 set2) topLevel irMap = graphSetExp (Difference set1 set2) topLevel irMap
graphSetExp (Intersection set1 set2) topLevel irMap = graphSetExp set1 topLevel irMap ++ graphSetExp set2 topLevel irMap
graphSetExp (PosIntersection _ set1 set2) topLevel irMap = graphSetExp (Intersection set1 set2) topLevel irMap
graphSetExp (Domain set1 set2) topLevel irMap = graphSetExp set1 topLevel irMap ++ graphSetExp set2 topLevel irMap
graphSetExp (PosDomain _ set1 set2) topLevel irMap = graphSetExp (Domain set1 set2) topLevel irMap
graphSetExp (Range set1 set2) topLevel irMap = graphSetExp set1 topLevel irMap ++ graphSetExp set2 topLevel irMap
graphSetExp (PosRange _ set1 set2) topLevel irMap = graphSetExp (Range set1 set2) topLevel irMap
graphSetExp (Join set1 set2) topLevel irMap = graphSetExp set1 topLevel irMap ++ graphSetExp set2 topLevel irMap
graphSetExp (PosJoin _ set1 set2) topLevel irMap = graphSetExp (Join set1 set2) topLevel irMap

graphEnumId (EnumIdIdent posident) topLevel irMap = graphPosIdent posident topLevel irMap
graphEnumId (PosEnumIdIdent _ posident) topLevel irMap = graphEnumId (EnumIdIdent posident) topLevel irMap

dropUid uid = let id = rest $ dropWhile (\x -> x /= '_') uid in if id == "" then uid else id

--so it fails more gracefully on empty lists
rest [] = []
rest (_:xs) = xs

getUid (PosIdent (pos, id)) irMap = if Map.lookup (range (PosIdent (pos, id))) irMap == Nothing
                        then "Lookup failed"
                        else let IRPExp pexp = head $ fromJust $ Map.lookup (range (PosIdent (pos, id))) irMap in
                          findUid id $ getIdentPExp pexp
                          where {getIdentPExp (PExp _ _ _ exp) = getIdentIExp exp;
                                 getIdentIExp (IFunExp _ exps) = concatMap getIdentPExp exps;
                                 getIdentIExp (IClaferId _ id _) = [id];
                                 getIdentIExp (IDeclPExp _ _ pexp) = getIdentPExp pexp;
                                 getIdentIExp _ = [];
                                 findUid name (x:xs) = if name == dropUid x then x else findUid name xs;
                                 findUid name []     = "Uid not found"}
--adjust this to return a list of all ids (this, ref, etc. included) and choose the UID that reduces to the input ID.
                        
getDivId span irMap = if Map.lookup span irMap == Nothing
                      then "Uid not Found"
                      else let IRClafer iClafer = head $ fromJust $ Map.lookup span irMap in
                        uid iClafer

getSuperId span irMap = if Map.lookup span irMap == Nothing
                        then "Uid not Found"
                        else let IRPExp pexp = head $ fromJust $ Map.lookup span irMap in
                          sident $ exp pexp

getUseId :: Span -> Map.Map Span [Ir] -> String
getUseId span irMap = if Map.lookup span irMap == Nothing
                      then "Uid not Found"
                      else let IRClafer iClafer = head $ fromJust $ Map.lookup span irMap in
                        sident $ exp $ head $ supers $ super iClafer

while bool exp = if bool then exp else []

htmlNewlines "" = "";
                               htmlNewlines ('\n':xs) = "&#10;" ++ htmlNewlines xs;
                               htmlNewlines (x:xs) = x:htmlNewlines xs

cleanOutput "" = ""
cleanOutput (' ':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput ('\n':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput (' ':'<':'b':'r':'>':xs) = "<br>"++cleanOutput xs
cleanOutput (x:xs) = x : cleanOutput xs
