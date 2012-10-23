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
module Language.Clafer.Generator.Graph (genSimpleGraph, genCVLGraph, traceAstModule, traceIrModule) where

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

genSimpleGraph m ir name = cleanOutput $ "digraph \"" ++ name ++ "\"\n{\nrankdir=BT;\nranksep=0.3;\nnodesep=0.1;\ngraph [fontname=Sans fontsize=11];\nnode [shape=box fontname=Sans fontsize=11 margin=0.020,0.020 height=0.2 ];\nedge [fontname=Sans fontsize=11];\n" ++ body ++ "}"
                           where body = graphSimpleModule m $ traceIrModule ir
                           
genCVLGraph m ir name = cleanOutput $ "digraph \"" ++ name ++ "\"\n{\nrankdir=BT;\nranksep=0.1;\nnodesep=0.1;\nnode [shape=box margin=0.025,0.025];\nedge [arrowhead=none];\n" ++ body ++ "}"
                       where body = graphCVLModule m $ traceIrModule ir

-- Simplified Notation Printer --
--toplevel: (Top_level (Boolean), Maybe Topmost parent, Maybe immediate parent)         
graphSimpleModule (Module [])     irMap = ""
graphSimpleModule (Module (x:xs)) irMap = graphSimpleDeclaration x (True, Nothing, Nothing) irMap ++ graphSimpleModule (Module xs) irMap
graphSimpleModule (PosModule _ declarations) irMap = graphSimpleModule (Module declarations) irMap

graphSimpleDeclaration (ElementDecl element)      topLevel irMap = graphSimpleElement element topLevel irMap
graphSimpleDeclaration (PosElementDecl _ element) topLevel irMap = graphSimpleDeclaration (ElementDecl element) topLevel irMap
graphSimpleDeclaration _                          _        _     = ""

graphSimpleElement (Subclafer clafer)  topLevel irMap = graphSimpleClafer clafer topLevel irMap
graphSimpleElement (PosSubclafer _ subclafer) topLevel irMap = graphSimpleElement (Subclafer subclafer) topLevel irMap
graphSimpleElement (ClaferUse name card elements) topLevel irMap = if snd3 topLevel == Nothing then "" else "\"" ++ fromJust (snd3 topLevel) ++ "\" -> \"" ++ graphSimpleName name topLevel irMap ++ "\" [arrowhead = onormal style = dashed constraint = false];\n"
graphSimpleElement (PosClaferUse span name card elements) topLevel irMap = if snd3 topLevel == Nothing then "" else "\"" ++ fromJust (snd3 topLevel) ++ "\" -> \"" ++ getUseId span irMap ++ "\" [arrowhead = onormal style = dashed constraint = false];\n"
graphSimpleElement _ _ _ = ""

graphSimpleElements ElementsEmpty topLevel irMap = ""
graphSimpleElements (PosElementsEmpty _) topLevel irMap = graphSimpleElements ElementsEmpty topLevel irMap
graphSimpleElements (ElementsList elements) topLevel irMap = concatMap (\x -> graphSimpleElement x topLevel irMap  ++ "\n") elements
graphSimpleElements (PosElementsList _ elements) topLevel irMap = graphSimpleElements (ElementsList elements) topLevel irMap 

graphSimpleClafer (Clafer abstract gCard id super card init elements) topLevel irMap = ""
graphSimpleClafer (PosClafer span abstract gCard id super card init elements) topLevel irMap
  | fst3 topLevel == True = let {tooltip = genTooltip (Module [ElementDecl (Subclafer (Clafer abstract gCard id super card init elements))]) irMap;
                               uid = getDivId span irMap} in
                             "\"" ++ uid ++ "\" [label=\"" ++ (head $ lines tooltip) ++ "\" URL=\"#" ++ uid ++ "\" tooltip=\"" ++ htmlNewlines tooltip ++ "\"];\n"
                             ++ graphSimpleSuper super (True, Just uid, Just uid) irMap ++ graphSimpleElements elements (False, Just uid, Just uid) irMap
  | otherwise             = let (PosIdent (_,ident)) = id in
                             graphSimpleSuper super (fst3 topLevel, snd3 topLevel, Just ident) irMap ++ graphSimpleElements elements (fst3 topLevel, snd3 topLevel, Just ident) irMap

graphSimpleSuper SuperEmpty topLevel irMap = ""
graphSimpleSuper (PosSuperEmpty _) topLevel irMap = graphSimpleSuper SuperEmpty topLevel irMap
graphSimpleSuper (SuperSome superHow setExp) topLevel irMap = let {parent [] = "error";
                                                            parent (uid@('c':xs):xss) = if '_' `elem` xs then uid else parent xss;
                                                            parent (xs:xss) = parent xss;
                                                            super = parent $ graphSimpleSetExp setExp topLevel irMap} in
                                                            if super == "error" then "" else "\"" ++ fromJust (snd3 topLevel) ++ "\" -> \"" ++ parent (graphSimpleSetExp setExp topLevel irMap) ++ "\"" ++ graphSimpleSuperHow superHow topLevel irMap
graphSimpleSuper (PosSuperSome _ superHow setExp) topLevel irMap = graphSimpleSuper (SuperSome superHow setExp) topLevel irMap

graphSimpleSuperHow SuperColon  topLevel irMap = " [arrowhead = onormal " ++ if fst3 topLevel == True then "constraint = true weight=100];\n" else "style = dashed weight=10 color=lightgray ];\n"
graphSimpleSuperHow (PosSuperColon _) topLevel irMap = graphSimpleSuperHow SuperColon topLevel irMap
graphSimpleSuperHow SuperArrow  topLevel irMap = " [arrowhead = vee weight=10 color=lightgray fontcolor=lightgray" ++ (if fst3 topLevel == True then "" else " label=" ++ (fromJust $ trd3 topLevel)) ++ "];\n"
graphSimpleSuperHow (PosSuperArrow _) topLevel irMap = graphSimpleSuperHow SuperArrow topLevel irMap
graphSimpleSuperHow SuperMArrow topLevel irMap = " [arrowhead = veevee weight=10 color=lightgray fontcolor=lightgray" ++ (if fst3 topLevel == True then "" else " label=" ++ (fromJust $ trd3 topLevel)) ++ "];\n"
graphSimpleSuperHow (PosSuperMArrow _) topLevel irMap = graphSimpleSuperHow SuperMArrow topLevel irMap     

graphSimpleName (Path modids) topLevel irMap = unwords $ map (\x -> graphSimpleModId x topLevel irMap) modids
graphSimpleName (PosPath _ modids) topLevel irMap = graphSimpleName (Path modids) topLevel irMap

graphSimpleModId (ModIdIdent posident) topLevel irMap = graphSimplePosIdent posident topLevel irMap
graphSimpleModId (PosModIdIdent _ posident) topLevel irMap = graphSimpleModId (ModIdIdent posident) topLevel irMap

graphSimplePosIdent (PosIdent (pos, id)) topLevel irMap = getUid (PosIdent (pos, id)) irMap

graphSimpleCard _ _ _ = ""
graphSimpleConstraint _ _ _ = ""
graphSimpleDecl _ _ _ = ""
graphSimpleInit _ _ _ = ""
graphSimpleInitHow _ _ _ = ""
graphSimpleExp _ _ _ = ""
graphSimpleQuant _ _ _ = ""
graphSimpleGoal _ _ _ = ""
graphSimpleSoftConstraint _ _ _ = ""
graphSimpleAbstract _ _ _ = ""
graphSimpleGCard _ _ _ = ""
graphSimpleNCard _ _ _ = ""
graphSimpleExInteger _ _ _ = ""

graphSimpleSetExp (ClaferId name) topLevel irMap = [graphSimpleName name topLevel irMap]
graphSimpleSetExp (PosClaferId _ name) topLevel irMap = graphSimpleSetExp (ClaferId name) topLevel irMap
graphSimpleSetExp (Union set1 set2) topLevel irMap = graphSimpleSetExp set1 topLevel irMap ++ graphSimpleSetExp set2 topLevel irMap
graphSimpleSetExp (PosUnion _ set1 set2) topLevel irMap = graphSimpleSetExp (Union set1 set2) topLevel irMap
graphSimpleSetExp (UnionCom set1 set2) topLevel irMap = graphSimpleSetExp set1 topLevel irMap ++ graphSimpleSetExp set2 topLevel irMap
graphSimpleSetExp (PosUnionCom _ set1 set2) topLevel irMap = graphSimpleSetExp (UnionCom set1 set2) topLevel irMap
graphSimpleSetExp (Difference set1 set2) topLevel irMap = graphSimpleSetExp set1 topLevel irMap ++ graphSimpleSetExp set2 topLevel irMap
graphSimpleSetExp (PosDifference _ set1 set2) topLevel irMap = graphSimpleSetExp (Difference set1 set2) topLevel irMap
graphSimpleSetExp (Intersection set1 set2) topLevel irMap = graphSimpleSetExp set1 topLevel irMap ++ graphSimpleSetExp set2 topLevel irMap
graphSimpleSetExp (PosIntersection _ set1 set2) topLevel irMap = graphSimpleSetExp (Intersection set1 set2) topLevel irMap
graphSimpleSetExp (Domain set1 set2) topLevel irMap = graphSimpleSetExp set1 topLevel irMap ++ graphSimpleSetExp set2 topLevel irMap
graphSimpleSetExp (PosDomain _ set1 set2) topLevel irMap = graphSimpleSetExp (Domain set1 set2) topLevel irMap
graphSimpleSetExp (Range set1 set2) topLevel irMap = graphSimpleSetExp set1 topLevel irMap ++ graphSimpleSetExp set2 topLevel irMap
graphSimpleSetExp (PosRange _ set1 set2) topLevel irMap = graphSimpleSetExp (Range set1 set2) topLevel irMap
graphSimpleSetExp (Join set1 set2) topLevel irMap = graphSimpleSetExp set1 topLevel irMap ++ graphSimpleSetExp set2 topLevel irMap
graphSimpleSetExp (PosJoin _ set1 set2) topLevel irMap = graphSimpleSetExp (Join set1 set2) topLevel irMap

graphSimpleEnumId (EnumIdIdent posident) topLevel irMap = graphSimplePosIdent posident topLevel irMap
graphSimpleEnumId (PosEnumIdIdent _ posident) topLevel irMap = graphSimpleEnumId (EnumIdIdent posident) topLevel irMap

-- CVL Printer --
--parent is Maybe the uid of the immediate parent
graphCVLModule (Module [])     irMap = ""
graphCVLModule (Module (x:xs)) irMap = graphCVLDeclaration x Nothing irMap ++ graphCVLModule (Module xs) irMap
graphCVLModule (PosModule _ declarations) irMap = graphCVLModule (Module declarations) irMap

graphCVLDeclaration (ElementDecl element)      parent irMap = graphCVLElement element parent irMap
graphCVLDeclaration (PosElementDecl _ element) parent irMap = graphCVLDeclaration (ElementDecl element) parent irMap
graphCVLDeclaration _                          _        _     = ""

graphCVLElement (Subclafer clafer)  parent irMap = graphCVLClafer clafer parent irMap
graphCVLElement (PosSubclafer _ subclafer) parent irMap = graphCVLElement (Subclafer subclafer) parent irMap
graphCVLElement (ClaferUse name card elements) parent irMap = if parent == Nothing then "" else "?" ++ " -> " ++ graphCVLName name parent irMap ++ " [arrowhead = onormal style = dashed constraint = false];\n"
graphCVLElement (PosClaferUse span name card elements) parent irMap = if parent == Nothing then "" else "?" ++ " -> " ++ getUseId span irMap ++ " [arrowhead = onormal style = dashed constraint = false];\n"
graphCVLElement (Subconstraint constraint) parent irMap = graphCVLConstraint constraint parent irMap
graphCVLElement (PosSubconstraint _ constraint) parent irMap = graphCVLElement (Subconstraint constraint) parent irMap
graphCVLElement _ _ _ = ""

graphCVLElements ElementsEmpty parent irMap = ""
graphCVLElements (PosElementsEmpty _) parent irMap = graphCVLElements ElementsEmpty parent irMap
graphCVLElements (ElementsList elements) parent irMap = concatMap (\x -> graphCVLElement x parent irMap  ++ "\n") elements
graphCVLElements (PosElementsList _ elements) parent irMap = graphCVLElements (ElementsList elements) parent irMap 

graphCVLClafer (Clafer abstract gCard id super card init elements) parent irMap = ""
graphCVLClafer (PosClafer span abstract gCard id super card init elements) parent irMap
   = let {tooltip = genTooltip (Module [ElementDecl (Subclafer (Clafer abstract gCard id super card init elements))]) irMap;
          uid = getDivId span irMap;
          gcard = graphCVLGCard gCard parent irMap;
          super' = graphCVLSuper super parent irMap} in
     "\"" ++ uid ++ "\" [URL=\"#" ++ uid ++ "\" label=\"" ++ dropUid uid ++ super' ++ (if choiceCard card then "\" style=rounded"  else " [" ++ graphCVLCard card parent irMap ++ "]\"")
     ++ (if super' == "" then "" else " shape=oval") ++ "];\n"
     ++ (if gcard == "" then "" else "g" ++ uid ++ " [label=\"" ++ gcard ++ "\" fontsize=10 shape=triangle];\ng" ++ uid ++ " -> " ++ uid ++ " [weight=10];\n")
     ++ (if parent==Nothing then "" else uid ++ " -> " ++ fromJust parent ++ (if lowerCard card == "0" then " [style=dashed]" else "") ++ ";\n")
     ++ graphCVLElements elements (if gcard == "" then (Just uid) else (Just $ "g" ++ uid)) irMap


graphCVLSuper SuperEmpty parent irMap = ""
graphCVLSuper (PosSuperEmpty _) parent irMap = graphCVLSuper SuperEmpty parent irMap
graphCVLSuper (SuperSome superHow setExp) parent irMap = graphCVLSuperHow superHow parent irMap ++ concat (graphCVLSetExp setExp parent irMap)
graphCVLSuper (PosSuperSome _ superHow setExp) parent irMap = graphCVLSuper (SuperSome superHow setExp) parent irMap

graphCVLSuperHow SuperColon _ _ = ":"
graphCVLSuperHow (PosSuperColon _) _ _ = ":"
graphCVLSuperHow SuperArrow _ _ = "->"
graphCVLSuperHow (PosSuperArrow _) _ _ = "->"
graphCVLSuperHow SuperMArrow _ _ = "->>"
graphCVLSuperHow (PosSuperMArrow _) _ _ = "->>"

graphCVLName (Path modids) parent irMap = unwords $ map (\x -> graphCVLModId x parent irMap) modids
graphCVLName (PosPath _ modids) parent irMap = graphCVLName (Path modids) parent irMap

graphCVLModId (ModIdIdent posident) parent irMap = graphCVLPosIdent posident parent irMap
graphCVLModId (PosModIdIdent _ posident) parent irMap = graphCVLModId (ModIdIdent posident) parent irMap

graphCVLPosIdent (PosIdent (pos, id)) parent irMap = getUid (PosIdent (pos, id)) irMap

graphCVLConstraint (Constraint exps) parent irMap = ""
graphCVLConstraint (PosConstraint span exps) parent irMap = let body = htmlNewlines $ genTooltip (Module [ElementDecl (Subconstraint (Constraint exps))]) irMap;
                                                                       uid = "\"" ++ getExpId span irMap ++ "\""
                                                                    in uid ++ " [label=\"" ++ body ++ "\" shape=parallelogram];\n" ++
                                                                      if parent == Nothing then "" else uid ++ " -> \"" ++ fromJust parent ++ "\";\n"

graphCVLCard card parent irMap = case card of
  CardEmpty  -> "1..1"
  CardLone  ->  "0..1"
  CardSome  ->  "1..*"
  CardAny  ->   "0..*"
  CardNum (PosInteger (_, n))  -> n ++ ".." ++ n
  CardInterval ncard  -> graphCVLNCard ncard parent irMap
  PosCardEmpty s  -> "1..1"
  PosCardLone s  ->  "0..1"
  PosCardSome s  ->  "1..*"
  PosCardAny s ->    "0..*"
  PosCardNum s (PosInteger (_, n))  -> n ++ ".." ++ n
  PosCardInterval s ncard  -> graphCVLNCard ncard parent irMap

graphCVLNCard nCard parent irMap = case nCard of
  NCard (PosInteger (pos, num)) exInteger -> num ++ ".." ++ graphCVLExInteger exInteger parent irMap
  PosNCard _ posInteger exInteger -> graphCVLNCard (NCard posInteger exInteger) parent irMap

graphCVLExInteger ExIntegerAst parent irMap = "*"
graphCVLExInteger (PosExIntegerAst _) parent irMap = graphCVLExInteger ExIntegerAst parent irMap
graphCVLExInteger (ExIntegerNum (PosInteger(pos, num))) parent irMap = num
graphCVLExInteger (PosExIntegerNum _ posInteger) parent irMap = graphCVLExInteger (ExIntegerNum posInteger) parent irMap

graphCVLGCard gCard parent irMap = case gCard of
  (GCardInterval ncard) -> graphCVLNCard ncard parent irMap
  (PosGCardInterval _ ncard) -> graphCVLNCard ncard parent irMap
  GCardEmpty        -> ""
  (PosGCardEmpty _) -> ""
  GCardXor          -> "1..1"
  (PosGCardXor _)   -> "1..1"
  GCardOr           -> "1..*"
  (PosGCardOr _)    -> "1..*"
  GCardMux          -> "0..1"
  (PosGCardMux _)   -> "0..1"
  GCardOpt          -> ""
  (PosGCardOpt _)   -> ""


graphCVLDecl _ _ _ = ""
graphCVLInit _ _ _ = ""
graphCVLInitHow _ _ _ = ""
graphCVLExp _ _ _ = ""
graphCVLQuant _ _ _ = ""
graphCVLGoal _ _ _ = ""
graphCVLSoftConstraint _ _ _ = ""
graphCVLAbstract _ _ _ = ""

graphCVLSetExp (ClaferId name) parent irMap = [graphCVLName name parent irMap]
graphCVLSetExp (PosClaferId _ name) parent irMap = graphCVLSetExp (ClaferId name) parent irMap
graphCVLSetExp (Union set1 set2) parent irMap = graphCVLSetExp set1 parent irMap ++ graphCVLSetExp set2 parent irMap
graphCVLSetExp (PosUnion _ set1 set2) parent irMap = graphCVLSetExp (Union set1 set2) parent irMap
graphCVLSetExp (UnionCom set1 set2) parent irMap = graphCVLSetExp set1 parent irMap ++ graphCVLSetExp set2 parent irMap
graphCVLSetExp (PosUnionCom _ set1 set2) parent irMap = graphCVLSetExp (UnionCom set1 set2) parent irMap
graphCVLSetExp (Difference set1 set2) parent irMap = graphCVLSetExp set1 parent irMap ++ graphCVLSetExp set2 parent irMap
graphCVLSetExp (PosDifference _ set1 set2) parent irMap = graphCVLSetExp (Difference set1 set2) parent irMap
graphCVLSetExp (Intersection set1 set2) parent irMap = graphCVLSetExp set1 parent irMap ++ graphCVLSetExp set2 parent irMap
graphCVLSetExp (PosIntersection _ set1 set2) parent irMap = graphCVLSetExp (Intersection set1 set2) parent irMap
graphCVLSetExp (Domain set1 set2) parent irMap = graphCVLSetExp set1 parent irMap ++ graphCVLSetExp set2 parent irMap
graphCVLSetExp (PosDomain _ set1 set2) parent irMap = graphCVLSetExp (Domain set1 set2) parent irMap
graphCVLSetExp (Range set1 set2) parent irMap = graphCVLSetExp set1 parent irMap ++ graphCVLSetExp set2 parent irMap
graphCVLSetExp (PosRange _ set1 set2) parent irMap = graphCVLSetExp (Range set1 set2) parent irMap
graphCVLSetExp (Join set1 set2) parent irMap = graphCVLSetExp set1 parent irMap ++ graphCVLSetExp set2 parent irMap
graphCVLSetExp (PosJoin _ set1 set2) parent irMap = graphCVLSetExp (Join set1 set2) parent irMap

graphCVLEnumId (EnumIdIdent posident) parent irMap = graphCVLPosIdent posident parent irMap
graphCVLEnumId (PosEnumIdIdent _ posident) parent irMap = graphCVLEnumId (EnumIdIdent posident) parent irMap

choiceCard CardEmpty = True
choiceCard (PosCardEmpty _) = choiceCard CardEmpty
choiceCard CardLone = True
choiceCard (PosCardLone _) = choiceCard CardLone
choiceCard (CardInterval nCard) = case nCard of
  PosNCard _ (PosInteger (_, low)) exInteger -> choiceCard' low exInteger
  NCard (PosInteger (_, low)) exInteger -> choiceCard' low exInteger
  where choiceCard' low exInteger = if low == "0" || low == "1"
                                    then case exInteger of
                                      ExIntegerAst -> False
                                      PosExIntegerAst _ -> False
                                      ExIntegerNum (PosInteger (_, high)) -> high == "0" || high == "1"
                                      PosExIntegerNum _ (PosInteger (_, high)) -> high == "0" || high == "1"
                                    else False
choiceCard (PosCardInterval _ nCard) = choiceCard (CardInterval nCard)
choiceCard _ = False

lowerCard card = takeWhile (/= '.') $ graphCVLCard card Nothing Map.empty

--Miscellaneous functions
dropUid uid = let id = rest $ dropWhile (\x -> x /= '_') uid in if id == "" then uid else id

rest [] = []
rest (_:xs) = xs

getUid (PosIdent (pos, id)) irMap = if Map.lookup (range (PosIdent (pos, id))) irMap == Nothing
                        then id
                        else let IRPExp pexp = head $ fromJust $ Map.lookup (range (PosIdent (pos, id))) irMap in
                          findUid id $ getIdentPExp pexp
                          where {getIdentPExp (PExp _ _ _ exp) = getIdentIExp exp;
                                 getIdentIExp (IFunExp _ exps) = concatMap getIdentPExp exps;
                                 getIdentIExp (IClaferId _ id _) = [id];
                                 getIdentIExp (IDeclPExp _ _ pexp) = getIdentPExp pexp;
                                 getIdentIExp _ = [];
                                 findUid name (x:xs) = if name == dropUid x then x else findUid name xs;
                                 findUid name []     = name}
                        
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

getExpId span irMap = if Map.lookup span irMap == Nothing
                      then "Uid not Found"
                      else let IRPExp pexp = head $ fromJust $ Map.lookup span irMap in pid pexp

while bool exp = if bool then exp else []

htmlNewlines "" = ""
htmlNewlines ('\n':xs) = "&#10;" ++ htmlNewlines xs
htmlNewlines (x:xs) = x:htmlNewlines xs

cleanOutput "" = ""
cleanOutput (' ':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput ('\n':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput (' ':'<':'b':'r':'>':xs) = "<br>"++cleanOutput xs
cleanOutput (x:xs) = x : cleanOutput xs
