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
import Language.Clafer.Front.Mapper(range)
import Language.Clafer.Intermediate.Tracing
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Generator.Html(genTooltip)
import qualified Data.Map as Map
import Data.Maybe
import Prelude hiding (exp)

genSimpleGraph :: Module -> IModule -> String -> Bool -> String
genSimpleGraph m ir name showRefs = cleanOutput $ "digraph \"" ++ name ++ "\"\n{\n\nrankdir=BT;\nranksep=0.3;\nnodesep=0.1;\ngraph [fontname=Sans fontsize=11];\nnode [shape=box color=lightgray fontname=Sans fontsize=11 margin=\"0.02,0.02\" height=0.2 ];\nedge [fontname=Sans fontsize=11];\n" ++ b ++ "}"
                           where b = graphSimpleModule m (traceIrModule ir) showRefs

genCVLGraph :: Module -> IModule -> String -> String                          
genCVLGraph m ir name = cleanOutput $ "digraph \"" ++ name ++ "\"\n{\nrankdir=BT;\nranksep=0.1;\nnodesep=0.1;\nnode [shape=box margin=\"0.025,0.025\"];\nedge [arrowhead=none];\n" ++ b ++ "}"
                       where b = graphCVLModule m $ traceIrModule ir

-- Simplified Notation Printer --
--toplevel: (Top_level (Boolean), Maybe Topmost parent, Maybe immediate parent)         
graphSimpleModule :: Module -> Map.Map Span [Ir] -> Bool -> String
graphSimpleModule (Module [])                _     _        = ""
graphSimpleModule (Module (x:xs))            irMap showRefs = graphSimpleDeclaration x (True, Nothing, Nothing) irMap showRefs ++ graphSimpleModule (Module xs) irMap showRefs
graphSimpleModule (PosModule _ declarations) irMap showRefs = graphSimpleModule (Module declarations) irMap showRefs

graphSimpleDeclaration :: Declaration
                          -> (Bool, Maybe String, Maybe String)
                          -> Map.Map Span [Ir]
                          -> Bool
                          -> String
graphSimpleDeclaration (ElementDecl element)      topLevel irMap showRefs = graphSimpleElement element topLevel irMap showRefs
graphSimpleDeclaration (PosElementDecl _ element) topLevel irMap showRefs = graphSimpleDeclaration (ElementDecl element) topLevel irMap showRefs
graphSimpleDeclaration _                          _        _     _        = ""

graphSimpleElement :: Element
                      -> (Bool, Maybe String, Maybe String)
                      -> Map.Map Span [Ir]
                      -> Bool
                      -> String
graphSimpleElement (Subclafer clafer)                     topLevel irMap showRefs = graphSimpleClafer clafer topLevel irMap showRefs
graphSimpleElement (PosSubclafer _ subclafer)             topLevel irMap showRefs = graphSimpleElement (Subclafer subclafer) topLevel irMap showRefs
graphSimpleElement (ClaferUse name _ _)         topLevel irMap _        = if snd3 topLevel == Nothing then "" else "\"" ++ fromJust (snd3 topLevel) ++ "\" -> \"" ++ graphSimpleName name topLevel irMap ++ "\" [arrowhead=vee arrowtail=diamond dir=both style=solid constraint=false minlen=2 arrowsize=0.6 penwidth=0.5 ];\n"
graphSimpleElement (PosClaferUse s _ _ _) topLevel irMap _        = if snd3 topLevel == Nothing then "" else "\"" ++ fromJust (snd3 topLevel) ++ "\" -> \"" ++ getUseId s irMap ++ "\" [arrowhead=vee arrowtail=diamond dir=both style=solid constraint=false minlen=2 arrowsize=0.6 penwidth=0.5 ];\n"
graphSimpleElement _ _ _ _ = ""

graphSimpleElements :: Elements
                      -> (Bool, Maybe String, Maybe String)
                      -> Map.Map Span [Ir]
                      -> Bool
                      -> String
graphSimpleElements ElementsEmpty                _        _     _        = ""
graphSimpleElements (PosElementsEmpty _)         topLevel irMap showRefs = graphSimpleElements ElementsEmpty topLevel irMap showRefs
graphSimpleElements (ElementsList es)      topLevel irMap showRefs = concatMap (\x -> graphSimpleElement x topLevel irMap showRefs ++ "\n") es
graphSimpleElements (PosElementsList _ es) topLevel irMap showRefs = graphSimpleElements (ElementsList es) topLevel irMap showRefs

graphSimpleClafer :: Clafer
                      -> (Bool, Maybe String, Maybe String)
                      -> Map.Map Span [Ir]
                      -> Bool
                      -> String 
graphSimpleClafer (Clafer _ _ _ _ _ _ _)         _        _     _ = ""
graphSimpleClafer (PosClafer s abstract gCard id' super' crd init' es) topLevel irMap showRefs
  | fst3 topLevel == True = let {tooltip = genTooltip (Module [ElementDecl (Subclafer (Clafer abstract gCard id' super' crd init' es))]) irMap;
                               uid' = getDivId s irMap} in
                             "\"" ++ uid' ++ "\" [label=\"" ++ (head $ lines tooltip) ++ "\" URL=\"#" ++ uid' ++ "\" tooltip=\"" ++ htmlNewlines tooltip ++ "\"];\n"
                             ++ graphSimpleSuper super' (True, Just uid', Just uid') irMap showRefs ++ graphSimpleElements es (False, Just uid', Just uid') irMap showRefs
  | otherwise             = let (PosIdent (_,ident')) = id' in
                             graphSimpleSuper super' (fst3 topLevel, snd3 topLevel, Just ident') irMap showRefs ++ graphSimpleElements es (fst3 topLevel, snd3 topLevel, Just ident') irMap showRefs

graphSimpleSuper :: Super
                  -> (Bool, Maybe String, Maybe String)
                  -> Map.Map Span [Ir]
                  -> Bool
                  -> String
graphSimpleSuper SuperEmpty _ _ _ = ""
graphSimpleSuper (PosSuperEmpty _) topLevel irMap showRefs = graphSimpleSuper SuperEmpty topLevel irMap showRefs
graphSimpleSuper (SuperSome superHow setExp) topLevel irMap showRefs = let {parent [] = "error";
                                                            parent (uid'@('c':xs):xss) = if '_' `elem` xs then uid' else parent xss;
                                                            parent (_:xss) = parent xss;
                                                            super' = parent $ graphSimpleSetExp setExp topLevel irMap} in
                                                            if super' == "error" then "" else "\"" ++ fromJust (snd3 topLevel) ++ "\" -> \"" ++ parent (graphSimpleSetExp setExp topLevel irMap) ++ "\"" ++ graphSimpleSuperHow superHow topLevel irMap showRefs
graphSimpleSuper (PosSuperSome _ superHow setExp) topLevel irMap showRefs = graphSimpleSuper (SuperSome superHow setExp) topLevel irMap showRefs

graphSimpleSuperHow :: SuperHow -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> Bool -> String
graphSimpleSuperHow SuperColon topLevel _ _ = " [" ++ if fst3 topLevel == True 
                                                                 then "arrowhead=onormal constraint=true weight=100];\n" 
                                                                 else "arrowhead=vee arrowtail=diamond dir=both style=solid weight=10 color=gray arrowsize=0.6 minlen=2 penwidth=0.5 constraint=true];\n"
graphSimpleSuperHow (PosSuperColon _) topLevel irMap showRefs  = graphSimpleSuperHow SuperColon topLevel irMap showRefs
graphSimpleSuperHow SuperArrow topLevel _ showRefs = " [arrowhead=vee arrowsize=0.6 penwidth=0.5 constraint=true weight=10 color=" ++ refColour showRefs ++ " fontcolor=" ++ refColour showRefs ++ (if fst3 topLevel == True then "" else " label=" ++ (fromJust $ trd3 topLevel)) ++ "];\n"
graphSimpleSuperHow (PosSuperArrow _) topLevel irMap showRefs = graphSimpleSuperHow SuperArrow topLevel irMap showRefs
graphSimpleSuperHow SuperMArrow topLevel _ showRefs = " [arrowhead=veevee arrowsize=0.6 minlen=1.5 penwidth=0.5 constraint=true weight=10 color=" ++ refColour showRefs ++ " fontcolor=" ++ refColour showRefs ++ (if fst3 topLevel == True then "" else " label=" ++ (fromJust $ trd3 topLevel)) ++ "];\n"
graphSimpleSuperHow (PosSuperMArrow _) topLevel irMap showRefs = graphSimpleSuperHow SuperMArrow topLevel irMap showRefs  

refColour :: Bool -> String 
refColour True = "lightgray" 
refColour False = "transparent"

graphSimpleName :: Name -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> String
graphSimpleName (Path modids) topLevel irMap = unwords $ map (\x -> graphSimpleModId x topLevel irMap) modids
graphSimpleName (PosPath _ modids) topLevel irMap = graphSimpleName (Path modids) topLevel irMap

graphSimpleModId :: ModId -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> String
graphSimpleModId (ModIdIdent posident) _ irMap = graphSimplePosIdent posident irMap
graphSimpleModId (PosModIdIdent _ posident) topLevel irMap = graphSimpleModId (ModIdIdent posident) topLevel irMap

graphSimplePosIdent :: PosIdent -> Map.Map Span [Ir] -> String
graphSimplePosIdent (PosIdent (pos, id')) irMap = getUid (PosIdent (pos, id')) irMap

{-graphSimpleCard _ _ _ = ""
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
graphSimpleExInteger _ _ _ = ""-}

graphSimpleSetExp :: SetExp -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> [String]
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

{-graphSimpleEnumId :: EnumId -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> String
graphSimpleEnumId (EnumIdIdent posident) _ irMap = graphSimplePosIdent posident irMap
graphSimpleEnumId (PosEnumIdIdent _ posident) topLevel irMap = graphSimpleEnumId (EnumIdIdent posident) topLevel irMap-}

-- CVL Printer --
--parent is Maybe the uid of the immediate parent
graphCVLModule :: Module -> Map.Map Span [Ir] -> String
graphCVLModule (Module [])     _ = ""
graphCVLModule (Module (x:xs)) irMap = graphCVLDeclaration x Nothing irMap ++ graphCVLModule (Module xs) irMap
graphCVLModule (PosModule _ declarations) irMap = graphCVLModule (Module declarations) irMap

graphCVLDeclaration :: Declaration -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLDeclaration (ElementDecl element)      parent irMap = graphCVLElement element parent irMap
graphCVLDeclaration (PosElementDecl _ element) parent irMap = graphCVLDeclaration (ElementDecl element) parent irMap
graphCVLDeclaration _                          _        _     = ""

graphCVLElement :: Element -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLElement (Subclafer clafer)  parent irMap = graphCVLClafer clafer parent irMap
graphCVLElement (PosSubclafer _ subclafer) parent irMap = graphCVLElement (Subclafer subclafer) parent irMap
graphCVLElement (ClaferUse name _ _) parent irMap = if parent == Nothing then "" else "?" ++ " -> " ++ graphCVLName name parent irMap ++ " [arrowhead = onormal style = dashed constraint = false];\n"
graphCVLElement (PosClaferUse s _ _ _) parent irMap = if parent == Nothing then "" else "?" ++ " -> " ++ getUseId s irMap ++ " [arrowhead = onormal style = dashed constraint = false];\n"
graphCVLElement (Subconstraint constraint) parent irMap = graphCVLConstraint constraint parent irMap
graphCVLElement (PosSubconstraint _ constraint) parent irMap = graphCVLElement (Subconstraint constraint) parent irMap
graphCVLElement _ _ _ = ""

graphCVLElements :: Elements -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLElements ElementsEmpty _ _ = ""
graphCVLElements (PosElementsEmpty _) parent irMap = graphCVLElements ElementsEmpty parent irMap
graphCVLElements (ElementsList es) parent irMap = concatMap (\x -> graphCVLElement x parent irMap  ++ "\n") es
graphCVLElements (PosElementsList _ es) parent irMap = graphCVLElements (ElementsList es) parent irMap 

graphCVLClafer :: Clafer -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLClafer (Clafer _ _ _ _ _ _ _) _ _ = ""
graphCVLClafer (PosClafer s _ gCard _ super' crd _ es) parent irMap
   = let {{-tooltip = genTooltip (Module [ElementDecl (Subclafer (Clafer abstract gCard id' super' crd init' es))]) irMap;-}
          uid' = getDivId s irMap;
          gcrd = graphCVLGCard gCard parent irMap;
          super'' = graphCVLSuper super' parent irMap} in
     "\"" ++ uid' ++ "\" [URL=\"#" ++ uid' ++ "\" label=\"" ++ dropUid uid' ++ super'' ++ (if choiceCard crd then "\" style=rounded"  else " [" ++ graphCVLCard crd parent irMap ++ "]\"")
     ++ (if super'' == "" then "" else " shape=oval") ++ "];\n"
     ++ (if gcrd == "" then "" else "g" ++ uid' ++ " [label=\"" ++ gcrd ++ "\" fontsize=10 shape=triangle];\ng" ++ uid' ++ " -> " ++ uid' ++ " [weight=10];\n")
     ++ (if parent==Nothing then "" else uid' ++ " -> " ++ fromJust parent ++ (if lowerCard crd == "0" then " [style=dashed]" else "") ++ ";\n")
     ++ graphCVLElements es (if gcrd == "" then (Just uid') else (Just $ "g" ++ uid')) irMap

graphCVLSuper :: Super -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLSuper SuperEmpty _ _ = ""
graphCVLSuper (PosSuperEmpty _) parent irMap = graphCVLSuper SuperEmpty parent irMap
graphCVLSuper (SuperSome superHow setExp) parent irMap = graphCVLSuperHow superHow ++ concat (graphCVLSetExp setExp parent irMap)
graphCVLSuper (PosSuperSome _ superHow setExp) parent irMap = graphCVLSuper (SuperSome superHow setExp) parent irMap

graphCVLSuperHow :: SuperHow -> String
graphCVLSuperHow SuperColon = ":"
graphCVLSuperHow (PosSuperColon _) = ":"
graphCVLSuperHow SuperArrow = "->"
graphCVLSuperHow (PosSuperArrow _) = "->"
graphCVLSuperHow SuperMArrow = "->>"
graphCVLSuperHow (PosSuperMArrow _) = "->>"

graphCVLName :: Name -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLName (Path modids) parent irMap = unwords $ map (\x -> graphCVLModId x parent irMap) modids
graphCVLName (PosPath _ modids) parent irMap = graphCVLName (Path modids) parent irMap

graphCVLModId :: ModId -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLModId (ModIdIdent posident) _ irMap = graphCVLPosIdent posident irMap
graphCVLModId (PosModIdIdent _ posident) parent irMap = graphCVLModId (ModIdIdent posident) parent irMap

graphCVLPosIdent :: PosIdent -> Map.Map Span [Ir] -> String
graphCVLPosIdent (PosIdent (pos, id')) irMap = getUid (PosIdent (pos, id')) irMap

graphCVLConstraint :: Constraint -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLConstraint (Constraint _) _ _ = ""
graphCVLConstraint (PosConstraint s exps') parent irMap = let body' = htmlNewlines $ genTooltip (Module [ElementDecl (Subconstraint (Constraint exps'))]) irMap;
                                                                       uid' = "\"" ++ getExpId s irMap ++ "\""
                                                                    in uid' ++ " [label=\"" ++ body' ++ "\" shape=parallelogram];\n" ++
                                                                      if parent == Nothing then "" else uid' ++ " -> \"" ++ fromJust parent ++ "\";\n"
graphCVLCard :: Card -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLCard  CardEmpty _ _ = "1..1"
graphCVLCard  CardLone _ _ =  "0..1"
graphCVLCard  CardSome _ _ =  "1..*"
graphCVLCard  CardAny _ _ =   "0..*"
graphCVLCard  (CardNum (PosInteger (_, n))) _ _ = n ++ ".." ++ n
graphCVLCard  (CardInterval ncard) parent irMap = graphCVLNCard ncard parent irMap
graphCVLCard  (PosCardEmpty _) _ _ = "1..1"
graphCVLCard  (PosCardLone _) _ _ =  "0..1"
graphCVLCard  (PosCardSome _) _ _ =  "1..*"
graphCVLCard  (PosCardAny _) _ _ =    "0..*"
graphCVLCard  (PosCardNum _ (PosInteger (_, n))) _ _ = n ++ ".." ++ n
graphCVLCard  (PosCardInterval _ ncard) parent irMap = graphCVLNCard ncard parent irMap

graphCVLNCard :: NCard -> Maybe String -> Map.Map Span [Ir] -> String 
graphCVLNCard (NCard (PosInteger (_, num)) exInteger) parent irMap = num ++ ".." ++ graphCVLExInteger exInteger parent irMap
graphCVLNCard (PosNCard _ posInteger exInteger) parent irMap = graphCVLNCard (NCard posInteger exInteger) parent irMap

graphCVLExInteger :: ExInteger -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLExInteger ExIntegerAst _ _ = "*"
graphCVLExInteger (PosExIntegerAst _) parent irMap = graphCVLExInteger ExIntegerAst parent irMap
graphCVLExInteger (ExIntegerNum (PosInteger(_, num))) _ _ = num
graphCVLExInteger (PosExIntegerNum _ posInteger) parent irMap = graphCVLExInteger (ExIntegerNum posInteger) parent irMap

graphCVLGCard :: GCard -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLGCard (GCardInterval ncard) parent irMap = graphCVLNCard ncard parent irMap
graphCVLGCard (PosGCardInterval _ ncard) parent irMap = graphCVLNCard ncard parent irMap
graphCVLGCard GCardEmpty _ _ = ""
graphCVLGCard (PosGCardEmpty _) _ _ = ""
graphCVLGCard GCardXor _ _ = "1..1"
graphCVLGCard (PosGCardXor _) _ _ = "1..1"
graphCVLGCard GCardOr _ _= "1..*"
graphCVLGCard (PosGCardOr _) _ _ = "1..*"
graphCVLGCard GCardMux _ _ = "0..1"
graphCVLGCard (PosGCardMux _) _ _ = "0..1"
graphCVLGCard GCardOpt _ _ = ""
graphCVLGCard (PosGCardOpt _) _ _ = ""


{-graphCVLDecl _ _ _ = ""
graphCVLInit _ _ _ = ""
graphCVLInitHow _ _ _ = ""
graphCVLExp _ _ _ = ""
graphCVLQuant _ _ _ = ""
graphCVLGoal _ _ _ = ""
graphCVLSoftConstraint _ _ _ = ""
graphCVLAbstract _ _ _ = ""-}

graphCVLSetExp :: SetExp -> Maybe String -> Map.Map Span [Ir] -> [String]
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

{-graphCVLEnumId (EnumIdIdent posident) _ irMap = graphCVLPosIdent posident irMap
graphCVLEnumId (PosEnumIdIdent _ posident) parent irMap = graphCVLEnumId (EnumIdIdent posident) parent irMap-}

choiceCard :: Card -> Bool
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

lowerCard :: Card -> String
lowerCard crd = takeWhile (/= '.') $ graphCVLCard crd Nothing Map.empty

--Miscellaneous functions
dropUid :: String -> String
dropUid uid' = let id' = rest $ dropWhile (\x -> x /= '_') uid' in if id' == "" then uid' else id'

rest :: String -> String
rest [] = []
rest (_:xs) = xs

getUid :: PosIdent -> Map.Map Span [Ir] -> String
getUid (PosIdent (pos, id')) irMap = if Map.lookup (range (PosIdent (pos, id'))) irMap == Nothing
                        then id'
                        else let IRPExp pexp = head $ fromJust $ Map.lookup (range (PosIdent (pos, id'))) irMap in
                          findUid id' $ getIdentPExp pexp
                          where {getIdentPExp (PExp _ _ _ exp') = getIdentIExp exp';
                                 getIdentIExp (IFunExp _ exps') = concatMap getIdentPExp exps';
                                 getIdentIExp (IClaferId _ id'' _) = [id''];
                                 getIdentIExp (IDeclPExp _ _ pexp) = getIdentPExp pexp;
                                 getIdentIExp _ = [];
                                 findUid name (x:xs) = if name == dropUid x then x else findUid name xs;
                                 findUid name []     = name}

getDivId :: Span -> Map.Map Span [Ir] -> String                  
getDivId s irMap = if Map.lookup s irMap == Nothing
                      then "Uid not Found"
                      else let IRClafer iClafer = head $ fromJust $ Map.lookup s irMap in
                        uid iClafer

{-getSuperId :: Span -> Map.Map Span [Ir] -> String
getSuperId s irMap = if Map.lookup s irMap == Nothing
                        then "Uid not Found"
                        else let IRPExp pexp = head $ fromJust $ Map.lookup s irMap in
                          sident $ exp pexp-}

getUseId :: Span -> Map.Map Span [Ir] -> String
getUseId s irMap = if Map.lookup s irMap == Nothing
                      then "Uid not Found"
                      else let IRClafer iClafer = head $ fromJust $ Map.lookup s irMap in
                        sident $ exp $ head $ supers $ super iClafer

getExpId :: Span -> Map.Map Span [Ir] -> String
getExpId s irMap = if Map.lookup s irMap == Nothing
                      then "Uid not Found"
                      else let IRPExp pexp = head $ fromJust $ Map.lookup s irMap in pid pexp

{-while :: Bool -> [IExp] -> [IExp]
while bool exp' = if bool then exp' else []-}

htmlNewlines :: String -> String
htmlNewlines "" = ""
htmlNewlines ('\n':xs) = "&#10;" ++ htmlNewlines xs
htmlNewlines (x:xs) = x:htmlNewlines xs

cleanOutput :: String -> String
cleanOutput "" = ""
cleanOutput (' ':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput ('\n':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput (' ':'<':'b':'r':'>':xs) = "<br>"++cleanOutput xs
cleanOutput (x:xs) = x : cleanOutput xs
