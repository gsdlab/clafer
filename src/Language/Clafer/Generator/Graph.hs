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
-- | Generates simple graph and CVL graph representation for a Clafer model in GraphViz DOT.
module Language.Clafer.Generator.Graph (genSimpleGraph, genCVLGraph, traceAstModule, traceIrModule) where

import Language.Clafer.Common(fst3,snd3,trd3)
import Language.Clafer.Front.AbsClafer
import Language.Clafer.Intermediate.Tracing
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Generator.Html(genTooltip)
import Control.Applicative
import qualified Data.Map as Map
import Data.Maybe
import Prelude hiding (exp)

-- | Generate a graph in the simplified notation
genSimpleGraph :: Module -> IModule -> String -> Bool -> String
genSimpleGraph m ir name showRefs = cleanOutput $ "digraph \"" ++ name ++ "\"\n{\n\nrankdir=BT;\nranksep=0.3;\nnodesep=0.1;\ngraph [fontname=Sans fontsize=11];\nnode [shape=box color=lightgray fontname=Sans fontsize=11 margin=\"0.02,0.02\" height=0.2 ];\nedge [fontname=Sans fontsize=11];\n" ++ b ++ "}"
                           where b = graphSimpleModule m (traceIrModule ir) showRefs

-- | Generate a graph in CVL variability abstraction notation
genCVLGraph :: Module -> IModule -> String -> String
genCVLGraph m ir name = cleanOutput $ "digraph \"" ++ name ++ "\"\n{\nrankdir=BT;\nranksep=0.1;\nnodesep=0.1;\nnode [shape=box margin=\"0.025,0.025\"];\nedge [arrowhead=none];\n" ++ b ++ "}"
                       where b = graphCVLModule m $ traceIrModule ir

-- Simplified Notation Printer --
--toplevel: (Top_level (Boolean), Maybe Topmost parent, Maybe immediate parent)
graphSimpleModule :: Module -> Map.Map Span [Ir] -> Bool -> String
graphSimpleModule (Module _ [])                _     _        = ""
graphSimpleModule (Module s (x:xs))            irMap showRefs = graphSimpleDeclaration x (True, Nothing, Nothing) irMap showRefs ++ graphSimpleModule (Module s xs) irMap showRefs

graphSimpleDeclaration :: Declaration
                          -> (Bool, Maybe String, Maybe String)
                          -> Map.Map Span [Ir]
                          -> Bool
                          -> String
graphSimpleDeclaration (ElementDecl _ element)      topLevel irMap showRefs = graphSimpleElement element topLevel irMap showRefs
graphSimpleDeclaration _                          _        _     _        = ""

graphSimpleElement :: Element
                      -> (Bool, Maybe String, Maybe String)
                      -> Map.Map Span [Ir]
                      -> Bool
                      -> String
graphSimpleElement (Subclafer _ clafer) topLevel irMap showRefs = graphSimpleClafer clafer topLevel irMap showRefs
graphSimpleElement (ClaferUse s _ _ _)  topLevel irMap _        = if snd3 topLevel == Nothing then "" else "\"" ++ fromJust (snd3 topLevel) ++ "\" -> \"" ++ getUseId s irMap ++ "\" [arrowhead=vee arrowtail=diamond dir=both style=solid constraint=true weight=5 minlen=2 arrowsize=0.6 penwidth=0.5 ];\n"
graphSimpleElement _ _ _ _ = ""

graphSimpleElements :: Elements
                      -> (Bool, Maybe String, Maybe String)
                      -> Map.Map Span [Ir]
                      -> Bool
                      -> String
graphSimpleElements (ElementsEmpty _)                _        _     _        = ""
graphSimpleElements (ElementsList _ es)      topLevel irMap showRefs = concatMap (\x -> graphSimpleElement x topLevel irMap showRefs ++ "\n") es

graphSimpleClafer :: Clafer
                      -> (Bool, Maybe String, Maybe String)
                      -> Map.Map Span [Ir]
                      -> Bool
                      -> String
-- top-level abstract and concrete
graphSimpleClafer (Clafer s abstract gCard id' super' reference' crd init' es) (True, _, _) irMap showRefs =
  let
    tooltip = genTooltip (Module s [ElementDecl s (Subclafer s (Clafer s abstract gCard id' super' reference' crd init' es))]) irMap
    firstLineQuoted = htmlChars $ head $ lines tooltip
    tooltipQuoted = htmlChars tooltip
    uid' = getDivId s irMap
  in
     "\"" ++
      uid' ++
      "\" [label=\"" ++
      firstLineQuoted ++
      "\" URL=\"#" ++
      uid' ++
      "\" tooltip=\"" ++
      tooltipQuoted ++
      "\"];\n" ++
      graphSimpleSuper super' (True, Just uid', Just uid') irMap showRefs ++
      graphSimpleReference reference' (True, Just uid', Just uid') irMap showRefs ++
      graphSimpleElements es (False, Just uid', Just uid') irMap showRefs
-- nested abstract
graphSimpleClafer (Clafer s abstract@(Abstract _) gCard id' super' reference' crd init' es) (False, _, _) irMap showRefs =
  let
    tooltip = genTooltip (Module s [ElementDecl s (Subclafer s (Clafer s abstract gCard id' super' reference' crd init' es))]) irMap
    firstLineQuoted = htmlChars $ head $ lines tooltip
    tooltipQuoted = htmlChars tooltip
    uid' = getDivId s irMap
  in
     "\"" ++
      uid' ++
      "\" [label=\"" ++
      firstLineQuoted ++
      "\" URL=\"#" ++
      uid' ++
      "\" tooltip=\"" ++
      tooltipQuoted ++
      "\"];\n" ++
      graphSimpleSuper super' (False, Just uid', Just uid') irMap showRefs ++
      graphSimpleReference reference' (False, Just uid', Just uid') irMap showRefs ++
      graphSimpleElements es (False, Just uid', Just uid') irMap showRefs
-- nested concrete
graphSimpleClafer (Clafer _ _ _ id' super' reference' _ _ es) topLevel irMap showRefs =
  let
    (PosIdent (_,ident')) = id'
  in
    graphSimpleSuper super' (fst3 topLevel, snd3 topLevel, Just ident') irMap showRefs ++
    graphSimpleReference reference' (fst3 topLevel, snd3 topLevel, Just ident') irMap showRefs ++
    graphSimpleElements es (fst3 topLevel, snd3 topLevel, Just ident') irMap showRefs

graphSimpleSuper :: Super
                  -> (Bool, Maybe String, Maybe String)
                  -> Map.Map Span [Ir]
                  -> Bool
                  -> String

parent :: [String] -> String
parent [] = "error"
parent (uid'@('c':xs):xss) = if '_' `elem` xs then uid' else parent xss
parent (_:xss) = parent xss

graphSimpleSuper (SuperEmpty _) _ _ _ = ""
graphSimpleSuper (SuperSome _ setExp) topLevel irMap _ =
  let
    super' = parent $ graphSimpleExp setExp topLevel irMap
  in
    if super' == "error"
      then ""
      else "\"" ++
           fromJust (snd3 topLevel) ++
           "\" -> \"" ++
           parent (graphSimpleExp setExp topLevel irMap) ++
           "\"" ++
           " [" ++ if fst3 topLevel == True
             then "arrowhead=onormal constraint=true weight=100];\n"
             else "arrowhead=vee arrowtail=diamond dir=both style=solid weight=10 color=gray arrowsize=0.6 minlen=2 penwidth=0.5 constraint=true];\n"

graphSimpleReference :: Reference -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> Bool -> String
graphSimpleReference (ReferenceEmpty _) _ _ _ = ""
graphSimpleReference (ReferenceSet _ setExp) topLevel irMap showRefs =
  case graphSimpleExp setExp topLevel irMap of
    ["integer"] -> ""
    ["int"] -> ""
    ["double"] -> ""
    ["real"] -> ""
    ["string"] -> ""
    [target] ->
       "\"" ++
       fromJust (snd3 topLevel) ++
       "\" -> \"" ++
       target ++
       "\"" ++
       " [arrowhead=vee arrowsize=0.6 penwidth=0.5 constraint=true weight=10 color=" ++
       refColour showRefs ++
       " fontcolor=" ++
       refColour showRefs ++
       (if fst3 topLevel == True then "" else " label=" ++
       (fromJust $ trd3 topLevel)) ++
       "];\n"
    _ -> ""
graphSimpleReference (ReferenceBag _ setExp) topLevel irMap showRefs =
  case graphSimpleExp setExp topLevel irMap of
    ["integer"] -> ""
    ["int"] -> ""
    ["real"] -> ""
    ["double"] -> ""
    ["string"] -> ""
    [target] ->
      ("\"" ++
        fromJust (snd3 topLevel) ++
        "\" -> \"" ++
        target ++
        "\"" ++
        " [arrowhead=veevee arrowsize=0.6 minlen=1.5 penwidth=0.5 constraint=true weight=10 color=" ++
        refColour showRefs ++
        " fontcolor=" ++
        refColour showRefs ++
        (if fst3 topLevel == True then "" else " label=" ++
        (fromJust $ trd3 topLevel)) ++ "];\n")
    _ -> ""
refColour :: Bool -> String
refColour True = "lightgray"
refColour False = "transparent"

graphSimpleName :: Name -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> String
graphSimpleName (Path _ modids) topLevel irMap = unwords $ map (\x -> graphSimpleModId x topLevel irMap) modids

graphSimpleModId :: ModId -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> String
graphSimpleModId (ModIdIdent _ posident) _ irMap = graphSimplePosIdent posident irMap

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
graphSimpleAssertion _ _ _ = ""
graphSimpleAbstract _ _ _ = ""
graphSimpleGCard _ _ _ = ""
graphSimpleNCard _ _ _ = ""
graphSimpleExInteger _ _ _ = ""-}

graphSimpleExp :: Exp -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> [String]
graphSimpleExp (ClaferId _ name) topLevel irMap = [graphSimpleName name topLevel irMap]
graphSimpleExp (EUnion _ set1 set2) topLevel irMap = graphSimpleExp set1 topLevel irMap ++ graphSimpleExp set2 topLevel irMap
graphSimpleExp (EUnionCom _ set1 set2) topLevel irMap = graphSimpleExp set1 topLevel irMap ++ graphSimpleExp set2 topLevel irMap
graphSimpleExp (EDifference _ set1 set2) topLevel irMap = graphSimpleExp set1 topLevel irMap ++ graphSimpleExp set2 topLevel irMap
graphSimpleExp (EIntersection _ set1 set2) topLevel irMap = graphSimpleExp set1 topLevel irMap ++ graphSimpleExp set2 topLevel irMap
graphSimpleExp (EDomain _ set1 set2) topLevel irMap = graphSimpleExp set1 topLevel irMap ++ graphSimpleExp set2 topLevel irMap
graphSimpleExp (ERange _ set1 set2) topLevel irMap = graphSimpleExp set1 topLevel irMap ++ graphSimpleExp set2 topLevel irMap
graphSimpleExp (EJoin _ set1 set2) topLevel irMap = graphSimpleExp set1 topLevel irMap ++ graphSimpleExp set2 topLevel irMap
graphSimpleExp _ _ _ = []

{-graphSimpleEnumId :: EnumId -> (Bool, Maybe String, Maybe String) -> Map.Map Span [Ir] -> String
graphSimpleEnumId (EnumIdIdent posident) _ irMap = graphSimplePosIdent posident irMap
graphSimpleEnumId (PosEnumIdIdent _ posident) topLevel irMap = graphSimpleEnumId (EnumIdIdent posident) topLevel irMap-}

-- CVL Printer --
--parent is Maybe the uid of the immediate parent
graphCVLModule :: Module -> Map.Map Span [Ir] -> String
graphCVLModule (Module _ [])     _ = ""
graphCVLModule (Module s (x:xs)) irMap = graphCVLDeclaration x Nothing irMap ++ graphCVLModule (Module s xs) irMap

graphCVLDeclaration :: Declaration -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLDeclaration (ElementDecl _ element)      parent' irMap = graphCVLElement element parent' irMap
graphCVLDeclaration _                          _        _     = ""

graphCVLElement :: Element -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLElement (Subclafer _ clafer)  parent' irMap = graphCVLClafer clafer parent' irMap
--graphCVLElement (ClaferUse _ name _ _) parent' irMap = if parent' == Nothing then "" else "?" ++ " -> " ++ graphCVLName name parent' irMap ++ " [arrowhead = onormal style = dashed constraint = false];\n"
graphCVLElement (ClaferUse s _ _ _) parent' irMap = if parent' == Nothing then "" else "?" ++ " -> " ++ getUseId s irMap ++ " [arrowhead = onormal style = dashed constraint = false];\n"
graphCVLElement (Subconstraint _ constraint) parent' irMap = graphCVLConstraint constraint parent' irMap
graphCVLElement (Subgoal _ constraint) parent' irMap = graphCVLGoal constraint parent' irMap
graphCVLElement (SubAssertion _ constraint) parent' irMap = graphCVLAssertion constraint parent' irMap

graphCVLElements :: Elements -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLElements (ElementsEmpty _) _ _ = ""
graphCVLElements (ElementsList _ es) parent' irMap = concatMap (\x -> graphCVLElement x parent' irMap  ++ "\n") es

graphCVLClafer :: Clafer -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLClafer (Clafer s _ gCard _ super' reference' crd _ es) parent' irMap
   = let {{-tooltip = genTooltip (Module [ElementDecl (Subclafer (Clafer abstract gCard id' super' crd init' es))]) irMap;-}
          uid' = getDivId s irMap;
          gcrd = graphCVLGCard gCard parent' irMap;
          super'' = graphCVLSuper super' parent' irMap;
          reference'' = graphCVLReference reference' parent' irMap} in
     "\"" ++ uid' ++ "\" [URL=\"#" ++ uid' ++ "\" label=\"" ++ dropUid uid' ++ super'' ++ reference'' ++ (if choiceCard crd then "\" style=rounded"  else " [" ++ graphCVLCard crd parent' irMap ++ "]\"")
     ++ (if super'' == "" then "" else " shape=oval") ++ "];\n"
     ++ (if gcrd == "" then "" else "g" ++ uid' ++ " [label=\"" ++ gcrd ++ "\" fontsize=10 shape=triangle];\ng" ++ uid' ++ " -> " ++ uid' ++ " [weight=10];\n")
     ++ (if parent'==Nothing then "" else uid' ++ " -> " ++ fromJust parent' ++ (if lowerCard crd == "0" then " [style=dashed]" else "") ++ ";\n")
     ++ graphCVLElements es (if gcrd == "" then (Just uid') else (Just $ "g" ++ uid')) irMap

graphCVLSuper :: Super -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLSuper (SuperEmpty _) _ _ = ""
graphCVLSuper (SuperSome _ setExp) parent' irMap = ":" ++ concat (graphCVLExp setExp parent' irMap)

graphCVLReference :: Reference -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLReference (ReferenceEmpty _) _ _ = ""
graphCVLReference (ReferenceSet _ setExp) parent' irMap = "->" ++ concat (graphCVLExp setExp parent' irMap)
graphCVLReference (ReferenceBag _ setExp) parent' irMap = "->>" ++ concat (graphCVLExp setExp parent' irMap)

graphCVLName :: Name -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLName (Path _ modids) parent' irMap = unwords $ map (\x -> graphCVLModId x parent' irMap) modids

graphCVLModId :: ModId -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLModId (ModIdIdent _ posident) _ irMap = graphCVLPosIdent posident irMap

graphCVLPosIdent :: PosIdent -> Map.Map Span [Ir] -> String
graphCVLPosIdent (PosIdent (pos, id')) irMap = getUid (PosIdent (pos, id')) irMap

graphCVLConstraint :: Constraint -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLConstraint (Constraint s exps') parent' irMap = let body' = htmlChars $ genTooltip (Module s [ElementDecl s (Subconstraint s (Constraint s exps'))]) irMap;
                                                                       uid' = "\"" ++ getExpId s irMap ++ "\""
                                                                    in uid' ++ " [label=\"" ++ body' ++ "\" shape=parallelogram];\n" ++
                                                                      if parent' == Nothing then "" else uid' ++ " -> \"" ++ fromJust parent' ++ "\";\n"

graphCVLAssertion :: Assertion -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLAssertion (Assertion s exps') parent' irMap = let body' = htmlChars $ genTooltip (Module s [ElementDecl s (SubAssertion s (Assertion s exps'))]) irMap;
                                                                       uid' = "\"" ++ getExpId s irMap ++ "\""
                                                                    in uid' ++ " [label=\"" ++ body' ++ "\" shape=parallelogram];\n" ++
                                                                      if parent' == Nothing then "" else uid' ++ " -> \"" ++ fromJust parent' ++ "\";\n"

graphCVLGoal :: Goal -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLGoal goal parent' irMap = let
    s = getSpan goal
    body' = htmlChars $ genTooltip (Module s [ElementDecl s (Subgoal s goal)]) irMap
    uid' = "\"" ++ getExpId s irMap ++ "\""
  in
    uid' ++
    " [label=\"" ++ body' ++ "\" shape=parallelogram];\n" ++
    if parent' == Nothing
    then ""
    else uid' ++ " -> \"" ++ fromJust parent' ++ "\";\n"

graphCVLCard :: Card -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLCard  (CardEmpty _) _ _ = "1..1"
graphCVLCard  (CardLone _) _ _ =  "0..1"
graphCVLCard  (CardSome _) _ _ =  "1..*"
graphCVLCard  (CardAny _) _ _ =    "0..*"
graphCVLCard  (CardNum _ (PosInteger (_, n))) _ _ = n ++ ".." ++ n
graphCVLCard  (CardInterval _ ncard) parent' irMap = graphCVLNCard ncard parent' irMap

graphCVLNCard :: NCard -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLNCard (NCard _ (PosInteger (_, num)) exInteger) parent' irMap = num ++ ".." ++ graphCVLExInteger exInteger parent' irMap

graphCVLExInteger :: ExInteger -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLExInteger (ExIntegerAst _) _ _ = "*"
graphCVLExInteger (ExIntegerNum _ (PosInteger(_, num))) _ _ = num

graphCVLGCard :: GCard -> Maybe String -> Map.Map Span [Ir] -> String
graphCVLGCard (GCardInterval _ ncard) parent' irMap = graphCVLNCard ncard parent' irMap
graphCVLGCard (GCardEmpty _) _ _ = ""
graphCVLGCard (GCardXor _) _ _ = "1..1"
graphCVLGCard (GCardOr _) _ _ = "1..*"
graphCVLGCard (GCardMux _) _ _ = "0..1"
graphCVLGCard (GCardOpt _) _ _ = ""


{-graphCVLDecl _ _ _ = ""
graphCVLInit _ _ _ = ""
graphCVLInitHow _ _ _ = ""
graphCVLExp _ _ _ = ""
graphCVLQuant _ _ _ = ""
graphCVLGoal _ _ _ = ""
graphCVLAssertion _ _ _ = ""
graphCVLAbstract _ _ _ = ""-}

graphCVLExp :: Exp -> Maybe String -> Map.Map Span [Ir] -> [String]
graphCVLExp (ClaferId _ name) parent' irMap = [graphCVLName name parent' irMap]
graphCVLExp (EUnion _ set1 set2) parent' irMap = graphCVLExp set1 parent' irMap ++ graphCVLExp set2 parent' irMap
graphCVLExp (EUnionCom _ set1 set2) parent' irMap = graphCVLExp set1 parent' irMap ++ graphCVLExp set2 parent' irMap
graphCVLExp (EDifference _ set1 set2) parent' irMap = graphCVLExp set1 parent' irMap ++ graphCVLExp set2 parent' irMap
graphCVLExp (EIntersection _ set1 set2) parent' irMap = graphCVLExp set1 parent' irMap ++ graphCVLExp set2 parent' irMap
graphCVLExp (EDomain _ set1 set2) parent' irMap = graphCVLExp set1 parent' irMap ++ graphCVLExp set2 parent' irMap
graphCVLExp (ERange _ set1 set2) parent' irMap = graphCVLExp set1 parent' irMap ++ graphCVLExp set2 parent' irMap
graphCVLExp (EJoin _ set1 set2) parent' irMap = graphCVLExp set1 parent' irMap ++ graphCVLExp set2 parent' irMap
graphCVLExp _ _ _ = []

{-graphCVLEnumId (EnumIdIdent posident) _ irMap = graphCVLPosIdent posident irMap
graphCVLEnumId (PosEnumIdIdent _ posident) parent irMap = graphCVLEnumId (EnumIdIdent posident) parent irMap-}

choiceCard :: Card -> Bool
choiceCard (CardEmpty _) = True
choiceCard (CardLone _) = True
choiceCard (CardInterval _ (NCard _ (PosInteger (_, low)) exInteger)) = if low == "0" || low == "1"
                                    then case exInteger of
                                      (ExIntegerAst _) -> False
                                      (ExIntegerNum _ (PosInteger (_, high))) -> high == "0" || high == "1"
                                    else False
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
getUid (PosIdent (pos, id')) irMap = if Map.lookup (getSpan (PosIdent (pos, id'))) irMap == Nothing
                        then id'
                        else let IRPExp pexp = head $ fromJust $ Map.lookup (getSpan (PosIdent (pos, id'))) irMap in
                          findUid id' $ getIdentPExp pexp
                          where {getIdentPExp (PExp _ _ _ exp') = getIdentIExp exp';
                                 getIdentIExp (IFunExp _ exps') = concatMap getIdentPExp exps';
                                 getIdentIExp (IClaferId _ id'' _ _) = [id''];
                                 getIdentIExp (IDeclPExp _ _ pexp) = getIdentPExp pexp;
                                 getIdentIExp _ = [];
                                 findUid name (x:xs) = if name == dropUid x then x else findUid name xs;
                                 findUid name []     = name}

getDivId :: Span -> Map.Map Span [Ir] -> String
getDivId s irMap = if Map.lookup s irMap == Nothing
                      then "Uid not Found"
                      else let IRClafer iClaf = head $ fromJust $ Map.lookup s irMap in
                        _uid iClaf

getUseId :: Span -> Map.Map Span [Ir] -> String
getUseId s irMap = if Map.lookup s irMap == Nothing
                      then "Uid not Found"
                      else let
                            IRClafer iClaf = head $ fromJust $ Map.lookup s irMap
                           in
                            fromMaybe "" $ _sident <$> _exp <$> _super iClaf

getExpId :: Span -> Map.Map Span [Ir] -> String
getExpId s irMap = if Map.lookup s irMap == Nothing
                      then "Uid not Found"
                      else let IRPExp pexp = head $ fromJust $ Map.lookup s irMap in _pid pexp

{-while :: Bool -> [IExp] -> [IExp]
while bool exp' = if bool then exp' else []-}

htmlChars :: String -> String
htmlChars "" = ""
htmlChars ('\n':xs) = "&#10;" ++ htmlChars xs
htmlChars ('\"':xs) = "&quot;" ++ htmlChars xs
htmlChars ('\'':xs) = "&#39;" ++ htmlChars xs
htmlChars ('&':xs) = "&amp;" ++ htmlChars xs
htmlChars ('~':xs) = "&tilde;" ++ htmlChars xs
htmlChars ('-':'>':'>':xs) = "-&gt;&gt;" ++ htmlChars xs
htmlChars ('-':'>':xs) = "-&gt;" ++ htmlChars xs
htmlChars (x:xs) = x:htmlChars xs

cleanOutput :: String -> String
cleanOutput "" = ""
cleanOutput (' ':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput ('\n':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput (' ':'<':'b':'r':'>':xs) = "<br>"++cleanOutput xs
cleanOutput (x:xs) = x : cleanOutput xs
