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
graphDeclaration _                          _        _     = "graphDeclaration\n"

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
         
graphGoal (Goal exps) topLevel irMap = ""
graphGoal (PosGoal _ exps) topLevel irMap = graphGoal (Goal exps) topLevel irMap

graphSoftConstraint (SoftConstraint exps) topLevel irMap = ""
graphSoftConstraint (PosSoftConstraint _ exps) topLevel irMap = graphSoftConstraint (SoftConstraint exps) topLevel irMap

graphAbstract _ _ _ = ""
--graphAbstract Abstract topLevel irMap = (while  "<span class=\"keyword\">") ++ "abstract" ++ (while  "</span>") ++ " "
--graphAbstract (PosAbstract _) topLevel irMap = graphAbstract Abstract topLevel irMap
--graphAbstract AbstractEmpty topLevel irMap = ""
--graphAbstract (PosAbstractEmpty _) topLevel irMap = graphAbstract AbstractEmpty topLevel irMap

graphGCard _ _ _ = ""{-
graphGCard gCard topLevel irMap = case gCard of
  (GCardInterval ncard) -> graphNCard ncard topLevel irMap
  (PosGCardInterval _ ncard) -> graphNCard ncard topLevel irMap
  GCardEmpty        -> ""
  (PosGCardEmpty _) -> ""
  GCardXor          -> while  "<span class=\"keyword\">" ++ "xor" ++ while  "</span>" ++ " "
  (PosGCardXor _)   -> while  "<span class=\"keyword\">" ++ "xor" ++ while  "</span>" ++ " "
  GCardOr           -> while  "<span class=\"keyword\">" ++ "or"  ++ while  "</span>" ++ " "
  (PosGCardOr _)    -> while  "<span class=\"keyword\">" ++ "or"  ++ while  "</span>" ++ " "
  GCardMux          -> while  "<span class=\"keyword\">" ++ "mux" ++ while  "</span>" ++ " "
  (PosGCardMux _)   -> while  "<span class=\"keyword\">" ++ "mux" ++ while  "</span>" ++ " "
  GCardOpt          -> while  "<span class=\"keyword\">" ++ "opt" ++ while  "</span>" ++ " "
  (PosGCardOpt _)   -> while  "<span class=\"keyword\">" ++ "opt" ++ while  "</span>" ++ " "
-}
graphNCard _ _ _ = ""
graphNCard (NCard (PosInteger (pos, num)) exInteger) topLevel irMap = num ++ ".." ++ graphExInteger exInteger topLevel irMap
graphNCard (PosNCard _ posinteger exinteger) topLevel irMap = graphNCard (NCard posinteger exinteger) topLevel irMap

graphExInteger _ _ _ = ""      
graphExInteger ExIntegerAst topLevel irMap = "*"
graphExInteger (PosExIntegerAst _) topLevel irMap = graphExInteger ExIntegerAst topLevel irMap
graphExInteger (ExIntegerNum (PosInteger(pos, num))) topLevel irMap = num
graphExInteger (PosExIntegerNum _ posInteger) topLevel irMap = graphExInteger (ExIntegerNum posInteger) topLevel irMap

graphName (Path modids) topLevel irMap = unwords $ map (\x -> graphModId x topLevel irMap) modids
graphName (PosPath _ modids) topLevel irMap = graphName (Path modids) topLevel irMap


graphModId (ModIdIdent posident) topLevel irMap = graphPosIdent posident topLevel irMap
graphModId (PosModIdIdent _ posident) topLevel irMap = graphModId (ModIdIdent posident) topLevel irMap

graphPosIdent (PosIdent (pos, id)) topLevel irMap = getUid (PosIdent (pos, id)) irMap

graphCard _ _ _ = ""
graphCard CardEmpty topLevel irMap = ""
graphCard (PosCardEmpty _) topLevel irMap = graphCard CardEmpty topLevel irMap
graphCard CardLone topLevel irMap = " ?"
graphCard (PosCardLone _) topLevel irMap = graphCard CardLone topLevel irMap
graphCard CardSome topLevel irMap = " +"
graphCard (PosCardSome _) topLevel irMap = graphCard CardSome topLevel irMap
graphCard CardAny topLevel irMap = " *"
graphCard (PosCardAny _) topLevel irMap = graphCard CardAny topLevel irMap
graphCard (CardNum (PosInteger (pos,num))) topLevel irMap = " " ++ num 
graphCard (PosCardNum _ posInteger) topLevel irMap = graphCard (CardNum posInteger) topLevel irMap
graphCard (CardInterval nCard) topLevel irMap = " " ++ graphNCard nCard topLevel irMap
graphCard (PosCardInterval _ nCard) topLevel irMap = graphCard (CardInterval nCard) topLevel irMap

graphConstraint _ _ _ = ""
--graphConstraint (Constraint exps) topLevel irMap = concatMap (\x -> graphConstraint' x topLevel irMap) exps
--graphConstraint (PosConstraint _ exps) topLevel irMap = graphConstraint (Constraint exps) topLevel irMap
--graphConstraint' exp topLevel irMap = (graphIndent indent ) ++ while  "<span class=\"keyword\">" ++ "[" ++ while  "</span>" ++ " " ++ graphExp exp topLevel irMap ++ " " ++ while  "<span class=\"keyword\">" ++ "]" ++ while  "</span></span></span><br>" ++ "\n"

graphDecl _ _ _ = ""
--graphDecl (Decl locids setExp) topLevel irMap = (while  "<span class=\"keyword\">") ++ ":" ++ (while  "</span>") ++ graphSetExp setExp topLevel irMap
--graphDecl (PosDecl _ locids setExp) topLevel irMap = graphDecl (Decl locids setExp) topLevel irMap

graphInit InitEmpty topLevel irMap = ""
graphInit (PosInitEmpty _) topLevel irMap = graphInit InitEmpty topLevel irMap
graphInit (InitSome initHow exp) topLevel irMap = graphInitHow initHow topLevel irMap ++ graphExp exp topLevel irMap
graphInit (PosInitSome _ initHow exp) topLevel irMap = graphInit (InitSome initHow exp) topLevel irMap

graphInitHow InitHow_1 topLevel irMap = " = "
graphInitHow (PosInitHow_1 _) topLevel irMap = graphInitHow InitHow_1 topLevel irMap
graphInitHow InitHow_2 topLevel irMap = " := "
graphInitHow (PosInitHow_2 _) topLevel irMap = graphInitHow InitHow_2 topLevel irMap

graphExp _ _ _ = "exp"{-
graphExp (DeclAllDisj decl exp) topLevel irMap = "all disj " ++ (graphDecl decl topLevel irMap) ++ " | " ++ (graphExp exp topLevel irMap)
graphExp (PosDeclAllDisj _ decl exp) topLevel irMap = graphExp (DeclAllDisj decl exp) topLevel irMap
graphExp (DeclAll     decl exp) topLevel irMap = "all " ++ (graphDecl decl topLevel irMap) ++ " | " ++ (graphExp exp topLevel irMap)
graphExp (PosDeclAll _ decl exp) topLevel irMap = graphExp (DeclAll decl exp) topLevel irMap
graphExp (DeclQuantDisj quant decl exp) topLevel irMap = (graphQuant quant topLevel irMap) ++ "disj" ++ (graphDecl decl topLevel irMap) ++ " | " ++ (graphExp exp topLevel irMap)
graphExp (PosDeclQuantDisj _ quant decl exp) topLevel irMap = graphExp (DeclQuantDisj quant decl exp) topLevel irMap
graphExp (DeclQuant     quant decl exp) topLevel irMap = (graphQuant quant topLevel irMap) ++ (graphDecl decl topLevel irMap) ++ " | " ++ (graphExp exp topLevel irMap)
graphExp (PosDeclQuant _ quant decl exp) topLevel irMap = graphExp (DeclQuant quant decl exp) topLevel irMap
graphExp (EGMax exp)            topLevel irMap = "max " ++ graphExp exp topLevel irMap
graphExp (PosEGMax _ exp)     topLevel irMap = graphExp (EGMax exp) topLevel irMap
graphExp (EGMin exp)            topLevel irMap = "min " ++ graphExp exp topLevel irMap
graphExp (PosEGMin _ exp) topLevel irMap = graphExp (EGMin exp) topLevel irMap
graphExp (ENeq exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " != " ++ (graphExp exp2 topLevel irMap)
graphExp (PosENeq _ exp1 exp2) topLevel irMap = graphExp (ENeq exp1 exp2) topLevel irMap
graphExp (ESetExp setExp)       topLevel irMap = graphSetExp setExp topLevel irMap
graphExp (PosESetExp _ setExp) topLevel irMap = graphExp (ESetExp setExp) topLevel irMap
graphExp (QuantExp quant exp)   topLevel irMap = graphQuant quant topLevel irMap ++ graphExp exp topLevel irMap
graphExp (PosQuantExp _ quant exp) topLevel irMap = graphExp (QuantExp quant exp) topLevel irMap
graphExp (EImplies exp1 exp2)   topLevel irMap = (graphExp exp1 topLevel irMap) ++ " => " ++ graphExp exp2 topLevel irMap
graphExp (PosEImplies _ exp1 exp2) topLevel irMap = graphExp (EImplies exp1 exp2) topLevel irMap
graphExp (EAnd exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " && " ++ graphExp exp2 topLevel irMap
graphExp (PosEAnd _ exp1 exp2) topLevel irMap = graphExp (EAnd exp1 exp2) topLevel irMap
graphExp (EOr exp1 exp2)        topLevel irMap = (graphExp exp1 topLevel irMap) ++ " || " ++ graphExp exp2 topLevel irMap
graphExp (PosEOr _ exp1 exp2) topLevel irMap = graphExp (EOr exp1 exp2) topLevel irMap
graphExp (EXor exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " xor " ++ graphExp exp2 topLevel irMap
graphExp (PosEXor _ exp1 exp2) topLevel irMap = graphExp (EXor exp1 exp2) topLevel irMap
graphExp (ENeg exp)             topLevel irMap = " !" ++ graphExp exp topLevel irMap
graphExp (PosENeg _ exp) topLevel irMap = graphExp (ENeg exp) topLevel irMap
graphExp (ELt exp1 exp2)        topLevel irMap = (graphExp exp1 topLevel irMap) ++ " < " ++ graphExp exp2 topLevel irMap
graphExp (PosELt _ exp1 exp2) topLevel irMap = graphExp (ELt exp1 exp2) topLevel irMap
graphExp (EGt exp1 exp2)        topLevel irMap = (graphExp exp1 topLevel irMap) ++ " > " ++ graphExp exp2 topLevel irMap
graphExp (PosEGt _ exp1 exp2) topLevel irMap = graphExp (EGt exp1 exp2) topLevel irMap
graphExp (EEq exp1 exp2)        topLevel irMap = (graphExp exp1 topLevel irMap) ++ " = " ++ graphExp exp2 topLevel irMap
graphExp (PosEEq _ exp1 exp2) topLevel irMap = graphExp (EEq exp1 exp2) topLevel irMap
graphExp (ELte exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " <= " ++ graphExp exp2 topLevel irMap
graphExp (PosELte _ exp1 exp2) topLevel irMap = graphExp (ELte exp1 exp2) topLevel irMap
graphExp (EGte exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " >= " ++ graphExp exp2 topLevel irMap
graphExp (PosEGte _ exp1 exp2) topLevel irMap = graphExp (EGte exp1 exp2) topLevel irMap
graphExp (EIn exp1 exp2)        topLevel irMap = (graphExp exp1 topLevel irMap) ++ " in " ++ graphExp exp2 topLevel irMap
graphExp (PosEIn _ exp1 exp2) topLevel irMap = graphExp (EIn exp1 exp2) topLevel irMap
graphExp (ENin exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " not in " ++ graphExp exp2 topLevel irMap
graphExp (PosENin _ exp1 exp2) topLevel irMap = graphExp (ENin exp1 exp2) topLevel irMap
graphExp (EIff exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " <=> " ++ graphExp exp2 topLevel irMap
graphExp (PosEIff _ exp1 exp2) topLevel irMap = graphExp (EIff exp1 exp2) topLevel irMap
graphExp (EAdd exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " + " ++ graphExp exp2 topLevel irMap
graphExp (PosEAdd _ exp1 exp2) topLevel irMap = graphExp (EAdd exp1 exp2) topLevel irMap
graphExp (ESub exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " - " ++ graphExp exp2 topLevel irMap
graphExp (PosESub _ exp1 exp2) topLevel irMap = graphExp (ESub exp1 exp2) topLevel irMap
graphExp (EMul exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " * " ++ graphExp exp2 topLevel irMap
graphExp (PosEMul _ exp1 exp2) topLevel irMap = graphExp (EMul exp1 exp2) topLevel irMap
graphExp (EDiv exp1 exp2)       topLevel irMap = (graphExp exp1 topLevel irMap) ++ " / " ++ graphExp exp2 topLevel irMap
graphExp (PosEDiv _ exp1 exp2) topLevel irMap = graphExp (EDiv exp1 exp2) topLevel irMap
graphExp (ECSetExp exp)         topLevel irMap = "#" ++ graphExp exp topLevel irMap
graphExp (PosECSetExp _ exp) topLevel irMap = graphExp (ECSetExp exp) topLevel irMap
graphExp (EMinExp exp)          topLevel irMap = "-" ++ graphExp exp topLevel irMap
graphExp (PosEMinExp _ exp) topLevel irMap = graphExp (EMinExp exp) topLevel irMap
graphExp (EImpliesElse exp1 exp2 exp3) topLevel irMap = "if " ++ (graphExp exp1 topLevel irMap) ++ " then " ++ (graphExp exp2 topLevel irMap) ++ " else " ++ (graphExp exp3 topLevel irMap)
graphExp (PosEImpliesElse _ exp1 exp2 exp3) topLevel irMap = graphExp (EImpliesElse exp1 exp2 exp3) topLevel irMap
graphExp (EInt (PosInteger (_, num))) topLevel irMap = num
graphExp (PosEInt _ posInteger) topLevel irMap = graphExp (EInt posInteger) topLevel irMap
graphExp (EDouble (PosDouble (_, num))) topLevel irMap = num
graphExp (PosEDouble _ posDouble) topLevel irMap = graphExp (EDouble posDouble) topLevel irMap
graphExp (EStr (PosString (_, str))) topLevel irMap = str
graphExp (PosEStr _ posString) topLevel irMap = graphExp (EStr posString) topLevel irMap
-}
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

graphQuant _ _ _ = "" {-
graphQuant quant topLevel irMap = case quant of
  QuantNo        -> while  (while  "<span class=\"keyword\">") ++ "no" ++ (while  "</span>") ++ " "
  PosQuantNo _   -> while  (while  "<span class=\"keyword\">") ++ "no" ++ (while  "</span>") ++ " "
  QuantLone      -> while  (while  "<span class=\"keyword\">") ++ "lone" ++ (while  "</span>") ++ " "
  PosQuantLone _ -> while  (while  "<span class=\"keyword\">") ++ "lone" ++ (while  "</span>") ++ " "
  QuantOne       -> while  (while  "<span class=\"keyword\">") ++ "one" ++ (while  "</span>") ++ " "
  PosQuantOne _  -> while  (while  "<span class=\"keyword\">") ++ "one" ++ (while  "</span>") ++ " "
  QuantSome      -> while  (while  "<span class=\"keyword\">") ++ "some" ++ (while  "</span>") ++ " "
  PosQuantSome _ -> while  (while  "<span class=\"keyword\">") ++ "some" ++ (while  "</span>") ++ " "
-}
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
