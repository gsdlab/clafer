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
module Language.Clafer.Generator.Html (genHtml, genText, genTooltip, printModule, traceAstModule, traceIrModule) where

import Language.Clafer.Front.Absclafer
import Language.Clafer.Front.LayoutResolver(revertLayout)
import Language.Clafer.Front.Mapper(range)
import Language.Clafer.Intermediate.Tracing
import Language.Clafer.Intermediate.Intclafer
import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Maybe
import Prelude hiding (exp)

genHtml x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) True
genText x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) False
genTooltip m ir = cleanOutput $ revertLayout $ printModule m ir False
                           
printModule (Module [])     irMap html = ""
printModule (Module (x:xs)) irMap html = (printDeclaration x 0 irMap html) ++ printModule (Module xs) irMap html
printModule (PosModule _ declarations) irMap html = printModule (Module declarations) irMap html

printDeclaration (EnumDecl posIdent enumIds)       indent irMap html = (while html "<span class=\"keyword\">") ++ "enum" ++ (while html "</span>") ++ " =" ++ (printPosIdentRef posIdent indent irMap html) ++ (concat $ intersperse ";" (map (\x -> printEnumId x indent irMap html) enumIds))
printDeclaration (PosEnumDecl _ posIdent enumIds)  indent irMap html = printDeclaration (EnumDecl posIdent enumIds) indent irMap html
printDeclaration (ElementDecl element)             indent irMap html = printElement element indent irMap html
printDeclaration (PosElementDecl _ element)        indent irMap html = printDeclaration (ElementDecl element) indent irMap html

printElement (Subclafer clafer) indent irMap html = printClafer clafer indent irMap html
printElement (PosSubclafer _ subclafer) indent irMap html = printElement (Subclafer subclafer) indent irMap html
printElement (Subconstraint constraint) indent irMap html = printConstraint constraint indent irMap html
printElement (PosSubconstraint _ constraint) indent irMap html = printElement (Subconstraint constraint) indent irMap html
printElement (ClaferUse name card elements) indent irMap html = (printIndent indent html) ++ "`" ++ printName name indent irMap html ++ printCard card indent irMap html ++ (while html "</span><br>") ++ "\n" ++ printElements elements indent irMap html
printElement (PosClaferUse _ name card elements) indent irMap html = printElement (ClaferUse name card elements) indent irMap html
printElement (Subgoal goal) indent irMap html = printGoal goal indent irMap html
printElement (PosSubgoal _ goal) indent irMap html = printElement (Subgoal goal) indent irMap html
printElement (Subsoftconstraint softConstraint) indent irMap html = printSoftConstraint softConstraint indent irMap html
printElement (PosSubsoftconstraint _ softConstraint) indent irMap html = printElement (Subsoftconstraint softConstraint) indent irMap html

printElements ElementsEmpty indent irMap html = ""
printElements (PosElementsEmpty _) indent irMap html = printElements ElementsEmpty indent irMap html
printElements (ElementsList elements) indent irMap html = "\n{" ++ (concatMap (\x -> printElement x (indent + 1) irMap html ++ "\n") elements) ++ "\n}"
printElements (PosElementsList _ elements) indent irMap html = printElements (ElementsList elements) indent irMap html

printClafer (Clafer abstract gCard id super card init elements) indent irMap html
  | indent == 0 = let (PosIdent (_, divid)) = id in
                    (while html ("<div id=\"" ++ divid ++ "\">\n")) ++ (concat [printAbstract abstract indent irMap html, printGCard gCard indent irMap html,
                    printPosIdent id indent irMap html, printSuper super indent irMap html, printCard card indent irMap html, printInit init indent irMap html])
                    ++ (while html "<br>") ++ "\n" ++ printElements elements indent irMap html ++ (while html "</div>\n<br>") ++ "\n"
  | otherwise   = let (PosIdent (_, divid)) = id in
                    (while html ("<span id=\"" ++ divid ++ "\" class=\"l" ++ show indent ++ "\">")) ++ (concat [printAbstract abstract indent irMap html, printGCard gCard indent irMap html,
                    printPosIdent id indent irMap html, printSuper super indent irMap html, printCard card indent irMap html, printInit init indent irMap html])
                    ++ (while html "</span><br>") ++ "\n" ++ printElements elements indent irMap html
printClafer (PosClafer span abstract gCard id super card init elements) indent irMap html
  | indent == 0 = let divId = getDivId span irMap in
                    (while html ("<div id=\"" ++ divId ++ "\">\n")) ++ (concat [printAbstract abstract indent irMap html, printGCard gCard indent irMap html,
                    printPosIdent id indent irMap html, printSuper super indent irMap html, printCard card indent irMap html, printInit init indent irMap html])
                    ++ (while html "<br>") ++ "\n" ++ printElements elements indent irMap html ++ (while html "</div>\n<br>") ++ "\n"
  | otherwise   = let uid = getDivId span irMap in
                    (while html ("<span id=\"" ++ uid ++ "\" class=\"l" ++ show indent ++ "\">")) ++ (concat [printAbstract abstract indent irMap html, printGCard gCard indent irMap html,
                    printPosIdent id indent irMap html, printSuper super indent irMap html, printCard card indent irMap html, printInit init indent irMap html])
                    ++ (while html "</span><br>") ++ "\n" ++ printElements elements indent irMap html
printGoal (Goal exps) indent irMap html = (if html then "&lt;&lt;" else "<<") ++ concatMap (\x -> printExp x indent irMap html) exps ++ if html then "&gt;&gt;" else ">>"
printGoal (PosGoal _ exps) indent irMap html = printGoal (Goal exps) indent irMap html

printSoftConstraint (SoftConstraint exps) indent irMap html = "(" ++ concatMap (\x -> printExp x indent irMap html) exps ++ ")"
printSoftConstraint (PosSoftConstraint _ exps) indent irMap html = printSoftConstraint (SoftConstraint exps) indent irMap html

printAbstract Abstract indent irMap html = (while html "<span class=\"keyword\">") ++ "abstract" ++ (while html "</span>") ++ " "
printAbstract (PosAbstract _) indent irMap html = printAbstract Abstract indent irMap html
printAbstract AbstractEmpty indent irMap html = ""
printAbstract (PosAbstractEmpty _) indent irMap html = printAbstract AbstractEmpty indent irMap html

printGCard gCard indent irMap html = case gCard of
  (GCardInterval ncard) -> printNCard ncard indent irMap html
  (PosGCardInterval _ ncard) -> printNCard ncard indent irMap html
  GCardEmpty        -> ""
  (PosGCardEmpty _) -> ""
  GCardXor          -> while html "<span class=\"keyword\">" ++ "xor" ++ while html "</span>" ++ " "
  (PosGCardXor _)   -> while html "<span class=\"keyword\">" ++ "xor" ++ while html "</span>" ++ " "
  GCardOr           -> while html "<span class=\"keyword\">" ++ "or"  ++ while html "</span>" ++ " "
  (PosGCardOr _)    -> while html "<span class=\"keyword\">" ++ "or"  ++ while html "</span>" ++ " "
  GCardMux          -> while html "<span class=\"keyword\">" ++ "mux" ++ while html "</span>" ++ " "
  (PosGCardMux _)   -> while html "<span class=\"keyword\">" ++ "mux" ++ while html "</span>" ++ " "
  GCardOpt          -> while html "<span class=\"keyword\">" ++ "opt" ++ while html "</span>" ++ " "
  (PosGCardOpt _)   -> while html "<span class=\"keyword\">" ++ "opt" ++ while html "</span>" ++ " "

printNCard (NCard (PosInteger (pos, num)) exInteger) indent irMap html = num ++ ".." ++ printExInteger exInteger indent irMap html
printNCard (PosNCard _ posinteger exinteger) indent irMap html = printNCard (NCard posinteger exinteger) indent irMap html
      
printExInteger ExIntegerAst indent irMap html = "*"
printExInteger (PosExIntegerAst _) indent irMap html = printExInteger ExIntegerAst indent irMap html
printExInteger (ExIntegerNum (PosInteger(pos, num))) indent irMap html = num
printExInteger (PosExIntegerNum _ posInteger) indent irMap html = printExInteger (ExIntegerNum posInteger) indent irMap html

printName (Path modids) indent irMap html = unwords $ map (\x -> printModId x indent irMap html) modids
printName (PosPath _ modids) indent irMap html = printName (Path modids) indent irMap html

printModId (ModIdIdent posident) indent irMap html = printPosIdentRef posident indent irMap html
printModId (PosModIdIdent _ posident) indent irMap html = printModId (ModIdIdent posident) indent irMap html

printPosIdent (PosIdent (pos, id)) indent irMap html = id

printPosIdentRef (PosIdent (pos, id)) indent irMap html
  = (while html ("<a href=\"#" ++ uid ++ "\"><span class=\"reference\">")) ++ dropUid id ++ (while html "</span></a>")
      where uid = getUid (PosIdent (pos, id)) irMap

printSuper SuperEmpty indent irMap html = ""
printSuper (PosSuperEmpty _) indent irMap html = printSuper SuperEmpty indent irMap html
printSuper (SuperSome superHow setExp) indent irMap html = printSuperHow superHow indent irMap html ++ printSetExp setExp indent irMap html
printSuper (PosSuperSome _ superHow setExp) indent irMap html = printSuper (SuperSome superHow setExp) indent irMap html

printSuperHow SuperColon  indent irMap html = (while html "<span class=\"keyword\">") ++ " :" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperColon _) indent irMap html = printSuperHow SuperColon indent irMap html
printSuperHow SuperArrow  indent irMap html = (while html "<span class=\"keyword\">") ++ " ->" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperArrow _) indent irMap html = printSuperHow SuperArrow indent irMap html
printSuperHow SuperMArrow indent irMap html = (while html "<span class=\"keyword\">") ++ " ->>" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperMArrow _) indent irMap html = printSuperHow SuperMArrow indent irMap html

printCard CardEmpty indent irMap html = ""
printCard (PosCardEmpty _) indent irMap html = printCard CardEmpty indent irMap html
printCard CardLone indent irMap html = " ?"
printCard (PosCardLone _) indent irMap html = printCard CardLone indent irMap html
printCard CardSome indent irMap html = " +"
printCard (PosCardSome _) indent irMap html = printCard CardSome indent irMap html
printCard CardAny indent irMap html = " *"
printCard (PosCardAny _) indent irMap html = printCard CardAny indent irMap html
printCard (CardNum (PosInteger (pos,num))) indent irMap html = " " ++ num 
printCard (PosCardNum _ posInteger) indent irMap html = printCard (CardNum posInteger) indent irMap html
printCard (CardInterval nCard) indent irMap html = " " ++ printNCard nCard indent irMap html
printCard (PosCardInterval _ nCard) indent irMap html = printCard (CardInterval nCard) indent irMap html

printConstraint (Constraint exps) indent irMap html = concatMap (\x -> printConstraint' x indent irMap html) exps
printConstraint (PosConstraint _ exps) indent irMap html = printConstraint (Constraint exps) indent irMap html
printConstraint' exp indent irMap html = (printIndent indent html) ++ while html "<span class=\"keyword\">" ++ "[" ++ while html "</span>" ++ " " ++ printExp exp indent irMap html ++ " " ++ while html "<span class=\"keyword\">" ++ "]" ++ while html "</span></span></span><br>" ++ "\n"

printDecl (Decl locids setExp) indent irMap html = (while html "<span class=\"keyword\">") ++ ":" ++ (while html "</span>") ++ printSetExp setExp indent irMap html
printDecl (PosDecl _ locids setExp) indent irMap html = printDecl (Decl locids setExp) indent irMap html

printInit InitEmpty indent irMap html = ""
printInit (PosInitEmpty _) indent irMap html = printInit InitEmpty indent irMap html
printInit (InitSome initHow exp) indent irMap html = printInitHow initHow indent irMap html ++ printExp exp indent irMap html
printInit (PosInitSome _ initHow exp) indent irMap html = printInit (InitSome initHow exp) indent irMap html

printInitHow InitHow_1 indent irMap html = " = "
printInitHow (PosInitHow_1 _) indent irMap html = printInitHow InitHow_1 indent irMap html
printInitHow InitHow_2 indent irMap html = " := "
printInitHow (PosInitHow_2 _) indent irMap html = printInitHow InitHow_2 indent irMap html

printExp (DeclAllDisj decl exp) indent irMap html = "all disj " ++ (printDecl decl indent irMap html) ++ " | " ++ (printExp exp indent irMap html)
printExp (PosDeclAllDisj _ decl exp) indent irMap html = printExp (DeclAllDisj decl exp) indent irMap html
printExp (DeclAll     decl exp) indent irMap html = "all " ++ (printDecl decl indent irMap html) ++ " | " ++ (printExp exp indent irMap html)
printExp (PosDeclAll _ decl exp) indent irMap html = printExp (DeclAll decl exp) indent irMap html
printExp (DeclQuantDisj quant decl exp) indent irMap html = (printQuant quant indent irMap html) ++ "disj" ++ (printDecl decl indent irMap html) ++ " | " ++ (printExp exp indent irMap html)
printExp (PosDeclQuantDisj _ quant decl exp) indent irMap html = printExp (DeclQuantDisj quant decl exp) indent irMap html
printExp (DeclQuant     quant decl exp) indent irMap html = (printQuant quant indent irMap html) ++ (printDecl decl indent irMap html) ++ " | " ++ (printExp exp indent irMap html)
printExp (PosDeclQuant _ quant decl exp) indent irMap html = printExp (DeclQuant quant decl exp) indent irMap html
printExp (EGMax exp)            indent irMap html = "max " ++ printExp exp indent irMap html
printExp (PosEGMax _ exp)     indent irMap html = printExp (EGMax exp) indent irMap html
printExp (EGMin exp)            indent irMap html = "min " ++ printExp exp indent irMap html
printExp (PosEGMin _ exp) indent irMap html = printExp (EGMin exp) indent irMap html
printExp (ENeq exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " != " ++ (printExp exp2 indent irMap html)
printExp (PosENeq _ exp1 exp2) indent irMap html = printExp (ENeq exp1 exp2) indent irMap html
printExp (ESetExp setExp)       indent irMap html = printSetExp setExp indent irMap html
printExp (PosESetExp _ setExp) indent irMap html = printExp (ESetExp setExp) indent irMap html
printExp (QuantExp quant exp)   indent irMap html = printQuant quant indent irMap html ++ printExp exp indent irMap html
printExp (PosQuantExp _ quant exp) indent irMap html = printExp (QuantExp quant exp) indent irMap html
printExp (EImplies exp1 exp2)   indent irMap html = (printExp exp1 indent irMap html) ++ " => " ++ printExp exp2 indent irMap html
printExp (PosEImplies _ exp1 exp2) indent irMap html = printExp (EImplies exp1 exp2) indent irMap html
printExp (EAnd exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " && " ++ printExp exp2 indent irMap html
printExp (PosEAnd _ exp1 exp2) indent irMap html = printExp (EAnd exp1 exp2) indent irMap html
printExp (EOr exp1 exp2)        indent irMap html = (printExp exp1 indent irMap html) ++ " || " ++ printExp exp2 indent irMap html
printExp (PosEOr _ exp1 exp2) indent irMap html = printExp (EOr exp1 exp2) indent irMap html
printExp (EXor exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " xor " ++ printExp exp2 indent irMap html
printExp (PosEXor _ exp1 exp2) indent irMap html = printExp (EXor exp1 exp2) indent irMap html
printExp (ENeg exp)             indent irMap html = " !" ++ printExp exp indent irMap html
printExp (PosENeg _ exp) indent irMap html = printExp (ENeg exp) indent irMap html
printExp (ELt exp1 exp2)        indent irMap html = (printExp exp1 indent irMap html) ++ " < " ++ printExp exp2 indent irMap html
printExp (PosELt _ exp1 exp2) indent irMap html = printExp (ELt exp1 exp2) indent irMap html
printExp (EGt exp1 exp2)        indent irMap html = (printExp exp1 indent irMap html) ++ " > " ++ printExp exp2 indent irMap html
printExp (PosEGt _ exp1 exp2) indent irMap html = printExp (EGt exp1 exp2) indent irMap html
printExp (EEq exp1 exp2)        indent irMap html = (printExp exp1 indent irMap html) ++ " = " ++ printExp exp2 indent irMap html
printExp (PosEEq _ exp1 exp2) indent irMap html = printExp (EEq exp1 exp2) indent irMap html
printExp (ELte exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " <= " ++ printExp exp2 indent irMap html
printExp (PosELte _ exp1 exp2) indent irMap html = printExp (ELte exp1 exp2) indent irMap html
printExp (EGte exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " >= " ++ printExp exp2 indent irMap html
printExp (PosEGte _ exp1 exp2) indent irMap html = printExp (EGte exp1 exp2) indent irMap html
printExp (EIn exp1 exp2)        indent irMap html = (printExp exp1 indent irMap html) ++ " in " ++ printExp exp2 indent irMap html
printExp (PosEIn _ exp1 exp2) indent irMap html = printExp (EIn exp1 exp2) indent irMap html
printExp (ENin exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " not in " ++ printExp exp2 indent irMap html
printExp (PosENin _ exp1 exp2) indent irMap html = printExp (ENin exp1 exp2) indent irMap html
printExp (EIff exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " <=> " ++ printExp exp2 indent irMap html
printExp (PosEIff _ exp1 exp2) indent irMap html = printExp (EIff exp1 exp2) indent irMap html
printExp (EAdd exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " + " ++ printExp exp2 indent irMap html
printExp (PosEAdd _ exp1 exp2) indent irMap html = printExp (EAdd exp1 exp2) indent irMap html
printExp (ESub exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " - " ++ printExp exp2 indent irMap html
printExp (PosESub _ exp1 exp2) indent irMap html = printExp (ESub exp1 exp2) indent irMap html
printExp (EMul exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " * " ++ printExp exp2 indent irMap html
printExp (PosEMul _ exp1 exp2) indent irMap html = printExp (EMul exp1 exp2) indent irMap html
printExp (EDiv exp1 exp2)       indent irMap html = (printExp exp1 indent irMap html) ++ " / " ++ printExp exp2 indent irMap html
printExp (PosEDiv _ exp1 exp2) indent irMap html = printExp (EDiv exp1 exp2) indent irMap html
printExp (ECSetExp exp)         indent irMap html = "#" ++ printExp exp indent irMap html
printExp (PosECSetExp _ exp) indent irMap html = printExp (ECSetExp exp) indent irMap html
printExp (EMinExp exp)          indent irMap html = "-" ++ printExp exp indent irMap html
printExp (PosEMinExp _ exp) indent irMap html = printExp (EMinExp exp) indent irMap html
printExp (EImpliesElse exp1 exp2 exp3) indent irMap html = "if " ++ (printExp exp1 indent irMap html) ++ " then " ++ (printExp exp2 indent irMap html) ++ " else " ++ (printExp exp3 indent irMap html)
printExp (PosEImpliesElse _ exp1 exp2 exp3) indent irMap html = printExp (EImpliesElse exp1 exp2 exp3) indent irMap html
printExp (EInt (PosInteger (_, num))) indent irMap html = num
printExp (PosEInt _ posInteger) indent irMap html = printExp (EInt posInteger) indent irMap html
printExp (EDouble (PosDouble (_, num))) indent irMap html = num
printExp (PosEDouble _ posDouble) indent irMap html = printExp (EDouble posDouble) indent irMap html
printExp (EStr (PosString (_, str))) indent irMap html = str
printExp (PosEStr _ posString) indent irMap html = printExp (EStr posString) indent irMap html

printSetExp (ClaferId name) indent irMap html = printName name indent irMap html
printSetExp (PosClaferId _ name) indent irMap html = printSetExp (ClaferId name) indent irMap html
printSetExp (Union set1 set2) indent irMap html = (printSetExp set1 indent irMap html) ++ "++" ++ (printSetExp set2 indent irMap html)
printSetExp (PosUnion _ set1 set2) indent irMap html = printSetExp (Union set1 set2) indent irMap html
printSetExp (UnionCom set1 set2) indent irMap html = (printSetExp set1 indent irMap html) ++ "," ++ (printSetExp set2 indent irMap html)
printSetExp (PosUnionCom _ set1 set2) indent irMap html = printSetExp (UnionCom set1 set2) indent irMap html
printSetExp (Difference set1 set2) indent irMap html = (printSetExp set1 indent irMap html) ++ "--" ++ (printSetExp set2 indent irMap html)
printSetExp (PosDifference _ set1 set2) indent irMap html = printSetExp (Difference set1 set2) indent irMap html
printSetExp (Intersection set1 set2) indent irMap html = (printSetExp set1 indent irMap html) ++ "&" ++ (printSetExp set2 indent irMap html)
printSetExp (PosIntersection _ set1 set2) indent irMap html = printSetExp (Intersection set1 set2) indent irMap html
printSetExp (Domain set1 set2) indent irMap html = (printSetExp set1 indent irMap html) ++ "<:" ++ (printSetExp set2 indent irMap html)
printSetExp (PosDomain _ set1 set2) indent irMap html = printSetExp (Domain set1 set2) indent irMap html
printSetExp (Range set1 set2) indent irMap html = (printSetExp set1 indent irMap html) ++ ":>" ++ (printSetExp set2 indent irMap html)
printSetExp (PosRange _ set1 set2) indent irMap html = printSetExp (Range set1 set2) indent irMap html
printSetExp (Join set1 set2) indent irMap html = (printSetExp set1 indent irMap html) ++ "." ++ (printSetExp set2 indent irMap html)
printSetExp (PosJoin _ set1 set2) indent irMap html = printSetExp (Join set1 set2) indent irMap html

printQuant quant indent irMap html = case quant of
  QuantNo        -> while html (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  PosQuantNo _   -> while html (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  QuantLone      -> while html (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  PosQuantLone _ -> while html (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  QuantOne       -> while html (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  PosQuantOne _  -> while html (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  QuantSome      -> while html (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "
  PosQuantSome _ -> while html (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "

printEnumId (EnumIdIdent posident) indent irMap html = printPosIdentRef posident indent irMap html
printEnumId (PosEnumIdIdent _ posident) indent irMap html = printEnumId (EnumIdIdent posident) indent irMap html

printIndent indent html = if indent == 0 || html == False then "" else "<span class=\"l" ++ show indent ++ "\">"

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

while bool exp = if bool then exp else []

cleanOutput "" = ""
cleanOutput (' ':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput ('\n':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput (' ':'<':'b':'r':'>':xs) = "<br>"++cleanOutput xs
cleanOutput (x:xs) = x : cleanOutput xs
