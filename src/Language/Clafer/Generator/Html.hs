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
module Language.Clafer.Generator.Html (genHtml, genText, printModule, traceAstModule, traceIrModule) where

import Language.Clafer.Front.Absclafer
import Language.Clafer.Front.LayoutResolver(revertLayout)
import Language.Clafer.Intermediate.Tracing
import Data.List (intersperse)

genHtml x = cleanOutput $ revertLayout $ printModule x True --make sure to add an "HTML" flag. True to output HTML tags, false for plain text
genText x = cleanOutput $ revertLayout $ printModule x False

printModule (Module [])     html = ""
printModule (Module (x:xs)) html = (printDeclaration x 0 html) ++ (printModule $ Module xs) html
printModule (PosModule _ declarations) html = printModule (Module declarations) html

printDeclaration (EnumDecl posIdent enumIds)       indent html = (while html "<span class=\"keyword\">") ++ "enum" ++ (while html "</span>") ++ " =" ++ (printPosIdentRef posIdent indent html) ++ (concat $ intersperse ";" (map (\x -> printEnumId x indent html) enumIds))
printDeclaration (PosEnumDecl _ posIdent enumIds)  indent html = printDeclaration (EnumDecl posIdent enumIds) indent html
printDeclaration (ElementDecl element)             indent html = printElement element indent html
printDeclaration (PosElementDecl _ element)        indent html = printDeclaration (ElementDecl element) indent html

printElement (Subclafer clafer) indent html = printClafer clafer indent html
printElement (PosSubclafer _ subclafer) indent html = printElement (Subclafer subclafer) indent html
printElement (Subconstraint constraint) indent html = (printIndent indent html) ++ printConstraint constraint indent html
printElement (PosSubconstraint _ constraint) indent html = printElement (Subconstraint constraint) indent html
printElement (ClaferUse name card elements) indent html = printIndent indent html ++ "`" ++ printName name indent html ++ printCard card indent html ++ printElements elements indent html
printElement (PosClaferUse _ name card elements) indent html = printElement (ClaferUse name card elements) indent html
printElement (Subgoal goal) indent html = printGoal goal indent html
printElement (PosSubgoal _ goal) indent html = printElement (Subgoal goal) indent html
printElement (Subsoftconstraint softConstraint) indent html = printSoftConstraint softConstraint indent html
printElement (PosSubsoftconstraint _ softConstraint) indent html = printElement (Subsoftconstraint softConstraint) indent html

printElements ElementsEmpty indent html = ""
printElements (PosElementsEmpty _) indent html = printElements ElementsEmpty indent html
printElements (ElementsList elements) indent html = "{" ++ (concatMap (\x -> printElement x (indent + 1) html ++ "\n") elements) ++ "\n}"
printElements (PosElementsList _ elements) indent html = printElements (ElementsList elements) indent html

printClafer (Clafer abstract gCard id super card init elements) indent html
  | indent == 0 = let (PosIdent (_, divid)) = id in -- needs to get uid
                    (while html ("<div id=\"" ++ divid ++ "\">\n")) ++ (concat [printAbstract abstract indent html, printGCard gCard indent html,
                    printPosIdent id indent html, printSuper super indent html, printCard card indent html, printInit init indent html])
                    ++ (while html "<br>") ++ "\n" ++ printElements elements indent html ++ (while html "</div>\n<br>") ++ "\n"
  | otherwise   = let (PosIdent (_, divid)) = id in -- needs to get uid
                    (while html ("<span id=\"" ++ divid ++ "\" class=\"l" ++ show indent ++ "\">")) ++ (concat [printAbstract abstract indent html, printGCard gCard indent html,
                    printPosIdent id indent html, printSuper super indent html, printCard card indent html, printInit init indent html])
                    ++ (while html "</span><br>") ++ "\n" ++ printElements elements indent html
printClafer (PosClafer _ abstract gCard id super card init elements) indent html = printClafer (Clafer abstract gCard id super card init elements) indent html

printGoal (Goal exps) indent html = (if html then "&lt;&lt;" else "<<") ++ concatMap (\x -> printExp x indent html) exps ++ if html then "&gt;&gt;" else ">>"
printGoal (PosGoal _ exps) indent html = printGoal (Goal exps) indent html

printSoftConstraint (SoftConstraint exps) indent html = "(" ++ concatMap (\x -> printExp x indent html) exps ++ ")"
printSoftConstraint (PosSoftConstraint _ exps) indent html = printSoftConstraint (SoftConstraint exps) indent html

printAbstract Abstract indent html = (while html "<span class=\"keyword\">") ++ "abstract" ++ (while html "</span>") ++ " "
printAbstract (PosAbstract _) indent html = printAbstract Abstract indent html
printAbstract AbstractEmpty indent html = ""
printAbstract (PosAbstractEmpty _) indent html = printAbstract AbstractEmpty indent html

printGCard gCard indent html = case gCard of
  (GCardInterval ncard) -> printNCard ncard indent html
  (PosGCardInterval _ ncard) -> printNCard ncard indent html
  GCardEmpty        -> ""
  (PosGCardEmpty _) -> ""
  GCardXor          -> (while html "<span class=\"keyword\">") ++ "xor" ++ (while html "</span>") ++ " "
  (PosGCardXor _)   -> (while html "<span class=\"keyword\">") ++ "xor" ++ (while html "</span>") ++ " "
  GCardOr           -> (while html "<span class=\"keyword\">") ++ "or"  ++ (while html "</span>") ++ " "
  (PosGCardOr _)    -> (while html "<span class=\"keyword\">") ++ "or"  ++ (while html "</span>") ++ " "
  GCardMux          -> (while html "<span class=\"keyword\">") ++ "mux" ++ (while html "</span>") ++ " "
  (PosGCardMux _)   -> (while html "<span class=\"keyword\">") ++ "mux" ++ (while html "</span>") ++ " "
  GCardOpt          -> (while html "<span class=\"keyword\">") ++ "opt" ++ (while html "</span>") ++ " "
  (PosGCardOpt _)   -> (while html "<span class=\"keyword\">") ++ "opt" ++ (while html "</span>") ++ " "

printNCard (NCard (PosInteger (pos, num)) exInteger) indent html = if validPos pos
    then case exInteger of
      ExIntegerAst                -> num ++ "..*"
      (ExIntegerNum (PosInteger (pos', num'))) -> num ++ ".." ++ num'
    else ""
printNCard (PosNCard _ ncard exInteger) indent html = printNCard (NCard ncard exInteger) indent html

printName (Path modids) indent html = unwords $ map (\x -> printModId x indent html) modids
printName (PosPath _ modids) indent html = printName (Path modids) indent html

printModId (ModIdIdent posident) indent html = printPosIdentRef posident indent html
printModId (PosModIdIdent _ posident) indent html = printModId (ModIdIdent posident) indent html

printPosIdent (PosIdent (pos, id)) indent html
  | validPos pos   = id ++ " " --identifier
  | otherwise      = ""

printPosIdentRef (PosIdent (pos, id)) indent html --need to lookup UID for 'id'
  | validPos pos   = (while html ("<a href=\"#" ++ id ++ "\"><span class=\"reference\">")) ++ dropUid id ++ (while html "</span></a>") ++ " " --reference
  | otherwise      = ""

printSuper SuperEmpty indent html = ""
printSuper (PosSuperEmpty _) indent html = printSuper SuperEmpty indent html
printSuper (SuperSome superHow setExp) indent html = printSuperHow superHow indent html ++ printSetExp setExp indent html
printSuper (PosSuperSome _ superHow setExp) indent html = printSuper (SuperSome superHow setExp) indent html

printSuperHow SuperColon  indent html = (while html "<span class=\"keyword\">") ++ ":" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperColon _) indent html = printSuperHow SuperColon indent html
printSuperHow SuperArrow  indent html = (while html "<span class=\"keyword\">") ++ "->" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperArrow _) indent html = printSuperHow SuperArrow indent html
printSuperHow SuperMArrow indent html = (while html "<span class=\"keyword\">") ++ "->>" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperMArrow _) indent html = printSuperHow SuperMArrow indent html

printCard CardEmpty indent html = ""
printCard (PosCardEmpty _) indent html = printCard CardEmpty indent html
printCard CardLone indent html = "?"
printCard (PosCardLone _) indent html = printCard CardLone indent html
printCard CardSome indent html = "+"
printCard (PosCardSome _) indent html = printCard CardSome indent html
printCard CardAny indent html = "*"
printCard (PosCardAny _) indent html = printCard CardAny indent html
printCard (CardNum (PosInteger (pos,num))) indent html =  if validPos pos then num else ""
printCard (PosCardNum _ posInteger) indent html = printCard (CardNum posInteger) indent html
printCard (CardInterval nCard) indent html = printNCard nCard indent html
printCard (PosCardInterval _ nCard) indent html = printCard (CardInterval nCard) indent html

printConstraint (Constraint exps) indent html = (while html "<span class=\"keyword\">") ++ "[" ++ (while html "</span>") ++ " " ++ (concat $ map (\x -> printExp x indent html) exps) ++ (while html "<span class=\"keyword\">") ++ "]" ++ (while html "</span></span><br>\n")
printConstraint (PosConstraint _ exps) indent html = printConstraint (Constraint exps) indent html

printDecl (Decl locids setExp) indent html = (while html "<span class=\"keyword\">") ++ ":" ++ (while html "</span>") ++ printSetExp setExp indent html
printDecl (PosDecl _ locids setExp) indent html = printDecl (Decl locids setExp) indent html

printInit InitEmpty indent html = ""
printInit (PosInitEmpty _) indent html = printInit InitEmpty indent html
printInit (InitSome initHow exp) indent html = printInitHow initHow indent html ++ printExp exp indent html
printInit (PosInitSome _ initHow exp) indent html = printInit (InitSome initHow exp) indent html

printInitHow InitHow_1 indent html = "= "
printInitHow (PosInitHow_1 _) indent html = printInitHow InitHow_1 indent html
printInitHow InitHow_2 indent html = ":= "
printInitHow (PosInitHow_2 _) indent html = printInitHow InitHow_2 indent html

printExp (DeclAllDisj decl exp) indent html = "all disj " ++ (printDecl decl indent html) ++ " | " ++ (printExp exp indent html)
printExp (PosDeclAllDisj _ decl exp) indent html = printExp (DeclAllDisj decl exp) indent html
printExp (DeclAll     decl exp) indent html = "all " ++ (printDecl decl indent html) ++ " | " ++ (printExp exp indent html)
printExp (PosDeclAll _ decl exp) indent html = printExp (DeclAll decl exp) indent html
printExp (DeclQuantDisj quant decl exp) indent html = (printQuant quant indent html) ++ "disj" ++ (printDecl decl indent html) ++ " | " ++ (printExp exp indent html)
printExp (PosDeclQuantDisj _ quant decl exp) indent html = printExp (DeclQuantDisj quant decl exp) indent html
printExp (DeclQuant     quant decl exp) indent html = (printQuant quant indent html) ++ (printDecl decl indent html) ++ " | " ++ (printExp exp indent html)
printExp (PosDeclQuant _ quant decl exp) indent html = printExp (DeclQuant quant decl exp) indent html
printExp (EGMax exp)            indent html = "max " ++ printExp exp indent html
printExp (PosEGMax _ exp)     indent html = printExp (EGMax exp) indent html
printExp (EGMin exp)            indent html = "min " ++ printExp exp indent html
printExp (PosEGMin _ exp) indent html = printExp (EGMin exp) indent html
printExp (ENeq exp1 exp2)       indent html = (printExp exp1 indent html) ++ "!= " ++ (printExp exp2 indent html)
printExp (PosENeq _ exp1 exp2) indent html = printExp (ENeq exp1 exp2) indent html
printExp (ESetExp setExp)       indent html = printSetExp setExp indent html
printExp (PosESetExp _ setExp) indent html = printExp (ESetExp setExp) indent html
printExp (QuantExp quant exp)   indent html = printQuant quant indent html ++ printExp exp indent html
printExp (PosQuantExp _ quant exp) indent html = printExp (QuantExp quant exp) indent html
printExp (EImplies exp1 exp2)   indent html = (printExp exp1 indent html) ++ "=> " ++ printExp exp2 indent html
printExp (PosEImplies _ exp1 exp2) indent html = printExp (EImplies exp1 exp2) indent html
printExp (EAnd exp1 exp2)       indent html = (printExp exp1 indent html) ++ "&& " ++ printExp exp2 indent html
printExp (PosEAnd _ exp1 exp2) indent html = printExp (EAnd exp1 exp2) indent html
printExp (EOr exp1 exp2)        indent html = (printExp exp1 indent html) ++ "|| " ++ printExp exp2 indent html
printExp (PosEOr _ exp1 exp2) indent html = printExp (EOr exp1 exp2) indent html
printExp (EXor exp1 exp2)       indent html = (printExp exp1 indent html) ++ "xor " ++ printExp exp2 indent html
printExp (PosEXor _ exp1 exp2) indent html = printExp (EXor exp1 exp2) indent html
printExp (ENeg exp)             indent html = " ! " ++ printExp exp indent html
printExp (PosENeg _ exp) indent html = printExp (ENeg exp) indent html
printExp (ELt exp1 exp2)        indent html = (printExp exp1 indent html) ++ "< " ++ printExp exp2 indent html
printExp (PosELt _ exp1 exp2) indent html = printExp (ELt exp1 exp2) indent html
printExp (EGt exp1 exp2)        indent html = (printExp exp1 indent html) ++ "> " ++ printExp exp2 indent html
printExp (PosEGt _ exp1 exp2) indent html = printExp (EGt exp1 exp2) indent html
printExp (EEq exp1 exp2)        indent html = (printExp exp1 indent html) ++ "= " ++ printExp exp2 indent html
printExp (PosEEq _ exp1 exp2) indent html = printExp (EEq exp1 exp2) indent html
printExp (ELte exp1 exp2)       indent html = (printExp exp1 indent html) ++ "<= " ++ printExp exp2 indent html
printExp (PosELte _ exp1 exp2) indent html = printExp (ELte exp1 exp2) indent html
printExp (EGte exp1 exp2)       indent html = (printExp exp1 indent html) ++ ">= " ++ printExp exp2 indent html
printExp (PosEGte _ exp1 exp2) indent html = printExp (EGte exp1 exp2) indent html
printExp (EIn exp1 exp2)        indent html = (printExp exp1 indent html) ++ "in " ++ printExp exp2 indent html
printExp (PosEIn _ exp1 exp2) indent html = printExp (EIn exp1 exp2) indent html
printExp (ENin exp1 exp2)       indent html = (printExp exp1 indent html) ++ "not in " ++ printExp exp2 indent html
printExp (PosENin _ exp1 exp2) indent html = printExp (ENin exp1 exp2) indent html
printExp (EIff exp1 exp2)       indent html = (printExp exp1 indent html) ++ "<=> " ++ printExp exp2 indent html
printExp (PosEIff _ exp1 exp2) indent html = printExp (EIff exp1 exp2) indent html
printExp (EAdd exp1 exp2)       indent html = (printExp exp1 indent html) ++ "+ " ++ printExp exp2 indent html
printExp (PosEAdd _ exp1 exp2) indent html = printExp (EAdd exp1 exp2) indent html
printExp (ESub exp1 exp2)       indent html = (printExp exp1 indent html) ++ "- " ++ printExp exp2 indent html
printExp (PosESub _ exp1 exp2) indent html = printExp (ESub exp1 exp2) indent html
printExp (EMul exp1 exp2)       indent html = (printExp exp1 indent html) ++ "* " ++ printExp exp2 indent html
printExp (PosEMul _ exp1 exp2) indent html = printExp (EMul exp1 exp2) indent html
printExp (EDiv exp1 exp2)       indent html = (printExp exp1 indent html) ++ "/ " ++ printExp exp2 indent html
printExp (PosEDiv _ exp1 exp2) indent html = printExp (EDiv exp1 exp2) indent html
printExp (ECSetExp exp)         indent html = "#" ++ printExp exp indent html
printExp (PosECSetExp _ exp) indent html = printExp (ECSetExp exp) indent html
printExp (EMinExp exp)          indent html = "-" ++ printExp exp indent html
printExp (PosEMinExp _ exp) indent html = printExp (EMinExp exp) indent html
printExp (EImpliesElse exp1 exp2 exp3) indent html = "if " ++ (printExp exp1 indent html) ++ " then " ++ (printExp exp2 indent html) ++ " else " ++ (printExp exp3 indent html)
printExp (PosEImpliesElse _ exp1 exp2 exp3) indent html = printExp (EImpliesElse exp1 exp2 exp3) indent html
printExp (EInt (PosInteger (pos, num))) indent html = if validPos pos then num else ""
printExp (PosEInt _ posInteger) indent html = printExp (EInt posInteger) indent html
printExp (EDouble (PosDouble (pos, num))) indent html = if validPos pos then num else ""
printExp (PosEDouble _ posDouble) indent html = printExp (EDouble posDouble) indent html
printExp (EStr (PosString (pos, str))) indent html = if validPos pos then str else ""
printExp (PosEStr _ posString) indent html = printExp (EStr posString) indent html

printSetExp (ClaferId name) indent html = printName name indent html
printSetExp (PosClaferId _ name) indent html = printSetExp (ClaferId name) indent html
printSetExp (Union set1 set2) indent html = (printSetExp set1 indent html) ++ "++" ++ (printSetExp set2 indent html)
printSetExp (PosUnion _ set1 set2) indent html = printSetExp (Union set1 set2) indent html
printSetExp (UnionCom set1 set2) indent html = (printSetExp set1 indent html) ++ "," ++ (printSetExp set2 indent html)
printSetExp (PosUnionCom _ set1 set2) indent html = printSetExp (UnionCom set1 set2) indent html
printSetExp (Difference set1 set2) indent html = (printSetExp set1 indent html) ++ "--" ++ (printSetExp set2 indent html)
printSetExp (PosDifference _ set1 set2) indent html = printSetExp (Difference set1 set2) indent html
printSetExp (Intersection set1 set2) indent html = (printSetExp set1 indent html) ++ "&" ++ (printSetExp set2 indent html)
printSetExp (PosIntersection _ set1 set2) indent html = printSetExp (Intersection set1 set2) indent html
printSetExp (Domain set1 set2) indent html = (printSetExp set1 indent html) ++ "<:" ++ (printSetExp set2 indent html)
printSetExp (PosDomain _ set1 set2) indent html = printSetExp (Domain set1 set2) indent html
printSetExp (Range set1 set2) indent html = (printSetExp set1 indent html) ++ ":>" ++ (printSetExp set2 indent html)
printSetExp (PosRange _ set1 set2) indent html = printSetExp (Range set1 set2) indent html
printSetExp (Join set1 set2) indent html = (printSetExp set1 indent html) ++ "." ++ (printSetExp set2 indent html)
printSetExp (PosJoin _ set1 set2) indent html = printSetExp (Join set1 set2) indent html

printQuant quant indent html = case quant of
  QuantNo        -> while html (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  PosQuantNo _   -> while html (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  QuantLone      -> while html (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  PosQuantLone _ -> while html (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  QuantOne       -> while html (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  PosQuantOne _  -> while html (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  QuantSome      -> while html (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "
  PosQuantSome _ -> while html (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "

printEnumId (EnumIdIdent posident) indent html = printPosIdentRef posident indent html
printEnumId (PosEnumIdIdent _ posident) indent html = printEnumId (EnumIdIdent posident) indent html

printIndent indent html = if indent == 0 || html == False then "" else "<span class=\"l" ++ show indent ++ "\">"

validPos (row, col)
  | row >= 0 && col >= 0 = True -- make strictly greater than when implementing source mapping
  | otherwise          = False

dropUid uid = let id = rest $ dropWhile (\x -> x /= '_') uid in if id == "" then uid else id
--dropUid = id --for now. Just testing.
--so it fails more gracefully on empty lists
rest [] = []
rest (_:xs) = xs

{-getUid span irMap = let iClafer = lookup span irMap in if iClafer == Nothing
                                                       then "error: UID not found."
                                                       else uid iClafer-}

while bool exp = if bool then exp else []

cleanOutput "" = ""
cleanOutput (' ':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput ('\n':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput (' ':'<':'b':'r':'>':xs) = "<br>"++cleanOutput xs
cleanOutput (x:xs) = x : cleanOutput xs
