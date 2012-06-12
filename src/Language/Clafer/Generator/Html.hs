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
module Language.Clafer.Generator.Html (genHtml) where

import Language.Clafer.Front.Absclafer
import Data.List (intersperse)

genHtml = printModule

printModule (Module [])     = ""
printModule (Module (x:xs)) = (printDeclaration x 0) ++ (printModule $ Module xs)

printDeclaration (EnumDecl posIdent enumIds) indent = "<span class=\"keyword\">enum</span>=" ++ (printPosIdentRef posIdent indent) ++ (concat $ intersperse ";" (map (\x -> printEnumId x (indent)) enumIds))
printDeclaration (ElementDecl element)       indent = printElement element indent

printElement (Subclafer (Clafer abstract gCard id super card init (ElementsList elements))) indent
  | indent == 0 = let (PosIdent (_, divid)) = id in
                    "<div id=\"" ++ divid ++ "\">\n" ++ (unwords [printAbstract abstract indent, printGCard gCard indent,
                    printPosIdent id indent, printSuper super indent, printCard card indent, printInit init indent])
                    ++ "<br>\n" ++ (concatMap (\x -> printElement x (indent + 1)) elements) ++ "</div>"
  | otherwise   = let (PosIdent (_, divid)) = id in
                    "<span id=\"" ++ divid ++ "\" class=\"l" ++ show indent ++ "\">" ++ (unwords [printAbstract abstract indent, printGCard gCard indent,
                    printPosIdent id indent, printSuper super indent, printCard card indent, printInit init indent])
                    ++ "</span>" ++ "<br>\n" ++ (concatMap (\x -> printElement x (indent + 1)) elements)
printElement (Subconstraint constraint) indent = (printIndent indent) ++ printConstraint constraint indent
printElement (ClaferUse name card elements) indent = printIndent indent ++ "`" ++ printName name indent ++ printCard card indent ++ printElements elements indent
printElement (Subgoal goal) indent = printGoal goal indent
printElement (Subsoftconstraint softConstraint) indent = printSoftConstraint softConstraint indent

printElements ElementsEmpty indent = ""
printElements (ElementsList elements) indent = "{" ++ (concatMap (\x -> printElement x (indent + 1)) elements) ++ "}"

printGoal (Goal exps) indent = "&lt;&lt;" ++ concatMap (\x -> printExp x indent) exps ++ "&gt;&gt;"

printSoftConstraint (SoftConstraint exps) indent = "(" ++ concatMap (\x -> printExp x indent) exps ++ ")"

printAbstract Abstract indent = "<span class=\"keyword\">abstract</span>"
printAbstract AbstractEmpty indent = ""

printGCard gCard indent = case gCard of
  (GCardInterval ncard) -> printNCard ncard indent
  GCardEmpty -> ""
  GCardXor   -> "<span class=\"keyword\">xor</span>"
  GCardOr    -> "<span class=\"keyword\">or</span>"
  GCardMux   -> "<span class=\"keyword\">mux</span>"
  GCardOpt   -> "<span class=\"keyword\">opt</span>"

printNCard (NCard (PosInteger (pos, num)) exInteger) indent = if validPos pos
    then case exInteger of
      ExIntegerAst                -> num ++ "..*"
      (ExIntegerNum (PosInteger (pos', num'))) -> num ++ ".." ++ num'
    else ""

printName (Path modids) indent = unwords $ map (\x -> printModId x indent) modids

printModId (ModIdIdent posident) indent = printPosIdentRef posident indent

printPosIdent (PosIdent (pos, id)) indent
  | validPos pos   = dropUid id --identifier
  | otherwise      = ""

printPosIdentRef (PosIdent (pos, id)) indent
  | validPos pos   = "<a href=\"#" ++ id ++ "\">" ++ dropUid id ++ "</a>" --reference
  | otherwise      = ""

printSuper SuperEmpty indent = ""
printSuper (SuperSome superHow setExp) indent = printSuperHow superHow indent ++ printSetExp setExp indent

printSuperHow SuperColon  indent = " <span class=\"keyword\">:</span> "
printSuperHow SuperArrow  indent = " <span class=\"keyword\">-></span> "
printSuperHow SuperMArrow indent = " <span class=\"keyword\">->></span> "

printCard CardEmpty indent = ""
printCard CardLone indent = "?"
printCard CardSome indent = "+"
printCard CardAny indent = "*"
printCard (CardNum (PosInteger (pos,num))) indent =  if validPos pos then num else ""
printCard (CardInterval nCard) indent = printNCard nCard indent

printConstraint (Constraint exps) indent = "<span class=\"keyword\">[</span> "  ++ (concat $ map (\x -> printExp x indent) exps) ++ " <span class=\"keyword\">]</span></span><br>\n"

printDecl (Decl locids setExp) indent = "<span class=\"keyword\">:</span>" ++ printSetExp setExp indent

printInit InitEmpty indent = ""
printInit (InitSome initHow exp) indent = printInitHow initHow indent ++ printExp exp indent

printInitHow InitHow_1 indent = "="
printInitHow InitHow_2 indent = ":="

printExp (DeclAllDisj decl exp) indent = "all disj " ++ (printDecl decl indent) ++ " | " ++ (printExp exp indent)
printExp (DeclAll     decl exp) indent = "all " ++ (printDecl decl indent) ++ " | " ++ (printExp exp indent)
printExp (DeclQuantDisj quant decl exp) indent = (printQuant quant indent) ++ "disj" ++ (printDecl decl indent) ++ " | " ++ (printExp exp indent)
printExp (DeclQuant     quant decl exp) indent = (printQuant quant indent) ++ (printDecl decl indent) ++ " | " ++ (printExp exp indent)
printExp (EGMax exp)            indent = "max " ++ printExp exp indent
printExp (EGMin exp)            indent = "min " ++ printExp exp indent
printExp (ENeq exp1 exp2)       indent = (printExp exp1 indent) ++ " != " ++ (printExp exp2 indent)
printExp (ESetExp setExp)       indent = printSetExp setExp indent
printExp (QuantExp quant exp)   indent = printQuant quant indent ++ printExp exp indent
printExp (EImplies exp1 exp2)   indent = (printExp exp1 indent) ++ " => " ++ printExp exp2 indent
printExp (EAnd exp1 exp2)       indent = (printExp exp1 indent) ++ " && " ++ printExp exp2 indent
printExp (EOr exp1 exp2)        indent = (printExp exp1 indent) ++ " || " ++ printExp exp2 indent
printExp (EXor exp1 exp2)       indent = (printExp exp1 indent) ++ " xor " ++ printExp exp2 indent
printExp (ENeg exp)             indent = " ! " ++ printExp exp indent
printExp (ELt exp1 exp2)        indent = (printExp exp1 indent) ++ " < " ++ printExp exp2 indent
printExp (EGt exp1 exp2)        indent = (printExp exp1 indent) ++ " > " ++ printExp exp2 indent
printExp (EEq exp1 exp2)        indent = (printExp exp1 indent) ++ " = " ++ printExp exp2 indent
printExp (ELte exp1 exp2)       indent = (printExp exp1 indent) ++ " <= " ++ printExp exp2 indent
printExp (EGte exp1 exp2)       indent = (printExp exp1 indent) ++ " >= " ++ printExp exp2 indent
printExp (EIn exp1 exp2)        indent = (printExp exp1 indent) ++ " in " ++ printExp exp2 indent
printExp (ENin exp1 exp2)       indent = (printExp exp1 indent) ++ " not in " ++ printExp exp2 indent
printExp (EIff exp1 exp2)       indent = (printExp exp1 indent) ++ " <=> " ++ printExp exp2 indent
printExp (EAdd exp1 exp2)       indent = (printExp exp1 indent) ++ " + " ++ printExp exp2 indent
printExp (ESub exp1 exp2)       indent = (printExp exp1 indent) ++ " - " ++ printExp exp2 indent
printExp (EMul exp1 exp2)       indent = (printExp exp1 indent) ++ " * " ++ printExp exp2 indent
printExp (EDiv exp1 exp2)       indent = (printExp exp1 indent) ++ " / " ++ printExp exp2 indent
printExp (ECSetExp exp)         indent = "#" ++ printExp exp indent
printExp (EMinExp exp)          indent = "-" ++ printExp exp indent
printExp (EImpliesElse exp1 exp2 exp3) indent = "if " ++ (printExp exp1 indent) ++ " then " ++ (printExp exp2 indent) ++ " else " ++ (printExp exp3 indent)
printExp (EInt (PosInteger (pos, num))) indent = if validPos pos then num else ""
printExp (EDouble (PosDouble (pos, num))) indent = if validPos pos then num else ""
printExp (EStr (PosString (pos, str))) indent = if validPos pos then str else ""

printSetExp (ClaferId name) indent = printName name indent
printSetExp (Union set1 set2) indent = (printSetExp set1 indent) ++ "++" ++ (printSetExp set2 indent)
printSetExp (UnionCom set1 set2) indent = (printSetExp set1 indent) ++ "," ++ (printSetExp set2 indent)
printSetExp (Difference set1 set2) indent = (printSetExp set1 indent) ++ "--" ++ (printSetExp set2 indent)
printSetExp (Intersection set1 set2) indent = (printSetExp set1 indent) ++ "&" ++ (printSetExp set2 indent)
printSetExp (Domain set1 set2) indent = (printSetExp set1 indent) ++ "<:" ++ (printSetExp set2 indent)
printSetExp (Range set1 set2) indent = (printSetExp set1 indent) ++ ":>" ++ (printSetExp set2 indent)
printSetExp (Join set1 set2) indent = (printSetExp set1 indent) ++ "." ++ (printSetExp set2 indent)

printQuant quant indent = case quant of
  QuantNo    -> "<span class=\"keyword\">no</span> "
  QuantLone  -> "<span class=\"keyword\">lone</span> "
  QuantOne   -> "<span class=\"keyword\">one</span> "
  QuantSome  -> "<span class=\"keyword\">some</span> "

printEnumId (EnumIdIdent posident) indent = printPosIdentRef posident indent

printIndent indent = if indent == 0 then "" else "<span class=\"l" ++ show indent ++ "\">"
-- printCloseIndent indent = if indent == 0 then "" else "</span>"

validPos (row, col)
  | row >= 0 && col >= 0 = True -- make strictly greater than when implementing source mapping
  | otherwise          = False

--dropUid id = rest $ dropWhile (\x -> x /= '_') id
dropUid = id --for now. Just testing.
--so it fails more gracefully on empty lists
rest [] = []
rest (x:xs) = xs
