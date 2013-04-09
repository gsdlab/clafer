{-
 Copyright (C) 2012 Christopher Walker, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Generator.Html (genHtml,
                                       genText,
                                       genTooltip,
                                       printModule,
                                       printDeclaration,
                                       printDecl,
                                       traceAstModule,
                                       traceIrModule,
                                       cleanOutput,
                                       revertLayout,
                                       printComment,
                                       printPreComment,
                                       printStandaloneComment,
                                       printInlineComment,
                                       highlightErrors) where

import Language.ClaferT
import Language.Clafer.Front.Absclafer
import Language.Clafer.Front.LayoutResolver(revertLayout)
import Language.Clafer.Front.Mapper(range)
import Language.Clafer.Intermediate.Tracing
import Language.Clafer.Intermediate.Intclafer
import Data.List (intersperse,genericSplitAt)
import qualified Data.Map as Map
import Data.Maybe
import Data.Char (isSpace)
import Prelude hiding (exp)


printPreComment :: Span -> [(Span, String)] -> ([(Span, String)], String)
printPreComment _ [] = ([], [])
printPreComment span@(Span (Pos row _) _) (c@((Span (Pos row' _) _), comment):cs)
  | row > row' = findAll row ((c:cs), [])
  | otherwise  = (c:cs, "")
    where findAll _ ([],comments) = ([],comments)
          findAll row ((c@((Span (Pos row' col') _), comment):cs), comments)
            | row > row' = case take 3 comment of
                '/':'/':'#':[] -> findAll row (cs, concat [comments, "<!-- " ++ trim (drop 2 comment) ++ " /-->\n"])
                '/':'/':_:[]   -> if col' == 1
                                  then findAll row (cs, concat [comments, printStandaloneComment comment ++ "\n"])
                                  else findAll row (cs, concat [comments, printInlineComment comment ++ "\n"])
                '/':'*':_:[]   -> findAll row (cs, concat [comments, printStandaloneComment comment ++ "\n"])
                otherwise      -> (cs, "Improper form of comment.")-- Should not happen. Bug.
            | otherwise  = ((c:cs), comments)
          findAll row ((c:cs), comments) = findAll row (cs, comments)
printPreComment _ cs = (cs,"")
printComment :: Span -> [(Span, String)] -> ([(Span, String)], String)
printComment _ [] = ([],[])
printComment span@(Span (Pos row _) _) (c@(Span (Pos row' col') _, comment):cs)
  | row == row' = case take 3 comment of
        '/':'/':'#':[] -> (cs,"<!-- " ++ trim (drop 2 comment) ++ " /-->\n")
        '/':'/':_:[]   -> if col' == 1 then (cs,printStandaloneComment comment) else (cs, printInlineComment comment)
        '/':'*':_:[]   -> (cs, printStandaloneComment comment)
        otherwise      -> (cs, "Improper form of comment.")-- Should not happen. Bug.
  | otherwise = (c:cs, "")
  where trim = let f = reverse. dropWhile isSpace in f . f
printComment _ cs = (cs,"")
printStandaloneComment comment = "<p class=\"standalonecomment\">" ++ comment ++ "</p>"
printInlineComment comment = "<span class=\"inlinecomment\">" ++ comment ++ "</span>"

genHtml :: Module -> IModule -> String
genHtml x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) True
genText x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) False
genTooltip m ir = unlines $ filter (\x -> trim x /= []) $ lines $ cleanOutput $ revertLayout $ printModule m ir False

printModule :: Module -> Map.Map Span [Ir] -> Bool -> String
printModule (Module [])     irMap html = ""
printModule (Module (x:xs)) irMap html = (printDeclaration x 0 irMap html []) ++ printModule (Module xs) irMap html
printModule (PosModule _ declarations) irMap html = printModule (Module declarations) irMap html

printDeclaration :: Declaration -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printDeclaration (EnumDecl posIdent enumIds)       indent irMap html comments = 
  (while html "<span class=\"keyword\">") ++ "enum" ++ (while html "</span>") ++ 
  " " ++ (printPosIdentRef posIdent indent irMap html comments) ++ " = " ++ 
  (concat $ intersperse " | " (map (\x -> printEnumId x indent irMap html comments) enumIds))
printDeclaration (PosEnumDecl _ posIdent enumIds)  indent irMap html comments = 
  printDeclaration (EnumDecl posIdent enumIds) indent irMap html comments
printDeclaration (ElementDecl element)             indent irMap html comments = printElement element indent irMap html comments
printDeclaration (PosElementDecl _ element)        indent irMap html comments = 
  printDeclaration (ElementDecl element) indent irMap html comments

printElement (Subclafer clafer) indent irMap html comments = printClafer clafer indent irMap html comments
printElement (PosSubclafer span subclafer) indent irMap html comments = printElement (Subclafer subclafer) indent irMap html comments
printElement (Subconstraint constraint) indent irMap html comments = printConstraint constraint indent irMap html comments
printElement (PosSubconstraint span constraint) indent irMap html comments = let (comments', preComments) = printPreComment span comments; (comments'', comment) = printComment span comments' in preComments ++ printElement (Subconstraint constraint) indent irMap html comments'' ++ comment ++ while html "<br>" ++ "\n"
printElement (ClaferUse name card elements) indent irMap html comments = (printIndent indent html) ++ "`" ++ printName name indent irMap html comments ++ printCard card indent irMap html comments ++ (while html "</span><br>") ++ "\n" ++ printElements elements indent irMap html comments
printElement (PosClaferUse span name card elements) indent irMap html comments = let (divId, superId) = getUseId span irMap;
                                                                                     (comments', preComments) = printPreComment span comments;
                                                                                     (comments'', comment) = printComment span comments' in
                                                                      preComments ++ (while html ("<span id=\"" ++ divId ++ "\" class=\"l" ++ show indent ++ "\">")) ++ "`" ++ (while html ("<a href=\"#" ++ superId ++ "\"><span class=\"reference\">")) ++ printName name indent irMap False [] --trick the printer into only printing the name
                                                                        ++ (while html "</span></a>") ++ printCard card indent irMap html comments ++ comment ++ (while html "</span><br>") ++ "\n" ++ printElements elements indent irMap html comments''
printElement (Subgoal goal) indent irMap html comments = printGoal goal indent irMap html comments
printElement (PosSubgoal span goal) indent irMap html comments = let (comments', preComments) = printPreComment span comments; (comments'', comment) = printComment span comments' in preComments ++ printElement (Subgoal goal) indent irMap html comments'' ++ comment
printElement (Subsoftconstraint softConstraint) indent irMap html comments = printSoftConstraint softConstraint indent irMap html comments
printElement (PosSubsoftconstraint span softConstraint) indent irMap html comments = let (comments', preComments) = printPreComment span comments; (comments'', comment) = printComment span comments' in preComments ++  printElement (Subsoftconstraint softConstraint) indent irMap html comments'' ++ comment

printElements ElementsEmpty indent irMap html comments = ""
printElements (PosElementsEmpty _) indent irMap html comments = printElements ElementsEmpty indent irMap html comments
printElements (ElementsList elements) indent irMap html comments = "\n{" ++ mapElements elements indent irMap html comments ++ "\n}"
    where mapElements []     indent irMap html comments = []
          mapElements (e:es) indent irMap html comments = if span e == noSpan
                                                          then (printElement e (indent + 1) irMap html comments {-++ "\n"-}) ++ mapElements es indent irMap html comments
                                                          else (printElement e (indent + 1) irMap html comments {-++ "\n"-}) ++ mapElements es indent irMap html (afterSpan (span e) comments)
          afterSpan span comments = let (Span _ (Pos line _)) = span in dropWhile (\(x, _) -> let (Span _ (Pos line' _)) = x in line' <= line) comments
          span (PosSubclafer s _) = s
          span (PosSubconstraint s _) = s
          span (PosClaferUse s _ _ _) = s
          span (PosSubgoal s _) = s
          span (PosSubsoftconstraint s _) = s
          span _ = noSpan
printElements (PosElementsList _ elements) indent irMap html comments = printElements (ElementsList elements) indent irMap html comments

printClafer (Clafer abstract gCard id super card init elements) indent irMap html comments
  | indent == 0 = let (PosIdent (_, divid)) = id in
                    (while html ("<div id=\"" ++ divid ++ "\">\n")) ++ (concat [printAbstract abstract indent irMap html comments, printGCard gCard indent irMap html comments,
                    printPosIdent id indent irMap html comments, printSuper super indent irMap html comments, printCard card indent irMap html comments, printInit init indent irMap html comments])
                    ++ (while html "<br>") ++ "\n" ++ printElements elements indent irMap html comments ++ (while html "</div>")
  | otherwise   = let (PosIdent (_, divid)) = id in
                    (while html ("<span id=\"" ++ divid ++ "\" class=\"l" ++ show indent ++ "\">")) ++ (concat [printAbstract abstract indent irMap html comments, printGCard gCard indent irMap html comments,
                    printPosIdent id indent irMap html comments, printSuper super indent irMap html comments, printCard card indent irMap html comments, printInit init indent irMap html comments])
                    ++ (while html "</span><br>") ++ "\n" ++ printElements elements indent irMap html comments
printClafer (PosClafer span abstract gCard id super card init elements) indent irMap html comments
  | indent == 0 = let divId = getDivId span irMap;
                      (comments', preComments) = printPreComment span comments;
                      (comments'', comment) = printComment span comments' in
                    preComments ++ (while html ("<div id=\"" ++ divId ++ "\">\n")) ++ (concat [printAbstract abstract indent irMap html comments, printGCard gCard indent irMap html comments,
                    printPosIdent id indent irMap html comments, printSuper super indent irMap html comments, printCard card indent irMap html comments, printInit init indent irMap html comments])
                    ++ comment ++ (while html "<br>") ++ "\n" ++ printElements elements indent irMap html comments'' ++ (while html "</div>")
  | otherwise   = let uid = getDivId span irMap;
                            (comments', preComments) = printPreComment span comments;
                            (comments'', comment) = printComment span comments' in
                    preComments ++ (while html ("<span id=\"" ++ uid ++ "\" class=\"l" ++ show indent ++ "\">")) ++ (concat [printAbstract abstract indent irMap html comments, printGCard gCard indent irMap html comments,
                    printPosIdent id indent irMap html comments, printSuper super indent irMap html comments, printCard card indent irMap html comments, printInit init indent irMap html comments]) ++ 
                    comment ++ (while html "</span><br>") ++ "\n" ++ printElements elements indent irMap html comments''
                    
printGoal (Goal exps) indent irMap html comments = (if html then "&lt;&lt;" else "<<") ++ concatMap (\x -> printExp x indent irMap html comments) exps ++ if html then "&gt;&gt;" else ">>"
printGoal (PosGoal _ exps) indent irMap html comments = printGoal (Goal exps) indent irMap html comments

printSoftConstraint (SoftConstraint exps) indent irMap html comments = "(" ++ concatMap (\x -> printExp x indent irMap html comments) exps ++ ")"
printSoftConstraint (PosSoftConstraint _ exps) indent irMap html comments = printSoftConstraint (SoftConstraint exps) indent irMap html comments

printAbstract Abstract indent irMap html comments = (while html "<span class=\"keyword\">") ++ "abstract" ++ (while html "</span>") ++ " "
printAbstract (PosAbstract _) indent irMap html comments = printAbstract Abstract indent irMap html comments
printAbstract AbstractEmpty indent irMap html comments = ""
printAbstract (PosAbstractEmpty _) indent irMap html comments = printAbstract AbstractEmpty indent irMap html comments

printGCard gCard indent irMap html comments = case gCard of
  (GCardInterval ncard) -> printNCard ncard indent irMap html comments
  (PosGCardInterval _ ncard) -> printNCard ncard indent irMap html comments
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

printNCard (NCard (PosInteger (pos, num)) exInteger) indent irMap html comments = num ++ ".." ++ printExInteger exInteger indent irMap html comments ++ " "
printNCard (PosNCard _ posinteger exinteger) indent irMap html comments = printNCard (NCard posinteger exinteger) indent irMap html comments
      
printExInteger ExIntegerAst indent irMap html comments = "*"
printExInteger (PosExIntegerAst _) indent irMap html comments = printExInteger ExIntegerAst indent irMap html comments
printExInteger (ExIntegerNum (PosInteger(pos, num))) indent irMap html comments = num
printExInteger (PosExIntegerNum _ posInteger) indent irMap html comments = printExInteger (ExIntegerNum posInteger) indent irMap html comments

printName (Path modids) indent irMap html comments = unwords $ map (\x -> printModId x indent irMap html comments) modids
printName (PosPath _ modids) indent irMap html comments = printName (Path modids) indent irMap html comments

printModId (ModIdIdent posident) indent irMap html comments = printPosIdentRef posident indent irMap html comments
printModId (PosModIdIdent _ posident) indent irMap html comments = printModId (ModIdIdent posident) indent irMap html comments

printPosIdent (PosIdent (pos, id)) indent irMap html comments = id

printPosIdentRef (PosIdent (pos, id)) indent irMap html comments
  = (while html ("<a href=\"#" ++ uid ++ "\"><span class=\"reference\">")) ++ id ++ (while html "</span></a>")
      where uid = getUid (PosIdent (pos, id)) irMap

printSuper SuperEmpty indent irMap html comments = ""
printSuper (PosSuperEmpty _) indent irMap html comments = printSuper SuperEmpty indent irMap html comments
printSuper (SuperSome superHow setExp) indent irMap html comments = printSuperHow superHow indent irMap html comments ++ printSetExp setExp indent irMap html comments
printSuper (PosSuperSome _ superHow setExp) indent irMap html comments = printSuper (SuperSome superHow setExp) indent irMap html comments

printSuperHow SuperColon  indent irMap html comments = (while html "<span class=\"keyword\">") ++ " :" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperColon _) indent irMap html comments = printSuperHow SuperColon indent irMap html comments
printSuperHow SuperArrow  indent irMap html comments = (while html "<span class=\"keyword\">") ++ " ->" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperArrow _) indent irMap html comments = printSuperHow SuperArrow indent irMap html comments
printSuperHow SuperMArrow indent irMap html comments = (while html "<span class=\"keyword\">") ++ " ->>" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperMArrow _) indent irMap html comments = printSuperHow SuperMArrow indent irMap html comments

printCard CardEmpty indent irMap html comments = ""
printCard (PosCardEmpty _) indent irMap html comments = printCard CardEmpty indent irMap html comments
printCard CardLone indent irMap html comments = " ?"
printCard (PosCardLone _) indent irMap html comments = printCard CardLone indent irMap html comments
printCard CardSome indent irMap html comments = " +"
printCard (PosCardSome _) indent irMap html comments = printCard CardSome indent irMap html comments
printCard CardAny indent irMap html comments = " *"
printCard (PosCardAny _) indent irMap html comments = printCard CardAny indent irMap html comments
printCard (CardNum (PosInteger (pos,num))) indent irMap html comments = " " ++ num 
printCard (PosCardNum _ posInteger) indent irMap html comments = printCard (CardNum posInteger) indent irMap html comments
printCard (CardInterval nCard) indent irMap html comments = " " ++ printNCard nCard indent irMap html comments
printCard (PosCardInterval _ nCard) indent irMap html comments = printCard (CardInterval nCard) indent irMap html comments

printConstraint (Constraint exps) indent irMap html comments = concatMap (\x -> printConstraint' x indent irMap html comments) exps
printConstraint (PosConstraint _ exps) indent irMap html comments = printConstraint (Constraint exps) indent irMap html comments
printConstraint' exp indent irMap html comments = (printIndent indent html) ++ while html "<span class=\"keyword\">" ++ "[" ++ while html "</span>"
                                                  ++ " " ++ printExp exp indent irMap html comments ++ " " ++ while html "<span class=\"keyword\">" ++ "]" ++ while html "</span>"
                                                  ++ (if indent == 0 then "" else while html "</span>") 

printDecl (Decl locids setExp) indent irMap html comments = 
  (concat $ intersperse "; " $ map printLocId locids) ++
  (while html "<span class=\"keyword\">") ++ " : " ++ (while html "</span>") ++ printSetExp setExp indent irMap html comments
  where
    printLocId :: LocId -> String
    printLocId (LocIdIdent (PosIdent (_, ident))) = ident
    printLocId (PosLocIdIdent _ (PosIdent (_, ident))) = ident
printDecl (PosDecl _ locids setExp) indent irMap html comments = printDecl (Decl locids setExp) indent irMap html comments

printInit InitEmpty indent irMap html comments = ""
printInit (PosInitEmpty _) indent irMap html comments = printInit InitEmpty indent irMap html comments
printInit (InitSome initHow exp) indent irMap html comments = printInitHow initHow indent irMap html comments ++ printExp exp indent irMap html comments
printInit (PosInitSome _ initHow exp) indent irMap html comments = printInit (InitSome initHow exp) indent irMap html comments

printInitHow InitHow_1 indent irMap html comments = " = "
printInitHow (PosInitHow_1 _) indent irMap html comments = printInitHow InitHow_1 indent irMap html comments
printInitHow InitHow_2 indent irMap html comments = " := "
printInitHow (PosInitHow_2 _) indent irMap html comments = printInitHow InitHow_2 indent irMap html comments

printExp (DeclAllDisj decl exp) indent irMap html comments = "all disj " ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp indent irMap html comments)
printExp (PosDeclAllDisj _ decl exp) indent irMap html comments = printExp (DeclAllDisj decl exp) indent irMap html comments
printExp (DeclAll     decl exp) indent irMap html comments = "all " ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp indent irMap html comments)
printExp (PosDeclAll _ decl exp) indent irMap html comments = printExp (DeclAll decl exp) indent irMap html comments
printExp (DeclQuantDisj quant decl exp) indent irMap html comments = (printQuant quant indent irMap html comments) ++ "disj" ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp indent irMap html comments)
printExp (PosDeclQuantDisj _ quant decl exp) indent irMap html comments = printExp (DeclQuantDisj quant decl exp) indent irMap html comments
printExp (DeclQuant     quant decl exp) indent irMap html comments = (printQuant quant indent irMap html comments) ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp indent irMap html comments)
printExp (PosDeclQuant _ quant decl exp) indent irMap html comments = printExp (DeclQuant quant decl exp) indent irMap html comments
printExp (EGMax exp)            indent irMap html comments = "max " ++ printExp exp indent irMap html comments
printExp (PosEGMax _ exp)     indent irMap html comments = printExp (EGMax exp) indent irMap html comments
printExp (EGMin exp)            indent irMap html comments = "min " ++ printExp exp indent irMap html comments
printExp (PosEGMin _ exp) indent irMap html comments = printExp (EGMin exp) indent irMap html comments
printExp (ENeq exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " != " ++ (printExp exp2 indent irMap html comments)
printExp (PosENeq _ exp1 exp2) indent irMap html comments = printExp (ENeq exp1 exp2) indent irMap html comments
printExp (ESetExp setExp)       indent irMap html comments = printSetExp setExp indent irMap html comments
printExp (PosESetExp _ setExp) indent irMap html comments = printExp (ESetExp setExp) indent irMap html comments
printExp (QuantExp quant exp)   indent irMap html comments = printQuant quant indent irMap html comments ++ printExp exp indent irMap html comments
printExp (PosQuantExp _ quant exp) indent irMap html comments = printExp (QuantExp quant exp) indent irMap html comments
printExp (EImplies exp1 exp2)   indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " => " ++ printExp exp2 indent irMap html comments
printExp (PosEImplies _ exp1 exp2) indent irMap html comments = printExp (EImplies exp1 exp2) indent irMap html comments
printExp (EAnd exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " && " ++ printExp exp2 indent irMap html comments
printExp (PosEAnd _ exp1 exp2) indent irMap html comments = printExp (EAnd exp1 exp2) indent irMap html comments
printExp (EOr exp1 exp2)        indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " || " ++ printExp exp2 indent irMap html comments
printExp (PosEOr _ exp1 exp2) indent irMap html comments = printExp (EOr exp1 exp2) indent irMap html comments
printExp (EXor exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " xor " ++ printExp exp2 indent irMap html comments
printExp (PosEXor _ exp1 exp2) indent irMap html comments = printExp (EXor exp1 exp2) indent irMap html comments
printExp (ENeg exp)             indent irMap html comments = " ! " ++ printExp exp indent irMap html comments
printExp (PosENeg _ exp) indent irMap html comments = printExp (ENeg exp) indent irMap html comments
printExp (ELt exp1 exp2)        indent irMap html comments = (printExp exp1 indent irMap html comments) ++ (if html then " &lt; " else " < ") ++ printExp exp2 indent irMap html comments
printExp (PosELt _ exp1 exp2) indent irMap html comments = printExp (ELt exp1 exp2) indent irMap html comments
printExp (EGt exp1 exp2)        indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " > " ++ printExp exp2 indent irMap html comments
printExp (PosEGt _ exp1 exp2) indent irMap html comments = printExp (EGt exp1 exp2) indent irMap html comments
printExp (EEq exp1 exp2)        indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " = " ++ printExp exp2 indent irMap html comments
printExp (PosEEq _ exp1 exp2) indent irMap html comments = printExp (EEq exp1 exp2) indent irMap html comments
printExp (ELte exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ (if html then " &lt;= " else " <= ") ++ printExp exp2 indent irMap html comments
printExp (PosELte _ exp1 exp2) indent irMap html comments = printExp (ELte exp1 exp2) indent irMap html comments
printExp (EGte exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " >= " ++ printExp exp2 indent irMap html comments
printExp (PosEGte _ exp1 exp2) indent irMap html comments = printExp (EGte exp1 exp2) indent irMap html comments
printExp (EIn exp1 exp2)        indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " in " ++ printExp exp2 indent irMap html comments
printExp (PosEIn _ exp1 exp2) indent irMap html comments = printExp (EIn exp1 exp2) indent irMap html comments
printExp (ENin exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " not in " ++ printExp exp2 indent irMap html comments
printExp (PosENin _ exp1 exp2) indent irMap html comments = printExp (ENin exp1 exp2) indent irMap html comments
printExp (EIff exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ (if html then " &lt;=&gt; " else " <=> ") ++ printExp exp2 indent irMap html comments
printExp (PosEIff _ exp1 exp2) indent irMap html comments = printExp (EIff exp1 exp2) indent irMap html comments
printExp (EAdd exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " + " ++ printExp exp2 indent irMap html comments
printExp (PosEAdd _ exp1 exp2) indent irMap html comments = printExp (EAdd exp1 exp2) indent irMap html comments
printExp (ESub exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " - " ++ printExp exp2 indent irMap html comments
printExp (PosESub _ exp1 exp2) indent irMap html comments = printExp (ESub exp1 exp2) indent irMap html comments
printExp (EMul exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " * " ++ printExp exp2 indent irMap html comments
printExp (PosEMul _ exp1 exp2) indent irMap html comments = printExp (EMul exp1 exp2) indent irMap html comments
printExp (EDiv exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " / " ++ printExp exp2 indent irMap html comments
printExp (PosEDiv _ exp1 exp2) indent irMap html comments = printExp (EDiv exp1 exp2) indent irMap html comments
printExp (ESumSetExp exp) indent irMap html comments = "sum " ++ printExp exp indent irMap html comments
printExp (PosESumSetExp _ exp) indent irMap html comments = printExp (ESumSetExp exp) indent irMap html comments
printExp (ECSetExp exp)         indent irMap html comments = "# " ++ printExp exp indent irMap html comments
printExp (PosECSetExp _ exp) indent irMap html comments = printExp (ECSetExp exp) indent irMap html comments
printExp (EMinExp exp)          indent irMap html comments = "-" ++ printExp exp indent irMap html comments
printExp (PosEMinExp _ exp) indent irMap html comments = printExp (EMinExp exp) indent irMap html comments
printExp (EImpliesElse exp1 exp2 exp3) indent irMap html comments = "if " ++ (printExp exp1 indent irMap html comments) ++ " then " ++ (printExp exp2 indent irMap html comments) ++ " else " ++ (printExp exp3 indent irMap html comments)
printExp (PosEImpliesElse _ exp1 exp2 exp3) indent irMap html comments = printExp (EImpliesElse exp1 exp2 exp3) indent irMap html comments
printExp (EInt (PosInteger (_, num))) indent irMap html comments = num
printExp (PosEInt _ posInteger) indent irMap html comments = printExp (EInt posInteger) indent irMap html comments
printExp (EDouble (PosDouble (_, num))) indent irMap html comments = num
printExp (PosEDouble _ posDouble) indent irMap html comments = printExp (EDouble posDouble) indent irMap html comments
printExp (EStr (PosString (_, str))) indent irMap html comments = str
printExp (PosEStr _ posString) indent irMap html comments = printExp (EStr posString) indent irMap html comments

printSetExp (ClaferId name) indent irMap html comments = printName name indent irMap html comments
printSetExp (PosClaferId _ name) indent irMap html comments = printSetExp (ClaferId name) indent irMap html comments
printSetExp (Union set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "++" ++ (printSetExp set2 indent irMap html comments)
printSetExp (PosUnion _ set1 set2) indent irMap html comments = printSetExp (Union set1 set2) indent irMap html comments
printSetExp (UnionCom set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ ", " ++ (printSetExp set2 indent irMap html comments)
printSetExp (PosUnionCom _ set1 set2) indent irMap html comments = printSetExp (UnionCom set1 set2) indent irMap html comments
printSetExp (Difference set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "--" ++ (printSetExp set2 indent irMap html comments)
printSetExp (PosDifference _ set1 set2) indent irMap html comments = printSetExp (Difference set1 set2) indent irMap html comments
printSetExp (Intersection set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "&" ++ (printSetExp set2 indent irMap html comments)
printSetExp (PosIntersection _ set1 set2) indent irMap html comments = printSetExp (Intersection set1 set2) indent irMap html comments
printSetExp (Domain set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "<:" ++ (printSetExp set2 indent irMap html comments)
printSetExp (PosDomain _ set1 set2) indent irMap html comments = printSetExp (Domain set1 set2) indent irMap html comments
printSetExp (Range set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ ":>" ++ (printSetExp set2 indent irMap html comments)
printSetExp (PosRange _ set1 set2) indent irMap html comments = printSetExp (Range set1 set2) indent irMap html comments
printSetExp (Join set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "." ++ (printSetExp set2 indent irMap html comments)
printSetExp (PosJoin _ set1 set2) indent irMap html comments = printSetExp (Join set1 set2) indent irMap html comments

printQuant quant indent irMap html comments = case quant of
  QuantNo        -> while html (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  PosQuantNo _   -> while html (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  QuantLone      -> while html (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  PosQuantLone _ -> while html (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  QuantOne       -> while html (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  PosQuantOne _  -> while html (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  QuantSome      -> while html (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "
  PosQuantSome _ -> while html (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "

printEnumId (EnumIdIdent posident) indent irMap html comments = printPosIdent posident indent irMap html comments
printEnumId (PosEnumIdIdent _ posident) indent irMap html comments = printEnumId (EnumIdIdent posident) indent irMap html comments

printIndent :: Int -> Bool -> String
printIndent indent html = if indent == 0 || html == False then "" else "<span class=\"l" ++ show indent ++ "\">"

dropUid :: String -> String
dropUid uid = let id = rest $ dropWhile (/= '_') uid 
              in if id == "" 
                then uid 
                else id

--so it fails more gracefully on empty lists
first [] = []
first (x:_) = x
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

getDivId span irMap = if Map.lookup span irMap == Nothing
                      then "Uid not Found"
                      else let IRClafer iClafer = head $ fromJust $ Map.lookup span irMap in
                        uid iClafer

{-getSuperId span irMap = if Map.lookup span irMap == Nothing
                        then "Uid not Found"
                        else let IRPExp pexp = head $ fromJust $ Map.lookup span irMap in
                          sident $ exp pexp-}

getUseId :: Span -> Map.Map Span [Ir] -> (String, String)
getUseId span irMap = if Map.lookup span irMap == Nothing
                      then ("Uid not Found", "Uid not Found")
                      else let IRClafer iClafer = head $ fromJust $ Map.lookup span irMap in
                        (uid iClafer, sident $ exp $ head $ supers $ super iClafer)

while bool exp = if bool then exp else []

cleanOutput "" = ""
cleanOutput (' ':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput ('\n':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput (' ':'<':'b':'r':'>':xs) = "<br>"++cleanOutput xs
cleanOutput (x:xs) = x : cleanOutput xs

trim = let f = reverse . dropWhile isSpace in f . f

highlightErrors :: String -> [ClaferErr] -> String
highlightErrors model errors = "<pre>\n" ++ unlines (replace "<!-- # FRAGMENT /-->" "</pre>\n<!-- # FRAGMENT /-->\n<pre>" --assumes the fragments have been concatenated
													  (highlightErrors' (replace "//# FRAGMENT" "<!-- # FRAGMENT /-->" (lines model)) errors)) ++ "</pre>"
	where
		replace x y []     = []
		replace x y (z:zs) = (if x == z then y else z):replace x y zs
		
		highlightErrors' :: [String] -> [ClaferErr] -> [String]
		highlightErrors' model [] = model
		highlightErrors' model ((ClaferErr msg):es) = highlightErrors' model es
		highlightErrors' model ((ParseErr ErrPos{modelPos = Pos l c, fragId = n} msg):es) = do
		  let (ls, lss) = genericSplitAt (l + toInteger n) model
		  let newLine = fst (genericSplitAt (c - 1) $ last ls) ++ "<span class=\"error\" title=\"Parsing failed at line " ++ show l ++ " column " ++ show c ++
						   "...\n" ++ msg ++ "\">" ++ (if snd (genericSplitAt (c - 1) $ last ls) == "" then "&nbsp;" else snd (genericSplitAt (c - 1) $ last ls)) ++ "</span>"
		  highlightErrors' (init ls ++ [newLine] ++ lss) es
		highlightErrors' model ((SemanticErr ErrPos{modelPos = Pos l c, fragId = n} msg):es) = do
		  let (ls, lss) = genericSplitAt (l + toInteger n) model
		  let newLine = fst (genericSplitAt (c - 1) $ last ls) ++ "<span class=\"error\" title=\"Compiling failed at line " ++ show l ++ " column " ++ show c ++
						   "...\n" ++ msg ++ "\">" ++ (if snd (genericSplitAt (c - 1) $ last ls) == "" then "&nbsp;" else snd (genericSplitAt (c - 1) $ last ls)) ++ "</span>"
		  highlightErrors' (init ls ++ [newLine] ++ lss) es