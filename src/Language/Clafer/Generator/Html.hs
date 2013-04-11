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
        '/':'/':_:[]   -> if col' == 1
                          then (cs, printStandaloneComment comment ++ "\n") 
                          else (cs, printInlineComment comment ++ "\n")
        '/':'*':_:[]   -> (cs, printStandaloneComment comment ++ "\n")
        otherwise      -> (cs, "Improper form of comment.")-- Should not happen. Bug.
  | otherwise = (c:cs, "")
  where trim = let f = reverse. dropWhile isSpace in f . f
printComment _ cs = (cs,"")
printStandaloneComment comment = "<div class=\"standalonecomment\">" ++ comment ++ "</div>"
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
printDeclaration (EnumDecl posIdent enumIds) indent irMap html comments = 
  let (PosIdent (_, divid)) = posIdent in
    printIndentId 0 html divid ++
    (while html "<span class=\"keyword\">") ++ "enum" ++ (while html "</span>") ++ 
    " " ++ 
    (printPosIdent posIdent indent irMap html comments) ++ 
    " = " ++ 
    (concat $ intersperse " | " (map (\x -> printEnumId x indent irMap html comments) enumIds)) ++
    printIndentEnd html
printDeclaration (PosEnumDecl span posIdent enumIds)  indent irMap html comments = 
    preComments ++
    printIndentId 0 html uid ++
    (while html "<span class=\"keyword\">") ++ "enum" ++ (while html "</span>") ++ 
    " " ++ 
    (printPosIdent posIdent indent irMap html comments) ++ 
    " = " ++ 
    (concat $ intersperse " | " (map (\x -> printEnumId x indent irMap html comments) enumIds)) ++
    comment ++
    printIndentEnd html
  where
    uid = getDivId span irMap;
    (comments', preComments) = printPreComment span comments;
    (_, comment) = printComment span comments'
printDeclaration (ElementDecl element)      indent irMap html comments = printElement element indent irMap html comments
printDeclaration (PosElementDecl _ element) indent irMap html comments = printDeclaration (ElementDecl element) indent irMap html comments

printElement (Subclafer clafer) indent irMap html comments = printClafer clafer indent irMap html comments
printElement (PosSubclafer span subclafer) indent irMap html comments = printElement (Subclafer subclafer) indent irMap html comments

printElement (ClaferUse name card elements) indent irMap html comments = 
  printIndent indent html ++ 
  "`" ++ printName name indent irMap html comments ++ 
  printCard card ++ 
  printIndentEnd html ++
  printElements elements indent irMap html comments
printElement (PosClaferUse span name card elements) indent irMap html comments = 
  preComments ++ 
  printIndentId indent html divId ++
  "`" ++ (while html ("<a href=\"#" ++ superId ++ "\"><span class=\"reference\">")) ++ 
  printName name indent irMap False [] --trick the printer into only printing the name
  ++ (while html "</span></a>") ++ 
  printCard card ++ 
  comment ++ 
  printIndentEnd html ++ 
  printElements elements indent irMap html comments''
  where
    (divId, superId) = getUseId span irMap;
    (comments', preComments) = printPreComment span comments;
    (comments'', comment) = printComment span comments' 

printElement (Subgoal goal) indent irMap html comments = printGoal goal indent irMap html comments
printElement (PosSubgoal span goal) indent irMap html comments = 
  preComments ++ 
  printIndent 0 html ++
  printElement (Subgoal goal) indent irMap html comments'' ++ 
  comment ++ 
  printIndentEnd html
  where
   (comments', preComments) = printPreComment span comments; 
   (comments'', comment) = printComment span comments' 

printElement (Subconstraint constraint) indent irMap html comments =
    printIndent indent html ++
    printConstraint constraint indent irMap html comments ++
    printIndentEnd html

printElement (PosSubconstraint span constraint) indent irMap html comments =
    preComments ++
    printIndent indent html ++ 
    printConstraint constraint indent irMap html comments'' ++
    comment ++
    printIndentEnd html  
  where
    (comments', preComments) = printPreComment span comments;
    (comments'', comment) = printComment span comments' 

printElement (Subsoftconstraint constraint) indent irMap html comments =
    printIndent indent html ++
    printSoftConstraint constraint indent irMap html comments ++
    printIndentEnd html

printElement (PosSubsoftconstraint span constraint) indent irMap html comments =
    preComments ++ 
    printIndent indent html ++ 
    printSoftConstraint constraint indent irMap html comments'' ++
    comment ++
    printIndentEnd html  
  where
    (comments', preComments) = printPreComment span comments;
    (comments'', comment) = printComment span comments' 

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

printClafer (Clafer abstract gCard id super card init elements) indent irMap html comments =
  printIndentId indent html divid ++ 
  claferDeclaration ++ 
  printElements elements indent irMap html comments ++
  printIndentEnd html
  where
    (PosIdent (_, divid)) = id;
    claferDeclaration = concat [
      printAbstract abstract html, 
      printGCard gCard html,
      printPosIdent id indent irMap html comments, 
      printSuper super indent irMap html comments, 
      printCard card, 
      printInit init indent irMap html comments]

printClafer (PosClafer span abstract gCard id super card init elements) indent irMap html comments =
  preComments ++ 
  printIndentId indent html uid ++ 
  claferDeclaration ++ 
  comment ++ 
  printElements elements indent irMap html comments'' ++
  printIndentEnd html
  where
    uid = getDivId span irMap;
    (comments', preComments) = printPreComment span comments;
    (comments'', comment) = printComment span comments'
    claferDeclaration = concat [
      printAbstract abstract html, 
      printGCard gCard html,
      printPosIdent id indent irMap html comments, 
      printSuper super indent irMap html comments, 
      printCard card, 
      printInit init indent irMap html comments]
                    
printGoal (Goal exps) indent irMap html comments = 
  (if html then "&lt;&lt;" else "<<") ++ 
  concatMap (\x -> printExp x indent irMap html comments) exps ++ 
  if html then "&gt;&gt;" else ">>" 
printGoal (PosGoal span exps) indent irMap html comments = printGoal (Goal exps) indent irMap html comments

printAbstract Abstract html = (while html "<span class=\"keyword\">") ++ "abstract" ++ (while html "</span>") ++ " "
printAbstract (PosAbstract _) html = printAbstract Abstract html
printAbstract AbstractEmpty        _ = ""
printAbstract (PosAbstractEmpty _) _ = ""

printGCard gCard html = case gCard of
  (GCardInterval ncard) -> printNCard ncard
  (PosGCardInterval _ ncard) -> printNCard ncard
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

printNCard (NCard (PosInteger (pos, num)) exInteger) = num ++ ".." ++ printExInteger exInteger ++ " "
printNCard (PosNCard _ posinteger exinteger) = printNCard (NCard posinteger exinteger)
      
printExInteger ExIntegerAst = "*"
printExInteger (PosExIntegerAst _) = printExInteger ExIntegerAst
printExInteger (ExIntegerNum (PosInteger(pos, num))) = num
printExInteger (PosExIntegerNum _ posInteger) = printExInteger (ExIntegerNum posInteger)

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

printCard CardEmpty = ""
printCard (PosCardEmpty _) = printCard CardEmpty
printCard CardLone = " ?"
printCard (PosCardLone _) = printCard CardLone
printCard CardSome = " +"
printCard (PosCardSome _) = printCard CardSome
printCard CardAny = " *"
printCard (PosCardAny _) = printCard CardAny
printCard (CardNum (PosInteger (pos,num))) = " " ++ num 
printCard (PosCardNum _ posInteger) = printCard (CardNum posInteger)
printCard (CardInterval nCard) = " " ++ printNCard nCard
printCard (PosCardInterval _ nCard) = printCard (CardInterval nCard)

printConstraint (Constraint exps) indent irMap html comments = (concatMap (\x -> printConstraint' x indent irMap html comments) exps)
printConstraint (PosConstraint span exps) indent irMap html comments = printConstraint (Constraint exps) indent irMap html comments
printConstraint' exp indent irMap html comments = 
    while html "<span class=\"keyword\">" ++ "[" ++ while html "</span>" ++
    " " ++ 
    printExp exp indent irMap html comments ++ 
    " " ++ 
    while html "<span class=\"keyword\">" ++ "]" ++ while html "</span>"

printSoftConstraint (SoftConstraint exps) indent irMap html comments = concatMap (\x -> printSoftConstraint' x indent irMap html comments) exps
printSoftConstraint (PosSoftConstraint _ exps) indent irMap html comments = printSoftConstraint (SoftConstraint exps) indent irMap html comments
printSoftConstraint' exp indent irMap html comments = 
    while html "<span class=\"keyword\">" ++ "(" ++ while html "</span>" ++ 
    " " ++
    printExp exp indent irMap html comments ++ 
    " " ++ 
    while html "<span class=\"keyword\">" ++ ")" ++ while html "</span>"

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
printInit (InitSome initHow exp) indent irMap html comments = printInitHow initHow  ++ printExp exp indent irMap html comments
printInit (PosInitSome _ initHow exp) indent irMap html comments = printInit (InitSome initHow exp) indent irMap html comments

printInitHow InitHow_1  = " = "
printInitHow (PosInitHow_1 _)  = printInitHow InitHow_1
printInitHow InitHow_2  = " := "
printInitHow (PosInitHow_2 _)  = printInitHow InitHow_2

printExp (DeclAllDisj decl exp) indent irMap html comments = "all disj " ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp indent irMap html comments)
printExp (PosDeclAllDisj _ decl exp) indent irMap html comments = printExp (DeclAllDisj decl exp) indent irMap html comments
printExp (DeclAll     decl exp) indent irMap html comments = "all " ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp indent irMap html comments)
printExp (PosDeclAll _ decl exp) indent irMap html comments = printExp (DeclAll decl exp) indent irMap html comments
printExp (DeclQuantDisj quant decl exp) indent irMap html comments = (printQuant quant html) ++ "disj" ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp indent irMap html comments)
printExp (PosDeclQuantDisj _ quant decl exp) indent irMap html comments = printExp (DeclQuantDisj quant decl exp) indent irMap html comments
printExp (DeclQuant     quant decl exp) indent irMap html comments = (printQuant quant html) ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp indent irMap html comments)
printExp (PosDeclQuant _ quant decl exp) indent irMap html comments = printExp (DeclQuant quant decl exp) indent irMap html comments
printExp (EGMax exp)            indent irMap html comments = "max " ++ printExp exp indent irMap html comments
printExp (PosEGMax _ exp)     indent irMap html comments = printExp (EGMax exp) indent irMap html comments
printExp (EGMin exp)            indent irMap html comments = "min " ++ printExp exp indent irMap html comments
printExp (PosEGMin _ exp) indent irMap html comments = printExp (EGMin exp) indent irMap html comments
printExp (ENeq exp1 exp2)       indent irMap html comments = (printExp exp1 indent irMap html comments) ++ " != " ++ (printExp exp2 indent irMap html comments)
printExp (PosENeq _ exp1 exp2) indent irMap html comments = printExp (ENeq exp1 exp2) indent irMap html comments
printExp (ESetExp setExp)       indent irMap html comments = printSetExp setExp indent irMap html comments
printExp (PosESetExp _ setExp) indent irMap html comments = printExp (ESetExp setExp) indent irMap html comments
printExp (QuantExp quant exp)   indent irMap html comments = printQuant quant html ++ printExp exp indent irMap html comments
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

printQuant quant html = case quant of
  QuantNo        -> (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  PosQuantNo _   -> (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  QuantLone      -> (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  PosQuantLone _ -> (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  QuantOne       -> (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  PosQuantOne _  -> (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  QuantSome      -> (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "
  PosQuantSome _ -> (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "

printEnumId (EnumIdIdent posident) indent irMap html comments = printPosIdent posident indent irMap html comments
printEnumId (PosEnumIdIdent _ posident) indent irMap html comments = printEnumId (EnumIdIdent posident) indent irMap html comments

printIndent :: Int -> Bool -> String
printIndent 0 html = (while html "<div>")
printIndent _ html = (while html "<div class=\"indent\">")

printIndentId :: Int -> Bool -> String -> String
printIndentId 0 html uid = (while html "<div id=\"" ++ uid ++ "\">")
printIndentId _ html uid = (while html "<div id=\"" ++ uid ++ "\" class=\"indent\">")

printIndentEnd :: Bool -> String
printIndentEnd html = (while html "</div>") ++ "\n"

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