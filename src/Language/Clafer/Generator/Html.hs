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
printPreComment (Span (Pos r _) _) (c@((Span (Pos r' _) _), _):cs)
  | r > r' = findAll r ((c:cs), [])
  | otherwise  = (c:cs, "")
    where findAll _ ([],comments) = ([],comments)
          findAll row ((c'@((Span (Pos row' col') _), comment):cs'), comments)
            | row > row' = case take 3 comment of
                '/':'/':'#':[] -> findAll row (cs', concat [comments, "<!-- " ++ trim (drop 2 comment) ++ " /-->\n"])
                '/':'/':_:[]   -> if col' == 1
                                  then findAll row (cs', concat [comments, printStandaloneComment comment ++ "\n"])
                                  else findAll row (cs', concat [comments, printInlineComment comment ++ "\n"])
                '/':'*':_:[]   -> findAll row (cs', concat [comments, printStandaloneComment comment ++ "\n"])
                _      -> (cs', "Improper form of comment.")-- Should not happen. Bug.
            | otherwise  = ((c':cs'), comments)
          findAll row ((_:cs'), comments) = findAll row (cs', comments)
printPreComment _ cs = (cs,"")
printComment :: Span -> [(Span, String)] -> ([(Span, String)], String)
printComment _ [] = ([],[])
printComment (Span (Pos row _) _) (c@(Span (Pos row' col') _, comment):cs)
  | row == row' = case take 3 comment of
        '/':'/':'#':[] -> (cs,"<!-- " ++ trim' (drop 2 comment) ++ " /-->\n")
        '/':'/':_:[]   -> if col' == 1
                          then (cs, printStandaloneComment comment ++ "\n") 
                          else (cs, printInlineComment comment ++ "\n")
        '/':'*':_:[]   -> (cs, printStandaloneComment comment ++ "\n")
        _      -> (cs, "Improper form of comment.")-- Should not happen. Bug.
  | otherwise = (c:cs, "")
  where trim' = let f = reverse. dropWhile isSpace in f . f
printComment _ cs = (cs,"")
printStandaloneComment :: String -> String
printStandaloneComment comment = "<div class=\"standalonecomment\">" ++ comment ++ "</div>"
printInlineComment :: String -> String
printInlineComment comment = "<span class=\"inlinecomment\">" ++ comment ++ "</span>"

genHtml :: Module -> IModule -> String
genHtml x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) True
genText :: Module -> IModule -> String
genText x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) False
genTooltip :: Module -> Map.Map Span [Ir] -> String
genTooltip m ir = unlines $ filter (\x -> trim x /= []) $ lines $ cleanOutput $ revertLayout $ printModule m ir False

printModule :: Module -> Map.Map Span [Ir] -> Bool -> String
printModule (Module [])     _ _ = ""
printModule (Module (x:xs)) irMap html = (printDeclaration x 0 irMap html []) ++ printModule (Module xs) irMap html
printModule (PosModule _ declarations) irMap html = printModule (Module declarations) irMap html

printDeclaration :: Declaration -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printDeclaration (EnumDecl posIdent enumIds) indent irMap html comments = 
  let (PosIdent (_, divid)) = posIdent in
    printIndentId 0 html divid ++
    (while html "<span class=\"keyword\">") ++ "enum" ++ (while html "</span>") ++ 
    " " ++ 
    (printPosIdent posIdent) ++ 
    " = " ++ 
    (concat $ intersperse " | " (map (\x -> printEnumId x indent irMap html comments) enumIds)) ++
    printIndentEnd html
printDeclaration (PosEnumDecl s posIdent enumIds)  indent irMap html comments = 
    preComments ++
    printIndentId 0 html uid' ++
    (while html "<sspan class=\"keyword\">") ++ "enum" ++ (while html "</span>") ++ 
    " " ++ 
    (printPosIdent posIdent) ++ 
    " = " ++ 
    (concat $ intersperse " | " (map (\x -> printEnumId x indent irMap html comments) enumIds)) ++
    comment ++
    printIndentEnd html
  where
    uid' = getDivId s irMap;
    (comments', preComments) = printPreComment s comments;
    (_, comment) = printComment s comments'
printDeclaration (ElementDecl element)      indent irMap html comments = printElement element indent irMap html comments
printDeclaration (PosElementDecl _ element) indent irMap html comments = printDeclaration (ElementDecl element) indent irMap html comments

printElement :: Element -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printElement (Subclafer clafer) indent irMap html comments = printClafer clafer indent irMap html comments
printElement (PosSubclafer _ subclafer) indent irMap html comments = printElement (Subclafer subclafer) indent irMap html comments

printElement (ClaferUse name crd es) indent irMap html comments = 
  printIndent indent html ++ 
  "`" ++ printName name indent irMap html comments ++ 
  printCard crd ++ 
  printIndentEnd html ++
  printElements es indent irMap html comments
printElement (PosClaferUse s name crd es) indent irMap html comments = 
  preComments ++ 
  printIndentId indent html divId ++
  "`" ++ (while html ("<a href=\"#" ++ superId ++ "\"><span class=\"reference\">")) ++ 
  printName name indent irMap False [] --trick the printer into only printing the name
  ++ (while html "</span></a>") ++ 
  printCard crd ++ 
  comment ++ 
  printIndentEnd html ++ 
  printElements es indent irMap html comments''
  where
    (divId, superId) = getUseId s irMap;
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments' 

printElement (Subgoal goal) indent irMap html comments = printGoal goal indent irMap html comments
printElement (PosSubgoal s goal) indent irMap html comments = 
  preComments ++ 
  printIndent 0 html ++
  printElement (Subgoal goal) indent irMap html comments'' ++ 
  comment ++ 
  printIndentEnd html
  where
   (comments', preComments) = printPreComment s comments; 
   (comments'', comment) = printComment s comments' 

printElement (Subconstraint constraint) indent irMap html comments =
    printIndent indent html ++
    printConstraint constraint indent irMap html comments ++
    printIndentEnd html

printElement (PosSubconstraint s constraint) indent irMap html comments =
    preComments ++
    printIndent indent html ++ 
    printConstraint constraint indent irMap html comments'' ++
    comment ++
    printIndentEnd html  
  where
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments' 

printElement (Subsoftconstraint constraint) indent irMap html comments =
    printIndent indent html ++
    printSoftConstraint constraint indent irMap html comments ++
    printIndentEnd html

printElement (PosSubsoftconstraint s constraint) indent irMap html comments =
    preComments ++ 
    printIndent indent html ++ 
    printSoftConstraint constraint indent irMap html comments'' ++
    comment ++
    printIndentEnd html  
  where
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments' 

printElements :: Elements -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printElements ElementsEmpty _ _ _ _ = ""
printElements (PosElementsEmpty _) indent irMap html comments = printElements ElementsEmpty indent irMap html comments
printElements (ElementsList es) indent irMap html comments = "\n{" ++ mapElements es indent irMap html comments ++ "\n}"
    where mapElements []     _ _ _ _ = []
          mapElements (e':es') indent' irMap' html' comments' = if span' e' == noSpan
                                                          then (printElement e' (indent' + 1) irMap' html' comments' {-++ "\n"-}) ++ mapElements es' indent' irMap' html' comments'
                                                          else (printElement e' (indent' + 1) irMap' html' comments' {-++ "\n"-}) ++ mapElements es' indent' irMap' html' (afterSpan (span' e') comments')
          afterSpan s comments' = let (Span _ (Pos line _)) = s in dropWhile (\(x, _) -> let (Span _ (Pos line' _)) = x in line' <= line) comments'
          span' (PosSubclafer s _) = s
          span' (PosSubconstraint s _) = s
          span' (PosClaferUse s _ _ _) = s
          span' (PosSubgoal s _) = s
          span' (PosSubsoftconstraint s _) = s
          span' _ = noSpan
printElements (PosElementsList _ es) indent irMap html comments = printElements (ElementsList es) indent irMap html comments

printClafer :: Clafer -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printClafer (Clafer abstract gCard id' super' crd init' es) indent irMap html comments =
  printIndentId indent html divid ++ 
  claferDeclaration ++ 
  printElements es indent irMap html comments ++
  printIndentEnd html
  where
    (PosIdent (_, divid)) = id';
    claferDeclaration = concat [
      printAbstract abstract html, 
      printGCard gCard html,
      printPosIdent id', 
      printSuper super' indent irMap html comments, 
      printCard crd, 
      printInit init' indent irMap html comments]

printClafer (PosClafer s abstract gCard id' super' crd init' es) indent irMap html comments =
  preComments ++ 
  printIndentId indent html uid' ++ 
  claferDeclaration ++ 
  comment ++ 
  printElements es indent irMap html comments'' ++
  printIndentEnd html
  where
    uid' = getDivId s irMap;
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments'
    claferDeclaration = concat [
      printAbstract abstract html, 
      printGCard gCard html,
      printPosIdent id', 
      printSuper super' indent irMap html comments, 
      printCard crd, 
      printInit init' indent irMap html comments]

printGoal :: Goal -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String               
printGoal (Goal exps') indent irMap html comments = 
  (if html then "&lt;&lt;" else "<<") ++ 
  concatMap (\x -> printExp x indent irMap html comments) exps' ++ 
  if html then "&gt;&gt;" else ">>" 
printGoal (PosGoal _ exps') indent irMap html comments = printGoal (Goal exps') indent irMap html comments

printAbstract :: Abstract -> Bool -> String
printAbstract Abstract html = (while html "<span class=\"keyword\">") ++ "abstract" ++ (while html "</span>") ++ " "
printAbstract (PosAbstract _) html = printAbstract Abstract html
printAbstract AbstractEmpty        _ = ""
printAbstract (PosAbstractEmpty _) _ = ""

printGCard :: GCard -> Bool -> String
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

printNCard :: NCard -> String
printNCard (NCard (PosInteger (_, num)) exInteger) = num ++ ".." ++ printExInteger exInteger ++ " "
printNCard (PosNCard _ posinteger exinteger) = printNCard (NCard posinteger exinteger)
  
printExInteger :: ExInteger -> String    
printExInteger ExIntegerAst = "*"
printExInteger (PosExIntegerAst _) = printExInteger ExIntegerAst
printExInteger (ExIntegerNum (PosInteger(_, num))) = num
printExInteger (PosExIntegerNum _ posInteger) = printExInteger (ExIntegerNum posInteger)

printName :: Name -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printName (Path modids) indent irMap html comments = unwords $ map (\x -> printModId x indent irMap html comments) modids
printName (PosPath _ modids) indent irMap html comments = printName (Path modids) indent irMap html comments

printModId :: ModId -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printModId (ModIdIdent posident) _ irMap html _ = printPosIdentRef posident irMap html
printModId (PosModIdIdent _ posident) indent irMap html comments = printModId (ModIdIdent posident) indent irMap html comments

printPosIdent :: PosIdent -> String
printPosIdent (PosIdent (_, id')) = id'

printPosIdentRef :: PosIdent -> Map.Map Span [Ir] -> Bool -> String
printPosIdentRef (PosIdent (p, id')) irMap html
  = (while html ("<a href=\"#" ++ uid' ++ "\"><span class=\"reference\">")) ++ id' ++ (while html "</span></a>")
      where uid' = getUid (PosIdent (p, id')) irMap

printSuper :: Super -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSuper SuperEmpty _ _ _ _ = ""
printSuper (PosSuperEmpty _) indent irMap html comments = printSuper SuperEmpty indent irMap html comments
printSuper (SuperSome superHow setExp) indent irMap html comments = printSuperHow superHow indent irMap html comments ++ printSetExp setExp indent irMap html comments
printSuper (PosSuperSome _ superHow setExp) indent irMap html comments = printSuper (SuperSome superHow setExp) indent irMap html comments

printSuperHow :: SuperHow -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSuperHow SuperColon  _ _ html _ = (while html "<span class=\"keyword\">") ++ " :" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperColon _) indent irMap html comments = printSuperHow SuperColon indent irMap html comments
printSuperHow SuperArrow  _ _ html _ = (while html "<span class=\"keyword\">") ++ " ->" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperArrow _) indent irMap html comments = printSuperHow SuperArrow indent irMap html comments
printSuperHow SuperMArrow _ _ html _ = (while html "<span class=\"keyword\">") ++ " ->>" ++ (while html "</span>") ++ " "
printSuperHow (PosSuperMArrow _) indent irMap html comments = printSuperHow SuperMArrow indent irMap html comments

printCard :: Card -> String
printCard CardEmpty = ""
printCard (PosCardEmpty _) = printCard CardEmpty
printCard CardLone = " ?"
printCard (PosCardLone _) = printCard CardLone
printCard CardSome = " +"
printCard (PosCardSome _) = printCard CardSome
printCard CardAny = " *"
printCard (PosCardAny _) = printCard CardAny
printCard (CardNum (PosInteger (_,num))) = " " ++ num 
printCard (PosCardNum _ posInteger) = printCard (CardNum posInteger)
printCard (CardInterval nCard) = " " ++ printNCard nCard
printCard (PosCardInterval _ nCard) = printCard (CardInterval nCard)

printConstraint ::  Constraint -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printConstraint (Constraint exps') indent irMap html comments = (concatMap (\x -> printConstraint' x indent irMap html comments) exps')
printConstraint (PosConstraint _ exps') indent irMap html comments = printConstraint (Constraint exps') indent irMap html comments
printConstraint' :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printConstraint' exp' indent irMap html comments = 
    while html "<span class=\"keyword\">" ++ "[" ++ while html "</span>" ++
    " " ++ 
    printExp exp' indent irMap html comments ++ 
    " " ++ 
    while html "<span class=\"keyword\">" ++ "]" ++ while html "</span>"

printSoftConstraint :: SoftConstraint -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSoftConstraint (SoftConstraint exps') indent irMap html comments = concatMap (\x -> printSoftConstraint' x indent irMap html comments) exps'
printSoftConstraint (PosSoftConstraint _ exps') indent irMap html comments = printSoftConstraint (SoftConstraint exps') indent irMap html comments
printSoftConstraint' :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSoftConstraint' exp' indent' irMap html comments = 
    while html "<span class=\"keyword\">" ++ "(" ++ while html "</span>" ++ 
    " " ++
    printExp exp' indent' irMap html comments ++ 
    " " ++ 
    while html "<span class=\"keyword\">" ++ ")" ++ while html "</span>"

printDecl :: Decl-> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printDecl (Decl locids setExp) indent irMap html comments = 
  (concat $ intersperse "; " $ map printLocId locids) ++
  (while html "<span class=\"keyword\">") ++ " : " ++ (while html "</span>") ++ printSetExp setExp indent irMap html comments
  where
    printLocId :: LocId -> String
    printLocId (LocIdIdent (PosIdent (_, ident'))) = ident'
    printLocId (PosLocIdIdent _ (PosIdent (_, ident'))) = ident'
printDecl (PosDecl _ locids setExp) indent irMap html comments = printDecl (Decl locids setExp) indent irMap html comments

printInit :: Init -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printInit InitEmpty _ _ _ _ = ""
printInit (PosInitEmpty _) indent irMap html comments = printInit InitEmpty indent irMap html comments
printInit (InitSome initHow exp') indent irMap html comments = printInitHow initHow  ++ printExp exp' indent irMap html comments
printInit (PosInitSome _ initHow exp') indent irMap html comments = printInit (InitSome initHow exp') indent irMap html comments

printInitHow :: InitHow -> String
printInitHow InitHow_1  = " = "
printInitHow (PosInitHow_1 _)  = printInitHow InitHow_1
printInitHow InitHow_2  = " := "
printInitHow (PosInitHow_2 _)  = printInitHow InitHow_2

printExp :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printExp (DeclAllDisj decl exp') indent irMap html comments = "all disj " ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp' indent irMap html comments)
printExp (PosDeclAllDisj _ decl exp') indent irMap html comments = printExp (DeclAllDisj decl exp') indent irMap html comments
printExp (DeclAll     decl exp') indent irMap html comments = "all " ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp' indent irMap html comments)
printExp (PosDeclAll _ decl exp') indent irMap html comments = printExp (DeclAll decl exp') indent irMap html comments
printExp (DeclQuantDisj quant' decl exp') indent irMap html comments = (printQuant quant' html) ++ "disj" ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp' indent irMap html comments)
printExp (PosDeclQuantDisj _ quant' decl exp') indent irMap html comments = printExp (DeclQuantDisj quant' decl exp') indent irMap html comments
printExp (DeclQuant     quant' decl exp') indent irMap html comments = (printQuant quant' html) ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp' indent irMap html comments)
printExp (PosDeclQuant _ quant' decl exp') indent irMap html comments = printExp (DeclQuant quant' decl exp') indent irMap html comments
printExp (EGMax exp')            indent irMap html comments = "max " ++ printExp exp' indent irMap html comments
printExp (PosEGMax _ exp')     indent irMap html comments = printExp (EGMax exp') indent irMap html comments
printExp (EGMin exp')            indent irMap html comments = "min " ++ printExp exp' indent irMap html comments
printExp (PosEGMin _ exp') indent irMap html comments = printExp (EGMin exp') indent irMap html comments
printExp (ENeq exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " != " ++ (printExp exp'2 indent irMap html comments)
printExp (PosENeq _ exp'1 exp'2) indent irMap html comments = printExp (ENeq exp'1 exp'2) indent irMap html comments
printExp (ESetExp setExp)       indent irMap html comments = printSetExp setExp indent irMap html comments
printExp (PosESetExp _ setExp) indent irMap html comments = printExp (ESetExp setExp) indent irMap html comments
printExp (QuantExp quant' exp')   indent irMap html comments = printQuant quant' html ++ printExp exp' indent irMap html comments
printExp (PosQuantExp _ quant' exp') indent irMap html comments = printExp (QuantExp quant' exp') indent irMap html comments
printExp (EImplies exp'1 exp'2)   indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " => " ++ printExp exp'2 indent irMap html comments
printExp (PosEImplies _ exp'1 exp'2) indent irMap html comments = printExp (EImplies exp'1 exp'2) indent irMap html comments
printExp (EAnd exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " && " ++ printExp exp'2 indent irMap html comments
printExp (PosEAnd _ exp'1 exp'2) indent irMap html comments = printExp (EAnd exp'1 exp'2) indent irMap html comments
printExp (EOr exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " || " ++ printExp exp'2 indent irMap html comments
printExp (PosEOr _ exp'1 exp'2) indent irMap html comments = printExp (EOr exp'1 exp'2) indent irMap html comments
printExp (EXor exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " xor " ++ printExp exp'2 indent irMap html comments
printExp (PosEXor _ exp'1 exp'2) indent irMap html comments = printExp (EXor exp'1 exp'2) indent irMap html comments
printExp (ENeg exp')             indent irMap html comments = " ! " ++ printExp exp' indent irMap html comments
printExp (PosENeg _ exp') indent irMap html comments = printExp (ENeg exp') indent irMap html comments
printExp (ELt exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ (if html then " &lt; " else " < ") ++ printExp exp'2 indent irMap html comments
printExp (PosELt _ exp'1 exp'2) indent irMap html comments = printExp (ELt exp'1 exp'2) indent irMap html comments
printExp (EGt exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " > " ++ printExp exp'2 indent irMap html comments
printExp (PosEGt _ exp'1 exp'2) indent irMap html comments = printExp (EGt exp'1 exp'2) indent irMap html comments
printExp (EEq exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " = " ++ printExp exp'2 indent irMap html comments
printExp (PosEEq _ exp'1 exp'2) indent irMap html comments = printExp (EEq exp'1 exp'2) indent irMap html comments
printExp (ELte exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ (if html then " &lt;= " else " <= ") ++ printExp exp'2 indent irMap html comments
printExp (PosELte _ exp'1 exp'2) indent irMap html comments = printExp (ELte exp'1 exp'2) indent irMap html comments
printExp (EGte exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " >= " ++ printExp exp'2 indent irMap html comments
printExp (PosEGte _ exp'1 exp'2) indent irMap html comments = printExp (EGte exp'1 exp'2) indent irMap html comments
printExp (EIn exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " in " ++ printExp exp'2 indent irMap html comments
printExp (PosEIn _ exp'1 exp'2) indent irMap html comments = printExp (EIn exp'1 exp'2) indent irMap html comments
printExp (ENin exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " not in " ++ printExp exp'2 indent irMap html comments
printExp (PosENin _ exp'1 exp'2) indent irMap html comments = printExp (ENin exp'1 exp'2) indent irMap html comments
printExp (EIff exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ (if html then " &lt;=&gt; " else " <=> ") ++ printExp exp'2 indent irMap html comments
printExp (PosEIff _ exp'1 exp'2) indent irMap html comments = printExp (EIff exp'1 exp'2) indent irMap html comments
printExp (EAdd exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " + " ++ printExp exp'2 indent irMap html comments
printExp (PosEAdd _ exp'1 exp'2) indent irMap html comments = printExp (EAdd exp'1 exp'2) indent irMap html comments
printExp (ESub exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " - " ++ printExp exp'2 indent irMap html comments
printExp (PosESub _ exp'1 exp'2) indent irMap html comments = printExp (ESub exp'1 exp'2) indent irMap html comments
printExp (EMul exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " * " ++ printExp exp'2 indent irMap html comments
printExp (PosEMul _ exp'1 exp'2) indent irMap html comments = printExp (EMul exp'1 exp'2) indent irMap html comments
printExp (EDiv exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " / " ++ printExp exp'2 indent irMap html comments
printExp (PosEDiv _ exp'1 exp'2) indent irMap html comments = printExp (EDiv exp'1 exp'2) indent irMap html comments
printExp (ESumSetExp exp') indent irMap html comments = "sum " ++ printExp exp' indent irMap html comments
printExp (PosESumSetExp _ exp') indent irMap html comments = printExp (ESumSetExp exp') indent irMap html comments
printExp (ECSetExp exp')         indent irMap html comments = "# " ++ printExp exp' indent irMap html comments
printExp (PosECSetExp _ exp') indent irMap html comments = printExp (ECSetExp exp') indent irMap html comments
printExp (EMinExp exp')          indent irMap html comments = "-" ++ printExp exp' indent irMap html comments
printExp (PosEMinExp _ exp') indent irMap html comments = printExp (EMinExp exp') indent irMap html comments
printExp (EImpliesElse exp'1 exp'2 exp'3) indent irMap html comments = "if " ++ (printExp exp'1 indent irMap html comments) ++ " then " ++ (printExp exp'2 indent irMap html comments) ++ " else " ++ (printExp exp'3 indent irMap html comments)
printExp (PosEImpliesElse _ exp'1 exp'2 exp'3) indent irMap html comments = printExp (EImpliesElse exp'1 exp'2 exp'3) indent irMap html comments
printExp (EInt (PosInteger (_, num))) _ _ _ _ = num
printExp (PosEInt _ posInteger) indent irMap html comments = printExp (EInt posInteger) indent irMap html comments
printExp (EDouble (PosDouble (_, num))) _ _ _ _ = num
printExp (PosEDouble _ posDouble) indent irMap html comments = printExp (EDouble posDouble) indent irMap html comments
printExp (EStr (PosString (_, str))) _ _ _ _ = str
printExp (PosEStr _ posString) indent irMap html comments = printExp (EStr posString) indent irMap html comments

printSetExp :: SetExp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
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

printQuant :: Quant -> Bool -> String
printQuant quant' html = case quant' of
  QuantNo        -> (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  PosQuantNo _   -> (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  QuantLone      -> (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  PosQuantLone _ -> (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  QuantOne       -> (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  PosQuantOne _  -> (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  QuantSome      -> (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "
  PosQuantSome _ -> (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "

printEnumId :: EnumId -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printEnumId (EnumIdIdent posident) _ _ _ _ = printPosIdent posident
printEnumId (PosEnumIdIdent _ posident) indent irMap html comments = printEnumId (EnumIdIdent posident) indent irMap html comments

printIndent :: Int -> Bool -> String
printIndent 0 html = (while html "<div>") ++ "\n"
printIndent _ html = (while html "<div class=\"indent\">") ++ "\n"

printIndentId :: Int -> Bool -> String -> String
printIndentId 0 html uid' = while html ("<div id=\"" ++ uid' ++ "\">") ++ "\n"
printIndentId _ html uid' = while html ("<div id=\"" ++ uid' ++ "\" class=\"indent\">") ++ "\n"

printIndentEnd :: Bool -> String
printIndentEnd html = (while html "</div>") ++ "\n"

dropUid :: String -> String
dropUid uid' = let id' = rest $ dropWhile (/= '_') uid' 
              in if id' == "" 
                then uid' 
                else id'

--so it fails more gracefully on empty lists
{-first :: [Char] -> Char
first [] = []
first (x:_) = x-}
rest :: [Char] -> [Char]
rest [] = []
rest (_:xs) = xs

getUid :: PosIdent -> Map.Map Span [Ir] -> String
getUid (PosIdent (pos', id')) irMap = if Map.lookup (range (PosIdent (pos', id'))) irMap == Nothing
                        then "Lookup failed"
                        else let IRPExp pexp = head $ fromJust $ Map.lookup (range (PosIdent (pos', id'))) irMap in
                          findUid id' $ getIdentPExp pexp
                          where {getIdentPExp (PExp _ _ _ exp') = getIdentIExp exp';
                                 getIdentIExp (IFunExp _ exps') = concatMap getIdentPExp exps';
                                 getIdentIExp (IClaferId _ id'' _) = [id''];
                                 getIdentIExp (IDeclPExp _ _ pexp) = getIdentPExp pexp;
                                 getIdentIExp _ = [];
                                 findUid name (x:xs) = if name == dropUid x then x else findUid name xs;
                                 findUid _ []     = "Uid not found"}

getDivId :: Span -> Map.Map Span [Ir] -> [Char]
getDivId s irMap = if Map.lookup s irMap == Nothing
                      then "Uid not Found"
                      else let IRClafer iClafer = head $ fromJust $ Map.lookup s irMap in
                        uid iClafer

{-getSuperId span irMap = if Map.lookup span irMap == Nothing
                        then "Uid not Found"
                        else let IRPExp pexp = head $ fromJust $ Map.lookup span irMap in
                          sident $ exp pexp-}

getUseId :: Span -> Map.Map Span [Ir] -> (String, String)
getUseId s irMap = if Map.lookup s irMap == Nothing
                      then ("Uid not Found", "Uid not Found")
                      else let IRClafer iClafer = head $ fromJust $ Map.lookup s irMap in
                        (uid iClafer, sident $ exp $ head $ supers $ super iClafer)

while :: Bool -> String -> String
while bool exp' = if bool then exp' else ""

cleanOutput :: String -> String
cleanOutput "" = ""
cleanOutput (' ':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput ('\n':'\n':xs) = cleanOutput $ '\n':xs
cleanOutput (' ':'<':'b':'r':'>':xs) = "<br>"++cleanOutput xs
cleanOutput (x:xs) = x : cleanOutput xs

trim :: String -> String
trim = let f = reverse . dropWhile isSpace in f . f

highlightErrors :: String -> [ClaferErr] -> String
highlightErrors model errors = "<pre>\n" ++ unlines (replace "<!-- # FRAGMENT /-->" "</pre>\n<!-- # FRAGMENT /-->\n<pre>" --assumes the fragments have been concatenated
													  (highlightErrors' (replace "//# FRAGMENT" "<!-- # FRAGMENT /-->" (lines model)) errors)) ++ "</pre>"
	where
		replace _ _ []     = []
		replace x y (z:zs) = (if x == z then y else z):replace x y zs
		
highlightErrors' :: [String] -> [ClaferErr] -> [String]
highlightErrors' model' [] = model'
highlightErrors' model' ((ClaferErr _):es) = highlightErrors' model' es
highlightErrors' model' ((ParseErr ErrPos{modelPos = Pos l c, fragId = n} msg'):es) =
  let (ls, lss) = genericSplitAt (l + toInteger n) model'
      newLine = fst (genericSplitAt (c - 1) $ last ls) ++ "<span class=\"error\" title=\"Parsing failed at line " ++ show l ++ " column " ++ show c ++
				   "...\n" ++ msg' ++ "\">" ++ (if snd (genericSplitAt (c - 1) $ last ls) == "" then "&nbsp;" else snd (genericSplitAt (c - 1) $ last ls)) ++ "</span>"
  in highlightErrors' (init ls ++ [newLine] ++ lss) es
highlightErrors' model' ((SemanticErr ErrPos{modelPos = Pos l c, fragId = n} msg'):es) = 
  let (ls, lss) = genericSplitAt (l + toInteger n) model'
      newLine = fst (genericSplitAt (c - 1) $ last ls) ++ "<span class=\"error\" title=\"Compiling failed at line " ++ show l ++ " column " ++ show c ++
				   "...\n" ++ msg' ++ "\">" ++ (if snd (genericSplitAt (c - 1) $ last ls) == "" then "&nbsp;" else snd (genericSplitAt (c - 1) $ last ls)) ++ "</span>"
  in highlightErrors' (init ls ++ [newLine] ++ lss) es
highlightErrors' _ _ = error "Function highlightErrors' from Html Generator did not expect a Parse/Sematic Err, given one." -- Should never happen