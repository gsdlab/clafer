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
-- | Generates HTML and plain text rendering of a Clafer model.
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
printStandaloneComment :: String -> String
printStandaloneComment comment = "<div class=\"standalonecomment\">" ++ comment ++ "</div>"
printInlineComment :: String -> String
printInlineComment comment = "<span class=\"inlinecomment\">" ++ comment ++ "</span>"

-- | Generate the model as HTML document
genHtml :: Module -> IModule -> String
genHtml x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) True
-- | Generate the model as plain text 
-- | This is used by the graph generator for tooltips
genText :: Module -> IModule -> String
genText x ir = cleanOutput $ revertLayout $ printModule x (traceIrModule ir) False
genTooltip :: Module -> Map.Map Span [Ir] -> String
genTooltip m ir = unlines $ filter (\x -> trim x /= []) $ lines $ cleanOutput $ revertLayout $ printModule m ir False

printModule :: Module -> Map.Map Span [Ir] -> Bool -> String
printModule (Module _ [])     _ _ = ""
printModule (Module s (x:xs)) irMap html = (printDeclaration x 0 irMap html []) ++ printModule (Module s xs) irMap html

printDeclaration :: Declaration -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printDeclaration (EnumDecl s posIdent enumIds)  indent irMap html comments = 
    preComments ++
    printIndentId 0 html ++
    (while html "<span class=\"keyword\">") ++ "enum" ++ (while html "</span>") ++ 
    " " ++ 
    (printPosIdent posIdent (Just uid') html) ++ 
    " = " ++ 
    (concat $ intersperse " | " (map (\x -> printEnumId x indent irMap html comments) enumIds)) ++
    comment ++
    printIndentEnd html
  where
    uid' = getUid posIdent irMap;
    (comments', preComments) = printPreComment s comments;
    (_, comment) = printComment s comments'
printDeclaration (ElementDecl _ element) indent irMap html comments = printElement element indent irMap html comments

printElement :: Element -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printElement (Subclafer _ clafer) indent irMap html comments = printClafer clafer indent irMap html comments

printElement (ClaferUse s name crd es) indent irMap html comments = 
  preComments ++ 
  printIndentId indent html ++
  "`" ++ (while html ("<a href=\"#" ++ superId ++ "\"><span class=\"reference\">")) ++ 
  printName name indent irMap False [] --trick the printer into only printing the name
  ++ (while html "</span></a>") ++ 
  printCard crd ++ 
  comment ++ 
  printIndentEnd html ++ 
  printElements es indent irMap html comments''
  where
    (_, superId) = getUseId s irMap;
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments' 

printElement (Subgoal s goal) indent irMap html comments = 
  preComments ++ 
  printIndent 0 html ++
  printGoal goal indent irMap html comments'' ++
  comment ++ 
  printIndentEnd html
  where
   (comments', preComments) = printPreComment s comments; 
   (comments'', comment) = printComment s comments' 

printElement (Subconstraint s constraint) indent irMap html comments =
    preComments ++
    printIndent indent html ++ 
    printConstraint constraint indent irMap html comments'' ++
    comment ++
    printIndentEnd html  
  where
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments' 

printElement (Subsoftconstraint s constraint) indent irMap html comments =
    preComments ++ 
    printIndent indent html ++ 
    printSoftConstraint constraint indent irMap html comments'' ++
    comment ++
    printIndentEnd html  
  where
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments' 

printElements :: Elements -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printElements (ElementsEmpty _) _ _ _ _ = ""
printElements (ElementsList _ es) indent irMap html comments = "\n{" ++ mapElements es indent irMap html comments ++ "\n}"
    where mapElements []     _ _ _ _ = []
          mapElements (e':es') indent' irMap' html' comments' = if span' e' == noSpan
                                                          then (printElement e' (indent' + 1) irMap' html' comments' {-++ "\n"-}) ++ mapElements es' indent' irMap' html' comments'
                                                          else (printElement e' (indent' + 1) irMap' html' comments' {-++ "\n"-}) ++ mapElements es' indent' irMap' html' (afterSpan (span' e') comments')
          afterSpan s comments' = let (Span _ (Pos line _)) = s in dropWhile (\(x, _) -> let (Span _ (Pos line' _)) = x in line' <= line) comments'
          span' (Subclafer s _) = s
          span' (Subconstraint s _) = s
          span' (ClaferUse s _ _ _) = s
          span' (Subgoal s _) = s
          span' (Subsoftconstraint s _) = s

printClafer :: Clafer -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printClafer (Clafer s abstract gCard id' super' crd init' es) indent irMap html comments =
  preComments ++ 
  printIndentId indent html ++ 
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
      printPosIdent id' (Just uid') html, 
      printSuper super' indent irMap html comments, 
      printCard crd, 
      printInit init' indent irMap html comments]

printGoal :: Goal -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String               
printGoal (Goal _ exps') indent irMap html comments = 
  (if html then "&lt;&lt;" else "<<") ++ 
  concatMap (\x -> printExp x indent irMap html comments) exps' ++ 
  if html then "&gt;&gt;" else ">>" 

printAbstract :: Abstract -> Bool -> String
printAbstract (Abstract _) html   = (while html "<span class=\"keyword\">") ++ "abstract" ++ (while html "</span>") ++ " "
printAbstract (AbstractEmpty _) _ = ""

printGCard :: GCard -> Bool -> String
printGCard gCard html = case gCard of
  (GCardInterval _ ncard) -> printNCard ncard
  (GCardEmpty _)          -> ""
  (GCardXor _)            -> (while html "<span class=\"keyword\">") ++ "xor" ++ (while html "</span>") ++ " "
  (GCardOr _)             -> (while html "<span class=\"keyword\">") ++ "or"  ++ (while html "</span>") ++ " "
  (GCardMux _)            -> (while html "<span class=\"keyword\">") ++ "mux" ++ (while html "</span>") ++ " "
  (GCardOpt _)            -> (while html "<span class=\"keyword\">") ++ "opt" ++ (while html "</span>") ++ " "

printNCard :: NCard -> String
printNCard (NCard _ (PosInteger (_, num)) exInteger) = num ++ ".." ++ printExInteger exInteger ++ " "
  
printExInteger :: ExInteger -> String    
printExInteger (ExIntegerAst _) = "*"
printExInteger (ExIntegerNum _ (PosInteger(_, num))) = num

printName :: Name -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printName (Path _ modids) indent irMap html comments = unwords $ map (\x -> printModId x indent irMap html comments) modids

printModId :: ModId -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printModId (ModIdIdent _ posident) _ irMap html _ = printPosIdentRef posident irMap html

printPosIdent :: PosIdent -> Maybe String -> Bool -> String
printPosIdent (PosIdent (_, id')) Nothing _ = id'
printPosIdent (PosIdent (_, id')) (Just uid') html = (while html $ "<span class=\"claferDecl\" id=\"" ++ uid' ++ "\">") ++ id' ++ (while html "</span>")

printPosIdentRef :: PosIdent -> Map.Map Span [Ir] -> Bool -> String
printPosIdentRef (PosIdent (p, id')) irMap html
  = (while html ("<a href=\"#" ++ uid' ++ "\"><span class=\"reference\">")) ++ id' ++ (while html "</span></a>")
      where uid' = getUid (PosIdent (p, id')) irMap

printSuper :: Super -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSuper (SuperEmpty _) _ _ _ _ = ""
printSuper (SuperSome _ superHow setExp) indent irMap html comments = printSuperHow superHow indent irMap html comments ++ printSetExp setExp indent irMap html comments

printSuperHow :: SuperHow -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSuperHow (SuperColon _)  _ _ html _ = (while html "<span class=\"keyword\">") ++ " :" ++ (while html "</span>") ++ " "
printSuperHow (SuperArrow _) _ _ html _ = (while html "<span class=\"keyword\">") ++ " ->" ++ (while html "</span>") ++ " "
printSuperHow (SuperMArrow _) _ _ html _ = (while html "<span class=\"keyword\">") ++ " ->>" ++ (while html "</span>") ++ " "

printCard :: Card -> String
printCard (CardEmpty _) = ""
printCard (CardLone _)  = " ?"
printCard (CardSome _)  = " +"
printCard (CardAny _)   = " *"
printCard (CardNum _ (PosInteger (_,num))) = " " ++ num 
printCard (CardInterval _ nCard) = " " ++ printNCard nCard

printConstraint ::  Constraint -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printConstraint (Constraint _ exps') indent irMap html comments = (concatMap (\x -> printConstraint' x indent irMap html comments) exps')

printConstraint' :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printConstraint' exp' indent irMap html comments = 
    while html "<span class=\"keyword\">" ++ "[" ++ while html "</span>" ++
    " " ++ 
    printExp exp' indent irMap html comments ++ 
    " " ++ 
    while html "<span class=\"keyword\">" ++ "]" ++ while html "</span>"

printSoftConstraint :: SoftConstraint -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSoftConstraint (SoftConstraint _ exps') indent irMap html comments = concatMap (\x -> printSoftConstraint' x indent irMap html comments) exps'
printSoftConstraint' :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSoftConstraint' exp' indent' irMap html comments = 
    while html "<span class=\"keyword\">" ++ "(" ++ while html "</span>" ++ 
    " " ++
    printExp exp' indent' irMap html comments ++ 
    " " ++ 
    while html "<span class=\"keyword\">" ++ ")" ++ while html "</span>"

printDecl :: Decl-> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printDecl (Decl _ locids setExp) indent irMap html comments = 
  (concat $ intersperse "; " $ map printLocId locids) ++
  (while html "<span class=\"keyword\">") ++ " : " ++ (while html "</span>") ++ printSetExp setExp indent irMap html comments
  where
    printLocId :: LocId -> String
    printLocId (LocIdIdent _ (PosIdent (_, ident'))) = ident'

printInit :: Init -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printInit (InitEmpty _) _ _ _ _ = ""
printInit (InitSome _ initHow exp') indent irMap html comments = printInitHow initHow  ++ printExp exp' indent irMap html comments

printInitHow :: InitHow -> String
printInitHow (InitHow_1 _) = " = "
printInitHow (InitHow_2 _) = " := "

printExp :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printExp (DeclAllDisj _ decl exp') indent irMap html comments = "all disj " ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp' indent irMap html comments)
printExp (DeclAll _     decl exp') indent irMap html comments = "all " ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp' indent irMap html comments)
printExp (DeclQuantDisj _ quant' decl exp') indent irMap html comments = (printQuant quant' html) ++ "disj" ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp' indent irMap html comments)
printExp (DeclQuant _     quant' decl exp') indent irMap html comments = (printQuant quant' html) ++ (printDecl decl indent irMap html comments) ++ " | " ++ (printExp exp' indent irMap html comments)
printExp (EGMax _ exp')            indent irMap html comments = "max " ++ printExp exp' indent irMap html comments
printExp (EGMin _ exp')            indent irMap html comments = "min " ++ printExp exp' indent irMap html comments
printExp (ENeq _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " != " ++ (printExp exp'2 indent irMap html comments)
printExp (ESetExp _ setExp)       indent irMap html comments = printSetExp setExp indent irMap html comments
printExp (QuantExp _ quant' exp')   indent irMap html comments = printQuant quant' html ++ printExp exp' indent irMap html comments
printExp (EImplies _ exp'1 exp'2)   indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " => " ++ printExp exp'2 indent irMap html comments
printExp (EAnd _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " && " ++ printExp exp'2 indent irMap html comments
printExp (EOr _ exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " || " ++ printExp exp'2 indent irMap html comments
printExp (EXor _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " xor " ++ printExp exp'2 indent irMap html comments
printExp (ENeg _ exp')             indent irMap html comments = " ! " ++ printExp exp' indent irMap html comments
printExp (ELt _ exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ (if html then " &lt; " else " < ") ++ printExp exp'2 indent irMap html comments
printExp (EGt _ exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " > " ++ printExp exp'2 indent irMap html comments
printExp (EEq _ exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " = " ++ printExp exp'2 indent irMap html comments
printExp (ELte _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ (if html then " &lt;= " else " <= ") ++ printExp exp'2 indent irMap html comments
printExp (EGte _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " >= " ++ printExp exp'2 indent irMap html comments
printExp (EIn _ exp'1 exp'2)        indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " in " ++ printExp exp'2 indent irMap html comments
printExp (ENin _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " not in " ++ printExp exp'2 indent irMap html comments
printExp (EIff _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ (if html then " &lt;=&gt; " else " <=> ") ++ printExp exp'2 indent irMap html comments
printExp (EAdd _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " + " ++ printExp exp'2 indent irMap html comments
printExp (ESub _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " - " ++ printExp exp'2 indent irMap html comments
printExp (EMul _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " * " ++ printExp exp'2 indent irMap html comments
printExp (EDiv _ exp'1 exp'2)       indent irMap html comments = (printExp exp'1 indent irMap html comments) ++ " / " ++ printExp exp'2 indent irMap html comments
printExp (ESumSetExp _ exp') indent irMap html comments = "sum " ++ printExp exp' indent irMap html comments
printExp (ECSetExp _ exp')         indent irMap html comments = "# " ++ printExp exp' indent irMap html comments
printExp (EMinExp _ exp')          indent irMap html comments = "-" ++ printExp exp' indent irMap html comments
printExp (EImpliesElse _ exp'1 exp'2 exp'3) indent irMap html comments = "if " ++ (printExp exp'1 indent irMap html comments) ++ " then " ++ (printExp exp'2 indent irMap html comments) ++ " else " ++ (printExp exp'3 indent irMap html comments)
printExp (EInt _ (PosInteger (_, num))) _ _ _ _ = num
printExp (EDouble _ (PosDouble (_, num))) _ _ _ _ = num
printExp (EStr _ (PosString (_, str))) _ _ _ _ = str

printSetExp :: SetExp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSetExp (ClaferId _ name) indent irMap html comments = printName name indent irMap html comments
printSetExp (Union _ set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "++" ++ (printSetExp set2 indent irMap html comments)
printSetExp (UnionCom _ set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ ", " ++ (printSetExp set2 indent irMap html comments)
printSetExp (Difference _ set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "--" ++ (printSetExp set2 indent irMap html comments)
printSetExp (Intersection _ set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "&" ++ (printSetExp set2 indent irMap html comments)
printSetExp (Domain _ set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "<:" ++ (printSetExp set2 indent irMap html comments)
printSetExp (Range _ set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ ":>" ++ (printSetExp set2 indent irMap html comments)
printSetExp (Join _ set1 set2) indent irMap html comments = (printSetExp set1 indent irMap html comments) ++ "." ++ (printSetExp set2 indent irMap html comments)

printQuant :: Quant -> Bool -> String
printQuant quant' html = case quant' of
  (QuantNo _)       -> (while html "<span class=\"keyword\">") ++ "no" ++ (while html "</span>") ++ " "
  (QuantNot _)       -> (while html "<span class=\"keyword\">") ++ "not" ++ (while html "</span>") ++ " "
  (QuantLone _)     -> (while html "<span class=\"keyword\">") ++ "lone" ++ (while html "</span>") ++ " "
  (QuantOne _)      -> (while html "<span class=\"keyword\">") ++ "one" ++ (while html "</span>") ++ " "
  (QuantSome _)     -> (while html "<span class=\"keyword\">") ++ "some" ++ (while html "</span>") ++ " "

printEnumId :: EnumId -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printEnumId (EnumIdIdent _ posident) _ irMap html _ = printPosIdent posident (Just uid') html
  where
    uid' = getUid posident irMap

printIndent :: Int -> Bool -> String
printIndent 0 html = (while html "<div>") ++ "\n"
printIndent _ html = (while html "<div class=\"indent\">") ++ "\n"

printIndentId :: Int -> Bool -> String
printIndentId 0 html = while html ("<div>") ++ "\n"
printIndentId _ html = while html ("<div class=\"indent\">") ++ "\n"

printIndentEnd :: Bool -> String
printIndentEnd html = (while html "</div>") ++ "\n"

dropUid :: String -> String
dropUid uid' = let id' = rest $ dropWhile (/= '_') uid' 
              in if id' == "" 
                then uid' 
                else id'

--so it fails more gracefully on empty lists
{-first :: String -> String
first [] = []
first (x:_) = x-}
rest :: String -> String
rest [] = []
rest (_:xs) = xs

getUid :: PosIdent -> Map.Map Span [Ir] -> String
getUid posIdent@(PosIdent (_, id')) irMap = 
    if Map.lookup (getSpan posIdent) irMap == Nothing
    then "Lookup failed"
    else let wrappedResult = head $ fromJust $ Map.lookup (getSpan posIdent) irMap in
      findUid id' $ unwrap wrappedResult
      where {unwrap (IRPExp pexp')       = getIdentPExp pexp';
             unwrap (IRClafer iClafer') = [ _uid iClafer' ];
             getIdentPExp (PExp _ _ _ exp') = getIdentIExp exp';
             getIdentIExp (IFunExp _ exps') = concatMap getIdentPExp exps';
             getIdentIExp (IClaferId _ id'' _) = [id''];
             getIdentIExp (IDeclPExp _ _ pexp) = getIdentPExp pexp;
             getIdentIExp _ = [];
             findUid name (x:xs) = if name == dropUid x then x else findUid name xs;
             findUid _ []     = "Uid not found"}

getDivId :: Span -> Map.Map Span [Ir] -> String
getDivId s irMap = if Map.lookup s irMap == Nothing
                      then "Uid not Found"
                      else let IRClafer iClaf = head $ fromJust $ Map.lookup s irMap in
                        _uid iClaf

{-getSuperId span irMap = if Map.lookup span irMap == Nothing
                        then "Uid not Found"
                        else let IRPExp pexp = head $ fromJust $ Map.lookup span irMap in
                          sident $ exp pexp-}

getUseId :: Span -> Map.Map Span [Ir] -> (String, String)
getUseId s irMap = if Map.lookup s irMap == Nothing
                      then ("Uid not Found", "Uid not Found")
                      else let IRClafer iClaf = head $ fromJust $ Map.lookup s irMap in
                        (_uid iClaf, _sident $ _exp $ head $ _supers $ _super iClaf)

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