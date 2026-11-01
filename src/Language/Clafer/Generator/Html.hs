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
module Language.Clafer.Generator.Html
  ( genHtml
  , genText
  , genTooltip
  , printModule
  , printDeclaration
  , printDecl
  , traceAstModule
  , traceIrModule
  , cleanOutput
  , revertLayout
  , printComment
  , printPreComment
  , printStandaloneComment
  , printInlineComment
  , highlightErrors
  , highlightErrorsIn
  , printFileHeader
  ) where

import Language.ClaferT
import Language.Clafer.Front.AbsClafer as AbsClafer
import Language.Clafer.Front.LayoutResolver(revertLayout)
import Language.Clafer.Intermediate.Tracing
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Import (ModelFile, modelPosition, fileStarts)

import Control.Applicative
import Data.List (intersperse,genericSplitAt)
import qualified Data.Map as Map
import Data.Maybe
import Data.Char (isSpace)
import Prelude hiding (exp)

printPreComment :: Span -> [(Span, String)] -> ([(Span, String)], String)
printPreComment _ [] = ([], [])
printPreComment (Span (Pos r _) _) (c@((Span (Pos r' _) _), _):cs)
  | r > r' = findAll r (c:cs, [])
  | otherwise  = (c:cs, "")
    where findAll _ ([],comments) = ([],comments)
          findAll row ((c'@((Span (Pos row' col') _), comment):cs'), comments)
            | row > row' = case take 3 comment of
                ['/', '/', '#'] -> findAll row (cs', concat [comments, printHtmlComment (trim (drop 2 comment)) ++ "\n"])
                ['/', '/', _]   -> if col' == 1
                                   then findAll row (cs', concat [comments, printStandaloneComment comment ++ "\n"])
                                   else findAll row (cs', concat [comments, printInlineComment comment ++ "\n"])
                ['/', '*', _]   -> findAll row (cs', concat [comments, printStandaloneComment comment ++ "\n"])
                _      -> (cs', "")
            | otherwise  = (c':cs', comments)
printComment :: Span -> [(Span, String)] -> ([(Span, String)], String)
printComment _ [] = ([],[])
printComment (Span (Pos row _) _) (c@(Span (Pos row' col') _, comment):cs)
  | row == row' = case take 3 comment of
        ['/', '/', '#'] -> (cs, printHtmlComment (trim' (drop 2 comment)) ++ "\n")
        ['/', '/', _]   -> if col' == 1
                           then (cs, printStandaloneComment comment ++ "\n")
                           else (cs, printInlineComment comment ++ "\n")
        ['/', '*', _]   -> (cs, printStandaloneComment comment ++ "\n")
        _      -> (cs, "")
  | otherwise = (c:cs, "")
  where trim' = let f = reverse. dropWhile isSpace in f . f
printStandaloneComment :: String -> String
printStandaloneComment comment = "<div class=\"standalonecomment\">" ++ replaceNLwithBR (escapeHtml comment) ++ "</div>"
  where
    replaceNLwithBR :: String   -> String
    replaceNLwithBR    ""        = ""
    replaceNLwithBR    ('\n':cs) = "<br>\n" ++ replaceNLwithBR cs
    replaceNLwithBR    (c:cs)    = c : replaceNLwithBR cs


printInlineComment :: String -> String
printInlineComment comment = "<span class=\"inlinecomment\">" ++ escapeHtml comment ++ "</span>"

-- | A //# comment as an HTML comment, e.g., <!-- # FRAGMENT /-->. Its text must not
-- contain "--", which could end the HTML comment early.
printHtmlComment :: String -> String
printHtmlComment text = "<!-- " ++ noDoubleDash text ++ " /-->"
  where
    noDoubleDash ('-':'-':cs) = "- " ++ noDoubleDash ('-':cs)
    noDoubleDash (c:cs)       = c : noDoubleDash cs
    noDoubleDash ""           = ""

-- | Escapes the text of a comment for HTML, so that it is shown as written.
escapeHtml :: String -> String
escapeHtml = concatMap escape
  where
    escape '&' = "&amp;"
    escape '<' = "&lt;"
    escape '>' = "&gt;"
    escape '"' = "&quot;"
    escape c   = [c]

printDeprecated :: String -> String -> Bool -> String
printDeprecated    s         m         html = while html ("<span class=\"deprecated\" title=\"" ++ "Deprecated. " ++ m ++ "\">")
                                              ++ s
                                              ++ while html "</span>"

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
printModule (Module s (x:xs)) irMap html = printDeclaration x 0 irMap html [] ++ printModule (Module s xs) irMap html

printDeclaration :: Declaration -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printDeclaration (EnumDecl s posIdent enumIds)  indent irMap html comments =
    preComments ++
    printIndentId 0 html ++
    while html "<span class=\"keyword\">" ++ "enum" ++ while html "</span>" ++
    " " ++
    printPosIdent posIdent mUid' html ++
    " = " ++
    concat (intersperse " | " (map (\x -> printEnumId x indent irMap html comments) enumIds)) ++
    comment ++
    printIndentEnd html
  where
    mUid' = getUid posIdent irMap;
    (comments', preComments) = printPreComment s comments;
    (_, comment) = printComment s comments'
printDeclaration (ElementDecl _ element) indent irMap html comments = printElement element indent irMap html comments

printElement :: Element -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printElement (Subclafer _ clafer) indent irMap html comments = printClafer clafer indent irMap html comments

printElement (ClaferUse s name crd es) indent irMap html comments =
  preComments ++
  printIndentId indent html ++
  "`" ++ while html ("<a href=\"#" ++ superId ++ "\"><span class=\"reference\">") ++
  printName name indent irMap False [] --trick the printer into only printing the name
  ++ while html "</span></a>" ++
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

printElement (SubAssertion s constraint) indent irMap html comments =
    preComments ++
    printIndent indent html ++
    printAssertion constraint indent irMap html comments'' ++
    comment ++
    printIndentEnd html
  where
    (comments', preComments) = printPreComment s comments;
    (comments'', comment) = printComment s comments'

printElements :: Elements -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printElements (ElementsEmpty _) _ _ _ _ = ""
printElements (ElementsList _ es) indent irMap html comments = "\n{" ++ mapElements es indent irMap html comments ++ "\n}"
    where mapElements []     _ _ _ _ = []
          mapElements (e':es') indent' irMap' html' comments'
            = if span' e' == noSpan
              then printElement e' (indent' + 1) irMap' html' comments' {-++ "\n"-} ++ mapElements es' indent' irMap' html' comments'
              else printElement e' (indent' + 1) irMap' html' comments' {-++ "\n"-} ++ mapElements es' indent' irMap' html' (afterSpan (span' e') comments')
          afterSpan s comments' = let (Span _ (Pos line _)) = s in dropWhile (\(x, _) -> let (Span _ (Pos line' _)) = x in line' <= line) comments'
          span' (Subclafer s _) = s
          span' (Subconstraint s _) = s
          span' (ClaferUse s _ _ _) = s
          span' (Subgoal s _) = s
          span' (SubAssertion s _) = s

printClafer :: Clafer -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printClafer (Clafer s abstract' tmod' gCard id' super' reference' crd init' trans' es) indent irMap html comments =
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
      printAbstract abstract' html,
      printModifiers tmod' html,
      printGCard gCard html,
      printPosIdent id' (Just uid') html,
      printSuper super' indent irMap html comments,
      printReference reference' indent irMap html comments,
      printCard crd,
      printInit init' indent irMap html comments,
      printTransition trans' indent irMap html comments]

printGoal :: Goal -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printGoal goal indent irMap html comments =
  (if html then "&lt;&lt;" else "<<") ++
  (case goal of
    (GoalMinimize _ exps') -> while html "<span class=\"keyword\">" ++ "minimize " ++ while html "</span>" ++ concatMap (\x -> printExp x indent irMap html comments) exps'
    (GoalMaximize _ exps') -> while html "<span class=\"keyword\">" ++ "maximize " ++ while html "</span>" ++ concatMap (\x -> printExp x indent irMap html comments) exps'
    (GoalMinDeprecated _ exps') -> printDeprecated "min " "Use `minimize` instead." html ++ concatMap (\x -> printExp x indent irMap html comments) exps'
    (GoalMaxDeprecated _ exps') -> printDeprecated "max " "Use `maximize` instead." html ++ concatMap (\x -> printExp x indent irMap html comments) exps'
  ) ++
  if html then "&gt;&gt;" else ">>"

printAbstract :: Abstract -> Bool -> String
printAbstract (Abstract _) html   = while html "<span class=\"keyword\">" ++ "abstract" ++ while html "</span>" ++ " "
printAbstract (AbstractEmpty _) _ = ""

printModifiers :: [TempModifier] -> Bool -> String
printModifiers tmods' html = concatMap printTempMod tmods'
  where
    printTempMod (AbsClafer.Final _)       = while html "<span class=\"tKeyword\">" ++ "final" ++ while html "</span>" ++ " "
    printTempMod (AbsClafer.FinalRef _)    = while html "<span class=\"tKeyword\">" ++ "finalref" ++ while html "</span>" ++ " "
    printTempMod (AbsClafer.FinalTarget _) = while html "<span class=\"tKeyword\">" ++ "finaltarget" ++ while html "</span>" ++ " "
    printTempMod (Initial _)               = while html "<span class=\"tKeyword\">" ++ "initial" ++ while html "</span>" ++ " "

printGCard :: GCard -> Bool -> String
printGCard gCard html = case gCard of
  (GCardInterval _ ncard) -> printNCard ncard
  (GCardEmpty _)          -> ""
  (GCardXor _)            -> while html "<span class=\"keyword\">" ++ "xor" ++ while html "</span>" ++ " "
  (GCardOr _)             -> while html "<span class=\"keyword\">" ++ "or"  ++ while html "</span>" ++ " "
  (GCardMux _)            -> while html "<span class=\"keyword\">" ++ "mux" ++ while html "</span>" ++ " "
  (GCardOpt _)            -> while html "<span class=\"keyword\">" ++ "opt" ++ while html "</span>" ++ " "

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
printPosIdent (PosIdent (_, id')) (Just uid') html = while html ("<span class=\"claferDecl\" id=\"" ++ uid' ++ "\">") ++ id' ++ while html "</span>"

printPosIdentRef :: PosIdent -> Map.Map Span [Ir] -> Bool -> String
printPosIdentRef (PosIdent (_, "dref")) _ html
  = while html "<span class=\"keyword\">" ++ "dref" ++ while html "</span>"
printPosIdentRef (PosIdent (_, "this")) _ html
  = while html "<span class=\"keyword\">" ++ "this" ++ while html "</span>"
printPosIdentRef (PosIdent (_, "parent")) _ html
  = while html "<span class=\"keyword\">" ++ "parent" ++ while html "</span>"
printPosIdentRef (PosIdent (_, "root")) _ html
  = while html "<span class=\"keyword\">" ++ "root" ++ while html "</span>"
printPosIdentRef (PosIdent (_, "ref")) _ html
  = printDeprecated "ref" "Use `dref` instead." html
printPosIdentRef (PosIdent (_, id')) _     False = id'
printPosIdentRef (PosIdent (p, id')) irMap True
  = case mUid' of
      Just uid' -> "<a href=\"#" ++ uid' ++ "\"><span class=\"reference\">" ++ id' ++ "</span></a>"
      Nothing   -> id'
  where
    mUid' = getUid (PosIdent (p, id')) irMap

printSuper :: Super -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printSuper (SuperEmpty _) _ _ _ _ = ""
printSuper (SuperSome _ setExp) indent irMap html comments = while html "<span class=\"keyword\">" ++ " : " ++ while html "</span>" ++ printOperand 26 setExp indent irMap html comments

printReference :: Reference -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printReference (ReferenceEmpty _) _ _ _ _ = ""
printReference (ReferenceSet _ setExp) indent irMap html comments = while html "<span class=\"keyword\">" ++ " -> " ++ while html "</span>" ++ printOperand 23 setExp indent irMap html comments
printReference (ReferenceBag _ setExp) indent irMap html comments = while html "<span class=\"keyword\">" ++ " ->> " ++ while html "</span>" ++ printOperand 23 setExp indent irMap html comments


printCard :: Card -> String
printCard (CardEmpty _) = ""
printCard (CardLone _)  = " ?"
printCard (CardSome _)  = " +"
printCard (CardAny _)   = " *"
printCard (CardNum _ (PosInteger (_,num))) = " " ++ num
printCard (CardInterval _ nCard) = " " ++ printNCard nCard

printConstraint ::  Constraint -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printConstraint (Constraint _ exps') indent irMap html comments = concatMap (\x -> printConstraint' x indent irMap html comments) exps'

printConstraint' :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printConstraint' exp' indent irMap html comments =
    while html "<span class=\"keyword\">" ++ "[" ++ while html "</span>" ++
    " " ++
    printExp exp' indent irMap html comments ++
    " " ++
    while html "<span class=\"keyword\">" ++ "]" ++ while html "</span>"

printAssertion :: Assertion -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printAssertion (Assertion _ exps') indent irMap html comments = concatMap (\x -> printAssertion' x indent irMap html comments) exps'
printAssertion' :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printAssertion' exp' indent' irMap html comments =
    while html "<span class=\"keyword\">" ++ "assert [" ++ while html "</span>" ++
    " " ++
    printExp exp' indent' irMap html comments ++
    " " ++
    while html "<span class=\"keyword\">" ++ "]" ++ while html "</span>"

printDecl :: Decl-> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printDecl (Decl _ locids setExp) indent irMap html comments =
  concat (intersperse "; " $ map printLocId locids) ++
  while html "<span class=\"keyword\">" ++ " : " ++ while html "</span>" ++ printOperand 21 setExp indent irMap html comments
  where
    printLocId :: LocId -> String
    printLocId (LocIdIdent _ (PosIdent (_, ident'))) = ident'

printVarBinding :: VarBinding-> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printVarBinding (VarBinding _ locid name) indent irMap html comments =
  printLocId locid ++
  while html "<span class=\"keyword\">" ++ " = " ++ while html "</span>" ++
  printName name indent irMap html comments
  where
    printLocId :: LocId -> String
    printLocId (LocIdIdent _ (PosIdent (_, ident'))) = ident'

printInit :: Init -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printInit (InitEmpty _) _ _ _ _ = ""
printInit (InitSome _ initHow exp') indent irMap html comments = printInitHow initHow  ++ printExp exp' indent irMap html comments

printInitHow :: InitHow -> String
printInitHow (InitConstant _) = " = "
printInitHow (InitDefault _) = " := "

printTransition :: Transition -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printTransition (TransitionEmpty _) _ _ _ _ = ""
printTransition (Transition _ (SyncTransArrow _) exp2) indent irMap html comments = (if html then "<span class=\"tKeyword\"> --&gt;&gt; </span>" else " -->> ") ++ printExp exp2 indent irMap html comments
printTransition (Transition _ (NextTransArrow _) exp2) indent irMap html comments = (if html then "<span class=\"tKeyword\"> --&gt; </span>" else " --> ") ++ printExp exp2 indent irMap html comments
printTransition (Transition _ (GuardedSyncTransArrow _ (TransGuard _ guardExp)) exp2) indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " -[" ++ while html "</span>" ++ printOperand 1 guardExp indent irMap html comments ++ (if html then "<span class=\"tKeyword\">]-&gt;&gt; </span>" else "]->> ")  ++ printExp exp2 indent irMap html comments
printTransition (Transition _ (GuardedNextTransArrow _ (TransGuard _ guardExp)) exp2) indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " -[" ++ while html "</span>" ++ printOperand 1 guardExp indent irMap html comments ++ (if html then "<span class=\"tKeyword\">]-&gt; </span>" else "]-> ") ++ printExp exp2 indent irMap html comments

printExp :: Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printExp (TransitionExp _ exp1 (SyncTransArrow _) exp2) indent irMap html comments = printOperand 1 exp1 indent irMap html comments ++ (if html then "<span class=\"tKeyword\"> --&gt;&gt; </span>" else " -->> ") ++ printOperand 0 exp2 indent irMap html comments
printExp (TransitionExp _ exp1 (NextTransArrow _) exp2) indent irMap html comments = printOperand 1 exp1 indent irMap html comments ++ (if html then "<span class=\"tKeyword\"> --&gt; </span>" else " --> ") ++ printOperand 0 exp2 indent irMap html comments
printExp (TransitionExp _ exp1 (GuardedSyncTransArrow _ (TransGuard _ guardExp)) exp2) indent irMap html comments = printOperand 1 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " -[" ++ while html "</span>" ++ printOperand 1 guardExp indent irMap html comments ++ (if html then "<span class=\"tKeyword\">]-&gt;&gt; </span>" else "]->> ")  ++ printOperand 0 exp2 indent irMap html comments
printExp (TransitionExp _ exp1 (GuardedNextTransArrow _ (TransGuard _ guardExp)) exp2) indent irMap html comments = printOperand 1 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " -[" ++ while html "</span>" ++ printOperand 1 guardExp indent irMap html comments ++ (if html then "<span class=\"tKeyword\">]-&gt; </span>" else "]-> ") ++ printOperand 0 exp2 indent irMap html comments
printExp (EDeclAllDisj _ decl exp') indent irMap html comments = "all disj " ++ printDecl decl indent irMap html comments ++ " | " ++ printOperand 1 exp' indent irMap html comments
printExp (EDeclAll _     decl exp') indent irMap html comments = "all " ++ printDecl decl indent irMap html comments ++ " | " ++ printOperand 1 exp' indent irMap html comments
printExp (EDeclQuantDisj _ quant' decl exp') indent irMap html comments = printQuant quant' html ++ "disj" ++ printDecl decl indent irMap html comments ++ " | " ++ printOperand 1 exp' indent irMap html comments
printExp (EDeclQuant _     quant' decl exp') indent irMap html comments = printQuant quant' html ++ printDecl decl indent irMap html comments ++ " | " ++ printOperand 1 exp' indent irMap html comments
printExp (LetExp _ varBinding exp') indent irMap html comments = while html "<span class=\"keyword\">" ++ "let " ++ while html "</span>" ++ printVarBinding varBinding indent irMap html comments ++ while html "<span class=\"keyword\">" ++ " in " ++ while html "</span>" ++ printOperand 1 exp' indent irMap html comments
printExp (TmpPatNever _ exp' patternScope)        indent irMap html comments = while html "<span class=\"tKeyword\">" ++ "never " ++ while html "</span>" ++ printOperand 3 exp' indent irMap html comments ++ printPatternScope patternScope indent irMap html comments
printExp (TmpPatSometime _ exp' patternScope)     indent irMap html comments = while html "<span class=\"tKeyword\">" ++ "sometime " ++ while html "</span>" ++ printOperand 3 exp' indent irMap html comments ++ printPatternScope patternScope indent irMap html comments
printExp (TmpPatLessOrOnce _ exp' patternScope)   indent irMap html comments = while html "<span class=\"tKeyword\">" ++ "lonce " ++ while html "</span>" ++ printOperand 3 exp' indent irMap html comments ++ printPatternScope patternScope indent irMap html comments
printExp (TmpPatAlways _ exp' patternScope)       indent irMap html comments = while html "<span class=\"tKeyword\">" ++ "always " ++ while html "</span>" ++ printOperand 3 exp' indent irMap html comments ++ printPatternScope patternScope indent irMap html comments
printExp (TmpPatPrecede _ exp1 exp2 patternScope) indent irMap html comments = printOperand 3 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " must precede " ++ while html "</span>" ++ printOperand 3 exp2 indent irMap html comments ++ printPatternScope patternScope indent irMap html comments
printExp (TmpPatFollow _ exp1 exp2 patternScope)  indent irMap html comments = printOperand 3 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " must follow " ++ while html "</span>" ++ printOperand 3 exp2 indent irMap html comments ++ printPatternScope patternScope indent irMap html comments
printExp (TmpInitially _ exp')    indent irMap html comments = while html "<span class=\"tKeyword\">" ++ "initially " ++ while html "</span>" ++ printOperand 3 exp' indent irMap html comments
printExp (TmpFinally _ exp')      indent irMap html comments = while html "<span class=\"tKeyword\">" ++ "finally " ++ while html "</span>" ++ printOperand 3 exp' indent irMap html comments
printExp (EGMax _ exp')           indent irMap html comments = "max " ++ printOperand 20 exp' indent irMap html comments
printExp (EGMin _ exp')           indent irMap html comments = "min " ++ printOperand 20 exp' indent irMap html comments
printExp (ENeq _ exp1 exp2)       indent irMap html comments = printOperand 15 exp1 indent irMap html comments ++ " != " ++ printOperand 16 exp2 indent irMap html comments
printExp (EQuantExp _ quant' exp') indent irMap html comments = printQuant quant' html ++ printOperand 20 exp' indent irMap html comments
printExp (EIff _ exp1 exp2)       indent irMap html comments = printOperand 3 exp1 indent irMap html comments ++ (if html then " &lt;=&gt; " else " <=> ") ++ printOperand 4 exp2 indent irMap html comments
printExp (EImplies _ exp1 exp2)   indent irMap html comments = printOperand 4 exp1 indent irMap html comments ++ (if html then " =&gt; " else " => ") ++ printOperand 5 exp2 indent irMap html comments
printExp (EAnd _ exp1 exp2)       indent irMap html comments = printOperand 7 exp1 indent irMap html comments ++ (if html then " &amp;&amp; " else " && ")  ++ printOperand 8 exp2 indent irMap html comments
printExp (EOr _ exp1 exp2)        indent irMap html comments = printOperand 5 exp1 indent irMap html comments ++ (if html then " &#124;&#124; " else " || ") ++ printOperand 6 exp2 indent irMap html comments
printExp (EXor _ exp1 exp2)       indent irMap html comments = printOperand 6 exp1 indent irMap html comments ++ " xor " ++ printOperand 7 exp2 indent irMap html comments
printExp (LtlU _ exp1 exp2)       indent irMap html comments = printOperand 8 exp1 indent irMap html comments ++ " U " ++ printOperand 9 exp2 indent irMap html comments
printExp (TmpUntil _ exp1 exp2)   indent irMap html comments = printOperand 8 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " until " ++ while html "</span>" ++ printOperand 9 exp2 indent irMap html comments
printExp (LtlW _ exp1 exp2)       indent irMap html comments = printOperand 9 exp1 indent irMap html comments ++ " W " ++ printOperand 10 exp2 indent irMap html comments
printExp (TmpWUntil _ exp1 exp2)  indent irMap html comments = printOperand 9 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " weakuntil " ++ while html "</span>" ++ printOperand 10 exp2 indent irMap html comments
printExp (LtlF _ exp')            indent irMap html comments = "F " ++ printOperand 10 exp' indent irMap html comments
printExp (TmpEventually _ exp')   indent irMap html comments = while html "<span class=\"tKeyword\">" ++ "eventually " ++ while html "</span>" ++ printOperand 10 exp' indent irMap html comments
printExp (LtlG _ exp')            indent irMap html comments = "G " ++ printOperand 10 exp' indent irMap html comments
printExp (TmpGlobally _ exp')     indent irMap html comments = while html "<span class=\"tKeyword\">" ++ "globally " ++ while html "</span>" ++ printOperand 10 exp' indent irMap html comments
printExp (LtlX _ exp')            indent irMap html comments = "X " ++ printOperand 10 exp' indent irMap html comments
printExp (TmpNext _ exp')         indent irMap html comments = while html "<span class=\"tKeyword\">" ++ "next " ++ while html "</span>" ++ printOperand 10 exp' indent irMap html comments
printExp (ENeg _ exp')            indent irMap html comments = " ! " ++ printOperand 11 exp' indent irMap html comments
printExp (ELt _ exp1 exp2)        indent irMap html comments = printOperand 15 exp1 indent irMap html comments ++ (if html then " &lt; " else " < ") ++ printOperand 16 exp2 indent irMap html comments
printExp (EGt _ exp1 exp2)        indent irMap html comments = printOperand 15 exp1 indent irMap html comments ++ (if html then " &gt; " else " > ") ++ printOperand 16 exp2 indent irMap html comments
printExp (EEq _ exp1 exp2)        indent irMap html comments = printOperand 15 exp1 indent irMap html comments ++ " = " ++ printOperand 16 exp2 indent irMap html comments
printExp (ELte _ exp1 exp2)       indent irMap html comments = printOperand 15 exp1 indent irMap html comments ++ (if html then " &lt;= " else " <= ") ++ printOperand 16 exp2 indent irMap html comments
printExp (EGte _ exp1 exp2)       indent irMap html comments = printOperand 15 exp1 indent irMap html comments ++ (if html then " &gt;= " else " >= ") ++ printOperand 16 exp2 indent irMap html comments
printExp (EIn _ exp1 exp2)        indent irMap html comments = printOperand 15 exp1 indent irMap html comments ++ " in " ++ printOperand 16 exp2 indent irMap html comments
printExp (ENin _ exp1 exp2)       indent irMap html comments = printOperand 15 exp1 indent irMap html comments ++ " not in " ++ printOperand 16 exp2 indent irMap html comments
printExp (EAdd _ exp1 exp2)       indent irMap html comments = printOperand 17 exp1 indent irMap html comments ++ " + " ++ printOperand 18 exp2 indent irMap html comments
printExp (ESub _ exp1 exp2)       indent irMap html comments = printOperand 17 exp1 indent irMap html comments ++ " - " ++ printOperand 18 exp2 indent irMap html comments
printExp (EMul _ exp1 exp2)       indent irMap html comments = printOperand 18 exp1 indent irMap html comments ++ " * " ++ printOperand 19 exp2 indent irMap html comments
printExp (EDiv _ exp1 exp2)       indent irMap html comments = printOperand 18 exp1 indent irMap html comments ++ (if html then " &#47; " else " / ") ++ printOperand 19 exp2 indent irMap html comments
printExp (ERem _ exp1 exp2)       indent irMap html comments = printOperand 18 exp1 indent irMap html comments ++ (if html then " &#37; " else " % ") ++ printOperand 19 exp2 indent irMap html comments
printExp (ESum _ exp')            indent irMap html comments = while html "<span class=\"keyword\">" ++ "sum " ++ while html "</span>" ++ printOperand 21 exp' indent irMap html comments
printExp (EProd _ exp')           indent irMap html comments = while html "<span class=\"keyword\">" ++ "product " ++ while html "</span>" ++ printOperand 21 exp' indent irMap html comments
printExp (ECard _ exp')           indent irMap html comments = "# " ++ printOperand 21 exp' indent irMap html comments
printExp (EMinExp _ exp')         indent irMap html comments = "-" ++ printOperand 21 exp' indent irMap html comments
printExp (EImpliesElse _ exp1 exp2 exp'3) indent irMap html comments
    = while html "<span class=\"keyword\">" ++ "if " ++ while html "</span>"
    ++ printOperand 1 exp1 indent irMap html comments
    ++ while html "<span class=\"keyword\">" ++ " then " ++ while html "</span>"
    ++ printOperand 1 exp2 indent irMap html comments
    ++ while html "<span class=\"keyword\">" ++ " else " ++ while html "</span>"
    ++ printOperand 1 exp'3 indent irMap html comments
printExp (ClaferId _ name)           indent irMap html comments = printName name indent irMap html comments
printExp (EUnion _ set1 set2)        indent irMap html comments = printOperand 23 set1 indent irMap html comments ++ "++" ++ printOperand 24 set2 indent irMap html comments
printExp (EUnionCom _ set1 set2)     indent irMap html comments = printOperand 23 set1 indent irMap html comments ++ ", " ++ printOperand 24 set2 indent irMap html comments
printExp (EDifference _ set1 set2)   indent irMap html comments = printOperand 24 set1 indent irMap html comments ++ "--" ++ printOperand 25 set2 indent irMap html comments
printExp (EIntersection _ set1 set2) indent irMap html comments = printOperand 25 set1 indent irMap html comments ++ "**" ++ printOperand 26 set2 indent irMap html comments
printExp (EIntersectionDeprecated _ set1 set2) indent irMap html comments = printOperand 26 set1 indent irMap html comments ++ printDeprecated "&amp;" "Use `**` instead." html ++ printOperand 27 set2 indent irMap html comments
printExp (EDomain _ set1 set2) indent irMap html comments = printOperand 21 set1 indent irMap html comments ++ "<:" ++ printOperand 22 set2 indent irMap html comments
printExp (ERange _ set1 set2)  indent irMap html comments = printOperand 22 set1 indent irMap html comments ++ ":>" ++ printOperand 23 set2 indent irMap html comments
printExp (EJoin _ set1 set2)   indent irMap html comments = printOperand 26 set1 indent irMap html comments ++ "." ++ printOperand 27 set2 indent irMap html comments
printExp (EInt _ (PosInteger (_, num))) _ _ _ _ = num
printExp (EDouble _ (PosDouble (_, num))) _ _ _ _ = num
printExp (EReal _ (PosReal (_, num))) _ _ _ _ = num
printExp (EStr _ (PosString (_, str))) _ _ _ _ = str

-- | Prints an operand at the precedence level that the grammar (src/clafer.cf) requires
--   there, in parentheses when its operator binds less tightly, e.g., X (a || b)
printOperand :: Int -> Exp -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printOperand level exp' indent irMap html comments
  | expPrec exp' < level = "(" ++ printExp exp' indent irMap html comments ++ ")"
  | otherwise            = printExp exp' indent irMap html comments

-- | The precedence level of an expression in the grammar, as in Front/PrintClafer.hs
expPrec :: Exp -> Int
expPrec exp' = case exp' of
  TransitionExp{}           -> 0
  EDeclAllDisj{}            -> 1
  EDeclAll{}                -> 1
  EDeclQuantDisj{}          -> 1
  EDeclQuant{}              -> 1
  EImpliesElse{}            -> 1
  LetExp{}                  -> 1
  TmpPatNever{}             -> 2
  TmpPatSometime{}          -> 2
  TmpPatLessOrOnce{}        -> 2
  TmpPatAlways{}            -> 2
  TmpPatPrecede{}           -> 2
  TmpPatFollow{}            -> 2
  TmpInitially{}            -> 2
  TmpFinally{}              -> 2
  EIff{}                    -> 3
  EImplies{}                -> 4
  EOr{}                     -> 5
  EXor{}                    -> 6
  EAnd{}                    -> 7
  LtlU{}                    -> 8
  TmpUntil{}                -> 8
  LtlW{}                    -> 9
  TmpWUntil{}               -> 9
  LtlF{}                    -> 10
  TmpEventually{}           -> 10
  LtlG{}                    -> 10
  TmpGlobally{}             -> 10
  LtlX{}                    -> 10
  TmpNext{}                 -> 10
  ENeg{}                    -> 11
  ELt{}                     -> 15
  EGt{}                     -> 15
  EEq{}                     -> 15
  ELte{}                    -> 15
  EGte{}                    -> 15
  ENeq{}                    -> 15
  EIn{}                     -> 15
  ENin{}                    -> 15
  EQuantExp{}               -> 16
  EAdd{}                    -> 17
  ESub{}                    -> 17
  EMul{}                    -> 18
  EDiv{}                    -> 18
  ERem{}                    -> 18
  EGMax{}                   -> 19
  EGMin{}                   -> 19
  ESum{}                    -> 20
  EProd{}                   -> 20
  ECard{}                   -> 20
  EMinExp{}                 -> 20
  EDomain{}                 -> 21
  ERange{}                  -> 22
  EUnion{}                  -> 23
  EUnionCom{}               -> 23
  EDifference{}             -> 24
  EIntersection{}           -> 25
  EIntersectionDeprecated{} -> 26
  EJoin{}                   -> 26
  ClaferId{}                -> 27
  EInt{}                    -> 27
  EDouble{}                 -> 27
  EReal{}                   -> 27
  EStr{}                    -> 27

printPatternScope :: PatternScope -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printPatternScope (PatScopeBefore _ exp')          indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " before " ++ while html "</span>" ++ (printOperand 11 exp' indent irMap html comments)
printPatternScope (PatScopeAfter _ exp')           indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " after " ++ while html "</span>" ++ (printOperand 11 exp' indent irMap html comments)
printPatternScope (PatScopeBetweenAnd _ exp1 exp2) indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " between " ++ while html "</span>" ++ printOperand 11 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " and " ++ while html "</span>" ++ printOperand 11 exp2 indent irMap html comments
printPatternScope (PatScopeAfterUntil _ exp1 exp2) indent irMap html comments = while html "<span class=\"tKeyword\">" ++ " after " ++ while html "</span>" ++ printOperand 11 exp1 indent irMap html comments ++ while html "<span class=\"tKeyword\">" ++ " until " ++ while html "</span>" ++ printOperand 11 exp2 indent irMap html comments
printPatternScope _                           _      _     _    _        = ""

printQuant :: Quant -> Bool -> String
printQuant quant' html = case quant' of
  (QuantNo _)   -> while html "<span class=\"keyword\">" ++ "no" ++ while html "</span>" ++ " "
  (QuantNot _)  -> while html "<span class=\"keyword\">" ++ "not" ++ while html "</span>" ++ " "
  (QuantLone _) -> while html "<span class=\"keyword\">" ++ "lone" ++ while html "</span>" ++ " "
  (QuantOne _)  -> while html "<span class=\"keyword\">" ++ "one" ++ while html "</span>" ++ " "
  (QuantSome _) -> while html "<span class=\"keyword\">" ++ "some" ++ while html "</span>" ++ " "

printEnumId :: EnumId -> Int -> Map.Map Span [Ir] -> Bool -> [(Span, String)] -> String
printEnumId (EnumIdIdent _ posident) _ irMap html _ = printPosIdent posident mUid' html
  where
    mUid' = getUid posident irMap

printIndent :: Int -> Bool -> String
printIndent 0 html = while html "<div>" ++ "\n"
printIndent _ html = while html "<div class=\"indent\">" ++ "\n"

printIndentId :: Int -> Bool -> String
printIndentId 0 html = while html "<div>" ++ "\n"
printIndentId _ html = while html "<div class=\"indent\">" ++ "\n"

printIndentEnd :: Bool -> String
printIndentEnd html = while html "</div>" ++ "\n"

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

getUid :: PosIdent -> Map.Map Span [Ir] -> Maybe String
getUid posIdent@(PosIdent (_, id')) irMap =
  case Map.lookup (getSpan posIdent) irMap of
    Nothing -> Nothing
    Just wrappedResultList -> listToMaybe $ mapMaybe (findUid id' . unwrap) wrappedResultList
  where
    unwrap (IRPExp pexp')       = getIdentPExp pexp'
    unwrap (IRClafer iClafer') = [ _uid iClafer' ]
    unwrap x = error $ "Html:getUid:unwrap called on: " ++ show x
    getIdentPExp (PExp _ _ _ exp') = getIdentIExp exp'
    getIdentIExp (IFunExp _ exps') = concatMap getIdentPExp exps'
    getIdentIExp (IClaferId _ id'' _ _) = [id'']
    getIdentIExp (IDeclPExp _ _ pexp) = getIdentPExp pexp
    getIdentIExp _ = []
    findUid name (x:xs) = if name == dropUid x then Just x else findUid name xs
    findUid _    []     = Nothing

getDivId :: Span -> Map.Map Span [Ir] -> String
getDivId s irMap = if isNothing $ Map.lookup s irMap
                      then "Uid not Found"
                      else let IRClafer iClaf = head $ fromJust $ Map.lookup s irMap in
                        _uid iClaf

getUseId :: Span -> Map.Map Span [Ir] -> (String, String)
getUseId s irMap = if isNothing $ Map.lookup s irMap
                      then ("Uid not Found", "Uid not Found")
                      else let IRClafer iClaf = head $ fromJust $ Map.lookup s irMap in
                        (_uid iClaf, fromMaybe "" $ _sident . _exp <$> _super iClaf)

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

-- | The model with its errors highlighted, for a model whose files are not known (e.g., a wiki
--   page): positions as @line 3 column 5@.
highlightErrors :: String -> [ClaferErr] -> String
highlightErrors = highlightErrorsIn []

-- | The model with its errors highlighted: each file under its name, and the positions of the
--   errors as @file.cfr:3:5@.
highlightErrorsIn :: [ModelFile] -> String -> [ClaferErr] -> String
highlightErrorsIn files model errors = "<pre>\n" ++ unlines (withHeaders $ replace "<!-- # FRAGMENT /-->" "</pre>\n<!-- # FRAGMENT /-->\n<pre>" --assumes the fragments have been concatenated
                            (highlightErrors' position (replace "//# FRAGMENT" "<!-- # FRAGMENT /-->" (lines model)) errors)) ++ "</pre>"
  where
    replace _ _ []     = []
    replace x y (z:zs) = (if x == z then y else z):replace x y zs
    position l c
      | null files = "line " ++ show l ++ " column " ++ show c
      | otherwise  = let (path, l') = modelPosition files l in path ++ ":" ++ show l' ++ ":" ++ show c
    -- the lines of the model, one per line of the text: each file starts with its name
    withHeaders = go 1 (fileStarts files)
      where
      go _ _ [] = []
      go n ((start, path) : starts) ls | start <= n = printFileHeader path : go n starts ls
      go n starts (l : ls) = l : go (n + 1) starts ls

highlightErrors' :: (Integer -> Integer -> String) -> [String] -> [ClaferErr] -> [String]
highlightErrors' _ model' [] = model'
highlightErrors' position model' (ClaferErr _:es) = highlightErrors' position model' es
highlightErrors' position model' (ParseErr ErrPos{modelPos = Pos l c, fragId = n} msg':es) =
  let (ls, lss) = genericSplitAt (l + toInteger n) model'
      newLine = fst (genericSplitAt (c - 1) $ last ls) ++ "<span class=\"error\" title=\"Parsing failed at " ++ position l c ++
           "...\n" ++ escapeHtml msg' ++ "\">" ++ (if snd (genericSplitAt (c - 1) $ last ls) == "" then "&nbsp;" else snd (genericSplitAt (c - 1) $ last ls)) ++ "</span>"
  in highlightErrors' position (init ls ++ [newLine] ++ lss) es
highlightErrors' position model' (SemanticErr ErrPos{modelPos = Pos l c, fragId = n} msg':es) =
  let (ls, lss) = genericSplitAt (l + toInteger n) model'
      newLine = fst (genericSplitAt (c - 1) $ last ls) ++ "<span class=\"error\" title=\"Compiling failed at " ++ position l c ++
           "...\n" ++ escapeHtml msg' ++ "\">" ++ (if snd (genericSplitAt (c - 1) $ last ls) == "" then "&nbsp;" else snd (genericSplitAt (c - 1) $ last ls)) ++ "</span>"
  in highlightErrors' position (init ls ++ [newLine] ++ lss) es

-- | The header of a file of the model in the HTML output: its name.
printFileHeader :: FilePath -> String
printFileHeader path = "<div class=\"file\">" ++ escapeHtml path ++ "</div>"
