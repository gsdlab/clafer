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

genHtml (Module [])     = ""
genHtml (Module (x:xs)) = (printDeclaration x 0) ++ (genHtml $ Module xs)
genHtml _ = "genHtml encountered an unknown pattern"

-- "Data Omitted" Lines are for me to quickly identify when pattern matching fails, but with useful info
printDeclaration (EnumDecl posIdent enumIds) indent = "enum" ++ (printPosIdent posIdent indent) ++ "Enum IDs" --placeholder
printDeclaration (ElementDecl element)       indent = printElement element indent

printElement (Subclafer (Clafer abstract gCard id super card init (ElementsList elements))) indent =
  (printIndent indent) ++
    (unwords [printAbstract abstract indent, printGCard gCard indent, printPosIdentAnchor id indent, printSuper super indent,
    printCard card indent, printInit init indent]) ++ "<br>" ++ (concatMap (\x -> printElement x (indent + 1)) elements)
printElement (Subconstraint constraint) indent = (printIndent indent) ++ printConstraint constraint indent
printElement element indent = "Element Omitted: " ++ show element

printAbstract Abstract indent = "<b>abstract</b>"
printAbstract AbstractEmpty indent = ""
printAbstract x _ = "Abstract Omitted"

printGCard gCard indent = case gCard of
  (GCardInterval ncard) -> printNCard ncard indent
  GCardEmpty -> ""
  GCardXor   -> "xor"
  GCardOr    -> "or"
  GCardMux   -> "mux"
  GCardOpt   -> "opt"
  _          -> "GCardInterval Omitted"

printNCard (NCard (PosInteger (pos, num)) exInteger) indent = if validPos pos
    then case exInteger of
      ExIntegerAst                -> num ++ "..*"
      (ExIntegerNum (PosInteger (pos', num'))) -> num ++ ".." ++ num'
    else ""

printName (Path modids) indent = unwords $ map (\x -> printModId x indent) modids
printName _             _      = "Name Omitted"

printModId (ModIdIdent posident) indent = printPosIdent posident indent

printPosIdentAnchor (PosIdent (pos, id)) indent
  | id == "clafer" = ""
  | validPos pos   = if indent == 0 then "<a name =\"" ++ id ++ "\">" ++ dropUid id ++ "</a>"
                                    else dropUid id
  | otherwise      = ""

printPosIdent (PosIdent (pos, id)) indent
  | id == "clafer" = ""
  | validPos pos   = dropUid id
  | otherwise      = ""

printSuper SuperEmpty indent = ""
printSuper (SuperSome superHow setExp) indent = let str = printSetExp setExp indent in
  if str /= ""
  then printSuperHow superHow indent ++ " " ++ str
  else ""
printSuper x _ = "Super Omitted"

printSuperHow SuperColon  indent = ":"
printSuperHow SuperArrow  indent = "-> "
printSuperHow SuperMArrow indent = "->> "
printSuperHow _           indent = "SuperHow Omitted"

printCard (CardInterval nCard) indent = printNCard nCard indent
printCard x _ = "Cardinality Omitted"

printConstraint (Constraint exps) indent = "[ "  ++ (concat $ map (\x -> printExp x indent) exps) ++ " ]<br>"

printDecl (Decl locids setExp) indent = ":" ++ printSetExp setExp indent

printInit InitEmpty indent = ""
printInit x _ = "Initialization Omitted"

printExp (DeclAllDisj decl exp) indent = (printDecl decl indent) ++ (printExp exp indent)
printExp (ENeq exp1 exp2)       indent = (printExp exp1 indent) ++ "!=" ++ (printExp exp2 indent)
printExp (ESetExp setExp)       indent = printSetExp setExp indent
printExp (EEq exp1 exp2)        indent = (printExp exp1 indent) ++ "=" ++ (printExp exp2 indent)
printExp (QuantExp quant exp)   indent = printQuant quant indent ++ printExp exp indent
printExp exp                    indent = "Exp Omitted:" ++ (show exp)

printSetExp (ClaferId name) indent = printName name indent
printSetExp (Union set1 set2) indent = (printSetExp set1 indent) ++ if not (printSetExp set1 indent == "" || printSetExp set2 indent == "")
                                                     then "++" ++ (printSetExp set2 indent)
                                                     else printSetExp set2 indent
printSetExp (UnionCom set1 set2) indent = (printSetExp set1 indent) ++ if not (printSetExp set1 indent == "" || printSetExp set2 indent == "")
                                                     then "," ++ (printSetExp set2 indent)
                                                     else printSetExp set2 indent
printSetExp (Difference set1 set2) indent = (printSetExp set1 indent) ++ if not (printSetExp set1 indent == "" || printSetExp set2 indent == "")
                                                     then "--" ++ (printSetExp set2 indent)
                                                     else printSetExp set2 indent
printSetExp (Join set1 set2) indent = (printSetExp set1 indent) ++ if not (printSetExp set1 indent == "" || printSetExp set2 indent == "")
                                                     then "." ++ (printSetExp set2 indent)
                                                     else printSetExp set2 indent
printSetExp _                 _ = "setExp Omitted"

printQuant quant indent = case quant of
  QuantNo    -> "no "
  QuantLone  -> "lone "
  QuantOne   -> "one "
  QuantSome  -> "some "
 

printIndent indent = replicate (indent * 2) ' '

validPos (row, col)
  | row >= 0 && col >= 0 = True
  | otherwise            = False

dropUid id = rest $ dropWhile (\x -> x /= '_') id
--so it fails more gracefully on empty lists
rest [] = []
rest (x:xs) = xs
