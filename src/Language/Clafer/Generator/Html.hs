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
module Language.Clafer.Generator.Html (genHtml, Tag) where

import Language.Clafer.Front.Absclafer

-- Structure of output for Wiki
-- I should probably add a "PandocHtml" flag for the wiki, and use "Html" for pure, web-ready html
-- [HtmlTag “<b>”, Text “This is an example”, HtmlTag “</b>”]
-- The wiki plugin can take this type-tagged info and convert it to pandoc,
-- so that this doesn't need to import Pandoc
-- it will have to include its own spaces (Space) and newlines (LineBreak)

data Tag = Html | Text deriving (Eq,Ord,Show) --this will be used later (see above)

genHtml (Module [])     = ""
genHtml (Module ((ElementDecl x):xs)) = (genHtmlh x 0) ++ (genHtml $ Module xs)
-- For some reason it is outputting too much indentation. I don't think it will be a large problem, though
genHtmlh (Subclafer (Clafer abstract gCard ident super card init (ElementsList elements))) indent =
  (printIndent indent) ++
    (unwords [printAbstract abstract, printGCard gCard, printId ident, printSuper super,
    printCard card, printInit init]) ++ "\n" ++ (concatMap (\x -> genHtmlh x (indent + 1)) elements)
genHtmlh _ _ = "END"

-- the "Data Omitted" Lines are for me to quickly identify when pattern matching fails, but with useful info
printIndent indent = replicate (indent * 2) ' '

printAbstract Abstract = "abstract"
printAbstract AbstractEmpty = ""
printAbstract x = "Abstract Omitted"

printGCard (GCardInterval (NCard (PosInteger (pos, num)) ExIntegerAst)) = ""
printGCard x = "GCardInterval Omitted"

printId (PosIdent (pos, id))
  | validPos pos = (tail $ dropWhile (\x -> x /= '_') id) -- drops the UID_ from UID_ID
  | otherwise    = "" 
printId x = "Id Omitted"

printSuper (SuperSome SuperColon (ClaferId (Path [ModIdIdent (PosIdent (pos,id))])))
  | validPos pos = ": " ++ id
  | otherwise    = ""
printSuper x = "Super Omitted"

printCard (CardInterval (NCard (PosInteger (pos1,num1)) (ExIntegerNum (PosInteger (pos2,num2)))))
  | validPos pos1 = num1 ++ ".." ++ num2
  | otherwise     = ""
printCard x = "Cardinality Omitted"

printInit x = "Initialization Omitted"

validPos (row, col)
  | row >= 0 && col >= 0 = True
  | otherwise            = False
