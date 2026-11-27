{-# LANGUAGE TypeApplications #-}
{-
 Copyright (C) 2026 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
-- | The oracle of the Java frontend's parser (check 8 of
--   design/java-compiler-frontend-feasibility.md): for each model, the parse tree
--   as 'printTree' prints it, or the parse error with its position. Each file is
--   parsed on its own, with the layout options of its first line, as
--   'Language.Clafer.parse' parses it, the same-line check included. Where the
--   compiler fails instead, e.g., with @EOF@ at a syntax error at the end of the model, the
--   line is @the compiler fails: @ and the message.
--
--   > cabal exec -- runghc test/print-parse-trees.hs OUTDIR FILE.cfr...
--
--   writes OUTDIR/FILE.cfr.tree for each file (test/print-parse-trees.sh).
import Control.Exception (SomeException, displayException, evaluate, try)
import Control.Monad (forM_)
import System.Environment (getArgs)
import System.FilePath (takeFileName, (</>))

import Language.Clafer
import Language.Clafer.ClaferArgs
import Language.Clafer.Import (fileOptions)
import Language.ClaferT
import Language.Clafer.Front.AbsClafer (Pos(..))
import Language.Clafer.Front.PrintClafer (printTree)

main :: IO ()
main = do
  outDir : files <- getArgs
  forM_ files $ \file -> do
    text <- readFile file
    -- the compiler fails, e.g., the parser at a syntax error at the end of the model (pp [] in
    -- ParClafer.y), and the lexer at a block comment with a character after U+00FF
    result <- try @SomeException $ evaluate $ let t = tree text in length t `seq` t
    writeFile (outDir </> takeFileName file ++ ".tree") $ case result of
      Right t -> t
      Left e -> "the compiler fails: " ++ takeWhile (/= '\n') (displayException e) ++ "\n"

tree :: String -> String
tree text = case runClafer options (addModuleFragment text >> parse >> getAst) of
  Right ast -> printTree ast ++ "\n"
  Left errs -> concatMap err errs
  where
  options = either (const defaultClaferArgs) id (fileOptions text)
  err (ParseErr ErrPos{modelPos = Pos l c} m) = "parse error " ++ show l ++ ":" ++ show c ++ ": " ++ m ++ "\n"
  err e = "error: " ++ show e ++ "\n"
