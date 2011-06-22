{-
 This file is part of the Clafer to Alloy Translator (clafer2alloy).

 Copyright (C) 2010 Kacper Bak <http://gsd.uwaterloo.ca/kbak>

 clafer2alloy is free software: you can redistribute it and/or modify
 it under the terms of the GNU Lesser General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 clafer2alloy is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Lesser General Public License for more details.

 You should have received a copy of the GNU Lesser General Public License
 along with clafer2alloy. (See files COPYING and COPYING.LESSER.)  If not,
 see <http://www.gnu.org/licenses/>.
-}
module Main where

import Prelude hiding (writeFile, readFile, print, putStrLn)

import System.IO

import IO  ( stdin, hGetContents )
import System ( getArgs, getProgName )

import System.Timeout
import Lexclafer2alloy
import Parclafer2alloy
import Desugarer
import TypeEngine
import Renamer
import SemanticAnalyzer
import StringAnalyzer
import Skelclafer2alloy
import Xmlclafer2alloy
import Ecoreclafer2alloy
import Printclafer2alloy
import Absclafer2alloy
import LayoutResolver


import ErrM

type ParseFun = [Token] -> Err Module

data Mode = AlloyOut | AlloyFile String | XmlOut | EcoreOut

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: Verbosity -> ParseFun -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run (AlloyFile f) v p

run :: Mode -> Verbosity -> ParseFun -> FilePath -> IO ()
run fileName v p s = let ts = resolveLayout $ myLLexer s in case p ts of
           Bad s    -> do putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                       --   putStrV v $ show ts
                          putStrLn s
           Ok  tree -> case fileName of
               AlloyOut -> putStrLn code
               XmlOut   -> clafer2xml tree''
               EcoreOut -> clafer2ecore tree''
               AlloyFile f -> do
                          putStrLn "\nParse Successful!"
--                          showTree v tree'
--                          putStrLn "\n[Symbol Table]"               
--                          putStrLn $ show st
                          let f' = take (length f - 4) f
--                          writeFile (f' ++ ".des") $ printTree tree'
--                          writeFile (f' ++ ".ana") $ printTree tree''
--                          showTree v tree''
                          putStrLn "\n[Interpreting]"
                          writeFile "data/output.als" code
                          writeFile (f' ++ ".als") code
             where
             tree'  = desugarModule tree
             st     = typeModule tree'
             tree'' = astrModule $ {-renameModule st $-} analyzeModule tree' st
             code   = transModule tree''


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do
  args <- getArgs
  let timeInSec = 10 * 10^6
  timeout timeInSec (case args of
      [] -> hGetContents stdin >>= run AlloyOut 2 pModule
      ("-x":[]) -> hGetContents stdin >>= run XmlOut 2 pModule
      ("-e":[]) -> hGetContents stdin >>= run EcoreOut 2 pModule
      fs -> mapM_ (runFile 2 pModule) fs)
  return ()