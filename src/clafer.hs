{-
 This file is part of the Clafer Translator (clafer).

 Copyright (C) 2010 Kacper Bak <http://gsd.uwaterloo.ca/kbak>

 clafer is free software: you can redistribute it and/or modify
 it under the terms of the GNU Lesser General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 clafer is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Lesser General Public License for more details.

 You should have received a copy of the GNU Lesser General Public License
 along with clafer. (See files COPYING and COPYING.LESSER.)  If not,
 see <http://www.gnu.org/licenses/>.
-}
{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Prelude hiding (writeFile, readFile, print, putStrLn)

import System.IO
import Control.Exception.Base
import IO  ( stdin, hGetContents )
import System ( getArgs, getProgName )
import System.Console.CmdArgs
import System.Timeout
import Control.Monad.State

import Common
import Front.Lexclafer
import Front.Parclafer
import Front.Printclafer
import Front.Absclafer
import Front.LayoutResolver
import Front.ErrM
import Intermediate.Desugarer
import Intermediate.Resolver
import Intermediate.StringAnalyzer
import Optimizer.Optimizer
import Generator.Stats
import Generator.Alloy
import Generator.Xml

type ParseFun = [Token] -> Err Module

myLLexer = myLexer

type VerbosityL = Int

putStrV :: VerbosityL -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()


run :: VerbosityL -> ParseFun -> ClaferArgs -> IO ()
run v p args = do
           input <- readFile $ file args
           let ts = (if not (new_layout args || no_layout args)
                     then resolveLayout else id) $ myLLexer $
                    (if (not $ no_layout args) && new_layout args
                     then resLayout else id)
                    input  in case p ts of
             Bad s    -> do putStrLn "\nParse              Failed...\n"
                            putStrV v "Tokens:"
                            putStrLn s
             Ok  tree -> do
                          let f = file args
                          conPutStrLn args "\nParse Successful!"
                          conPutStrLn args "[Desugaring]"
                          dTree <- evaluate $! desugarModule tree
                          let f'    = take (length f - 4) f
                          -- writeFile (f' ++ ".des") $ printTree $
                          --  sugarModule dTree
                          let dTree' = findDupModule args dTree
                          let au = allUnique dTree'
                          let args' = args{force_resolver = not au ||
                                           force_resolver args}
                          conPutStrLn args "[Resolving]"
                          (rTree, genv) <- evaluate $!
                                           resolveModule args' dTree'
                          conPutStrLn args "[Analyzing String]"
                          aTree <- evaluate $! astrModule rTree
                          conPutStrLn args "[Optimizing]"
                          oTree <- evaluate $ optimizeModule args' (aTree, genv)
                          -- writeFile (f' ++ ".ana") $ printTree $
                          --  sugarModule oTree
                          conPutStrLn args "[Generating Code]"
                          let stats = showStats au $ statsModule oTree
                          when (not $ no_stats args) $ putStrLn stats
                          conPutStrLn args "[Saving File]"
                          let (ext, code) = case (mode args) of
                                Alloy -> ("als", addStats (genModule (mode args) (oTree, genv)) stats)
                                Alloy42 -> ("als", addStats (genModule (mode args) (oTree, genv)) stats)
                                Xml ->   ("xml", genXmlModule oTree)
                          if console_output args
                             then putStrLn code
                             else writeFile (f' ++ "." ++ ext) code

conPutStrLn args s = when (not $ console_output args) $ putStrLn s

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree


addStats code stats = "/*\n" ++ stats ++ "*/\n" ++ code


showStats au (Stats na nr nc nconst sgl) =
  unlines [ "All clafers: " ++ (show (na + nr + nc)) ++ " | Abstract: " ++ (show na) ++ " | Concrete: " ++ (show nc) ++ " | References: " ++ (show nr)
          , "Constraints: " ++ show nconst
          , "Global scope: " ++ showInterval sgl
          , "All names unique: " ++ show au]


showInterval (n, ExIntegerAst) = show n ++ "..*"
showInterval (n, ExIntegerNum m) = show n ++ ".." ++ show m

clafer = ClaferArgs {
  mode = Alloy &= help "Generated output type" &= name "m",
  console_output = False &= help "Output code on console" &= name "o",
  flatten_inheritance = def &= help "Flatten inheritance" &= name "i",
  file = def &= args,
  timeout_analysis = def &= help "Timeout for analysis",
  no_layout = def &= help "Don't resolve off-side rule layout" &= name "l",
  new_layout = def &= help "Use new fast layout resolver (experimental)" &= name "nl",
  check_duplicates = def &= help "Check duplicated clafer names",
  force_resolver = def &= help "Force name resolution" &= name "f",
  keep_unused = def &= help "Keep unused abstract clafers" &= name "k",
  no_stats = def &= help "Don't print statistics" &= name "s"
 } &= summary "Clafer v0.0.2"

main :: IO ()
main = do
  args <- cmdArgs clafer
  let timeInSec = (timeout_analysis args) * 10^6
  if timeInSec > 0
    then timeout timeInSec $ run 2 pModule args
    else Just `liftM` run 2 pModule args
  return ()