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

type ParseFun = [Token] -> Err Module

data Mode = AlloyOut | AlloyFile String | XmlOut | EcoreOut

myLLexer = myLexer

type VerbosityL = Int

putStrV :: VerbosityL -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()


run :: VerbosityL -> ParseFun -> ClaferArgs -> IO ()
run v p args = do
           input <- readFile $ file args
           let ts = myLLexer $ (if no_layout args then id else resLayout) input  in case p ts of
             Bad s    -> do putStrLn "\nParse              Failed...\n"
                            putStrV v "Tokens:"
                            putStrLn s
             Ok  tree -> do
                          let f = file args
                          putStrLn "\nParse Successful!"
                          putStrLn "[Desugaring]"
                          dTree <- evaluate $! desugarModule args tree
                          let f'    = take (length f - 4) f
                          writeFile (f' ++ ".des") $ printTree $
                            sugarModule dTree
                          putStrLn "[Resolving]"
                          (rTree, genv) <- evaluate $! resolveModule args dTree
                          putStrLn "[Analyzing String]"
                          aTree <- evaluate $! astrModule rTree
                          putStrLn "[Optimizing]"
                          oTree <- evaluate $ optimizeModule args (aTree, genv)
                          writeFile (f' ++ ".ana") $ printTree $
                            sugarModule oTree
                          putStrLn "[Generating Code]"
                          code <- evaluate $! genModule (oTree, genv)
                          putStrLn "[Saving File]"
                          printStats $ statsModule oTree
                          writeFile (f' ++ ".als") code


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree


printStats (Stats na nr nc nconst sgl) = do
  putStrLn $ "All clafers: " ++ (show (na + nr + nc)) ++ " | Abstract: " ++ (show na) ++ " | Concrete: " ++ (show nc) ++ " | References: " ++ (show nr)
  putStrLn $ "Constraints: " ++ show nconst
  putStrLn $ "Global scope: " ++ showInterval sgl


showInterval (n, ExIntegerAst) = show n ++ "..*"
showInterval (n, ExIntegerNum m) = show n ++ ".." ++ show m

clafer = ClaferArgs {
  unroll_inheritance = def &= help "Unroll inheritance" &= name "i",
  file = def &= args,
  timeout_analysis = def &= help "Timeout for analysis",
  no_layout = def &= help "Don't resolve off-side rule layout" &= name "l",
  check_duplicates = def &= help "Check duplicated clafer names",
  unique_identifiers = def &= help "Assume that all identifiers are unique. Turns off the name resolver." &= name "u",
  synthetic_root = def &= help "Introduce synthetic root" &= name "r"
 } &= summary "Clafer v0.0.2"

main :: IO ()
main = do
  args <- cmdArgs clafer
  let timeInSec = (timeout_analysis args) * 10^6
  if timeInSec > 0 then timeout timeInSec $ run 2 pModule args
  else Just `liftM` run 2 pModule args
  return ()