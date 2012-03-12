{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Prelude hiding (writeFile, readFile, print, putStrLn)

import System.IO
import System.Cmd
import System.Exit
import Control.Exception.Base
import IO  ( stdin, hGetContents )
import System ( getArgs, getProgName )
import System.Timeout
import Control.Monad.State
import System.Environment.Executable
import Data.Maybe

import Common
import ClaferArgs
import Front.Lexclafer
import Front.Parclafer
import Front.Printclafer
import Front.Absclafer hiding (Clafer)
import Front.LayoutResolver
import Front.ErrM
import Intermediate.Desugarer
import Intermediate.Resolver
import Intermediate.StringAnalyzer
import Intermediate.Transformer
import Optimizer.Optimizer
import Generator.Stats
import Generator.Alloy
import Generator.Xml
import Generator.Schema

type ParseFun = [Token] -> Err Module

myLLexer = myLexer

type VerbosityL = Int

putStrV :: VerbosityL -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()


start v p args = if fromJust $ schema args
  then putStrLn Generator.Schema.xsd
  else run v p args


run :: VerbosityL -> ParseFun -> ClaferArgs -> IO ()
run v p args = do
           input <- readFile $ file args
           conPutStrLn args (file args)
           let ts = (if not 
                        ((fromJust $ new_layout args) ||
                         (fromJust $ no_layout args))
                     then 
                       resolveLayout 
                     else 
                       id) 
                    $ myLLexer $
                    (if (not $ fromJust $ no_layout args) &&
                        (fromJust $ new_layout args)
                     then 
                       resLayout 
                     else 
                       id)
                    input  in case p ts of
             Bad s    -> do putStrLn "\nParse              Failed...\n"
                            putStrV v "Tokens:"
                            putStrLn s
                            exitFailure
             Ok  tree -> do
                          let f = stripFileName $ file args
                          conPutStrLn args "\nParse Successful!"
                          dTree <- desugar args tree
                          oTree <- analyze args dTree
                          f' <- generate f args oTree
                          when (fromJust $ validate args) $ runValidate args f'

stripFileName f = case dropWhile (/= '.') $ reverse f of
  [] -> f
  xs -> reverse $ tail xs

desugar args tree = do
  conPutStrLn args "[Desugaring]"
  let dTree = desugarModule tree
  return dTree
  -- writeFile (f ++ ".des") $ printTree $
  --  sugarModule dTree

analyze args tree = do
  let dTree' = findDupModule args tree
  let au = allUnique dTree'
  let args' = args{skip_resolver = Just $ au && (fromJust $ skip_resolver args)}
  conPutStrLn args "[Resolving]"
  let (rTree, genv) = resolveModule args' dTree'
  conPutStrLn args "[Analyzing String]"
  let aTree = astrModule rTree
  conPutStrLn args "[Transforming]"
  let tTree = transModule aTree
  conPutStrLn args "[Optimizing]"
  return $ (optimizeModule args' (tTree, genv), genv, au)
  -- writeFile (f ++ ".ana") $ printTree $
  --  sugarModule oTree

generate f args (oTree, genv, au) = do
  conPutStrLn args "[Generating Code]"
  let stats = showStats au $ statsModule oTree
  when (not $ fromJust $ no_stats args) $ putStrLn stats
  conPutStrLn args "[Saving File]"
  let alloyCode = genModule args (oTree, genv)
  let addCommentStats = if fromJust $ no_stats args then const else addStats
  let (ext, code) = case (fromJust $ mode args) of
                      Alloy   -> ("als", addCommentStats (fst alloyCode) stats)
                      Alloy42 -> ("als", addCommentStats (fst alloyCode) stats)
                      Xml     -> ("xml", genXmlModule oTree)
                      Clafer  -> ("des.cfr", printTree $ sugarModule oTree)
  let f' = f ++ "." ++ ext
  if fromJust $ console_output args then putStrLn code else writeFile f' code
  let mf = f ++ "." ++ "map"
  when (fromJust $ alloy_mapping args) $ writeFile mf $ show $ snd alloyCode
  return f'

conPutStrLn args s = when (not $ fromJust $ console_output args) $ putStrLn s

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree


addStats code stats = "/*\n" ++ stats ++ "*/\n" ++ code


showStats au (Stats na nr nc nconst ngoals sgl) =
  unlines [ "All clafers: " ++ (show (na + nr + nc)) ++ " | Abstract: " ++ (show na) ++ " | Concrete: " ++ (show nc) ++ " | References: " ++ (show nr)          , "Constraints: " ++ show nconst
          , "Goals: " ++ show ngoals  
          , "Global scope: " ++ showInterval sgl
          , "All names unique: " ++ show au]


showInterval (n, ExIntegerAst) = show n ++ "..*"
showInterval (n, ExIntegerNum m) = show n ++ ".." ++ show m

runValidate args fo = do
  let path = (fromJust $ tooldir args) ++ "/"
  case (fromJust $ mode args) of
    Xml -> do
      writeFile "ClaferIR.xsd" Generator.Schema.xsd
      voidf $ system $ "java -classpath " ++ path ++ " XsdCheck ClaferIR.xsd " ++ fo
    Alloy ->   voidf $ system $ validateAlloy path "4" ++ fo
    Alloy42 -> voidf $ system $ validateAlloy path "4.2-rc" ++ fo
    Clafer ->  voidf $ system $ "./clafer -s " ++ fo

validateAlloy path version = "java -cp " ++ path ++ "alloy" ++ version ++ ".jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler "

main :: IO ()
main = do
  args <- mainArgs
  let timeInSec = (fromJust $ timeout_analysis args) * 10^6
  if timeInSec > 0
    then timeout timeInSec $ start 2 pModule args
    else Just `liftM` start 2 pModule args
  return ()
