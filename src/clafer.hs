{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Prelude hiding (writeFile, readFile, print, putStrLn)

import System.IO
import Control.Exception.Base
import IO  ( stdin, hGetContents )
import System ( getArgs, getProgName )
import System.Console.CmdArgs
import System.Timeout

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
import Generator.Alloy

type ParseFun = [Token] -> Err Module

data Mode = AlloyOut | AlloyFile String | XmlOut | EcoreOut

myLLexer = myLexer

type VerbosityL = Int

putStrV :: VerbosityL -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

{-
runFile :: VerbosityL -> ParseFun -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run (AlloyFile f) v p
-}
run :: VerbosityL -> ParseFun -> ClaferArgs -> IO ()
run v p args = do
           input <- readFile $ file args
           let ts = resolveLayout $ myLLexer input  in case p ts of
             Bad s    -> do putStrLn "\nParse              Failed...\n"
                            putStrV v "Tokens:"
                            putStrLn s
             Ok  tree -> do
                          let f = file args
                          putStrLn "\nParse Successful!"
                          putStrLn "[Desugaring]"
                          dTree <- evaluate $! desugarModule tree
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
                          writeFile (f' ++ ".als") code


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

clafer = ClaferArgs {
  unroll_inheritance = def &= help "Unroll inheritance",
  file = def &= args} &= summary "Clafer v0.0.2"

main :: IO ()
main = do
  args <- cmdArgs clafer
--  args <- getArgs
  let timeInSec = 10 * 10^6
  timeout timeInSec (
    run 2 pModule args)
--case args of
--      [] -> hGetContents stdin >>= 
--      ("-x":[]) -> hGetContents stdin >>= run XmlOut 2 pModule
--      ("-e":[]) -> hGetContents stdin >>= run EcoreOut 2 pModule
--      fs -> mapM_ (runFile 2 pModule) fs
--  )
  return ()