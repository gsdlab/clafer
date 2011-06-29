module Main where

import Prelude hiding (writeFile, readFile, print, putStrLn)

import System.IO

import IO  ( stdin, hGetContents )
import System ( getArgs, getProgName )

import System.Timeout

import Front.Lexclafer
import Front.Parclafer
import Front.Printclafer
import Front.Absclafer
import Front.LayoutResolver
import Front.ErrM
import Intermediate.Desugarer
import Intermediate.Resolver
import Intermediate.StringAnalyzer
import Generator.Alloy

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
                          putStrLn s
           Ok  tree -> case fileName of
--               AlloyOut -> putStrLn code
--               XmlOut   -> clafer2xml tree''
--               EcoreOut -> clafer2ecore tree''
               AlloyFile f -> do
                          putStrLn "\nParse Successful!"
--                          putStrLn "\n[Symbol Table]"               
--                          putStrLn $ show st
                          let f' = take (length f - 4) f
                          writeFile (f' ++ ".des") $ printTree $ sugarModule tree'
                          writeFile (f' ++ ".ana") $ printTree $ sugarModule tree''
--                          showTree v tree''
                          putStrLn "\n[Interpreting]"
--                          writeFile "data/output.als" code
                          writeFile (f' ++ ".als") code
             where
             tree'  = desugarModule tree
             tree'' = astrModule $ resolveModule tree'
             code   = genModule tree''


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
--      ("-x":[]) -> hGetContents stdin >>= run XmlOut 2 pModule
--      ("-e":[]) -> hGetContents stdin >>= run EcoreOut 2 pModule
      fs -> mapM_ (runFile 2 pModule) fs)
  return ()


