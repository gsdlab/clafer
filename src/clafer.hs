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
import System.IO  ( stdin, hGetContents )
import System.Cmd
import System.Exit
import Control.Exception.Base
import System.Environment ( getArgs, getProgName )
import System.Timeout
import Control.Monad.State
import System.Environment.Executable
import Data.Maybe
import System.FilePath.Posix

import Language.Clafer

putStrV :: VerbosityL -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

run :: VerbosityL -> ClaferArgs -> InputModel -> IO ()
run v args input = do
  case addModuleFragment args input of
    Bad s    -> do putStrLn "\nParse Failed...\n"
                   putStrV v "Tokens:"
                   putStrLn s
                   exitFailure
    Ok  tree -> do
                   let oTree = compile args tree
                   f' <- save args oTree
                   when (fromJust $ validate args) $ runValidate args f'                      

save :: ClaferArgs -> (IModule, GEnv, Bool) -> IO [Char]
save    args          oTree                 = do
  let result = generate args oTree
  when (not $ fromJust $ no_stats args) $ putStrLn (statistics result)
  let f = dropExtension $ file args                      
  let f' = f ++ "." ++ (extension result)
  if fromJust $ console_output args then putStrLn (outputCode result) else writeFile f' (outputCode result)
  when (fromJust $ alloy_mapping args) $ writeFile (f ++ "." ++ "map") $ fromJust (mappingToAlloy result)
  return f'
  
conPutStrLn args s = when (not $ fromJust $ console_output args) $ putStrLn s

runValidate :: ClaferArgs -> [Char] -> IO ()
runValidate args fo = do
  let path = (fromJust $ tooldir args) ++ "/"
  case (fromJust $ mode args) of
    Xml -> do
      writeFile "ClaferIR.xsd" claferIRXSD
      voidf $ system $ "java -classpath " ++ path ++ " XsdCheck ClaferIR.xsd " ++ fo
    Alloy ->   voidf $ system $ validateAlloy path "4" ++ fo
    Alloy42 -> voidf $ system $ validateAlloy path "4.2-rc" ++ fo
    Clafer ->  voidf $ system $ path ++ "/clafer -s -m=clafer " ++ fo

validateAlloy :: String -> String -> String
validateAlloy path version = "java -cp " ++ path ++ "alloy" ++ version ++ ".jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler "

main :: IO ()
main = do
  (args, model) <- mainArgs
  let timeInSec = (fromJust $ timeout_analysis args) * 10^6
  if timeInSec > 0
    then timeout timeInSec $ start 2 args model
    else Just `liftM` start 2 args model
  return ()

start :: VerbosityL -> ClaferArgs -> InputModel-> IO ()
start v args model = if fromJust $ schema args
  then putStrLn claferIRXSD
  else run v args model
  
