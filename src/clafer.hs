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
import System.FilePath.Posix

import Language.Clafer

type ParseFun = [Token] -> Err Module

type VerbosityL = Int

putStrV :: VerbosityL -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()


start v p args model = if fromJust $ schema args
  then putStrLn claferIRXSD
  else run v p args model


run :: VerbosityL -> ParseFun -> ClaferArgs -> String -> IO ()
run v p args input = do
--           conPutStrLn args (file args)
           let ts = (if not 
                        ((fromJust $ new_layout args) ||
                         (fromJust $ no_layout args))
                     then 
                       resolveLayout 
                     else 
                       id) 
                    $ myLexer $
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
                          let f = dropExtension $ file args
--                          conPutStrLn args "\nParse Successful!"
                          dTree <- desugar args tree
                          oTree <- analyze args dTree
                          f' <- generate f args oTree
                          when (fromJust $ validate args) $ runValidate args f'


conPutStrLn args s = when (not $ fromJust $ console_output args) $ putStrLn s

runValidate args fo = do
  let path = (fromJust $ tooldir args) ++ "/"
  case (fromJust $ mode args) of
    Xml -> do
      writeFile "ClaferIR.xsd" claferIRXSD
      voidf $ system $ "java -classpath " ++ path ++ " XsdCheck ClaferIR.xsd " ++ fo
    Alloy ->   voidf $ system $ validateAlloy path "4" ++ fo
    Alloy42 -> voidf $ system $ validateAlloy path "4.2-rc" ++ fo
    Clafer ->  voidf $ system $ path ++ "/clafer -s -m=clafer " ++ fo

validateAlloy path version = "java -cp " ++ path ++ "alloy" ++ version ++ ".jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler "

main :: IO ()
main = do
  (args, model) <- mainArgs
  let timeInSec = (fromJust $ timeout_analysis args) * 10^6
  if timeInSec > 0
    then timeout timeInSec $ start 2 pModule args model
    else Just `liftM` start 2 pModule args model
  return ()
