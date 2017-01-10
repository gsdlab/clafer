{-
 Copyright (C) 2012-2015 Kacper Bak, Jimmy Liang, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
{-# LANGUAGE DeriveDataTypeable, NamedFieldPuns #-}
module Main where

import Prelude hiding (writeFile, readFile, print, putStrLn)

import Data.Functor (void)
import System.IO
import System.Timeout
import System.Process (system)

import Language.Clafer

main :: IO ()
main = do
  (args', model) <- mainArgs
  let timeInSec = (timeout_analysis args') * 10^(6::Integer)
  if timeInSec > 0
    then timeout timeInSec $ start args' model
    else Just `fmap` start args' model
  return ()

start :: ClaferArgs -> InputModel-> IO ()
start args' model = if ecore2clafer args'
  then runEcore2Clafer (file args') $ (tooldir args')
  else runCompiler Nothing args' model

runEcore2Clafer :: FilePath -> FilePath -> IO ()
runEcore2Clafer    ecoreFile toolPath
  | null ecoreFile = do
      putStrLn "Error: Provide a file name of an ECore model."
  | otherwise      = do
      putStrLn $ "Converting " ++ ecoreFile ++ " into Clafer"
      void $ system $ "java -jar " ++ toolPath ++ "/ecore2clafer.jar " ++ ecoreFile
