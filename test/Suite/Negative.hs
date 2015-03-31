{-# LANGUAGE TemplateHaskell #-}
{-
 Copyright (C) 2013 Luke Brown <http://gsd.uwaterloo.ca>

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
module Suite.Negative (tg_Test_Suite_Negative) where

import Functions
import Control.Monad
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH
import Language.Clafer.ClaferArgs

tg_Test_Suite_Negative :: TestTree
tg_Test_Suite_Negative = $(testGroupGenerator)

negativeClaferModels :: IO [([Char], String)]
negativeClaferModels = do
    claferModels <- getClafers "test/negative"
    return $ filter ((`notElem` crashModels) . fst ) claferModels
    where
        crashModels = ["i127-loop.cfr", "i141-constraints.cfr"]
{-Put models in the list above that completly crash
  the compiler, this will avoid crashing the test suite
  Note: If the model is giving an unexpected error it
  should be located in failing/negative not here!-}

case_failTest :: Assertion
case_failTest = do
    claferModels <- negativeClaferModels
    let compiledClafers = map (\(file', model) -> (file', compileOneFragment defaultClaferArgs model)) claferModels
    forM_ compiledClafers (\(file', compiled) ->
        when (compiledCheck compiled) $ putStrLn (file' ++ " compiled when it should not have."))
    (andMap (not . compiledCheck . snd) compiledClafers
        @? "test/negative fail: The above clafer models compiled.")
