{-# OPTIONS_GHC -XTemplateHaskell #-}
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
import qualified Data.List as List
import Data.Monoid
import Control.Monad
import Language.Clafer
import Language.ClaferT
import Language.Clafer.Css
import Test.Framework
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.HUnit
import Test.QuickCheck
import System.Directory
import System.IO

tg_testsuite = $(testGroupGenerator)

main = defaultMain[tg_testsuite]

checkClaferExt "dst.cfr" = True
checkClaferExt file = if ((eman == "")) then False else (txe == "rfc") && (takeWhile (/='.') (tail eman) /= "tsd")
	where (txe, eman) = span (/='.') (reverse file)

getClafers dir = do
					files <- getDirectoryContents dir
					let claferFiles = List.filter checkClaferExt files
					claferModels <- mapM (\x -> readFile (dir++"/"++x)) claferFiles
					return $ zip claferFiles claferModels
					

positiveClafers = getClafers "test/positive"



compileOneFragment :: ClaferArgs -> InputModel -> Either [ClaferErr] CompilerResult
compileOneFragment args model =
 	runClafer args $
		do
			addModuleFragment model
			parse
			compile
			generate

compiledCheck :: Either a b -> Bool
compiledCheck (Left _) = False
compiledCheck (Right _) = True

fromLeft (Left a) = a

case_compileTest :: Assertion
case_compileTest = do 
					clafers <- positiveClafers
					let compiledClafers = map (compileOneFragment defaultClaferArgs) (map snd clafers)
					mapM_ (\(file, compiled) -> when (not $ compiledCheck compiled) $ putStrLn (file ++ " Error: " ++ (show $ fromLeft compiled))) (zip (map fst clafers) compiledClafers)
					(getAll $ List.foldr mappend (All True) (map (All . compiledCheck) compiledClafers)) @? "Errors in the above claferModels from positive"