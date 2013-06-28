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


getClafers :: FilePath -> IO [(String, String)]
getClafers dir = do
					files <- getDirectoryContents dir
					let claferFiles = List.filter checkClaferExt files
					claferModels <- mapM (\x -> readFile (dir++"/"++x)) claferFiles
					return $ zip claferFiles claferModels
checkClaferExt "dst.cfr" = True
checkClaferExt file = if ((eman == "")) then False else (txe == "rfc") && (takeWhile (/='.') (tail eman) /= "esd")
	where (txe, eman) = span (/='.') (reverse file)
				
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

fromLeft :: Either a b -> a
fromLeft (Left a) = a

andMap :: (a -> Bool) -> [a] -> Bool
andMap f lst = and $ map f lst

positiveClafers = getClafers "test/positive"


case_compileTest :: Assertion
case_compileTest = do 
					clafers <- positiveClafers
					let compiledClafers = map (\(file, model) -> (file, compileOneFragment defaultClaferArgs model)) clafers
					forM_ compiledClafers (\(file, compiled) -> when (not $ compiledCheck compiled) $ putStrLn (file ++ " Error: " ++ (show $ fromLeft compiled)))
					(andMap (compiledCheck . snd) compiledClafers) @? "test/positive fail: The above claferModels did not compile."

case_refrence_Unused_Absstract_Clafer :: Assertion
case_refrence_Unused_Absstract_Clafer = do
				model <- readFile "positive/i235.cfr"
				let compiledClafers = 
					[("None", compileOneFragment defaultClaferArgs{scope_strategy = Just None} model), ("Simple", compileOneFragment defaultClaferArgs{scope_strategy = Just Simple} model), ("Full", compileOneFragment defaultClaferArgs{scope_strategy = Just Full} model)]
				forM_ compiledClafers (\(ss, compiled) -> 
					when (not $ compiledCheck compiled) $ putStrLn ("i235.cfr failed for scope_strategy = " ++ ss))
				(andMap (compiledCheck . snd) compiledClafers 
					@? "refrence_Unused_Absstract_Clafer (i235) failed, error for refrencing unused abstract clafer")