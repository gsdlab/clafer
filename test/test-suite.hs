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
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Control.Monad
import Language.Clafer
import Language.ClaferT
import Language.Clafer.Css
import Language.Clafer.Intermediate.Intclafer
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


getClafers :: FilePath -> IO [(String, String)] -- The first string is the file name, the second is the contents.
getClafers dir = do
					files <- getDirectoryContents dir
					let claferFiles = List.filter checkClaferExt files
					claferModels <- mapM (\x -> readFile (dir++"/"++x)) claferFiles
					return $ zip claferFiles claferModels
checkClaferExt "dst.cfr" = True
checkClaferExt file = if ((eman == "")) then False else (txe == "rfc") && (takeWhile (/='.') (tail eman) /= "tsd")
	where (txe, eman) = span (/='.') (reverse file)					

compileOneFragment :: ClaferArgs -> InputModel -> Either [ClaferErr] CompilerResult
compileOneFragment args model =
    runClafer args $
    	do
        	addModuleFragment model
        	parse
        	compile
        	generate
compileOneFragmentS :: ClaferArgs -> InputModel -> (Either [ClaferErr] CompilerResult, SnapShots)
compileOneFragmentS args model =
    runClaferS args $
    	do
        	addModuleFragment model
        	parse
        	compile
        	generate

andMap :: (a -> Bool) -> [a] -> Bool
andMap f lst = and $ map f lst

fst3 :: (a, b, c) -> a
fst3 (x,_,_) = x

positiveClafers = getClafers "test/positive"


case_numberOfSnapShots1 :: Assertion -- Make sure all snapshots are taken when debug is set to True!
case_numberOfSnapShots1 = do
	clafers <- positiveClafers
	let ssSizes = map (\(file, model) -> (file, Map.size $ snd $ compileOneFragmentS defaultClaferArgs{debug = Just True} model)) clafers
	forM_ ssSizes (\(file, ssSize) -> when(ssSize/=10) $ putStrLn (file ++ " failed, took " ++ show ssSize ++ " snapshot(s) expected 10"))
	(andMap ((==10) . snd) ssSizes) @? "Error not all snapshots were taken when debug was set to True! (For models gotten from test/positive)"

case_numberOfSnapShots2 :: Assertion -- Make sure no snapshots are taken when debug is set to False!
case_numberOfSnapShots2 = do
	clafers <- positiveClafers
	let ssSizes = map (\(file, model) -> (file, Map.size $ snd $ compileOneFragmentS defaultClaferArgs{debug = Just False} model)) clafers
	forM_ ssSizes (\(file, ssSize) -> when(ssSize/=0) $ putStrLn (file ++ " failed, took " ++ show ssSize ++ " snapshot(s) expected 0"))
	(andMap ((==0) . snd) ssSizes) @? "Error snapshots were taken when debug was set to False! (For models gotten from test/positive)"

case_IDCheck :: Assertion 
case_IDCheck = do 
	clafers <- positiveClafers
	let claferSnapshotIElements = map (\(file, model) -> (file, (Map.map (mDecls. fst3 . fromJust)) $ (Map.filter (/=Nothing)) $ (Map.map cIr) $ snd $ compileOneFragmentS defaultClaferArgs{debug = Just True} model)) clafers
	(andMap ((andMap ((andMap idCheck) . snd)) . Map.toList . snd) claferSnapshotIElements) @? "Error Clafers contain empty Parent Id's! (For models gotten from test/positive)"
	where
		idCheck (IEConstraint _ c) = (pid c) /= ""
		idCheck (IEClafer c) = andMap ((/= "") . pid) (supers $ super c) && andMap idCheck (Language.Clafer.Intermediate.Intclafer.elements c)
		idCheck _ = True