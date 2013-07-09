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
import Language.Clafer.Intermediate.Intclafer
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe
import Data.Foldable (foldMap)
import Data.Monoid
import Control.Monad
import Language.Clafer
import Language.ClaferT
import Language.Clafer.Css
import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import qualified Language.Clafer.Intermediate.Intclafer as I
import Test.Framework
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.HUnit
import Test.QuickCheck
import System.Directory
import System.IO

tg_testsuite = $(testGroupGenerator) -- Test Case
main = defaultMain[tg_testsuite]     -- Generator

{-Helper Functions-}
---------------------
getClafers :: FilePath -> IO [(String, String)] -- The first string is the file name, the second is the contents.
getClafers dir = do
					files <- getDirectoryContents dir
					let claferFiles = List.filter checkClaferExt files
					claferModels <- mapM (\x -> readFile (dir++"/"++x)) claferFiles
					return $ zip claferFiles claferModels
checkClaferExt "dst.cfr" = True
checkClaferExt file = if ((eman == "")) then False else (txe == "rfc") && (takeWhile (/='.') (tail eman) /= "sed")
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

compiledCheck :: Either a b -> Bool
compiledCheck (Left _) = False
compiledCheck (Right _) = True

fromLeft :: Either a b -> a
fromLeft (Left a) = a

andMap :: (a -> Bool) -> [a] -> Bool
andMap f lst = and $ map f lst

lukesRule :: I.PExp -> Bool -- empty PID <=> noSpan
lukesRule p = ((I.pid p)/="" && (I.inPos p)/=noSpan) || ((I.pid p)=="" && (I.inPos p)==noSpan)

positiveClaferModels :: IO [(String, String)] -- IO [(File, Contents)]
positiveClaferModels = getClafers "test/positive"


{-Test Cases-}
---------------

case_compileTest :: Assertion -- Tests to check all files in test/positive compile
case_compileTest = do 
	claferModels <- positiveClaferModels
	let compiledClafers = map (\(file, model) -> 
		(file, compileOneFragment defaultClaferArgs model)) claferModels
	forM_ compiledClafers (\(file, compiled) -> 
		when (not $ compiledCheck compiled) $ putStrLn (file ++ " Error: " ++ (show $ fromLeft compiled)))
	(andMap (compiledCheck . snd) compiledClafers 
		@? "test/positive fail: The above claferModels did not compile.")

case_refrence_Unused_Absstract_Clafer :: Assertion -- Test to make sure i235 compiles for both ss = none / Simple
case_refrence_Unused_Absstract_Clafer = do
	model <- readFile "test/positive/i235.cfr"
	let compiledClafers = 
		[("None", compileOneFragment defaultClaferArgs{scope_strategy = None} model), ("Simple", compileOneFragment defaultClaferArgs{scope_strategy = Simple} model)]
	forM_ compiledClafers (\(ss, compiled) -> 
		when (not $ compiledCheck compiled) $ putStrLn ("i235.cfr failed for scope_strategy = " ++ ss))
	(andMap (compiledCheck . snd) compiledClafers 
		@? "refrence_Unused_Absstract_Clafer (i235) failed, error for refrencing unused abstract clafer")

case_nonemptyCards :: Assertion
case_nonemptyCards = do
	claferModels <- positiveClaferModels
	let compiledClafeIrs = foldMap getIR $ map (\(file, model) -> (file, compileOneFragment defaultClaferArgs model)) claferModels
	forM_ compiledClafeIrs (\(file, ir) ->
		let emptys = foldMapIR isEmptyCard ir
		in when (emptys /= []) $ putStrLn (file ++ " Error: Contains empty Card's after analysis at\n" ++ emptys))
	(andMap ((/=[]) . foldMapIR isEmptyCard . snd) compiledClafeIrs
		@? "nonempty Card test failed. Files contain empty card's after fully compiling")
	where
		getIR (file, (Right (CompilerResult{claferEnv = ClaferEnv{cIr = Just (iMod, _, _)}}))) = [(file, iMod)]
		getIR _ = []
		isEmptyCard (IRClafer (IClafer{cinPos=(Span (Pos l c) _), card = Nothing})) = "Line " ++ show l ++ " column " ++ show c ++ "\n"
		isEmptyCard (IRClafer (IClafer{cinPos=(PosSpan _ (Pos l c) _), card = Nothing})) = "Line " ++ show l ++ " column " ++ show c ++ "\n"
		isEmptyCard	_ = ""

case_numberOfSnapShots1 :: Assertion -- Make sure all snapshots are taken when debug is set to True!
case_numberOfSnapShots1 = do
	claferModels <- positiveClaferModels
	let ssSizes = map (\(file, model) -> 
		(file, Map.size $ snd $ compileOneFragmentS defaultClaferArgs{debug = True} model)) claferModels
	forM_ ssSizes (\(file, ssSize) -> 
		when(ssSize/=numberOfSS) $ putStrLn (file ++ " failed, took " ++ show ssSize ++ " snapshot(s) expected " ++ show numberOfSS))
	(andMap ((==numberOfSS) . snd) ssSizes 
		@? "Failed, not all snapshots were taken when debug was set to True!\n Did you remeber to update the total number of snapshots after adding new snapshot? (For models gotten from test/positive)")

case_numberOfSnapShots2 :: Assertion -- Make sure no snapshots are taken when debug is set to False!
case_numberOfSnapShots2 = do
	claferModels <- positiveClaferModels
	let ssSizes = map (\(file, model) -> 
		(file, Map.size $ snd $ compileOneFragmentS defaultClaferArgs{debug = False} model)) claferModels
	forM_ ssSizes (\(file, ssSize) -> 
		when(ssSize/=0) $ putStrLn (file ++ " failed, took " ++ show ssSize ++ " snapshot(s) expected 0"))
	(andMap ((==0) . snd) ssSizes 
		@? "Failed, snapshots were taken when debug was set to False! (For models gotten from test/positive)")

case_IDCheck :: Assertion -- Make sure all non empty parent ID's are unique and all Parent ID's pass lukesRule
case_IDCheck = do
	claferModels <- positiveClaferModels
	let claferSnapShotPids = map (\(file, model) -> 
		(file, Map.toList $ (Map.map (foldMapIR getPids . fst3 . fromJust)) $ (Map.filter (/=Nothing)) $ (Map.map cIr) $ snd $ compileOneFragmentS defaultClaferArgs{debug = True} model)) claferModels
	forM_ claferSnapShotPids (\(file, mMap) -> 
		when (not $ (andMap (\x -> ((filter (/="") $ (map I.pid) $ snd x)==(filter (/="") $ List.nub $ (map I.pid) $ snd x))) mMap)) $ do
			putStrLn ("Duplicate Parent Id's in " ++ file ++ ", Failed at stage(s)\n")
			forM_ mMap (\(ssID, pMap) -> 
				when ((filter (/="") $ map I.pid pMap) /= (filter (/="") $ List.nub $ map I.pid pMap)) $ do
					putStrLn (show ssID)
					printDups pMap)
			putStrLn "")
	forM_ claferSnapShotPids (\(file, mMap) ->
		when (not $ andMap ((andMap lukesRule) . snd) mMap) $ do
			putStrLn ("Failed lukesRule (empty PID <=> noSpan) at stage(s)\n")
			forM_ mMap (\(ssID, pMap) -> 
				when (not $ (andMap lukesRule pMap)) $ do
					putStrLn (show ssID)
					printFails pMap)
			putStrLn "")
	let dupResult = andMap (andMap (\x -> ((filter (/="") x)==(filter (/="") (List.nub x))))) (map  (\x -> (map ((map I.pid) . snd)) $ snd x) claferSnapShotPids)
	let lukesResult = andMap  ((andMap ((andMap lukesRule) . snd)) . snd) claferSnapShotPids
	(dupResult && lukesResult @? 
		(errorMsg lukesResult dupResult) ++ "(For models gotten from test/positive)")
	where
		getPids :: Ir -> [PExp]
		getPids (I.IRPExp p) = [p]
		getPids _ = []
		printDups :: [I.PExp] -> IO ()
		printDups (p1:ps) = do
			when ((I.pid p1) /= "" && (I.pid p1) `elem` (map I.pid ps)) $ do
				putStr ("   The PID " ++ show p1 ++ "\thas duplicates with ")
				forM_ ps (\p2 -> when ((I.pid p1)==(I.pid p2)) $ putStr ((I.pid p2) ++ " "))	
				putStrLn ""
			printDups ps
		printDups [] = putStrLn ""
		printFails :: [I.PExp] -> IO ()
		printFails (p:ps) = do
			when (not $ lukesRule p) $ 
				putStrLn ("   " ++ show p ++ " failed lukesRule (empty PID <=> noSpan)") 
			printFails ps
		printFails [] = putStrLn ""
		errorMsg :: Bool -> Bool -> String
		errorMsg True False = "Failed, Clafers PExp's non empty Parent Id's are not unique! "
		errorMsg False True = "Failed, Clafers PExp's don't pass lukeRule where empty PID <=> noSpan! "
		errorMsg False False = "Failed, Clafers PExp's don't pass lukeRule where empty PID <=> noSpan and non empty Parent Id's are not unique! "