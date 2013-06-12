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
import Language.Clafer.Common
import qualified Language.Clafer.Intermediate.Intclafer as I
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

andMap :: (a -> Bool) -> [a] -> Bool
andMap f lst = and $ map f lst

positiveClaferModels :: IO [(String, String)] -- IO [(File, Contents)]
positiveClaferModels = getClafers "test/positive"


case_numberOfSnapShots1 :: Assertion -- Make sure all snapshots are taken when debug is set to True!
case_numberOfSnapShots1 = do
	claferModels <- positiveClaferModels
	let ssSizes = map (\(file, model) -> 
		(file, Map.size $ snd $ compileOneFragmentS defaultClaferArgs{debug = Just True} model)) claferModels
	forM_ ssSizes (\(file, ssSize) -> 
		when(ssSize/=11) $ putStrLn (file ++ " failed, took " ++ show ssSize ++ " snapshot(s) expected 11"))
	(andMap ((==11) . snd) ssSizes) @? "Error not all snapshots were taken when debug was set to True! (For models gotten from test/positive)"

case_numberOfSnapShots2 :: Assertion -- Make sure no snapshots are taken when debug is set to False!
case_numberOfSnapShots2 = do
	claferModels <- positiveClaferModels
	let ssSizes = map (\(file, model) -> 
		(file, Map.size $ snd $ compileOneFragmentS defaultClaferArgs{debug = Just False} model)) claferModels
	forM_ ssSizes (\(file, ssSize) -> 
		when(ssSize/=0) $ putStrLn (file ++ " failed, took " ++ show ssSize ++ " snapshot(s) expected 0"))
	(andMap ((==0) . snd) ssSizes) @? "Error snapshots were taken when debug was set to False! (For models gotten from test/positive)"

case_IDCheck :: Assertion -- Make sure none of the parent ID's are empty
case_IDCheck = do 
	claferModels <- positiveClaferModels
	let claferSnapshotResults = map (\(file, model) -> 
		(file, Map.toList $ (Map.map ((andMap idCheck) . I.mDecls. fst3 . fromJust)) $ (Map.filter (/=Nothing)) $ (Map.map cIr) $ snd $ compileOneFragmentS defaultClaferArgs{debug = Just True} model)) claferModels
	forM_ claferSnapshotResults (\(file,mMap) -> when (not $ andMap snd mMap) $ do 
		putStrLn ("Empty Parent Id in " ++ file ++ ", Failed at stage(s)")
		forM_ mMap (\(ssID, result) -> when (not result) $ putStrLn ("   " ++ show ssID)))
	(andMap ((andMap snd) . snd) claferSnapshotResults) @? "Error Clafers contain empty Parent Id's! (For models gotten from test/positive)"
	where
		idCheck :: I.IElement -> Bool
		idCheck (I.IEConstraint _ c) = ((I.pid c) /= "") && (iexpCheck $ I.exp c)
		idCheck (I.IEClafer c) = andMap (iexpCheck . I.exp) (I.supers $ I.super c) && andMap ((/= "") . I.pid) (I.supers $ I.super c) && andMap idCheck (I.elements c)
		idCheck _ = True
		iexpCheck :: I.IExp -> Bool
		iexpCheck (I.IDeclPExp _ o b) = andMap ((/="") . I.pid . I.body) o && andMap (iexpCheck . I.exp . I.body) o && ((I.pid b) /= "") && (iexpCheck $ I.exp b)
		iexpCheck (I.IFunExp _ p) = andMap ((/="") . I.pid) p && andMap (iexpCheck . I.exp) p
		iexpCheck _ = True

case_IDUnique :: Assertion -- Make sure all parent ID's are unique 
case_IDUnique = do
	claferModels <- positiveClaferModels
	let claferSnapShotPids = map (\(file, model) -> 
		(file, Map.toList $ (Map.map (getPidsEle . I.mDecls . fst3 . fromJust)) $ (Map.filter (/=Nothing)) $ (Map.map cIr) $ snd $ compileOneFragmentS defaultClaferArgs{debug = Just True} model)) claferModels
	forM_ claferSnapShotPids (\(file, mMap) -> 
		when (not $ (andMap (\x -> (((map snd) $ snd x)==(List.nub $ (map snd) $ snd x))) mMap)) $ do
			putStrLn ("Duplicate Parent Id's in " ++ file ++ ", Failed at stage(s)\n")
			forM_ mMap (\(ssID, pMap) -> when (pMap /= (List.nub pMap)) $ do
				putStrLn (show ssID)
				printDups pMap)
			putStrLn "")
	let pIDs = (map  (\x -> (map ((map snd) . snd)) $ snd x) claferSnapShotPids)
	(andMap (andMap (\x -> (x==(List.nub x)))) pIDs 
		@? "Error Clafers contain non unique Parent ID's! (For models gotten from test/positive)")
	where
		getPidsEle :: [I.IElement] -> [(String, String)] -- [(GeneratedName, PID)]
		getPidsEle ((I.IEConstraint _ (I.PExp t p s i)):es) = ((genPExpName t s i), p) : (getPidsExp i) ++ (getPidsEle es)
		getPidsEle ((I.IEClafer c):es) = (join $ map (\p -> ((genPExpName (I.iType p) (I.inPos p) (I.exp p)),(I.pid p)):(getPidsExp (I.exp p))) (I.supers $ I.super c)) ++ (getPidsEle $ I.elements c) ++ (getPidsEle es)
		getPidsEle ((I.IEGoal _ (I.PExp t p s i)):es) = ((genPExpName t s i), p) : (getPidsExp i) ++ (getPidsEle es)
		getPidsEle [] = []
		getPidsExp :: I.IExp -> [(String, String)] -- [(GeneratedName, PID)]
		getPidsExp (I.IDeclPExp _ o (I.PExp t p s i)) = ((genPExpName t s i), p) : (map (\x -> ((genPExpName (I.iType $ I.body x) (I.inPos $ I.body x) (I.exp $ I.body x)), (I.pid $ I.body x))) o) ++ (join $ map (getPidsExp . I.exp . I.body) o) ++ (getPidsExp i)
		getPidsExp (I.IFunExp _ p) = map (\x -> ((genPExpName (I.iType x) (I.inPos x) (I.exp x)), (I.pid x))) p ++ (join $ map (getPidsExp . I.exp) p)
		getPidsExp _ = []
		printDups :: [(String, String)] -> IO () -- [(GeneratedName, PID) -> IO ()]
		printDups ((x,y):xs) = do
			when (y `elem` (map snd xs)) $ do
				putStr ("   The PID " ++ y ++ "\thas duplicates for " ++ x ++ " ")
				forM_ xs (\(u,w) -> when (w==y) $ putStr (u ++ " "))	
				putStrLn ""
			printDups xs
		printDups [] = putStrLn ""