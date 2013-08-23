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
module Suite.Positive (tg_Test_Suite_Positive) where

import Prelude hiding (exp)
import Functions
import Language.Clafer.Intermediate.Intclafer
import Data.Foldable (foldMap)
import Data.Monoid
import Data.Maybe
import Control.Monad
import Language.Clafer
import Language.ClaferT
import qualified Test.Framework as T
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.HUnit
import qualified Data.Map as Map

tg_Test_Suite_Positive :: T.Test
tg_Test_Suite_Positive = $(testGroupGenerator)
 
positiveClaferModels :: IO [(String, String)]
positiveClaferModels = getClafers "test/positive"

case_compileTest :: Assertion
case_compileTest = do 
	claferModels <- positiveClaferModels
	let compiledClafers = map (\(file', model) -> 
		(file', compileOneFragment defaultClaferArgs model)) claferModels
	forM_ compiledClafers (\(file', compiled) -> 
		when (not $ compiledCheck compiled) $ putStrLn (file' ++ " Error: " ++ (show $ fromLeft compiled)))
	(andMap (compiledCheck . snd) compiledClafers 
		@? "test/positive fail: The above claferModels did not compile.")

case_refrence_Unused_Absstract_Clafer :: Assertion
case_refrence_Unused_Absstract_Clafer = do
	model <- readFile "test/positive/i235.cfr"
	let compiledClafers = 
		[("None", compileOneFragment defaultClaferArgs{scope_strategy = None} model), ("Simple", compileOneFragment defaultClaferArgs{scope_strategy = Simple} model)]
	forM_ compiledClafers (\(ss, compiled) -> 
		when (not $ compiledCheck compiled) $ putStrLn ("i235.cfr failed for scope_strategy = " ++ ss))
	(andMap (compiledCheck . snd) compiledClafers 
		@? "refrence_Unused_Absstract_Clafer (i235) failed, error for refrencing unused abstract clafer")

case_nonempty_Cards :: Assertion
case_nonempty_Cards = do
	claferModels <- positiveClaferModels
	let compiledClaferIrs = 
		foldMap getIR $ map (\(file', model) ->
			(file', compileOneFragment defaultClaferArgs model)) claferModels
	forM_ compiledClaferIrs (\(file', ir') ->
		let emptys = foldMapIR isEmptyCard ir'
		in when (emptys /= []) $ putStrLn (file' ++ " Error: Contains empty Card's after analysis at\n" ++ emptys))
	(andMap ((==[]) . foldMapIR isEmptyCard . snd) compiledClaferIrs
		@? "nonempty Card test failed. Files contain empty card's after fully compiling")
	where
		isEmptyCard (IRClafer (IClafer{cinPos=(Span (Pos l c) _), card = Nothing})) = "Line " ++ show l ++ " column " ++ show c ++ "\n"
		isEmptyCard (IRClafer (IClafer{cinPos=(PosSpan _ (Pos l c) _), card = Nothing})) = "Line " ++ show l ++ " column " ++ show c ++ "\n"
		isEmptyCard	_ = ""

case_stringEqual :: Assertion
case_stringEqual = do
	let strMap = stringMap $ fromRight $ compileOneFragment defaultClaferArgs "A\n    text1 : string = \"some text\"\n    text2 : string = \"some text\""
	((Map.size strMap) == 1 
		@? "Error string's assigned to differnet numbers!")

case_correctElementParents :: Assertion
case_correctElementParents = do
	claferModels <- positiveClaferModels
	let compiledClaferIrs = foldMap getIR $ map (\(file', model) -> (file', compileOneFragment defaultClaferArgs model)) claferModels
	forM_ compiledClaferIrs (\(file', ir') ->
		let parentsMatch = getAll $ foldMapIR parentCheck ir'
		in when (not $ parentsMatch) $ putStrLn (file' ++ " Error: Ir's element parents were not properly matched"))
	(andMap (getAll . foldMapIR parentCheck . snd) compiledClaferIrs 
		@? "Correct Parent test failed. Files contain non matching parents in the Ir for elements after fully compiling") 
	where
		parentCheck :: Ir -> All
		parentCheck (IRClafer clafer)
			= All $ (clafer == (iSuperParent $ super clafer)) 
				&& (clafer == (iReferenceParent $ reference clafer)) 
					&& (and $ map elementCheck $ elements clafer)
			where
				elementCheck :: IElement -> Bool
				elementCheck (IEClafer claf) = claferParent claf /= Nothing && clafer == (fromJust $ claferParent claf)
				elementCheck (IEConstraint par _ _) = par /= Nothing &&  clafer == (fromJust par)
				elementCheck (IEGoal par _ _) = par /= Nothing &&  clafer == (fromJust par)
		parentCheck _ = All True

case_correctPExpParents :: Assertion
case_correctPExpParents = do
	claferModels <- positiveClaferModels
	let compiledClaferIrs = foldMap getIR $ map (\(file', model) -> (file', compileOneFragment defaultClaferArgs model)) claferModels
	forM_ compiledClaferIrs (\(file', ir') ->
		let parentsMatch = getAll $ foldMapIR parentCheck ir'
		in when (not $ parentsMatch) $ putStrLn (file' ++ " Error: Ir's PExp parents were not properly matched"))
	(andMap (getAll . foldMapIR parentCheck . snd) compiledClaferIrs 
		@? "Correct Parent test failed. Files contain non matching parents in the Ir for PExp's after fully compiling") 
	where
		parentCheck :: Ir -> All
		parentCheck (IRPExp pexp) = 
			All $ case exp pexp of
				(IDeclPExp _ _ pexp') -> pExpParent pexp' /= Nothing && pexp == (fromJust $ pExpParent pexp')
				(IFunExp _ pexps) -> and $ flip map pexps $ \pexp' -> pExpParent pexp' /= Nothing && pexp == (fromJust $ pExpParent pexp')
				_ -> True
		parentCheck _ = All True