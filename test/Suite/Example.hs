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
module Suite.Example (tg_Test_Suite_Example) where

import qualified Data.List as List
import qualified Data.Map as Map
import Data.Monoid
import Control.Monad
import Language.Clafer
import Language.Clafer.Css
import Test.Framework
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.HUnit
import Test.QuickCheck
import Language.Clafer.ClaferArgs
import Control.Monad
import System.Directory
import System.IO
import Functions

tg_Test_Suite_Example = $(testGroupGenerator)

case_1 :: Assertion
case_1 = assertEqual "for luckynumber" "WIN!" (luckynumber 42)

case_2 :: Assertion
case_2 =
	do 
		let a = luckynumber 7
		assertEqual "for luckynumber" "WIN!" a
		let b = (luckynumber 2) == (luckynumber 4)
		assertBool ("Falied! Lucky number must be either 2 or 4") b

case_3 = assertString "This will always fail :("

prop_4 :: [Int] -> Bool
prop_4 xs = reverse (reverse xs) == xs

prop_5 :: [Int] -> Property 
prop_5 xs = (length xs) >= 5 ==> (length (take 5 xs)) == 5 
	where types = (xs :: [Int])

case_6 :: Assertion
case_6 = List.sort [1,8,6,5,3,9,0,2,4,10] @?= [0..9]

case_7 = 
	do
		False @? "Always fails =("
		True @? "You will never see this msg =D"
		[0..9] @=? List.sort [1,8,6,5,3,9,0,2,4,10]

case_8 = assertString ""

prop_9 x = 	x >= 5 ==>
			x <= 10 ==>
			luckynumber x == "LOSE!"
	where types = (x :: Int)


case_10 :: Assertion
case_10 = do 
	let e1 = fromRight $ fmap claferEnv $ compileOneFragment defaultClaferArgs "A"
	let e2 = fromRight $ fmap claferEnv $ compileOneFragment defaultClaferArgs "B"
	assertBool ("This shouldn't fail") (e1 == e1)
	assertBool ("This should fail") (e1 == e2)

case_11 :: Assertion
case_11 = do
			clafers <- positiveClafers
			getAll (List.foldr (\x -> mappend (All $ x==x)) (All True) clafers) @? "Error in one of clafers"

--Example of generator
newtype ArbitraryClafer = ArbitraryClafer {getModel :: String} deriving Show

instance Arbitrary ArbitraryClafer where
	arbitrary = do 
					clafers <- getClafers "positive"
					clafer <- elements clafers
					return $ ArbitraryClafer clafer


prop_12 :: ArbitraryClafer -> Bool
prop_12 model = (getModel model) == (getModel model)


luckynumber :: Int -> Bool
luckynumber 7 = True
luckynumber _ = False