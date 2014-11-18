{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
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
import Control.Lens
import Data.Data.Lens
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Language.Clafer
import Language.Clafer.QNameUID
import Language.Clafer.Intermediate.Intclafer

import Suite.Positive
import Suite.Negative
import Suite.SimpleScopeAnalyser
import Functions
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

tg_Main_Test_Suite :: TestTree
tg_Main_Test_Suite = $(testGroupGenerator)

main :: IO ()
main = defaultMain $ testGroup "Tests" [tg_Main_Test_Suite, tg_Test_Suite_Positive, tg_Test_Suite_Negative, tg_Test_Suite_SimpleScopeAnalyser]

{-
a            // ::a -> c1_a
    b        // ::a::b -> c2_b
b            // ::b -> c5_b
c            // ::c -> c7_c
    d        // ::c::d -> c8_d
         b   // ::c::d::b -> c9_b
d            // ::d -> c13_d
    b        // ::d::b -> c14_b

"b" -> "c2_b", "c5_b", "c9_b", "c14_b"
"d::b" -> "c9_b", "c14_b"
"c::d" -> "c8_d"
"d" -> "c8_d", "c13_d"
"x" -> []

a\n    b\nb\nc\n    d\n         b\nd\n    b
-}
model :: String
model = "a\n    b\nb\nc\n    d\n         b\nd\n    b"

case_FQMapLookup :: Assertion
case_FQMapLookup = do
	let
		(Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs model
		qNameMaps = deriveQNameMaps iModule
	[ "c1_a" ] == getUIDs qNameMaps "::a"  @? "UID for `::a` different from `c1_a`"
	[ "c2_b" ] == getUIDs qNameMaps "::a::b"  @? "UID for `::a::b` different from `c2_b`"
	[ "c5_b" ] == getUIDs qNameMaps "::b"  @? "UID for `::b` different from `c5_b`"
	[ "c7_c" ] == getUIDs qNameMaps "::c"  @? "UID for `::c` different from `c7_c`"
	[ "c8_d" ] == getUIDs qNameMaps "::c::d"  @? "UID for `::c::d` different from `c8_d`"
	[ "c8_d" ] == getUIDs qNameMaps "c::d"  @? "UID for `c::d` different from `c8_d`"
	[ "c9_b" ] == getUIDs qNameMaps "::c::d::b"  @? "UID for `::c::d::b` different from `c9_b`"
	[ "c13_d" ] == getUIDs qNameMaps "::d"  @? "UID for `::d` different from `c13_d`"
	[ "c14_b" ] == getUIDs qNameMaps "::d::b"  @? "UID for `::d::b` different from `c14_b`"
	null ([ "c2_b", "c5_b", "c9_b", "c14_b" ] \\ (getUIDs qNameMaps "b" )) @? "UIDs for `b` different from 'c2_b', 'c3_b', 'c6_b', 'c14_b' "
	null ([ "c9_b", "c14_b" ] \\ (getUIDs qNameMaps "d::b" )) @? "UIDs for `d::b` different from `c6_b`, `c14_b` "
	null ([ "c8_d", "c13_d" ] \\ (getUIDs qNameMaps "d" )) @? "UIDs for `d` different from `c8_d`, `c7_d` "	
	null (getUIDs qNameMaps "x") @? "UID for `x` different from []"
	null (getUIDs qNameMaps "::x") @? "UID for `::x` different from []"

case_AllClafersGenerics :: Assertion
case_AllClafersGenerics = do
	let
		(Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs model
		allClafers :: [ IClafer ]
		allClafers = universeOn biplate iModule
		allClafersUids = map _uid allClafers
	allClafersUids == [ "c1_a", "c2_b", "c5_b", "c7_c", "c8_d", "c9_b", "c13_d", "c14_b"] @? "All clafers\n" ++ show allClafersUids