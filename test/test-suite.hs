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
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Language.Clafer
import Language.Clafer.QNameUID

import Suite.Positive
import Suite.Negative
import Functions
import Test.HUnit
import Test.Framework
import Test.Framework.TH
import Test.Framework.Providers.HUnit

tg_Main_Test_Suite = $(testGroupGenerator)
main = defaultMain[tg_Main_Test_Suite, tg_Test_Suite_Positive, tg_Test_Suite_Negative]

{-
a            // ::a -> c0_a
    b        // ::a::b -> c0_b
b            // ::b -> c1_b
c            // ::c -> c0_c
    d        // ::c::d -> c0_d
         b   // ::c::d::b -> c2_b
d            // ::d -> c1_d
    b        // ::d::b -> c3_b

"b" -> "c0_b", "c1_b", "c2_b", "c3_b"
"d::b" -> "c2_b", "c3_b"
"c::d" -> "c0_d"
"d" -> "c0_d", "c1_d"
"x" -> []

a\n    b\nb\nc\n    d\n         b\nd\n    b
-}
case_FQMapLookup :: Assertion
case_FQMapLookup = do
	let
		(Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs "a\n    b\nb\nc\n    d\n         b\nd\n    b"
		qNameMaps = deriveQNameMaps iModule
	[ "c0_a" ] == (getUIDs qNameMaps "::a" ) @? "UID for `::a` different from `c0_a`"
	[ "c0_b" ] == (getUIDs qNameMaps "::a::b" ) @? "UID for `::a::b` different from `c0_b`"
	[ "c1_b" ] == (getUIDs qNameMaps "::b" ) @? "UID for `::b` different from `c1_b`"
	[ "c0_c" ] == (getUIDs qNameMaps "::c" ) @? "UID for `::c` different from `c0_c`"
	[ "c0_d" ] == (getUIDs qNameMaps "::c::d" ) @? "UID for `::c::d` different from `c0_d`"
	[ "c0_d" ] == (getUIDs qNameMaps "c::d" ) @? "UID for `c::d` different from `c0_d`"
	[ "c2_b" ] == (getUIDs qNameMaps "::c::d::b" ) @? "UID for `::c::d::b` different from `c2_b`"
	[ "c1_d" ] == (getUIDs qNameMaps "::d" ) @? "UID for `::d` different from `c1_d`"
	[ "c3_b" ] == (getUIDs qNameMaps "::d::b" ) @? "UID for `::d::b` different from `c3_d`"
	null ([ "c0_b", "c1_b", "c2_b", "c3_b" ] \\ (getUIDs qNameMaps "b" )) @? "UIDs for `b` different from `c0_b`, `c1_b`, `c2_b`, `c3_b` "
	null ([ "c2_b", "c3_b" ] \\ (getUIDs qNameMaps "d::b" )) @? "UIDs for `d::b` different from `c2_b`, `c3_b` "
	null ([ "c0_d", "c1_d" ] \\ (getUIDs qNameMaps "d" )) @? "UIDs for `d` different from `c0_d`, `c1_d` "	
	null (getUIDs qNameMaps "x") @? "UID for `x` different from []"
	null (getUIDs qNameMaps "::x") @? "UID for `::x` different from []"

