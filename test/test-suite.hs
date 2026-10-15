{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
{-
 Copyright (C) 2013-2017 Luke Brown, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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

import Suite.SimpleScopeAnalyser
import Suite.Redefinition
import Suite.TypeSystem
import Functions
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

tg_Main_Test_Suite :: TestTree
tg_Main_Test_Suite = $(testGroupGenerator)

main :: IO ()
main = defaultMain $ testGroup "Tests"
    [ tg_Test_Suite_TypeSystem
    , tg_Test_Suite_Redefinition
    , tg_Main_Test_Suite
    , tg_Test_Suite_SimpleScopeAnalyser
    ]

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
model :: String
model = "a\n    b\nb\nc\n    d\n         b\nd\n    b"

case_FQMapLookup :: Assertion
case_FQMapLookup = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs model
        qNameMaps = deriveQNameMaps iModule
    [ "c0_a" ] == getUIDs qNameMaps "::a"  @? "UID for `::a` different from `c0_a`"
    [ "c0_b" ] == getUIDs qNameMaps "::a::b"  @? "UID for `::a::b` different from `c0_b`"
    [ "c1_b" ] == getUIDs qNameMaps "::b"  @? "UID for `::b` different from `c1_b`"
    [ "c0_c" ] == getUIDs qNameMaps "::c"  @? "UID for `::c` different from `c0_c`"
    [ "c0_d" ] == getUIDs qNameMaps "::c::d"  @? "UID for `::c::d` different from `c0_d`"
    [ "c0_d" ] == getUIDs qNameMaps "c::d"  @? "UID for `c::d` different from `c0_d`"
    [ "c2_b" ] == getUIDs qNameMaps "::c::d::b"  @? "UID for `::c::d::b` different from `c2_b`"
    [ "c1_d" ] == getUIDs qNameMaps "::d"  @? "UID for `::d` different from `c1_d`"
    [ "c3_b" ] == getUIDs qNameMaps "::d::b"  @? "UID for `::d::b` different from `c3_d`"
    null ([ "c0_b", "c1_b", "c2_b", "c3_b" ] \\ (getUIDs qNameMaps "b" )) @? "UIDs for `b` different from `c0_b`, `c1_b`, `c2_b`, `c3_b` "
    null ([ "c2_b", "c3_b" ] \\ (getUIDs qNameMaps "d::b" )) @? "UIDs for `d::b` different from `c2_b`, `c3_b` "
    null ([ "c0_d", "c1_d" ] \\ (getUIDs qNameMaps "d" )) @? "UIDs for `d` different from `c0_d`, `c1_d` "
    null (getUIDs qNameMaps "x") @? "UID for `x` different from []"
    null (getUIDs qNameMaps "::x") @? "UID for `::x` different from []"

case_AllClafersGenerics :: Assertion
case_AllClafersGenerics = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs model
        allClafers :: [ IClafer ]
        allClafers = universeOn biplate iModule
        allClafersUids = map _uid allClafers
    allClafersUids == [ "c0_a", "c0_b", "c1_b", "c0_c", "c0_d", "c2_b", "c1_d", "c3_b"] @? "All clafers\n" ++ show allClafersUids

{-
An abstract clafer which no concrete clafer extends is removed, unless a
reference or a constraint names it: then it is kept, without instances.
-}
unusedAbstractModel :: String
unusedAbstractModel = "abstract Property\nabstract Unused\nabstract Named\nComponent\n    properties -> Property *\n[ no Named ]"

case_ReferencedUnusedAbstractKept :: Assertion
case_ReferencedUnusedAbstractKept = do
    let
        results = fromRight $ compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} unusedAbstractModel
        alloy = outputCode $ fromJust $ Map.lookup Alloy results
        choco = outputCode $ fromJust $ Map.lookup Choco results
    ("c0_Property = Abstract" `isInfixOf` choco) @? "Choco: the referenced Property is not declared\n" ++ choco
    ("c0_Named = Abstract" `isInfixOf` choco) @? "Choco: Named, used in a constraint, is not declared\n" ++ choco
    not ("c0_Unused" `isInfixOf` choco) @? "Choco: the unused Unused is declared\n" ++ choco
    ("abstract sig c0_Property" `isInfixOf` alloy) @? "Alloy: the referenced Property is not declared\n" ++ alloy
    ("fact { #c0_Property = 0 }" `isInfixOf` alloy) @? "Alloy: Property may have instances\n" ++ alloy
    not ("c0_Unused" `isInfixOf` alloy) @? "Alloy: the unused Unused is declared\n" ++ alloy

-- The integer range of the Choco output can be set with --minint and --maxint,
-- also in //# OPTIONS; without them, chocosolver chooses it.
case_ChocoIntRange :: Assertion
case_ChocoIntRange = do
    let
        choco args' model' = outputCode $ fromJust $ Map.lookup Choco $ fromRight $ compileOneFragment args' model'
        withOptions = "//# OPTIONS --minint=-500 --maxint=500\nx -> integer = 170\n"
    ("intRange(-500, 500);" `isInfixOf` choco defaultClaferArgs{mode = [Choco]} withOptions) @? "OPTIONS ignored"
    not ("intRange" `isInfixOf` choco defaultClaferArgs{mode = [Choco]} "x -> integer = 1\n") @? "Range set without options"
    ("intRange(-128, 100);" `isInfixOf` choco defaultClaferArgs{mode = [Choco], maxint = Just 100} "x -> integer = 1\n") @? "--maxint ignored"

-- A clafer which extends itself is reported as such, not as a missing super.
case_SelfInheritanceReported :: Assertion
case_SelfInheritanceReported =
    case compileOneFragment defaultClaferArgs "abstract A : A\nb : A" of
        Left errs' -> ("inherits from itself" `isInfixOf` show errs') @? "Unexpected errors\n" ++ show errs'
        Right _ -> assertFailure "abstract A : A compiled"
