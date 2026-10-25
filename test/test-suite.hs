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
import qualified Data.Aeson as Aeson
import Data.Data.Lens
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.String (fromString)
import Language.Clafer
import Language.Clafer.QNameUID
import Language.Clafer.Front.AbsClafer (Span (..), noSpan)
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
Comments are shown as written in the HTML output: their markup is escaped, and
a //# comment, which becomes an HTML comment, cannot end it early with "--".
-}
commentsModel :: String
commentsModel = "// standalone <b>tags</b> & \"quotes\"\nA\n    B // inline <i>x</i>\n//# note -- with -->\n"

case_HtmlCommentsEscaped :: Assertion
case_HtmlCommentsEscaped = do
    let
        html = outputCode $ fromJust $ Map.lookup Html $ fromRight $ compileOneFragment defaultClaferArgs{mode = [Html], add_comments = True} commentsModel
    ("// standalone &lt;b&gt;tags&lt;/b&gt; &amp; &quot;quotes&quot;" `isInfixOf` html) @? "The standalone comment is not escaped\n" ++ html
    ("// inline &lt;i&gt;x&lt;/i&gt;" `isInfixOf` html) @? "The inline comment is not escaped\n" ++ html
    not ("<b>" `isInfixOf` html || "<i>" `isInfixOf` html) @? "Markup from a comment is in the HTML\n" ++ html
    ("<!-- # note - - with - -> /-->" `isInfixOf` html) @? "The //# comment contains \"--\"\n" ++ html

{-
Clafer names may contain apostrophes, but the UIDs are identifiers in the Alloy
and Choco (JavaScript) outputs, where apostrophes are not allowed: they become
"__prime__", and same' and same__prime__ still get different UIDs.
-}
apostropheModel :: String
apostropheModel = "A\n    same' ?\n    same__prime__ ?\n    links' -> same' *\n    [ some same' ]\n"

case_ApostrophesNotInUIDs :: Assertion
case_ApostrophesNotInUIDs = do
    let
        results = fromRight $ compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} apostropheModel
        alloy = outputCode $ fromJust $ Map.lookup Alloy results
        choco = outputCode $ fromJust $ Map.lookup Choco results
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy results
        clafers :: [ IClafer ]
        clafers = universeOn biplate iModule
        uidsOf name = [ _uid c | c <- clafers, _ident c == name ]
    uidsOf "same'" == ["c0_same__prime__"] @? "UID of same' is not c0_same__prime__: " ++ show (uidsOf "same'")
    uidsOf "same__prime__" == ["c1_same__prime__"] @? "UID of same__prime__ is not c1_same__prime__: " ++ show (uidsOf "same__prime__")
    uidsOf "links'" == ["c0_links__prime__"] @? "UID of links' is not c0_links__prime__: " ++ show (uidsOf "links'")
    not ("c0_same'" `isInfixOf` alloy) @? "Alloy: an apostrophe in a UID\n" ++ alloy
    ("sig c0_same__prime__" `isInfixOf` alloy && "sig c1_same__prime__" `isInfixOf` alloy) @? "Alloy: same' and same__prime__ are not two signatures\n" ++ alloy
    not ("c0_same'" `isInfixOf` choco) @? "Choco: an apostrophe in a UID\n" ++ choco
    ("c0_same__prime__ = c0_A.addChild(\"c0_same__prime__\")" `isInfixOf` choco) @? "Choco: same' is not declared as c0_same__prime__\n" ++ choco

{-
The JSON IR has the source positions of the clafers and expressions: lines and
columns from 1, with an exclusive end; a tab advances to the next column 8k+1.
-}
positionsModel :: String
positionsModel = "A\n  b ?\nC\n\td ?\n[ some b ]\n"

case_JsonPositions :: Assertion
case_JsonPositions = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs positionsModel
        clafers :: [ IClafer ]
        clafers = universeOn biplate iModule
        posOf name = [ Aeson.toJSON $ _cinPos c | c <- clafers, _ident c == name ]
        constraintPos = [ Aeson.toJSON $ _inPos e | IEConstraint _ e <- _mDecls iModule ]
        jsonSpan (l1, c1) (l2, c2) = Aeson.object [ (fromString "start", jsonPos l1 c1), (fromString "end", jsonPos l2 c2) ]
        jsonPos :: Integer -> Integer -> Aeson.Value
        jsonPos l c = Aeson.object [ (fromString "line", Aeson.toJSON l), (fromString "column", Aeson.toJSON c) ]
    posOf "b" == [ jsonSpan (2, 3) (2, 6) ] @? "Position of b: " ++ show (posOf "b")
    posOf "d" == [ jsonSpan (4, 9) (4, 12) ] @? "Position of d, indented with a tab: " ++ show (posOf "d")
    constraintPos == [ jsonSpan (5, 3) (5, 9) ] @? "Position of the constraint: " ++ show constraintPos
    Aeson.toJSON noSpan == Aeson.Null @? "noSpan is not null"

{-
Comments do not count in the layout: a line which starts with a comment is
indented as if the comment was not there, at the column where it starts. The
positions of the clafers are unchanged.
-}
commentLayoutModel :: String
commentLayoutModel = "A\n  /*history*/ xor on\n    normal\n    flashing\n  /*history*/ off\n      // further right\n  B /* trailing */\n/* a block\n   comment */ C\n"

case_CommentsNotInLayout :: Assertion
case_CommentsNotInLayout = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs commentLayoutModel
        clafers :: [ IClafer ]
        clafers = universeOn biplate iModule
        parentOf name = [ _parentUID c | c <- clafers, _ident c == name ]
        startOf name = [ (l, c') | c <- clafers, _ident c == name, let Span (Pos l c') _ = _cinPos c ]
    map parentOf ["on", "normal", "flashing", "off", "B", "C"] == map (:[]) ["c0_A", "c0_on", "c0_on", "c0_A", "c0_A", "root"]
        @? "Wrong nesting: " ++ show (map parentOf ["on", "normal", "flashing", "off", "B", "C"])
    startOf "on" == [(2, 15)] @? "Position of on changed: " ++ show (startOf "on")

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
