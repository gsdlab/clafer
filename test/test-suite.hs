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
import Control.Monad (forM_)
import qualified Data.Aeson as Aeson
import Data.Data.Lens
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.String (fromString)
import Language.Clafer
import Language.Clafer.Import
import Language.Clafer.QNameUID
import Language.Clafer.ClaferArgs (ClaferMode (Clafer))
import Language.Clafer.Front.AbsClafer (Span (..), noSpan)
import Language.Clafer.Intermediate.Intclafer
import Language.ClaferT (CErr (..), ErrPos (..), modifyEnv)
import Language.Clafer.Generator.Html (highlightErrorsIn)
import Language.Clafer.Generator.Explicit (withoutOrigins)

import Network.URI (parseURI)
import Network.Socket (tupleToHostAddress)
import System.Directory (createDirectoryIfMissing, createDirectoryLink, createFileLink, getTemporaryDirectory, removeDirectoryRecursive, removePathForcibly)

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
The UID of each clafer is its least-partially-qualified name:

a            // root__a, ::a -> a
    b        // root__a__b, ::a::b -> a__b
b            // root__b, ::b -> root__b
c            // root__c, ::c -> c
    d        // root__c__d, ::c::d -> c__d
         b   // root__c__d__b, ::c::d::b -> c__d__b
d            // root__d, ::d -> root__d
    b        // root__d__b, ::d::b -> root__d__b

"b" -> "a__b", "root__b", "c__d__b", "root__d__b"
"d::b", "d__b" -> "c__d__b", "root__d__b"
"c::d", "c__d" -> "c__d"
"d" -> "c__d", "root__d"
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
    [ "a" ] == getUIDs qNameMaps "::a"  @? "UID for `::a` different from `a`"
    [ "a__b" ] == getUIDs qNameMaps "::a::b"  @? "UID for `::a::b` different from `a__b`"
    [ "root__b" ] == getUIDs qNameMaps "::b"  @? "UID for `::b` different from `root__b`"
    [ "c" ] == getUIDs qNameMaps "::c"  @? "UID for `::c` different from `c`"
    [ "c__d" ] == getUIDs qNameMaps "::c::d"  @? "UID for `::c::d` different from `c__d`"
    [ "c__d" ] == getUIDs qNameMaps "c::d"  @? "UID for `c::d` different from `c__d`"
    [ "c__d__b" ] == getUIDs qNameMaps "::c::d::b"  @? "UID for `::c::d::b` different from `c__d__b`"
    [ "root__d" ] == getUIDs qNameMaps "::d"  @? "UID for `::d` different from `root__d`"
    [ "root__d__b" ] == getUIDs qNameMaps "::d::b"  @? "UID for `::d::b` different from `root__d__b`"
    null ([ "a__b", "root__b", "c__d__b", "root__d__b" ] \\ (getUIDs qNameMaps "b" )) @? "UIDs for `b` different from `a__b`, `root__b`, `c__d__b`, `root__d__b`"
    null ([ "c__d__b", "root__d__b" ] \\ (getUIDs qNameMaps "d::b" )) @? "UIDs for `d::b` different from `c__d__b`, `root__d__b`"
    null ([ "c__d", "root__d" ] \\ (getUIDs qNameMaps "d" )) @? "UIDs for `d` different from `c__d`, `root__d`"
    -- the same with __, the separator of the UIDs, and root__ for ::
    [ "a" ] == getUIDs qNameMaps "root__a"  @? "UID for `root__a` different from `a`"
    [ "root__b" ] == getUIDs qNameMaps "root__b"  @? "UID for `root__b` different from `root__b`"
    [ "c__d" ] == getUIDs qNameMaps "c__d"  @? "UID for `c__d` different from `c__d`"
    [ "c__d__b" ] == getUIDs qNameMaps "root__c__d__b"  @? "UID for `root__c__d__b` different from `c__d__b`"
    null ([ "c__d__b", "root__d__b" ] \\ (getUIDs qNameMaps "d__b" )) @? "UIDs for `d__b` different from `c__d__b`, `root__d__b`"
    Just "root__c__d__b" == getFQName qNameMaps "c__d__b"  @? "FQ name of `c__d__b`: " ++ show (getFQName qNameMaps "c__d__b")
    Just "root__d" == getLPQName qNameMaps "root__d"  @? "LPQ name of `root__d`: " ++ show (getLPQName qNameMaps "root__d")
    null (getUIDs qNameMaps "x") @? "UID for `x` different from []"
    null (getUIDs qNameMaps "::x") @? "UID for `::x` different from []"

-- | A name that is a prefix of another name does not match it
case_QNamesWholeNames :: Assertion
case_QNamesWholeNames = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs "light\n    yellow\n    yellow_on\n"
        qNameMaps = deriveQNameMaps iModule
    [ "yellow" ] == getUIDs qNameMaps "yellow"  @? "UIDs for `yellow`: " ++ show (getUIDs qNameMaps "yellow")
    [ "yellow" ] == getUIDs qNameMaps "light::yellow"  @? "UIDs for `light::yellow`: " ++ show (getUIDs qNameMaps "light::yellow")
    [ "yellow" ] == getUIDs qNameMaps "light__yellow"  @? "UIDs for `light__yellow`: " ++ show (getUIDs qNameMaps "light__yellow")
    Just "yellow" == getLPQName qNameMaps "yellow"  @? "LPQ name of `yellow`: " ++ show (getLPQName qNameMaps "yellow")

case_AllClafersGenerics :: Assertion
case_AllClafersGenerics = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs model
        allClafers :: [ IClafer ]
        allClafers = universeOn biplate iModule
        allClafersUids = map _uid allClafers
    allClafersUids == [ "a", "a__b", "root__b", "c", "c__d", "c__d__b", "root__d", "root__d__b"] @? "All clafers\n" ++ show allClafersUids

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
Clafer names may contain apostrophes, but the UIDs are identifiers, in Clafer and in
the Alloy and Choco (JavaScript) outputs: an apostrophe becomes "_prime". same'
and same_prime still get different UIDs: the one later in the model gets __2.
-}
apostropheModel :: String
apostropheModel = "A\n    same' ?\n    same_prime ?\n    links' -> same' *\n    [ some same' ]\n"

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
    uidsOf "same'" == ["same_prime"] @? "UID of same' is not same_prime: " ++ show (uidsOf "same'")
    uidsOf "same_prime" == ["same_prime__2"] @? "UID of same_prime is not same_prime__2: " ++ show (uidsOf "same_prime")
    uidsOf "links'" == ["links_prime"] @? "UID of links' is not links_prime: " ++ show (uidsOf "links'")
    not ("same'" `isInfixOf` alloy) @? "Alloy: an apostrophe in a UID\n" ++ alloy
    ("sig same_prime" `isInfixOf` alloy && "sig same_prime__2" `isInfixOf` alloy) @? "Alloy: same' and same_prime are not two signatures\n" ++ alloy
    not ("same'" `isInfixOf` choco) @? "Choco: an apostrophe in a UID\n" ++ choco
    ("$same_prime = $A.addChild(\"same_prime\")" `isInfixOf` choco) @? "Choco: same' is not declared as same_prime\n" ++ choco

{-
The UIDs do not depend on the outputs: a clafer named sig (an Alloy keyword) or show (the
Alloy output's predicate) keeps its UID, and so does r_x next to x (r_x is the relation of x);
the Alloy output renames them, and the variables of the Choco output are $ and the UID.
-}
alloyNamesModel :: String
alloyNamesModel = "sig ?\nshow ?\nx\nr_x ?\n[ some sig => some show ]\n"

case_UIDsNotOfTheOutputs :: Assertion
case_UIDsNotOfTheOutputs = do
    let
        results = fromRight $ compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} alloyNamesModel
        alloy = outputCode $ fromJust $ Map.lookup Alloy results
        choco = outputCode $ fromJust $ Map.lookup Choco results
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy results
        uids = map _uid (universeOn biplate iModule :: [ IClafer ])
    uids == ["sig", "show", "x", "r_x"] @? "UIDs: " ++ show uids
    all (`isInfixOf` alloy) ["lone sig sig_1", "lone sig show_1", "one sig x", "lone sig r_x_1", "(some sig_1) => (some show_1)"]
        @? "Alloy: the clafers are not renamed\n" ++ alloy
    not ("sig sig\n" `isInfixOf` alloy) @? "Alloy: a signature named sig\n" ++ alloy
    all (`isInfixOf` choco) ["$sig = Clafer(\"sig\")", "$show = Clafer(\"show\")", "$r_x = Clafer(\"r_x\")"]
        @? "Choco: the clafers are not declared by their UIDs\n" ++ choco

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
    map parentOf ["on", "normal", "flashing", "off", "B", "C"] == map (:[]) ["A", "on", "on", "A", "A", "root"]
        @? "Wrong nesting: " ++ show (map parentOf ["on", "normal", "flashing", "off", "B", "C"])
    startOf "on" == [(2, 15)] @? "Position of on changed: " ++ show (startOf "on")

{-
A group cardinality whose lower bound the children cannot reach is an error.
The children include the inherited ones, and the group cardinality may be
inherited or redefined: myGroup's 2..2 is satisfiable with d and the inherited
a, b and c. An abstract clafer's group may get its children from subclafers.
-}
groupsModel :: String
groupsModel = "abstract or SuperGroup\n   a ?\n   b ?\n   c ?\n\n2..2 myGroup : SuperGroup\n   d ?\n\nabstract xor Empty\nfilled : Empty\n   e ?\n   f ?\n"

case_UnsatisfiableGroupRejected :: Assertion
case_UnsatisfiableGroupRejected = do
    let
        compiles model' = either (const False) (const True) $ compileOneFragment defaultClaferArgs model'
        errorsOf model' = either show (const "") $ compileOneFragment defaultClaferArgs model'
    compiles groupsModel @? "Inherited children are not counted\n" ++ errorsOf groupsModel
    ("of Mode cannot be satisfied" `isInfixOf` errorsOf "Phone\n   xor Mode\n") @? "xor over no children compiled: " ++ errorsOf "Phone\n   xor Mode\n"
    ("of bare cannot be satisfied" `isInfixOf` errorsOf (groupsModel ++ "bare : Empty\n")) @? "Inherited xor over no children compiled"
    ("of tooFew cannot be satisfied" `isInfixOf` errorsOf "3..* tooFew\n   x ?\n   y 0..1\n") @? "3..* over two optional children compiled"
    compiles "2..* many\n   x *\n" @? "2..* over x * rejected"

{-
An ambiguous name of a super is not unique, with the paths of the candidates
(#115); two candidates in the same namespace are a duplicate definition.
-}
case_AmbiguousSuperName :: Assertion
case_AmbiguousSuperName = do
    let
        errorsOf model' = either show (const "") $ compileOneFragment defaultClaferArgs model'
        ambiguous = errorsOf "A\n    abstract T\nB\n    abstract T\nx : T\n"
        duplicate = errorsOf "abstract T\nabstract T\nx : T\n"
    all (`isInfixOf` ambiguous) ["clafer \\\"T\\\" is not unique", "A.A__T", "B.B__T"] @? "Wrong error for an ambiguous super: " ++ ambiguous
    ("cannot be defined because the name should be unique in the same namespace" `isInfixOf` duplicate) @? "Wrong error for a duplicate super: " ++ duplicate

{-
A group cardinality at the start of a line belongs to the clafer on that line,
not to the clafer on the line before, which has no cardinality (#117).
-}
case_GroupCardinalityOnNextLine :: Assertion
case_GroupCardinalityOnNextLine = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs "a\n2..3 b\n  c\n  d\nf\n  g\n  1..2 h\n    i\n"
        clafers :: [ IClafer ]
        clafers = universeOn biplate iModule
        cardOf name = [ _card c | c <- clafers, _ident c == name ]
        gcardOf name = [ _interval <$> _gcard c | c <- clafers, _ident c == name ]
    map cardOf ["a", "b", "f", "g", "h"] == replicate 5 [Just (1, 1)] @? "Wrong cardinalities: " ++ show (map cardOf ["a", "b", "f", "g", "h"])
    map gcardOf ["b", "h"] == [[Just (2, 3)], [Just (1, 2)]] @? "Wrong group cardinalities: " ++ show (map gcardOf ["b", "h"])
    map cardOf ["c", "d", "i"] == replicate 3 [Just (0, 1)] @? "Children not optional: " ++ show (map cardOf ["c", "d", "i"])

{-
A child without a multiplicity is mandatory under the default group (no group
cardinality or 0..*) and optional under a keyword group, opt included, also when
the group is inherited, or under another range. Only keywords set _isKeyword.
-}
childDefaultsModel :: String
childDefaultsModel = "opt Extras\n  sunroof\nabstract opt Options\n  usb\nCar : Options\n  towbar\nxor Engine\n  gas\n0..3 Colours\n  red\nPlain\n  seat\n0..* Free\n  x\n"

case_ChildDefaultsOfGroups :: Assertion
case_ChildDefaultsOfGroups = do
    let
        (Just (iModule, _, _)) = cIr $ claferEnv $ fromJust $ Map.lookup Alloy $ fromRight $ compileOneFragment defaultClaferArgs childDefaultsModel
        clafers :: [ IClafer ]
        clafers = universeOn biplate iModule
        cardOf name = [ _card c | c <- clafers, _ident c == name ]
        keywordOf name = [ _isKeyword <$> _gcard c | c <- clafers, _ident c == name ]
        optional' = [ "sunroof", "usb", "towbar", "gas", "red" ]
        mandatory = [ "seat", "x" ]
    all (\n -> cardOf n == [Just (0, 1)]) optional' @? "Not optional: " ++ show (map cardOf optional')
    all (\n -> cardOf n == [Just (1, 1)]) mandatory @? "Not mandatory: " ++ show (map cardOf mandatory)
    map keywordOf ["Extras", "Car", "Engine", "Colours", "Free"] == map (\k -> [Just k]) [True, True, True, False, False]
        @? "Wrong _isKeyword: " ++ show (map keywordOf ["Extras", "Car", "Engine", "Colours", "Free"])

{-
A model imports other files with --import, in its //# OPTIONS or on the command
line: the imports are followed transitively, each file is included once, before
the files importing it, and a path in //# OPTIONS is relative to its file. The
options of all files are combined.
-}
importFiles :: [(FilePath, String)]
importFiles =
  [ ("lib/base.cfr", "//# OPTIONS --maxint=63\nabstract Base\n  x -> integer\n")
  , ("lib/mid.cfr",  "//# OPTIONS --import=base.cfr --maxint=127 --minint=-5 -k\nabstract Mid : Base\n")
  , ("sys.cfr",      "//# OPTIONS --import=lib/mid.cfr --import=lib/base.cfr -m choco\nSys : Mid\n  [ x = 100 ]\n")
  , ("cli.cfr",      "Gadget : Base\n")
  , ("bad.cfr",      "//# OPTIONS --import=lib/base.cfr\nBad : Base\n  [ y = 1 ]\n")
  , ("c1.cfr",       "//# OPTIONS --import=c2.cfr\nA\n")
  , ("c2.cfr",       "//# OPTIONS --import=c1.cfr\nB\n")
  , ("missing.cfr",  "//# OPTIONS --import=nothere.cfr\nA\n")
  , ("lib/run.cfr",  "//# OPTIONS -v\nabstract R\n")
  , ("run.cfr",      "//# OPTIONS --import=lib/run.cfr\nr : R\n")
  , ("lib/nl.cfr",   "//# OPTIONS --nl\nabstract N\n")
  , ("nl.cfr",       "//# OPTIONS --import=lib/nl.cfr\nn : N\n")
  ]

case_Imports :: Assertion
case_Imports = do
    tmp <- getTemporaryDirectory
    let dir = tmp ++ "/clafer-test-imports"
        path name = dir ++ "/" ++ name
        readModel' name args' = readModel args'{file = path name}
    createDirectoryIfMissing True (dir ++ "/lib")
    mapM_ (\(name, text) -> writeFile (path name) text) importFiles
    -- a chain and a diamond: base once, before mid, before sys; the options combined
    Right (args', files) <- readModel' "sys.cfr" claferDefaults
    map modelFilePath files == map path ["lib/base.cfr", "lib/mid.cfr", "sys.cfr"] @? "Files: " ++ show (map modelFilePath files)
    (maxint args', minint args', mode args', keep_unused args') == (Just 127, Just (-5), [Choco], True)
        @? "Combined options: " ++ show (maxint args', minint args', mode args', keep_unused args')
    let results = fromRight $ compileOneFragment args'{mode = [Choco]} $ modelText files
    ("intRange(-5, 127);" `isInfixOf` outputCode (fromJust $ Map.lookup Choco results)) @? "No combined integer range"
    -- the command line's arguments take precedence, and its imports are relative to the current folder
    Right (cliArgs, cliFiles) <- readModel' "cli.cfr" claferDefaults{imports = [path "lib/base.cfr"], maxint = Just 7}
    (map modelFilePath cliFiles, maxint cliArgs) == (map path ["lib/base.cfr", "cli.cfr"], Just 7)
        @? "Command line import: " ++ show (map modelFilePath cliFiles, maxint cliArgs)
    -- an error in a file is reported at its line in that file
    Right (_, badFiles) <- readModel' "bad.cfr" claferDefaults
    case compileOneFragment defaultClaferArgs $ modelText badFiles of
      Left [SemanticErr ErrPos{modelPos = Pos l c} _] ->
        (modelPosition badFiles l, c) == ((path "bad.cfr", 3), 5) @? "Error position: " ++ show (modelPosition badFiles l, c)
      result -> assertFailure $ "bad.cfr: " ++ either show (const "compiled") result
    -- cycles, missing files, options of the compilation in an imported file, different layouts
    let failsWith name expected = do
          result <- readModel' name claferDefaults
          case result of
            Left message -> (expected `isInfixOf` message) @? name ++ ": " ++ message
            Right _      -> assertFailure $ name ++ " was read"
    failsWith "c1.cfr" "Import cycle: "
    failsWith "missing.cfr" "nothere.cfr does not exist"
    failsWith "run.cfr" "the option -v can only be given on the command line"
    failsWith "nl.cfr" "The option --nl must be the same in all files"
    removeDirectoryRecursive dir

{-
The spans of the JSON IR and the HTML output give the files of the model: each span
names its file, with the lines in that file, and the HTML shows each file under its
name, also the errors' positions.
-}
filesModel :: [ModelFile]
filesModel =
  [ ModelFile "lib.cfr" "abstract L\n  x ?\n"
  , ModelFile "m.cfr" "// the model\nA : L\n  [ x ]\n" ]

-- | Compiles the files of a model, as the compiler does.
compileFiles :: ClaferArgs -> [ModelFile] -> Either [ClaferErr] (Map.Map ClaferMode CompilerResult)
compileFiles args' files = runClafer args' $ do
    addModuleFragment $ modelText files
    modifyEnv $ \env -> env{inputFiles = files}
    parse
    iModule <- desugar Nothing
    compile iModule
    generate

case_SpansInFiles :: Assertion
case_SpansInFiles = do
    let results = fromRight $ compileFiles defaultClaferArgs{mode = [JSON, Html]} filesModel
        output m = outputCode $ fromJust $ Map.lookup m results
        Just json = Aeson.decode (fromString $ output JSON) :: Maybe Aeson.Value
        -- the files and start lines of the spans
        spans :: Aeson.Value -> [(String, Integer)]
        spans (Aeson.Object o) = case (Aeson.fromJSON (Aeson.Object o)) of
          Aeson.Success (SpanInFile f l) -> [(f, l)]
          _ -> concatMap spans (toListOf folded o)
        spans (Aeson.Array a) = concatMap spans (toListOf folded a)
        spans _ = []
        html = output Html
    (sort $ nub $ spans json) == [("lib.cfr", 1), ("lib.cfr", 2), ("m.cfr", 2), ("m.cfr", 3)]
        @? "Spans: " ++ show (sort $ nub $ spans json)
    let headers = [ i | (i, l) <- zip [0 :: Int ..] (lines html), "<div class=\"file\">" `isPrefixOf` l ]
    (map (lines html !!) headers == ["<div class=\"file\">lib.cfr</div>", "<div class=\"file\">m.cfr</div>"])
        @? "File headers: " ++ show (map (lines html !!) headers)
    -- an error in a file: the HTML error output gives its file and line
    let bad = [ head filesModel, ModelFile "m.cfr" "A : L\n  [ y ]\n" ]
    case compileFiles defaultClaferArgs{mode = [Html]} bad of
      Left errs -> ("Compiling failed at m.cfr:2:5..." `isInfixOf` highlightErrorsIn bad (modelText bad) errs)
                     @? "Error HTML: " ++ highlightErrorsIn bad (modelText bad) errs
      Right _ -> assertFailure "m.cfr compiled"

-- | A span in a file, as in the JSON IR: its file and start line.
data SpanInFile = SpanInFile String Integer

instance Aeson.FromJSON SpanInFile where
  parseJSON = Aeson.withObject "span" $ \o -> do
    f <- o Aeson..: fromString "file"
    start <- o Aeson..: fromString "start"
    l <- start Aeson..: fromString "line"
    return $ SpanInFile f l

{-
A model which may come from anyone (e.g., in a web tool) is compiled with --import-root: a
local import must be inside one of the roots, after resolving .. and symbolic links. The
options that run tools or restrict the imports cannot be set in //# OPTIONS.
-}
case_ImportRestrictions :: Assertion
case_ImportRestrictions = do
    tmp <- getTemporaryDirectory
    let dir = tmp ++ "/clafer-test-roots"
        path name = dir ++ "/" ++ name
    removePathForcibly dir  -- left by a failed run
    createDirectoryIfMissing True (path "session")
    createDirectoryIfMissing True (path "Examples")
    writeFile (path "Examples/lib.cfr") "abstract Lib\n"
    writeFile (path "outside.cfr") "abstract Outside\n"
    createDirectoryLink (path "Examples") (path "session/Examples")
    createFileLink (path "outside.cfr") (path "session/escape.cfr")
    let compileWith imports' = do
          writeFile (path "session/model.cfr") $ "//# OPTIONS " ++ imports' ++ "\nA\n"
          readModel claferDefaults{file = path "session/model.cfr", import_root = [path "session", path "Examples"]}
        allowed imports' = compileWith imports' >>= \r -> either (\m -> assertFailure $ imports' ++ ": " ++ m) (const $ return ()) r
        refused imports' expected = compileWith imports' >>= \r -> case r of
          Left message -> (expected `isInfixOf` message) @? imports' ++ ": " ++ message
          Right _      -> assertFailure $ imports' ++ " was read"
        outside = "is outside the folders from which files can be imported"
    allowed "--import=Examples/lib.cfr"
    refused "--import=../outside.cfr" outside
    refused ("--import=" ++ path "outside.cfr") outside
    refused "--import=escape.cfr" outside
    refused "--import=../nothere.cfr" outside
    refused "--import=nothere.cfr" "does not exist"
    refused "--import=../../../etc/hostname" "etc/hostname is not a .cfr file"
    refused "--import=http://example.org/index.php?x=.cfr" "is not a .cfr file"
    refused "-v" "the option -v can only be given on the command line"
    refused "--tooldir=/tmp --import-root=/" "the options --tooldir, --import-root can only be given on the command line"
    refused "--public-imports --import-base=http://example.org/" "the options --public-imports, --import-base can only be given"
    removeDirectoryRecursive dir

case_PublicAddresses :: Assertion
case_PublicAddresses = do
    let public = isPublicAddress . tupleToHostAddress
    map public [(8, 8, 8, 8), (140, 82, 112, 3), (172, 32, 0, 1), (100, 128, 0, 1)] @?= [True, True, True, True]
    map public [ (127, 0, 0, 1), (10, 1, 2, 3), (172, 16, 0, 1), (192, 168, 1, 1), (169, 254, 169, 254)
               , (0, 0, 0, 0), (100, 64, 0, 1), (224, 0, 0, 1), (255, 255, 255, 255), (198, 18, 0, 1) ]
        @?= replicate 10 False

{-
An import must be a .cfr file, and a URL import must not be served as a web page.
-}
case_ModelFilesOnly :: Assertion
case_ModelFilesOnly = do
    map isModelPath ["lib.cfr", "/models/design space.cfr"] @?= [True, True]
    map isModelPath ["/etc/hostname", "/index.php", "lib.cfr.bak", ""] @?= replicate 4 False
    map (isModelContentType . fmap fromString) [Nothing, Just "text/plain; charset=utf-8", Just "application/octet-stream"]
        @?= [True, True, True]
    map (isModelContentType . Just . fromString)
        ["text/html", "Text/HTML; charset=UTF-8", "application/json", "application/problem+json", "application/xml", "image/svg+xml"]
        @?= replicate 6 False

{-
An import is relative to the importing file: to its folder, or to its URL. A
file:// URL is a local path, and a model read from a URL can only import URLs.
-}
case_ImportLocations :: Assertion
case_ImportLocations = do
    let url = fromJust . parseURI
        systemURL = Remote $ url "https://example.org/models/system.cfr"
    location "file:///tmp/a%20b.cfr" == Local "/tmp/a b.cfr" @? "file:// URL"
    location "http://example.org/a.cfr" == Remote (url "http://example.org/a.cfr") @? "http:// URL"
    importLocation (Local "models/system.cfr") "lib/base.cfr" == Right (Local "models/lib/base.cfr") @? "relative to a folder"
    importLocation (Local "system.cfr") "../base.cfr" == Right (Local "../base.cfr") @? "relative to the current folder"
    importLocation systemURL "lib/base.cfr" == Right (Remote $ url "https://example.org/models/lib/base.cfr") @? "relative to a URL"
    importLocation systemURL "../shared/base.cfr" == Right (Remote $ url "https://example.org/shared/base.cfr") @? "a parent of a URL"
    importLocation systemURL "design space.cfr" == Right (Remote $ url "https://example.org/models/design%20space.cfr") @? "a space in a URL"
    importLocation (Local "system.cfr") "https://example.org/base.cfr" == Right (Remote $ url "https://example.org/base.cfr") @? "a URL from a local file"
    isLeft (importLocation systemURL "/etc/hostname") @? "a local path from a URL"
    isLeft (importLocation systemURL "file:///etc/hostname") @? "a file:// URL from a URL"
  where
    isLeft = either (const True) (const False)

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
    ("$Property = Abstract" `isInfixOf` choco) @? "Choco: the referenced Property is not declared\n" ++ choco
    ("$Named = Abstract" `isInfixOf` choco) @? "Choco: Named, used in a constraint, is not declared\n" ++ choco
    not ("$Unused" `isInfixOf` choco) @? "Choco: the unused Unused is declared\n" ++ choco
    ("abstract sig Property" `isInfixOf` alloy) @? "Alloy: the referenced Property is not declared\n" ++ alloy
    ("fact { #Property = 0 }" `isInfixOf` alloy) @? "Alloy: Property may have instances\n" ++ alloy
    not ("sig Unused" `isInfixOf` alloy) @? "Alloy: the unused Unused is declared\n" ++ alloy

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

-- After an explicit dref, the names are the children of the reference's target (#108):
-- this.dref.speed means this.speed, in the static and the temporal generators.
case_ExplicitDrefNavigation :: Assertion
case_ExplicitDrefNavigation = do
    let
        output mode' constraint = fmap (outputCode . fromJust . Map.lookup mode') $ compileOneFragment defaultClaferArgs{mode = [mode']} $ unlines
            [ "abstract Port"
            , "    speed -> integer"
            , "hub : Port"
            , "l -> Port"
            , "    " ++ constraint ]
        same mode' a b = case (output mode' a, output mode' b) of
            (Right a', Right b') -> a' == b' @? (show mode' ++ ": " ++ a ++ " differs from " ++ b)
            (Left errs', _) -> assertFailure $ a ++ ": " ++ show errs'
            (_, Left errs') -> assertFailure $ b ++ ": " ++ show errs'
    forM_ [Alloy, Choco] $ \mode' -> do
        same mode' "[ this.speed = 3 ]" "[ this.dref.speed = 3 ]"
        same mode' "[ this.speed = 3 ]" "[ dref.speed = 3 ]"
        same mode' "[ this.speed = 3 ]" "[ this.dref.speed.dref = 3 ]"
    same Alloy "[ G this.speed = 3 ]" "[ G this.dref.speed = 3 ]"
    case output Alloy "[ all t : this.dref | t.speed = 3 ]" of
        Right _ -> return ()
        Left errs' -> assertFailure $ show errs'

-- The parent of an instance of a top-level clafer is the synthetic root, a navigation from which
-- is a navigation from the top level (#112).
case_ParentOfTopLevel :: Assertion
case_ParentOfTopLevel = do
    let
        model constraint = unlines [ "a", "b", "    " ++ constraint ]
        output mode' constraint = fmap (outputCode . fromJust . Map.lookup mode') $ compileOneFragment defaultClaferArgs{mode = [mode']} $ model constraint
        same mode' x y = case (output mode' x, output mode' y) of
            (Right x', Right y') -> x' == y' @? (show mode' ++ ": " ++ x ++ " differs from " ++ y)
            (Left errs', _) -> assertFailure $ x ++ ": " ++ show errs'
            (_, Left errs') -> assertFailure $ y ++ ": " ++ show errs'
        refused x expected = case compileOneFragment defaultClaferArgs x of
            Left errs' -> (expected `isInfixOf` show errs') @? ("Unexpected errors\n" ++ show errs')
            Right _ -> assertFailure $ x ++ " compiled"
    forM_ [Alloy, Choco] $ \mode' -> do
        same mode' "[ some a ]" "[ some parent.a ]"
        same mode' "[ some a ]" "[ some this.parent.a ]"
        same mode' "[ some a ]" "[ some root.a ]"
        same mode' "[ all v : b | some a ]" "[ all v : b | some v.parent.a ]"
    same Alloy "[ G some a ]" "[ G some parent.a ]"
    -- the root as a value is a constant: true as 0 < 1, false as 1 < 0, and 1 for #root
    let contains mode' x expected = case output mode' x of
            Right x' -> (expected `isInfixOf` x') @? (show mode' ++ ": " ++ x ++ " is not " ++ expected ++ "\n" ++ x')
            Left errs' -> assertFailure $ x ++ ": " ++ show errs'
    contains Alloy "[ some parent ]" "{ 0 < 1 }"
    contains Alloy "[ no root ]" "{ 1 < 0 }"
    contains Alloy "[ #this.parent = 1 ]" "{ 0 < 1 }"
    contains Choco "[ some parent ]" "lessThan(constant(0), constant(1))"
    -- the parent of a set of instances of a top-level clafer is the root when an instance exists
    let optional constraint = unlines [ "a ?", "b", "    " ++ constraint ]
        sameOptional mode' x y = case (compile' mode' x, compile' mode' y) of
            (Right x', Right y') -> x' == y' @? (show mode' ++ ": " ++ x ++ " differs from " ++ y)
            (Left errs', _) -> assertFailure $ x ++ ": " ++ show errs'
            (_, Left errs') -> assertFailure $ y ++ ": " ++ show errs'
        compile' mode' = fmap (outputCode . fromJust . Map.lookup mode') . compileOneFragment defaultClaferArgs{mode = [mode']} . optional
    forM_ [Alloy, Choco] $ \mode' -> do
        sameOptional mode' "[ some a ]" "[ some a.parent ]"
        sameOptional mode' "[ no a ]" "[ no a.parent ]"
    case compile' Alloy "[ some a.parent.a ]" of
        Right x' -> ("some ((some a) => (a) else none)" `isInfixOf` x') @? x'
        Left errs' -> assertFailure $ show errs'
    refused (unlines [ "abstract Feat", "f1 : Feat", "g", "    f2 : Feat", "[ all v : Feat | some v.parent ]" ]) "take the parent of `this`"
    -- some subclafers of Feat are at the top level and some nested: its constraint is split on this
    case compileOneFragment defaultClaferArgs{mode = [Alloy, Choco]} (unlines [ "abstract Feat", "    [ some parent ]", "f1 : Feat", "g", "    f2 : Feat" ]) of
        Right r -> do
            let alloy = outputCode $ fromJust $ Map.lookup Alloy r
                choco = outputCode $ fromJust $ Map.lookup Choco r
            ("((this in f1) => (0 < 1)) && ((this in (g.@r_f2)) => (some (this & (g.@r_f2)).~(@r_f2)))" `isInfixOf` alloy) @? alloy
            ("joinParent(inter($this(), join(global($g), $f2)))" `isInfixOf` choco) @? choco
        Left errs' -> assertFailure $ show errs'

-- final, finalref and finaltarget on a clafer that inherits its reference fix the reference in
-- the temporal output (#109).
case_FinalInheritedReference :: Assertion
case_FinalInheritedReference =
    forM_ ["final", "finalref", "finaltarget", ""] $ \modifier ->
        case compileOneFragment defaultClaferArgs{mode = [Clafer], core = True} (unlines
                [ "abstract Engine", "gas : Engine", "abstract Car", "    abstract engine -> Engine"
                , "    xor gear", "        initial park --> drive", "        drive"
                , "tesla : Car", "    " ++ modifier ++ " motor : engine" ]) of
            Right r -> let explicit = outputCode $ fromJust $ Map.lookup Clafer r
                           -- final and finalref fix the reference of each motor, finaltarget the
                           -- targets of the motors of a tesla (kbak/clafer-semantics#127), as
                           -- constraints of the core (kbak/clafer-semantics#192)
                           eachFixed = "[all motor_1 : this | all motor_2 : motor_1.dref | X ((some motor_1.dref) => (motor_2 in motor_1.dref))]" `isInfixOf` explicit
                           targetsFixed = "[all motor_2 : this.dref | X (motor_2 in this.parent.motor.dref)]" `isInfixOf` explicit
                       in (eachFixed, targetsFixed, "final" `isInfixOf` explicit) == (modifier `elem` ["final", "finalref"], modifier == "finaltarget", False)
                            @? (modifier ++ ": " ++ explicit)
            Left errs' -> assertFailure $ modifier ++ ": " ++ show errs'

-- A clafer which extends itself is reported as such, not as a missing super.
case_SelfInheritanceReported :: Assertion
case_SelfInheritanceReported =
    case compileOneFragment defaultClaferArgs "abstract A : A\nb : A" of
        Left errs' -> ("inherits from itself" `isInfixOf` show errs') @? "Unexpected errors\n" ++ show errs'
        Right _ -> assertFailure "abstract A : A compiled"

-- The initializer := is the initial value of a reference (kbak/clafer-semantics#164): the same as
-- = in a static model, and the value in the first state of each lifetime of the clafer in a
-- temporal model. It is no longer an assertion (#116).
case_InitialValue :: Assertion
case_InitialValue = do
    let
        output modes' model = fmap (\r -> map (\m -> outputCode $ fromJust $ Map.lookup m r) modes') $ compileOneFragment defaultClaferArgs{mode = modes'} $ unlines model
        static' how = [ "A 2", "    x -> integer " ++ how ++ " 10", "    y -> integer ? " ++ how ++ " x + 1"
                      , "    zs -> integer 0..2 " ++ how ++ " 1, 2", "abstract Val -> integer " ++ how ++ " 2", "v1 : Val" ]
        explicit model = case output [Clafer] model of
            Right [x] -> return x
            Right _ -> assertFailure "no explicit model" >> return ""
            Left errs' -> assertFailure (show errs') >> return ""
        has model expected = do
            x <- explicit model
            (expected `isInfixOf` x) @? (expected ++ " not in\n" ++ x)
    -- a static model: the same Alloy and Choco outputs as with =, and no assertion; the explicit
    -- form keeps the initializers as written
    case (output [Alloy, Choco, Clafer] $ static' ":=", output [Alloy, Choco, Clafer] $ static' "=") of
        (Right a, Right b) -> do
            take 2 a == take 2 b @? ("differs from =:\n" ++ unlines a)
            not (any ("assert" `isInfixOf`) a) @? ("an assertion:\n" ++ unlines a)
            not ("--tl" `isInfixOf` last a) @? ("temporal:\n" ++ last a)
            ("0..* x -> int 1..1 := each 10 {}" `isInfixOf` last a) @? ("not :=:\n" ++ last a)
            ("0..* x -> int 1..1 = 10 {}" `isInfixOf` last b) @? ("not =:\n" ++ last b)
        (Left errs', _) -> assertFailure $ show errs'
        (_, Left errs') -> assertFailure $ show errs'
    -- a temporal model: the initializers as written, with their values in the context of the
    -- parent (explicit initializers)
    let temporal = [ "A", "    y -> integer", "    x -> integer ? := y + 1", "        y -> integer"
                   , "    z -> integer := this.y", "    zs -> integer * := 1, 2", "finalref f -> integer ? := A.y"
                   , "[ F some A.x ]" ]
    has temporal "0..* x -> int 0..1 := each this.A__y.dref + 1 {"
    has temporal "0..* z -> int 1..1 := each this.A__y.dref {}"
    has temporal "0..* zs -> int 0..* := together 1 ++ 2 {}"
    -- a finalref reference keeps the value it starts with, also when the value of A.y changes
    has temporal "finalref 0..* f -> int 0..1 := each A.A__y.dref {}"
    x <- explicit temporal
    not ("assert" `isInfixOf` x) @? ("an assertion:\n" ++ x)

-- The Alloy output of a model, static or temporal.
alloyOf :: [String] -> Either String String
alloyOf model = case compileOneFragment defaultClaferArgs{mode = [Alloy]} $ unlines model of
    Right r -> Right $ outputCode $ fromJust $ Map.lookup Alloy r
    Left errs' -> Left $ show errs'

hasAlloy :: [String] -> String -> Assertion
hasAlloy model expected = case alloyOf model of
    Right alloy -> (expected `isInfixOf` alloy) @? (expected ++ " not in\n" ++ alloy)
    Left errs' -> assertFailure errs'

lacksAlloy :: [String] -> String -> Assertion
lacksAlloy model unexpected = case alloyOf model of
    Right alloy -> not (unexpected `isInfixOf` alloy) @? (unexpected ++ " in\n" ++ alloy)
    Left errs' -> assertFailure errs'

-- A := under an inherited = is reported as an initializer that does not redefine the =, not as
-- one without effect: an equal value repeats it, another one leaves no instance, which forces an
-- optional clafer to be absent (#124).
case_InitializerUnderInheritedConstant :: Assertion
case_InitializerUnderInheritedConstant =
    forM_ ["r : Ref := 2", "r : Ref := 3", "r : Ref ? := 3"] $ \sub ->
        case compileOneFragment defaultClaferArgs{mode = [Alloy]} (unlines [ "abstract Ref -> integer = 2", sub ]) of
            Right r -> do
                let stats = statistics $ fromJust $ Map.lookup Alloy r
                ("the initializer ':=' of r does not redefine the initializer '=' of Ref, which r inherits: both hold" `isInfixOf` stats) @? (sub ++ ": " ++ stats)
                not ("no effect" `isInfixOf` stats) @? (sub ++ ": " ++ stats)
            Left errs' -> assertFailure $ sub ++ ": " ++ show errs'

-- A reference that refines an inherited one has the target of the inherited one in the temporal
-- output, as in the static one (#120).
case_RefinedReferenceTemporal :: Assertion
case_RefinedReferenceTemporal =
    hasAlloy [ "abstract Ref -> integer", "r : Ref -> integer", "[ G (r.dref = 1) ]" ]
        "always (this in alive_r implies (this.@r_ref in this.@Ref_ref))"

-- The set reference keys (#121, #125): per parent, for the reference a concrete clafer inherits
-- too, and none for a top-level abstract clafer, in both outputs; none for a bag reference.
case_SetReferenceKeys :: Assertion
case_SetReferenceKeys = do
    let model = [ "Target 2", "abstract Ref -> Target", "r : Ref 2", "a : Ref", "c : Ref"
                , "abstract BagRef ->> Target", "b : BagRef 2" ]
    hasAlloy model "all disj x, y : r | (x.@Ref_ref) != (y.@Ref_ref)"
    lacksAlloy model "all disj x, y : Ref"
    lacksAlloy model "all disj x, y : b"
    hasAlloy (model ++ ["[ G some r ]"]) "all disj x, y : this.@r_r | (x.@Ref_ref) != (y.@Ref_ref)"
    lacksAlloy (model ++ ["[ G some r ]"]) "all disj x, y : this.@r_b"

-- An instance has no reference while it does not exist (#122).
case_AbsentReference :: Assertion
case_AbsentReference = do
    hasAlloy [ "x -> integer ?", "[ G some x ]" ] "always (this not in alive_x implies no this.@x_ref)"
    -- an inherited reference: the instances of the abstract clafer are those of its subclafers
    hasAlloy [ "abstract Ref -> integer", "r : Ref ?", "[ G some r ]" ] "always (this not in alive_Ref implies no this.@Ref_ref)"

-- | The explicit model keeps the enumerations, initializers, behavioral patterns and
--   transitions; its core (--core) has them lowered, as the backends get them
--   (doc/rich-and-core-explicit.md).
case_RichAndCoreExplicit :: Assertion
case_RichAndCoreExplicit = do
    let model = [ "enum Color = red | green", "light -> Color", "p ?", "q ?", "r ?"
                , "Box ?", "    on ?", "    off ?", "    x -> integer := 3", "    [ on --> off --> on ]"
                , "[ never p between q and r ]" ]
        explicit core' = case compileOneFragment defaultClaferArgs{mode = [Clafer], core = core'} (unlines model) of
            Right r -> return $ outputCode $ fromJust $ Map.lookup Clafer r
            Left errs' -> assertFailure (show errs') >> return ""
        has core' expected = do
            x <- explicit core'
            (expected `isInfixOf` x) @? (expected ++ " not in\n" ++ x)
    has False "enum Color = red | green"
    has False "0..* x -> int 1..1 := each 3 {}"
    has False "[(some this.on) --> (some this.off) --> (some this.on)]"
    has False "[never (some p) between (some q) and (some r)]"
    -- the enumeration is final in a temporal model: its literals do not change (#127)
    has True "abstract 0..* Color 0..* {}"
    has True "[all red_1 : this | X (red_1 in red)]"
    has True "[(!(previous (some this))) => (this.dref = 3)]"
    has True "[(some this.on) => (X ((some this.off) && (X (some this.on))))]"
    has True "[G ((((some q) && (no r)) && (F (some r))) => ((no p) U (some r)))]"

-- | Both explicit models print the top-level declarations where they were written: the
--   clafers, the enumerations and the constraints.
case_ExplicitDeclarationOrder :: Assertion
case_ExplicitDeclarationOrder = do
    let model = unlines [ "a ?", "[ some a ]", "enum E = x | y", "b -> E" ]
        explicit core' = case compileOneFragment defaultClaferArgs{mode = [Clafer], core = core'} model of
            Right r -> return $ drop 1 $ lines $ outputCode $ fromJust $ Map.lookup Clafer r
            Left errs' -> assertFailure (show errs') >> return []
    rich <- explicit False
    rich == ["0..* a 0..1 {}", "[some a]", "enum E = x | y", "0..* b -> E 1..1 {}"] @? ("rich:\n" ++ unlines rich)
    core'' <- explicit True
    take 3 core'' == ["0..* a 0..1 {}", "[some a]", "abstract 0..* E 0..* {}"] && last core'' == "0..* b -> E 1..1 {}"
        @? ("core:\n" ++ unlines core'')

-- | Real and double, which no backend solves, are printed in the rich and the core explicit
--   model, which compile to themselves.
case_RealsPrinted :: Assertion
case_RealsPrinted = do
    let model = [ "a -> real", "b -> double ?", "c -> real := 2.5", "[ a.dref = 1.5 ]", "[ some b => b.dref > a.dref * 2 ]" ]
        explicit core' m = case compileOneFragment defaultClaferArgs{mode = [Clafer], core = core'} (unlines m) of
            Right r -> return $ outputCode $ fromJust $ Map.lookup Clafer r
            Left errs' -> assertFailure (show errs') >> return ""
    forM_ [False, True] $ \core' -> do
      x <- explicit core' model
      all (`isInfixOf` x) ["0..* a -> real 1..1", "0..* b -> double 0..1", "[a.dref = 1.5]"] @? ("reals missing (core: " ++ show core' ++ "):\n" ++ x)
      y <- explicit core' (lines x)
      x == y @? ("Not a fixpoint (core: " ++ show core' ++ "):\n" ++ x ++ "\n" ++ y)

-- | An abstract clafer that nothing needs stays in both explicit models and the JSON IR, which
--   print the model as written; the Alloy and Choco outputs leave it out to solve less, unless
--   it is kept (-k).
case_UnusedAbstractsKept :: Assertion
case_UnusedAbstractsKept = do
    let model = unlines [ "abstract Unused", "    x ?", "abstract Base", "b : Base" ]
        output keep core' mode' = case compileOneFragment defaultClaferArgs{mode = [mode'], core = core', keep_unused = keep} model of
            Right r -> return $ outputCode $ fromJust $ Map.lookup mode' r
            Left errs' -> assertFailure (show errs') >> return ""
        has keep core' mode' expected = do
            x <- output keep core' mode'
            (expected `isInfixOf` x) == True @? (show (mode', core', keep) ++ ": " ++ expected ++ " not in\n" ++ x)
        lacks keep mode' unexpected = do
            x <- output keep False mode'
            not (unexpected `isInfixOf` x) @? (show (mode', keep) ++ ": " ++ unexpected ++ " in\n" ++ x)
    has False False Clafer "abstract 0..* Unused 0..* {\n  0..* x 0..1 {}\n}"
    has False True Clafer "abstract 0..* Unused 0..* {\n  0..* x 0..1 {}\n}"
    has False False JSON "Unused"
    has False True JSON "Unused"
    lacks False Alloy "Unused"
    lacks False Choco "Unused"
    has True False Alloy "abstract sig Unused"
    has True False Choco "Unused"

-- | The JSON IR is the rich IR, or with --core the core IR that the backends get.
case_JsonRichAndCore :: Assertion
case_JsonRichAndCore = do
    let model = [ "enum Color = red | green", "light -> Color", "p ?", "q ?", "r ?"
                , "Box ?", "    on ?", "    off ?", "    x -> integer := 3", "    [ on --> off ]"
                , "[ never p between q and r ]" ]
        json core' = case compileOneFragment defaultClaferArgs{mode = [JSON], core = core'} (unlines model) of
            Right r -> return $ outputCode $ fromJust $ Map.lookup JSON r
            Left errs' -> assertFailure (show errs') >> return ""
        has core' expected = do
            x <- json core'
            (expected `isInfixOf` x) @? (expected ++ " not in the JSON IR (core: " ++ show core' ++ ")")
        hasNot core' unexpected = do
            x <- json core'
            not (unexpected `isInfixOf` x) @? (unexpected ++ " in the JSON IR (core: " ++ show core' ++ ")")
    has False "\"_op\":\"never between\""
    has False "\"_op\":\"-->\""
    has False "\"_enum\":true"
    has False "IEInitializer"
    hasNot True "\"_op\":\"never between\""
    hasNot True "\"_op\":\"-->\""
    hasNot True "\"_enum\":true"
    hasNot True "IEInitializer"
    has True "\"_op\":\"U\""
    has True "\"_op\":\"previous\""
    hasNot True "\"_op\":\"initially\""

-- | The initializers stay as written in the rich explicit model and are lowered to LTL in the
--   core; a per-instance := whose value has temporal operators is evaluated in the parent's
--   context when the instance appears, which the core says with the past-time operator
--   previous (gsdlab/clafer#127, doc/rich-and-core-explicit.md).
case_CoreInitializers :: Assertion
case_CoreInitializers = do
    let model = [ "P ?", "    b ?", "    x -> integer ? := 1", "    y -> integer = 2"
                , "    xs -> integer * := 1, 2", "    t -> integer * := if (X some b) then 1 else 2"
                , "    z -> integer := if (X some b) then 1 else 2"
                , "abstract Val -> integer := 1", "v : Val"
                , "abstract Vs -> integer * := 3", "vs : Vs"
                , "[ G some P ]" ]
        explicit core' = case compileOneFragment defaultClaferArgs{mode = [Clafer], core = core'} (unlines model) of
            Right r -> return $ outputCode $ fromJust $ Map.lookup Clafer r
            Left errs' -> assertFailure (show errs') >> return ""
        has core' expected = do
            x <- explicit core'
            (expected `isInfixOf` x) @? (expected ++ " not in\n" ++ x)
        hasNot core' unexpected = do
            x <- explicit core'
            not (unexpected `isInfixOf` x) @? (unexpected ++ " in\n" ++ x)
    -- rich: as written, with the clocks of := (kbak/clafer-semantics#194)
    has False "0..* x -> int 0..1 := each 1 {}"
    has False "0..* y -> int 1..1 = 2 {}"
    has False "0..* xs -> int 0..* := together 1 ++ 2 {}"
    has False "abstract 0..* Val -> int 0..* := each 1 {}"
    has False "abstract 0..* Vs -> int 0..* := together 3 {}"
    -- core: per instance, a fixed value, parent birth, time zero
    has True "0..* x -> int 0..1 {\n    [(!(previous (some this))) => (this.dref = 1)]"
    has True "[(some this.y) => (this.y.dref = 2)]"
    has True "[(!(previous (some this))) => ((some this.xs) => (this.xs.dref = (1 ++ 2)))]"
    has True "abstract 0..* Val -> int 0..* {\n  [(!(previous (some this))) => (this.dref = 1)]"
    has True "[(!(previous (some root))) => ((some Vs) => (Vs.dref = 3))]"
    -- a collection is initialized at the parent's birth, in the parent's context, so its
    -- temporal value needs no past-time operator
    has True "[(!(previous (some this))) => ((some this.t) => (this.t.dref = (if (X (some this.b)) then 1 else 2)))]"
    -- per instance with a temporal value: in the context of the parent, each instance that
    -- appears, i.e., was not there in the previous state, has the value (#127)
    has False "0..* z -> int 1..1 := each if (X (some this.b)) then 1 else 2 {}"
    has True "[all z_1 : this.z | (!(previous (z_1 in this.z))) => (z_1.dref = (if (X (some this.b)) then 1 else 2))]"
    has True "0..* z -> int 1..1 {}"
    hasNot True ":="
    hasNot True "= 2 {}"

-- The written clocks of := (kbak/clafer-semantics#194): := each initializes each instance at its
-- birth and := together the instances under a parent at its birth (all the instances of a
-- top-level abstract clafer at time zero), whatever the multiplicity. On a concrete clafer with
-- more than one instance, := each is one equation for each instance, also in a static model,
-- not the equation of all the instances together. The rich explicit model writes the clocks.
case_InitializerClocks :: Assertion
case_InitializerClocks = do
    let model = [ "P ?", "    xs -> integer * := each 1", "    x -> integer ? := together 2"
                , "    ys -> integer 2 := each 3, 4"
                , "abstract Val -> integer 0..3 := each 5", "v : Val ?"
                , "abstract Wal -> integer 0..3 := together 6", "w : Wal ?" ]
        temporal = model ++ [ "[ G some P ]" ]
        explicit core' m = case compileOneFragment defaultClaferArgs{mode = [Clafer], core = core'} (unlines m) of
            Right r -> return $ outputCode $ fromJust $ Map.lookup Clafer r
            Left errs' -> assertFailure (show errs') >> return ""
        has core' m expected = do
            x <- explicit core' m
            (expected `isInfixOf` x) @? (expected ++ " not in\n" ++ x)
    forM_ [model, temporal] $ \m -> mapM_ (has False m)
      [ "0..* xs -> int 0..* := each 1 {}", "0..* x -> int 0..1 := together 2 {}"
      , "0..* ys -> int 2..2 := each 3 ++ 4 {}", "abstract 0..* Val -> int 0..3 := each 5 {}"
      , "abstract 0..* Wal -> int 0..3 := together 6 {}" ]
    -- static: each instance on its own, or all together; the abstract := each has a value with
    -- at most one element, so the equation of all its instances is the same
    mapM_ (has True model)
      [ "[all xs_1 : this.xs | xs_1.dref = 1]", "[(some this.x) => (this.x.dref = 2)]"
      , "[all ys_1 : this.ys | ys_1.dref = (3 ++ 4)]", "[(some Val) => (Val.dref = 5)]"
      , "[(some Wal) => (Wal.dref = 6)]" ]
    -- temporal: at each instance's birth, at the parent's birth, at time zero
    mapM_ (has True temporal)
      [ "0..* xs -> int 0..* {\n    [(!(previous (some this))) => (this.dref = 1)]"
      , "[(!(previous (some this))) => ((some this.x) => (this.x.dref = 2))]"
      , "0..* ys -> int 2..2 {\n    [(!(previous (some this))) => (this.dref = (3 ++ 4))]"
      , "abstract 0..* Val -> int 0..* {\n  [(!(previous (some this))) => (this.dref = 5)]"
      , "[(!(previous (some root))) => ((some Wal) => (Wal.dref = 6))]" ]
    -- both explicit models compile to themselves
    forM_ [model, temporal] $ \m -> forM_ [False, True] $ \core' -> do
      x <- explicit core' m
      y <- explicit core' (lines x)
      x == y @? ("Not a fixpoint (core: " ++ show core' ++ "):\n" ++ x ++ "\n" ++ y)

-- The support limits of the initializers (#126, kbak/clafer-semantics#170): a per-instance :=
-- of an abstract clafer needs a value with at most one element, and on an abstract clafer
-- with :=, a multiplicity other than * has no meaning. Every mode rejects them, also the rich
-- explicit model, which would otherwise print them as supported forms, in static and temporal
-- models, also for an abstract clafer that nothing extends. A single reference with several
-- values is a warning.
case_InitializerDiagnostics :: Assertion
case_InitializerDiagnostics = do
    let
        temporal = "[ G some v ]\n"
        compileIn modes' core' = compileOneFragment defaultClaferArgs{mode = modes', core = core'}
        allModes = [ ([Clafer], False), ([Clafer], True), ([JSON], False), ([JSON], True), ([Alloy], False) ]
        rejected expected model' = forM_ [ "", temporal ] $ \t -> forM_ allModes $ \(modes', core') ->
          case compileIn modes' core' (model' ++ t) of
            Left errs' -> (expected `isInfixOf` show errs') @? "Unexpected errors for\n" ++ model' ++ t ++ show errs'
            Right _ -> assertFailure $ "Compiled in " ++ show (modes', core') ++ ":\n" ++ model' ++ t
        -- the rich and the core explicit model compile to themselves
        admitted model' = forM_ [ "", temporal ] $ \t -> forM_ [False, True] $ \core' -> do
          let explicit m = case compileIn [Clafer] core' m of
                Right r -> Right $ outputCode $ fromJust $ Map.lookup Clafer r
                Left errs' -> Left errs'
          case explicit (model' ++ t) of
            Right x -> either (const Nothing) Just (explicit x) == Just x @? "Not a fixpoint (core: " ++ show core' ++ "):\n" ++ x ++ "\n" ++ either show id (explicit x)
            Left errs' -> assertFailure $ "Rejected:\n" ++ model' ++ t ++ show errs'
        warnings model' = case compileIn [Clafer] False model' of
          Right r -> statistics $ fromJust $ Map.lookup Clafer r
          Left errs' -> show errs'
        scalar = "its initial value, which must have at most one element"
        scalarValue = "could not be established for"
        bound = "requires an explicit clock"
        several = "is a single reference, which cannot equal the several values"
        severalEach = "each instance of xs is a single reference"
    -- scalar admission
    rejected scalar "abstract Val -> integer := 1, 2\nv : Val\n"
    rejected scalar "abstract Val -> integer := 1, 2\nv ?\n"
    rejected (scalarValue ++ " 'pool.dref'") "pool ->> integer *\n[ #pool <= 1 ]\nabstract Val -> integer := pool.dref\nv : Val\n"
    rejected scalar "P *\n  q -> integer\nabstract Val -> integer := P.q.dref\nv : Val\n"
    mapM_ (admitted . (++ "\nv : Val\n"))
      [ "abstract Val -> integer := 1"
      , "abstract Val -> integer := 1, 1"
      , "seed -> integer ?\nabstract Val -> integer := seed.dref"
      , "pool ->> integer *\nabstract Val -> integer := pool.dref ** 1"
      , "abstract Val -> integer := 1 / 0"
      , "P\n  q -> integer\nabstract Val -> integer := P.q.dref + 1"
      , "seed ?\nabstract Val -> integer := if some seed then 1 else 2"
      , "pool -> integer *\nabstract Val -> integer := #pool"
      -- a collection initializer, which initializes all the instances together
      , "abstract Val -> integer * := 1, 2"
      , "abstract Val -> integer 0..* := 1, 2"
      -- = is not an initial value, and its multiplicity is the one of the instances
      , "abstract Val -> integer = 1, 2"
      ]
    -- the multiplicity of an abstract clafer with :=, as written
    forM_ ["?", "1", "2", "1..*", "+", "0..3"] $ \m -> do
      rejected ("the top-level abstract clafer Val with the multiplicity " ++ m ++ " " ++ bound) ("abstract Val -> integer " ++ m ++ " := 1\nv : Val\n")
      -- with an explicit clock, every multiplicity (kbak/clafer-semantics#194), with the scalar
      -- admission of a per-instance := of an abstract clafer
      admitted $ "abstract Val -> integer " ++ m ++ " := each 1\nv : Val\n"
      admitted $ "abstract Val -> integer " ++ m ++ " := together 1, 2\nv : Val\n"
      rejected scalar $ "abstract Val -> integer " ++ m ++ " := each 1, 2\nv : Val\n"
    -- an explicit clock overrides the shorthand of the multiplicity
    mapM_ (admitted . (++ "\nv : Val\n"))
      [ "abstract Val -> integer := together 1, 2", "abstract Val -> integer * := each 1" ]
    rejected scalar "abstract Val -> integer * := each 1, 2\nv : Val\n"
    -- the multiplicity of a nested abstract clafer is not limited (only * is a clock there,
    -- #129); its per-instance := has the same scalar admission, in the parent's context
    let nested m = "abstract Base\n  q -> integer\n  " ++ m ++ "\nv : Base\n  x : Base.Val\n"
    admitted $ nested "abstract Val -> integer ? := 1"
    admitted $ nested "abstract Val -> integer := this.q.dref"
    rejected scalar $ nested "abstract Val -> integer := 1, 2"
    -- a single reference with several values
    (several `isInfixOf` warnings "P\n  x -> integer ? := 1, 2\n") @? "No warning for := 1, 2"
    ("initializer '='" `isInfixOf` warnings "P\n  x -> integer ? = 1, 2\n") @? "No warning for = 1, 2"
    (several `isInfixOf` warnings "P\n  x -> integer ? := together 1, 2\n") @? "No warning for := together 1, 2"
    -- each instance with several values (kbak/clafer-semantics#194)
    (severalEach `isInfixOf` warnings "P\n  xs -> integer * := each 1, 2\n") @? "No warning for := each 1, 2"
    mapM_ (\m -> not (several `isInfixOf` warnings m || severalEach `isInfixOf` warnings m) @? "Warning for\n" ++ m)
      [ "P\n  x -> integer ? := 1, 1\n", "P\n  xs -> integer * := 1, 2\n", "P\n  x -> integer ? := 1\n"
      , "abstract Val -> integer = 1, 2\nv : Val\n", "P\n  xs -> integer * := together 1, 2\n"
      , "P\n  xs -> integer * := each 1, 1\n" ]

-- The finality modifiers are constraints of the core (kbak/clafer-semantics#192): the explicit
-- core model has no modifier left, compiles to itself, and the rich model keeps the modifiers.
case_FinalityLowered :: Assertion
case_FinalityLowered = do
    let model = [ "abstract engine -> integer", "A ?", "    final b ?", "    finalref r -> integer"
                , "    finaltarget ts -> integer *", "    final m : engine", "final top ?", "[ G some A ]" ]
        explicit core' m = case compileOneFragment defaultClaferArgs{mode = [Clafer], core = core'} (unlines m) of
            Right r -> return $ outputCode $ fromJust $ Map.lookup Clafer r
            Left errs' -> assertFailure (show errs') >> return ""
    rich <- explicit False model
    all (`isInfixOf` rich) ["final 0..* b", "finalref", "finaltarget", "final 0..* m : engine", "final 0..* top"] @? ("modifiers not kept:\n" ++ rich)
    x <- explicit True model
    not (any (`isInfixOf` x) ["final", "finalref", "finaltarget"]) @? ("a modifier in the core:\n" ++ x)
    all (`isInfixOf` x)
      [ "[all b_1 : this | X (b_1 in this.parent.b)]"
      , "[all r_1 : this | all r_2 : r_1.dref | X ((some r_1.dref) => (r_2 in r_1.dref))]"
      , "[all ts_2 : this.dref | (previous (some this.parent)) => (previous (ts_2 in this.parent.ts.dref))]"
      , "[all m_1 : this | all m_2 : m_1.dref | X ((some m_1.dref) => (m_2 in m_1.dref))]"
      , "[all top_1 : this | X (top_1 in top)]" ] @? ("constraints missing:\n" ++ x)
    y <- explicit True (lines x)
    x == y @? ("Not a fixpoint:\n" ++ x ++ "\n" ++ y)

-- The modifier initial is a constraint of the parent in the core (kbak/clafer-semantics#195):
-- the parent has an instance in its first state, the model at the start of the trace at the top
-- level; a subclafer of a top-level abstract clafer inherits it. The rich model keeps it.
case_InitialLowered :: Assertion
case_InitialLowered = do
    let model = [ "initial top ?", "A ?", "    initial b ?", "abstract S", "    initial c ?", "T : S ?"
                , "abstract initial Ub", "V : Ub ?", "[ G some A ]" ]
        explicit core' m = case compileOneFragment defaultClaferArgs{mode = [Clafer], core = core'} (unlines m) of
            Right r -> return $ outputCode $ fromJust $ Map.lookup Clafer r
            Left errs' -> assertFailure (show errs') >> return ""
    rich <- explicit False model
    all (`isInfixOf` rich) ["initial 0..* top", "initial 0..* b", "abstract initial 0..* Ub"] @? ("modifiers not kept:\n" ++ rich)
    x <- explicit True model
    not ("initial " `isInfixOf` x) @? ("a modifier in the core:\n" ++ x)
    all (`isInfixOf` x)
      [ "[(!(previous (some root))) => (some top)]", "[(!(previous (some root))) => (some V)]"
      , "[(!(previous (some this))) => (some this.b)]"
      , "[(!(previous (some this))) => (some this.c)]" ] @? ("constraints missing:\n" ++ x)
    y <- explicit True (lines x)
    x == y @? ("Not a fixpoint:\n" ++ x ++ "\n" ++ y)

-- With --record-provenance, the explicit core model has the origin of each clafer and constraint
-- that a lowering made, as a comment with the rich construct and its position, as in the messages; the comments do not
-- change the core, which compiles to the same core. Without the flag, the core and the JSON have
-- no origins.
case_RecordProvenance :: Assertion
case_RecordProvenance = do
    let model = [ "enum Color = red | green", "abstract Tools 1..3", "hammer : Tools ?", "initial a ?"
                , "    final b ?", "x -> integer := 1", "xor m", "    initial idle --> busy", "    busy"
                , "[ never busy before a ]" ]
        output mode' provenance m = case compileOneFragment defaultClaferArgs{mode = [mode'], core = True, record_provenance = provenance} (unlines m) of
            Right r -> return $ outputCode $ fromJust $ Map.lookup mode' r
            Left errs' -> assertFailure (show errs') >> return ""
    x <- output Clafer True model
    all (`isInfixOf` x)
      [ "] // abstract multiplicity, 2:1", "{} // enum, 1:1", "] // final, 5:5", "] // :=, 6:1"
      , "] // initial, 4:1", "] // initial, 8:5", "] // transition, 8:13", "] // never before, 10:3" ] @? ("origins missing:\n" ++ x)
    plain <- output Clafer False model
    not ("//" `isInfixOf` drop 1 (dropWhile (/= '\n') plain)) @? ("an origin without the flag:\n" ++ plain)
    -- the comments of the origins are what a core with them compiles to without
    withoutOrigins x == plain @? ("the comments of the origins not removed:\n" ++ withoutOrigins x)
    withoutOrigins "[x = \"a // b\"]\n" == "[x = \"a // b\"]\n" @? "a comment that is not an origin removed"
    y <- output Clafer False (lines x)
    plain == y @? ("The core with origins is not the core:\n" ++ plain ++ "\n" ++ y)
    json <- output JSON False model
    not ("Origin" `isInfixOf` json) @? "an origin in the JSON without the flag"
    jsonWith <- output JSON True model
    ("\"_eOrigin\"" `isInfixOf` jsonWith && "\"_cOrigin\"" `isInfixOf` jsonWith) @? "no origin in the JSON with the flag"

-- The multiplicity of an abstract clafer bounds the number of all its instances (#129,
-- kbak/clafer-semantics#193): globally at the top level, per parent instance when nested, in
-- every state. The rich model keeps it as written, the core has it as a constraint, which
-- static and temporal Alloy and Choco get, and a subclafer's multiplicity is not checked
-- against it. Only the authored multiplicity is a bound.
case_AbstractMultiplicity :: Assertion
case_AbstractMultiplicity = do
    let
        compileIn modes' core' m = compileOneFragment defaultClaferArgs{mode = modes', core = core'} $ unlines m
        outputOf modes' core' m = case compileIn modes' core' m of
            Right r -> return $ outputCode $ fromJust $ Map.lookup (fromJust $ listToMaybe modes') r
            Left errs' -> assertFailure (show errs') >> return ""
        hasOut modes' core' m expected = do
            x <- outputOf modes' core' m
            (expected `isInfixOf` x) @? (expected ++ " not in\n" ++ x)
        lacksOut modes' core' m unexpected = do
            x <- outputOf modes' core' m
            not (unexpected `isInfixOf` x) @? (unexpected ++ " in\n" ++ x)
        tools = [ "abstract Tools 3..6", "hammer : Tools 4", "saw : Tools 4" ]
        nested = [ "abstract Base", "    abstract Val ?", "P : Base 2", "    x : Base.Val ?", "    y : Base.Val ?" ]
    -- no refinement error, although each subclafer has more instances than the bound allows together
    hasOut [Clafer] False tools "abstract 0..* Tools 3..6 {}"
    hasOut [Clafer] True tools "[((#Tools) >= 3) && ((#Tools) <= 6)]"
    hasOut [Clafer] True tools "abstract 0..* Tools 0..* {}"
    hasOut [Alloy] False tools "fact { ((#Tools) >= 3) && ((#Tools) <= 6) }"
    hasOut [Choco] False tools "Constraint(and(greaterThanEqual(card(global($Tools)), constant(3)), lessThanEqual(card(global($Tools)), constant(6))));"
    -- in every state of a temporal model
    hasOut [Alloy] False (tools ++ ["[ G some hammer ]"]) "fact { always (((#alive_Tools) >= 3) && ((#alive_Tools) <= 6)) }"
    -- per parent instance: the explicit core keeps the multiplicity of a nested abstract
    -- clafer (AbstractMultiplicity.nested in the semantics), the backends get a constraint
    hasOut [Clafer] True nested "abstract 0..* Val 0..1 {}"
    lacksOut [Clafer] True nested "#this.Val"
    hasOut [Alloy] False nested "(#(this.@r_Val)) <= 1"
    -- both explicit models compile to themselves
    forM_ [tools, nested] $ \m -> forM_ [False, True] $ \core' -> do
        x <- outputOf [Clafer] core' m
        y <- outputOf [Clafer] core' (lines x)
        x == y @? "Not a fixpoint (core: " ++ show core' ++ "):\n" ++ x ++ "\n" ++ y
    -- without a multiplicity, no bound; an unused abstract clafer has no instances, which is no bound
    lacksOut [Clafer] True [ "abstract Tools", "hammer : Tools 4" ] "#Tools"
    lacksOut [Clafer] True [ "abstract Tools", "b ?" ] "#Tools"
    -- an unused abstract clafer with a lower bound is kept, and the bound leaves no instance
    hasOut [Clafer] True [ "abstract Tools 2", "b ?" ] "[(#Tools) = 2]"
    -- the scope leaves room for the upper bound, which a subclafer may reach alone
    hasOut [Alloy] False [ "abstract Tools 3..6", "hammer : Tools *" ] "6 hammer"

-- The simple scope analysis reads the rich IR: the upper bounds of the abstract clafers, which
-- bound their subclafers, globally or per parent instance; the counting constraints; the set
-- references to a target that the multiplicities bound. The temporal Alloy output encodes the
-- literals of an enumeration as constants.
case_RichScopes :: Assertion
case_RichScopes = do
    let
        outputOf m = case compileOneFragment defaultClaferArgs{mode = [Alloy]} $ unlines m of
            Right r -> return $ outputCode $ fromJust $ Map.lookup Alloy r
            Left errs' -> assertFailure (show errs') >> return ""
        runLine m = do
            x <- outputOf m
            return $ fromMaybe "" $ find ("run show" `isPrefixOf`) $ lines x
        scopes m expected = do
            l <- runLine m
            forM_ expected $ \e -> (e `isInfixOf` l) @? (e ++ " not in: " ++ l)
        has m expected = do
            x <- outputOf m
            (expected `isInfixOf` x) @? (expected ++ " not in\n" ++ x)
        lacks m unexpected = do
            x <- outputOf m
            not (unexpected `isInfixOf` x) @? (unexpected ++ " in\n" ++ x)
    -- the upper bound of a top-level abstract clafer, also for the abstract clafer itself
    scopes [ "abstract Tools 3..6", "hammer : Tools *", "saw : Tools *" ] [ "6 Tools", "6 hammer", "6 saw" ]
    scopes [ "abstract Tools 3..6", "hammer : Tools 0..2", "saw : Tools 1..5" ] [ "6 Tools", "2 hammer", "5 saw" ]
    -- per parent instance for a nested abstract clafer
    scopes [ "abstract Shop", "    abstract Tools 2..4", "    hammer : Tools *", "s1 : Shop", "s2 : Shop" ] [ "8 Tools", "8 hammer" ]
    -- counting constraints, also with the number first and in a conjunction
    scopes [ "A *", "[ #A > 4 ]", "B *", "    c ?", "[ 3 <= #B.c && #B >= 2 ]" ] [ "5 A", "3 B", "3 c" ]
    -- a set reference to a bounded target, not a bag, nor a reference to an unbounded target
    scopes [ "enum Color = red | green | blue", "Car 2", "    paint -> Color 0..10", "    tint ->> Color 0..10" ]
           [ "6 paint", "20 tint" ]
    scopes [ "Gs *", "Car 2", "    paint -> Gs 0..10" ] [ "20 paint" ]
    -- the subclafers of an abstract clafer may share targets (#125); a count through a reference
    -- counts targets
    scopes [ "Target 2", "abstract Ref -> Target", "r : Ref 2", "a : Ref", "c : Ref", "[ #r.dref = 2 ]" ] [ "4 Ref" ]
    -- the literals of an enumeration are constants in the temporal Alloy output
    let enum = [ "enum Color = red | green", "Car", "    color -> Color", "    [ color = red => X color = green ]" ]
    has enum "one sig red extends Color"
    has enum "fun alive_red : set red { red }"
    has enum "r_red : set red"
    lacks enum "p_red"
    lacks enum "red_1"

-- The past-time operators (#127): previous, once, historically, since and triggered are core
-- operators, which both explicit models print as written; their keywords are reserved; a model
-- with them is temporal; in the temporal Alloy output, they are Alloy's operators at the top
-- level and in the context of a top-level clafer, and look back only in the current lifetime of
-- the parent otherwise; their negations are their duals.
case_PastOperators :: Assertion
case_PastOperators = do
    let
        pastModel = [ "a ?", "b ?", "Q *", "    P ?", "        c ?", "        d ?"
                , "        [ G (c => previous d) ]", "        [ G !(once c) ]", "        [ G (c since d) ]"
                , "[ G (a => previous b) ]", "[ G (historically a || a since b) ]", "[ G (a triggered b) ]"
                , "[ G !(previous a) ]", "[ G !(a since b) ]", "[ G some Q ]" ]
        compileIn modes' core' m = compileOneFragment defaultClaferArgs{mode = modes', core = core'} $ unlines m
        output modes' core' m = case compileIn modes' core' m of
            Right r -> return $ fromJust $ Map.lookup (fromJust $ listToMaybe modes') r
            Left errs' -> assertFailure (show errs') >> return NoCompilerResult{reason = ""}
        hasIn modes' core' expected = do
            x <- outputCode <$> output modes' core' pastModel
            (expected `isInfixOf` x) @? (expected ++ " not in\n" ++ x)
    -- the explicit models, as written, and fixpoints
    forM_ [False, True] $ \core' -> do
        hasIn [Clafer] core' "[G ((some a) => (previous (some b)))]"
        hasIn [Clafer] core' "[G ((historically (some a)) || ((some a) since (some b)))]"
        hasIn [Clafer] core' "[G ((some a) triggered (some b))]"
        hasIn [Clafer] core' "[G (!(once (some this.c)))]"
        x <- outputCode <$> output [Clafer] core' pastModel
        y <- outputCode <$> output [Clafer] core' (lines x)
        x == y @? "Not a fixpoint (core: " ++ show core' ++ "):\n" ++ x ++ "\n" ++ y
    hasIn [JSON] True "\"_op\":\"previous\""
    -- the top level, and a clafer whose parent is not the root, with the negations as duals
    hasIn [Alloy] False "fact { always (always ((some alive_a) => (before (some alive_b)))) }"
    hasIn [Alloy] False "fact { always (always (not before not (!(some alive_a)))) }"
    hasIn [Alloy] False "fact { always (always ((!(some alive_a)) triggered (!(some alive_b)))) }"
    hasIn [Alloy] False "before (some self_.(@p_P :> alive_Q) and (some self_.@r_d))"
    hasIn [Alloy] False "not (some self_.(@p_P :> alive_Q) since (some self_.(@p_P :> alive_Q) and not (!(some self_.@r_c))))"
    hasIn [Alloy] False "((some self_.(@p_P :> alive_Q) and (some self_.@r_c)) since (some self_.(@p_P :> alive_Q) and (some self_.@r_d)))"
    -- a temporal pastModel: no Choco output
    choco <- output [Choco] False pastModel
    case choco of
      NoCompilerResult{} -> return ()
      _ -> assertFailure "Choco output of a pastModel with past-time operators"
    -- the keywords are reserved
    forM_ ["previous", "once", "historically", "since", "triggered"] $ \k ->
      case compileIn [Clafer] False [k ++ " ?"] of
        Left _ -> return ()
        Right _ -> assertFailure $ "A clafer named " ++ k ++ " compiled"

-- The value of an initializer with temporal operators is evaluated in the context of the parent
-- (#123), where the initializer is a constraint (#127): its obligations are bounded by the parent
-- of the parent, P, and an instance of x appears when it was not there in the previous state of
-- that lifetime. Without temporal operators, the value is the initial value in the context of x.
case_InitialValueTemporalContext :: Assertion
case_InitialValueTemporalContext = do
    let model inner = [ "P ?", "    Box ?", "        flag ?", "        x -> integer := if " ++ inner ++ " then 1 else 2"
                      , "[ initially (some P.Box && X no P.Box) ]" ]
    hasAlloy (model "X (some flag)") "fact { all self_ : Box | always (self_ in alive_Box implies (all  x_1 : self_.@r_x | (before (some self_.(@p_Box :> alive_P) and (x_1 in (self_.@r_x)))) || ((x_1.@x_ref) = ((after (not some self_.(@p_Box :> alive_P) or (some self_.@r_flag))) => 1 else 2)))) }"
    hasAlloy (model "initially (some flag)") "(((!(before (some self_.(@p_Box :> alive_P) and (some (self_ & alive_Box))))) => (some self_.@r_flag)) => 1 else 2)"
    hasAlloy (model "some flag") "((some (self_.(@p_x :> alive_Box)).@r_flag) => 1 else 2)"
