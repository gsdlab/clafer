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
import Language.Clafer.Front.AbsClafer (Span (..), noSpan)
import Language.Clafer.Intermediate.Intclafer
import Language.ClaferT (CErr (..), ErrPos (..), modifyEnv)
import Language.Clafer.Generator.Html (highlightErrorsIn)

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
        case compileOneFragment defaultClaferArgs{mode = [Alloy]} (unlines
                [ "abstract Engine", "gas : Engine", "abstract Car", "    abstract engine -> Engine"
                , "    xor gear", "        initial park --> drive", "        drive"
                , "tesla : Car", "    " ++ modifier ++ " motor : engine" ]) of
            Right r -> let alloy = outputCode $ fromJust $ Map.lookup Alloy r
                           fixed = "implies (this.@engine_ref)' = this.@engine_ref)" `isInfixOf` alloy
                       in fixed == (modifier /= "") @? (modifier ++ ": " ++ alloy)
            Left errs' -> assertFailure $ modifier ++ ": " ++ show errs'

-- A clafer which extends itself is reported as such, not as a missing super.
case_SelfInheritanceReported :: Assertion
case_SelfInheritanceReported =
    case compileOneFragment defaultClaferArgs "abstract A : A\nb : A" of
        Left errs' -> ("inherits from itself" `isInfixOf` show errs') @? "Unexpected errors\n" ++ show errs'
        Right _ -> assertFailure "abstract A : A compiled"
