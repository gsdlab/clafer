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
module Suite.SimpleScopeAnalyser (tg_Test_Suite_SimpleScopeAnalyser) where

import Language.Clafer
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.JSONMetaData
import Language.Clafer.QNameUID
import Functions

import Data.List (isInfixOf)
import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH


tg_Test_Suite_SimpleScopeAnalyser :: TestTree
tg_Test_Suite_SimpleScopeAnalyser = $(testGroupGenerator)

model :: String
model = unlines
            [ "a 0..0"
            , "b ?"
            , "c"
            , "d *"
            , "e +"
            , "f 2..4"
            , "g 3..*"
            , "gs -> g 2"
            , "abstract H"
            , "    i ?"
            , "    j *"
            , "    k 2"
            , "Hs -> H 3..*"
            , "H1 : H 2"
            , "    H12 : H 2"
            , "H2 : H 4..4"
            , "H3 : H 1..2"
            , "H4 : H 5..*"
            , "Hs2 -> H 0..*"
            , "Hs3 -> H 5..8"
            , "    l ?"
            , "abstract FF : H"
            , "f1 : FF 2..5"
            , "    m 0"
            , "i1 -> integer 2..4"
            , "i2 ->> integer ?"
            , "i3 -> integer *"
            , "i4 ->> integer *"
            , "s1 -> string 2..*"
            , "s2 ->> string"
            , "s3 -> string +"
            , "s4 ->> string +"
            ]

expectedScopesSet :: M.Map UID Integer
expectedScopesSet = M.fromList $ [ ("a", 0)
                            --   , ("b", 1)  -- uses global scope
                            --   , ("c", 1)  -- uses global scope
                            --   , ("d", 1)  -- uses global scope
                            --   , ("e", 1)  -- uses global scope
                                 , ("f", 4)
                                 , ("g", 3)
                                 , ("gs", 2)
                                 , ("H", 22)
                                 , ("i", 22)
                                 , ("j", 22)
                                 , ("k", 44)
                                 , ("Hs", 22)
                                 , ("H1", 2)
                                 , ("H12", 4)
                                 , ("H2", 4)
                                 , ("H3", 2)
                                 , ("H4", 5)
                                 , ("Hs2", 22)
                                 , ("Hs3", 8)
                                 , ("l", 8)
                                 , ("FF", 5)
                                 , ("f1", 5)
                                 , ("m", 0)
                                 , ("i1", 4)
                            --   , ("i2", 1) -- uses global scope
                            --   , ("i3", 1) -- uses global scope
                            --   , ("i4", 1) -- uses global scope
                                 , ("s1", 2)
                            --   , ("s2", 1) -- uses global scope
                            --   , ("s3", 1) -- uses global scope
                            --   , ("s4", 1) -- uses global scope
                                 ]


-- aggregates a difference
aggregateDifference :: UID -> Integer -> Integer -> Maybe String
aggregateDifference k computedV expectedV =
    if computedV == expectedV
    then Nothing
    else Just $ k ++ " | computed: " ++ show computedV ++ " | expected: " ++ show expectedV ++ " |"

-- prints only computed scopes missing in expected
onlyComputed :: M.Map UID Integer -> M.Map UID String
onlyComputed = M.mapWithKey (\k v -> k ++ " | computed: " ++ show v ++ " | no expected |")


-- prints only expected scopes missing in computed
onlyExpected :: M.Map UID Integer -> M.Map UID String
onlyExpected = M.mapWithKey (\k v -> k ++ " | no computed | expected: " ++ show v ++ " |")

case_ScopeTest :: Assertion
case_ScopeTest = do
    let
        -- use simple scope inference
        (Right compilerResultMap) = compileOneFragment defaultClaferArgs model
        (Just compilerResult) = M.lookup Alloy compilerResultMap
        computedScopesSet :: M.Map UID Integer
        computedScopesSet = M.fromList $ scopesList compilerResult

        differences = M.mergeWithKey aggregateDifference onlyComputed onlyExpected computedScopesSet expectedScopesSet

    (M.size differences) == 0 @?
        "Computed scopes different from expected:\n" ++ (unlines $ M.foldl (\acc v -> v:acc) [] differences)


-- The lower bound of a group cardinality is covered: four C with at least 2 Items each,
-- and two D with at least 3 of their at most 2 Ys or of their Zs.
case_ScopeFromGroupCardinality :: Assertion
case_ScopeFromGroupCardinality = do
    let
        groupModel = unlines
            [ "abstract 2..3 A"
            , "    Item *"
            , "C : A 4"
            , "3..4 D 2"
            , "    Y 0..2"
            , "    Z *"
            ]
        (Right compilerResultMap) = compileOneFragment defaultClaferArgs groupModel
        (Just compilerResult) = M.lookup Alloy compilerResultMap
        computedScopes = M.fromList $ scopesList compilerResult
    M.lookup "Item" computedScopes @?= Just 8
    M.lookup "Y" computedScopes @?= Just 4
    M.lookup "Z" computedScopes @?= Just 6

-- A reference with an unbounded multiplicity may point to all 20 B in each of the 6 A, so its scope is
-- 120, above 100: the statistics warn and suggest an upper bound. With the upper bound 3, it is 18.
case_LargeReferenceScopeWarning :: Assertion
case_LargeReferenceScopeWarning = do
    let
        refsModel card' = unlines
            [ "abstract B"
            , "B1 : B 20"
            , "A 6"
            , "    refs -> B " ++ card'
            ]
        statisticsOf m = let
            (Right compilerResultMap) = compileOneFragment defaultClaferArgs m
            (Just compilerResult) = M.lookup Alloy compilerResultMap
          in statistics compilerResult
        warning = "the scope of refs -> B 0..* is 120, since refs may point to all 20 B in each of its parents."
    (warning `isInfixOf` statisticsOf (refsModel "*")) @?
        "No large scope warning in:\n" ++ statisticsOf (refsModel "*")
    ("refs -> B 0..10" `isInfixOf` statisticsOf (refsModel "*")) @? "No upper bound suggested"
    (not $ "Warning" `isInfixOf` statisticsOf (refsModel "0..3")) @?
        "Unexpected warning in:\n" ++ statisticsOf (refsModel "0..3")

case_ReadScopesJSON :: Assertion
case_ReadScopesJSON = do
    let
        -- use simple scope inference
        (Right compilerResultMap) = compileOneFragment defaultClaferArgs model
        (Just compilerResult) = M.lookup Alloy compilerResultMap
        Just (iModule, _, _) = cIr $ claferEnv compilerResult

        qNameMaps = deriveQNameMaps iModule

        computedScopes :: [ (UID, Integer) ]
        computedScopes = scopesList compilerResult

        scopesInJSON = generateJSONScopes qNameMaps computedScopes
        decodedScopes = parseJSONScopes qNameMaps scopesInJSON

        differences = M.mergeWithKey aggregateDifference onlyComputed onlyExpected (M.fromList computedScopes) (M.fromList decodedScopes)

    (M.size differences) == 0 @?
        "Parsed scopes different from original:\n" ++ (unlines $ M.foldl (\acc v -> v:acc) [] differences)

-- | chocosolver's scope files (ScopeFile) name clafers by their UIDs and also give the default scope
-- | and the ranges: the clafer scopes are read, by UID or by name, and the other entries are skipped.
case_ReadChocoScopesJSON :: Assertion
case_ReadChocoScopesJSON = do
    let
        (Right compilerResultMap) = compileOneFragment defaultClaferArgs model
        (Just compilerResult) = M.lookup Alloy compilerResultMap
        Just (iModule, _, _) = cIr $ claferEnv compilerResult
        qNameMaps = deriveQNameMaps iModule
        scopesInJSON = unlines
            [ "["
            , "{\"lpqName\": \"b\", \"scope\": 2},"
            , "{\"lpqName\": \"H::k\", \"scope\": 5},"
            , "{\"defaultScope\": 1},"
            , "{\"int\": [-8, 7]},"
            , "{\"decimal\": [-2.5, 2.5]}"
            , "]" ]
    M.fromList (parseJSONScopes qNameMaps scopesInJSON) @?= M.fromList [ ("b", 2), ("k", 5) ]

-- | The least-partially-qualified name of the only clafer of a model is its name; the search for it
-- | did not end (clafer --meta-data hung on such a model).
case_LpqNameOfOnlyClafer :: Assertion
case_LpqNameOfOnlyClafer = do
    let
        (Right compilerResultMap) = compileOneFragment defaultClaferArgs "x\n"
        (Just compilerResult) = M.lookup Alloy compilerResultMap
        Just (iModule, _, _) = cIr $ claferEnv compilerResult
    getLPQName (deriveQNameMaps iModule) "x" @?= Just "x"
