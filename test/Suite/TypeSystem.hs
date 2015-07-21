{-# LANGUAGE TemplateHaskell #-}
{-
 Copyright (C) 2015 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Suite.TypeSystem (tg_Test_Suite_TypeSystem) where

import Language.Clafer
import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.TypeSystem

import Functions

import qualified Data.Map as M
import Data.Maybe (isJust)
import Data.StringMap
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

tg_Test_Suite_TypeSystem :: TestTree
tg_Test_Suite_TypeSystem = $(testGroupGenerator)

model :: String
model = unlines
    [ "abstract A"             -- c0_A
    , "    abstract as -> A *" -- c0_as
    , "abstract B : A"         -- c0_B
    , "    as : as -> B *"     -- c1_as
    , "b : B"                  -- c0_b
    , "    [ as = b ]"
    , "    [ as.ref = b ]"
    ]

case_TypeSystemTest :: Assertion
case_TypeSystemTest = case compileOneFragment defaultClaferArgs{keep_unused=True} model of
  Left errors -> assertFailure $ show errors
  Right compilerResultMap -> case M.lookup Alloy compilerResultMap of
    Nothing -> assertFailure "No Alloy result in the result map"
    Just compilerResult ->
      let
        um' :: StringMap IClafer
        um' = uidIClaferMap $ claferEnv compilerResult

        root_TClafer = getTClaferByUID um' "root"
        clafer_TClafer = getTClaferByUID um' "clafer"
        c0_A_TClafer = getTClaferByUID um' "c0_A"
        c0_A_TClaferR = Just $ TClafer [ "c0_A" ]
        c0_A_TMap = getDrefTMapByUID um' "c0_A"
        c0_as_TMap = getDrefTMapByUID um' "c0_as"
        c0_as_TMapR = Just (TMap {_so = TClafer {_hi = ["c0_as"]}, _ta = TClafer {_hi = ["c0_A"]}})
        c0_B_TClafer = getTClaferByUID um' "c0_B"
        c0_B_TClaferR = Just $ TClafer [ "c0_B", "c0_A" ]
        c1_as_TClafer = getTClaferByUID um' "c1_as"
        c1_as_TClaferR = Just $ TClafer [ "c1_as", "c0_as" ]
        c1_as_TMap = getDrefTMapByUID um' "c1_as"
        c1_as_TMapR = Just (TMap {_so = TClafer {_hi = ["c1_as","c0_as"]}, _ta = TClafer {_hi = [ "c0_B", "c0_A" ]}})
        c0_b_TClafer = getTClaferByUID um' "c0_b"
        c0_b_TClaferR = Just $ TClafer [ "c0_b", "c0_B", "c0_A" ]
      in do
        (isJust $ findIClafer um' "c0_A")    @? ("Clafer c0_A not found" ++ show um')
        root_TClafer == Just rootTClafer     @? ("Incorrect class type for 'root':\ngot        '" ++ show root_TClafer ++ "'\ninstead of '" ++ show rootTClafer ++ "'")
        clafer_TClafer == Just claferTClafer @? ("Incorrect class type for 'clafer':\ngot        '" ++ show clafer_TClafer ++ "'\ninstead of '" ++ show claferTClafer ++ "'")
        c0_A_TClafer == c0_A_TClaferR        @? ("Incorrect class type for 'c0_A':\ngot        '" ++ show c0_A_TClafer ++ "'\ninstead of '" ++ show c0_A_TClaferR ++ "'")
        c0_A_TMap == Nothing                 @? ("Incorrect map type for 'c0_A':\ngot        '" ++ show c0_A_TMap ++ "'\nbut it is \nt a reference.")
        c0_as_TMap == c0_as_TMapR            @? ("Incorrect map type for 'c0_as':\ngot        '" ++ show c0_as_TMap ++ "'\ninstead of '" ++ show c0_as_TMapR ++ "'")
        c0_B_TClafer == c0_B_TClaferR        @? ("Incorrect class type for 'c0_B':\ngot        '" ++ show c0_B_TClafer ++ "'\ninstead of '" ++ show c0_B_TClaferR ++ "'")
        c1_as_TClafer == c1_as_TClaferR      @? ("Incorrect class type for 'c1_as':\ngot        '" ++ show c1_as_TClafer ++ "'\ninstead of '" ++ show c1_as_TClaferR ++ "'")
        c1_as_TMap == c1_as_TMapR            @? ("Incorrect map type for 'c1_as':\ngot        '" ++ show c1_as_TMap ++ "'\ninstead of '" ++ show c1_as_TMapR ++ "'")
        c0_b_TClafer == c0_b_TClaferR        @? ("Incorrect class type for 'c0_b':\ngot        '" ++ show c0_b_TClafer ++ "'\ninstead of '" ++ show c0_b_TClaferR ++ "'")
