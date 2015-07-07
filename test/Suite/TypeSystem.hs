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
    ]

case_TypeSystemTest :: Assertion
case_TypeSystemTest = case compileOneFragment defaultClaferArgs{keep_unused=True} model of
    Left errors -> assertFailure $ show errors
    Right compilerResultMap -> case M.lookup Alloy42 compilerResultMap of
        Nothing -> assertFailure "No Alloy42 result in the result map"
        Just compilerResult -> let
                uidIClaferMap' :: StringMap IClafer
                uidIClaferMap' = uidIClaferMap $ claferEnv compilerResult

                root_TClafer = getTClaferByUID uidIClaferMap' "root"
                clafer_TClafer = getTClaferByUID uidIClaferMap' "clafer"
                c0_A_TClafer = getTClaferByUID uidIClaferMap' "c0_A"
                c0_A_TClaferR = Just $ TClafer [ "c0_A" ]
                c0_A_TMap = getTMapByUID uidIClaferMap' "c0_A"
                c0_as_TMap = getTMapByUID uidIClaferMap' "c0_as"
                c0_as_TMapR = Just $ TMap (TClafer [ "c0_A" ]) (TClafer [ "c0_as" ])
                --c0_B_TClafer = getTClaferByUID uidIClaferMap' "c0_B"
                --c0_B_TClaferR = Just $ TClafer False False $ TClafer [ "c0_B", "c0_A" ]
            in do
                (isJust $ findIClafer uidIClaferMap' "c0_A") @? ("TypeSystemTest: clafer c0_A not found" ++ show uidIClaferMap')
                root_TClafer == Just rootTClafer @? ("TypeSystemTest: incorrect class type for 'root'. Got '" ++ show root_TClafer ++ "' instead of '" ++ show rootTClafer ++ "'")
                clafer_TClafer == Just claferTClafer @? ("TypeSystemTest: incorrect class type for 'clafer'. Got '" ++ show clafer_TClafer ++ "' instead of '" ++ show claferTClafer ++ "'")
                c0_A_TClafer == c0_A_TClaferR @? ("TypeSystemTest: incorrect class type for 'c0_A'. Got '" ++ show c0_A_TClafer ++ "' instead of '" ++ show c0_A_TClaferR ++ "'")
                c0_A_TMap == Nothing @? ("TypeSystemTest: incorrect map type for 'c0_A'. Got '" ++ show c0_A_TMap ++ "'' but it is not a reference.")
                c0_as_TMap == c0_as_TMapR @? ("TypeSystemTest: incorrect map type for 'c0_as'. Got '" ++ show c0_as_TMap ++ "' instead of '" ++ show c0_as_TMapR ++ "'")
                -- c0_B_TClafer == c0_B_TClaferR @? ("TypeSystemTest: incorrect type for 'c0_B'. Got '" ++ show c0_B_TClafer ++ "' instead of '" ++ show c0_B_TClaferR ++ "'")
