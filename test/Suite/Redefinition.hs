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
module Suite.Redefinition (tg_Test_Suite_Redefinition) where

import Language.Clafer
import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer

import Functions

import qualified Data.Map as M
import Data.Maybe (isNothing, isJust, fromJust)
import Data.StringMap
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

tg_Test_Suite_Redefinition :: TestTree
tg_Test_Suite_Redefinition = $(testGroupGenerator)

model :: String
model = unlines
    [ "abstract Component"
    , "    abstract InPort ->> Signal"
    , "    abstract OutPort ->> Signal"
    , "abstract Signal"
    , "abstract Command : Signal"
    , "abstract MotorCommand : Command"
    , "abstract Request : Signal"
    , "stop : Request"
    , "abstract Controller : Component"
    , "    abstract req : InPort -> Request ?"  -- bag to set and cardinality refinement
    , "    down : Request"
    , "WinController : Controller"
    , "    req : req -> stop"             -- redefinition
    , "    cmd : OutPort -> MotorCommand" -- nested inheritance which requires inheritance hierarchy traversal
    , "abstract Person -> Person 2"
    , "Alice : Person ->> Bob 3"          -- improper refinement (cardinality, bag to set, type)
    , "Bob : Person 2"                    -- proper refinement (cardinality, no ref)
    ]


case_NestedInheritanceMatchTest :: Assertion
case_NestedInheritanceMatchTest = case compileOneFragment defaultClaferArgs model of
    Left errors -> assertFailure $ show errors
    Right compilerResultMap -> case M.lookup Alloy42 compilerResultMap of
        Nothing -> assertFailure "No Alloy42 result in the result map"
        Just compilerResult -> let
                uidIClaferMap' :: StringMap IClafer
                uidIClaferMap' = uidIClaferMap $ claferEnv compilerResult
                c0_req = fromJust $ findIClafer uidIClaferMap' "c0_req"
                c0_req_match = matchNestedInheritance uidIClaferMap' c0_req
                c1_req = fromJust $ findIClafer uidIClaferMap' "c1_req"
                c1_req_match = matchNestedInheritance uidIClaferMap' c1_req
                c0_cmd = fromJust $ findIClafer uidIClaferMap' "c0_cmd"
                c0_cmd_match = matchNestedInheritance uidIClaferMap' c0_cmd
                c0_Component = fromJust $ findIClafer uidIClaferMap' "c0_Component"
                c0_Component_match = matchNestedInheritance uidIClaferMap' c0_Component
                c0_InPort = fromJust $ findIClafer uidIClaferMap' "c0_InPort"
                c0_InPort_match = matchNestedInheritance uidIClaferMap' c0_InPort
                c0_WinController = fromJust $ findIClafer uidIClaferMap' "c0_WinController"
                c0_WinController_match = matchNestedInheritance uidIClaferMap' c0_WinController
                c0_down = fromJust $ findIClafer uidIClaferMap' "c0_down"
                c0_down_match = matchNestedInheritance uidIClaferMap' c0_down
                c0_Alice = fromJust $ findIClafer uidIClaferMap' "c0_Alice"
                c0_Alice_match = matchNestedInheritance uidIClaferMap' c0_Alice
                c0_Bob = fromJust $ findIClafer uidIClaferMap' "c0_Bob"
                c0_Bob_match = matchNestedInheritance uidIClaferMap' c0_Bob
            in do
                isJust c0_req_match @? ("NestedInheritanceMatch not found for " ++ show c0_req)
                isProperNesting uidIClaferMap' (c0_req_match) @? ("Improper nesting for " ++ show c0_req)
                (True, True, True) == isProperRefinement uidIClaferMap' (c0_req_match) @? ("Improper refinement for " ++ show c0_req)
                (not $ isProperRedefinition (c0_req_match)) @? ("Improper redefinition for " ++ show c0_req)

                isJust c1_req_match @? ("NestedInheritanceMatch not found for " ++ show c1_req)
                isProperNesting uidIClaferMap' (c1_req_match) @? ("Improper nesting for " ++ show c1_req)
                (True, True, True) == isProperRefinement uidIClaferMap' (c1_req_match) @? ("Improper refinement for " ++ show c1_req)
                isProperRedefinition (c1_req_match) @? ("Improper redefinition for " ++ show c1_req)

                isJust c0_cmd_match @? ("NestedInheritanceMatch not found for " ++ show c0_cmd)
                isProperNesting uidIClaferMap' (c0_cmd_match) @? ("Improper nesting for " ++ show c0_cmd)
                (True, True, True) == isProperRefinement uidIClaferMap' (c0_cmd_match) @? ("Improper refinement for " ++ show c0_cmd)
                (not $ isProperRedefinition (c0_cmd_match)) @? ("Improper redefinition for " ++ show c0_cmd)

                isNothing c0_Component_match @? ("Non-existing match found for " ++ show c0_Component)
                isNothing c0_InPort_match @? ("Non-existing match found for " ++ show c0_InPort)

                isJust c0_WinController_match @? ("NestedInheritanceMatch not found for" ++ show c0_WinController)

                isJust c0_down_match @? ("NestedInheritanceMatch not found for" ++ show c0_down)
                (not $ isProperNesting uidIClaferMap' (c0_down_match)) @? ("Improper nesting for " ++ show c0_down)
                (True, True, True) == (isProperRefinement uidIClaferMap' (c0_down_match)) @? ("Improper refinement for " ++ show c0_down)
                (not $ isProperRedefinition (c0_down_match)) @? ("Improper redefinition for " ++ show c0_down)

                isJust c0_Alice_match @? ("NestedInheritanceMatch not found for " ++ show c0_Alice)
                isProperNesting uidIClaferMap' (c0_Alice_match) @? ("Improper nesting for " ++ show c0_Alice)
                (False, False, True) == (isProperRefinement uidIClaferMap' (c0_Alice_match)) @? ("Improper refinement for " ++ show c0_Alice)
                (not $ isProperRedefinition (c0_Alice_match)) @? ("Improper redefinition for " ++ show c0_Alice)

                isJust c0_Bob_match @? ("NestedInheritanceMatch not found for " ++ show c0_Bob)
                isProperNesting uidIClaferMap' (c0_Bob_match) @? ("Improper nesting for " ++ show c0_Bob)
                (True, True, True) == (isProperRefinement uidIClaferMap' (c0_Bob_match)) @? ("Improper refinement for " ++ show c0_Bob)
                (not $ isProperRedefinition (c0_Bob_match)) @? ("Improper redefinition for " ++ show c0_Bob)
