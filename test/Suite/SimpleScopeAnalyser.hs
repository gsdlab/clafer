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

import qualified Data.Map as M

import qualified Test.Framework as T
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.HUnit


tg_Test_Suite_SimpleScopeAnalyser :: T.Test
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
			, "abstract F : H"
			, "f1 : F 2..5"
			, "    m 0"
			]

expectedScopesSet :: M.Map UID Integer
expectedScopesSet = M.fromList $ [ ("c0_a", 0) 
							--	 , ("c0_b", 1)	-- uses global scope
							--	 , ("c0_c", 1)	-- uses global scope
							--	 , ("c0_d", 1) 	-- uses global scope
							--	 , ("c0_e", 1)	-- uses global scope
								 , ("c0_f", 4)
								 , ("c0_g", 3)
								 , ("c0_gs", 2)
								 , ("c0_H", 22)
								 , ("c0_i", 22)
								 , ("c0_j", 22)
								 , ("c0_k", 44)
								 , ("c0_Hs", 16)  -- not sure where the 16 comes from
								 , ("c0_H1", 2)
								 , ("c0_H12", 4)
								 , ("c0_H2", 4)
								 , ("c0_H3", 2)
								 , ("c0_H4", 5)
								 , ("c0_Hs2", 16)  -- not sure where the 16 comes from
								 , ("c0_Hs3", 8)
								 , ("c0_l", 8)
								 , ("c0_F", 5)
								 , ("c0_f1", 5)
								 , ("c0_m", 0)
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