{-# OPTIONS_GHC -XTemplateHaskell #-}
import Language.Clafer
import Language.ClaferT
import Language.Clafer.Css
import Test.Framework
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.HUnit
import Test.QuickCheck
import qualified Data.Map as Map

tg_testsuite = $(testGroupGenerator)

main = defaultMain[tg_testsuite]

compileOneFragment :: ClaferArgs -> InputModel -> Either [ClaferErr] CompilerResult
compileOneFragment args model =
    runClafer args $
    	do
        	addModuleFragment model
        	parse
        	compile
        	generate
compileOneFragmentS :: ClaferArgs -> InputModel -> (Either [ClaferErr] CompilerResult, SnapShots)
compileOneFragmentS args model =
    runClaferS args $
    	do
        	addModuleFragment model
        	parse
        	compile
        	generate


case_numberOfSnapShots1 :: Assertion
case_numberOfSnapShots1 = 
	(Map.size $ snd $ compileOneFragmentS defaultClaferArgs{debug = Just True} "A") == 10 
		@? "Error not all snapshots were taken"

case_numberOfSnapShots2 :: Assertion
case_numberOfSnapShots2 = 
	(Map.size $ snd $ compileOneFragmentS defaultClaferArgs{debug = Just False} "A") == 0 
		@? "Error not all snapshots were taken"

