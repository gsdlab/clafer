{-# OPTIONS_GHC -XTemplateHaskell #-}
import qualified Data.List as List
import Data.Monoid
import Language.Clafer
import Language.ClaferT
import Language.Clafer.Css
import Test.Framework
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.HUnit
import Test.QuickCheck
import System.Directory
import System.IO

tg_testsuite = $(testGroupGenerator)

main = defaultMain[tg_testsuite]

getClafer file = do
					clafer <- readFile file
					return clafer

getClafers dir = do
					files <- getDirectoryContents dir
					let clafers = List.filter (\f -> (dropWhile (/='.') f) == "cfr") files
					mapM getClafer clafers

positiveClafers = do
					clafers <- getClafers "test/positive"
					return clafers


compileOneFragment :: ClaferArgs -> InputModel -> Either [ClaferErr] CompilerResult
compileOneFragment args model =
 	runClafer args $
		do
			addModuleFragment model
			parse
			compile
			generate

compiledCheck :: Either a b -> Bool
compiledCheck (Left _) = False
compiledCheck (Right _) = True

case_compileTest :: Assertion
case_compileTest = do 
						clafers <- positiveClafers
						getAll (List.foldr (\x -> mappend $ All $ compiledCheck $ compileOneFragment defaultClaferArgs x) (All True) clafers) @? "Error in one of clafers in positive"