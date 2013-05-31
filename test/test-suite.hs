{-# OPTIONS_GHC -XTemplateHaskell #-}
import Data.List
import Data.Map 
import Test.Framework
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.HUnit
import Test.QuickCheck
import Language.Clafer
import Language.ClaferT
import Language.Clafer.ClaferArgs

tg_testsuite = $(testGroupGenerator)

main = defaultMain[tg_testsuite]