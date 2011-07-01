module Optimizer.Optimizer where

import Data.Maybe
import Data.List

import Common
import Front.Absclafer
import Intermediate.Intclafer

optimizeModule :: IModule -> IModule
optimizeModule declarations =
  remUnusedAbs $ map optimizeDeclaration declarations


optimizeDeclaration :: IDeclaration -> IDeclaration
optimizeDeclaration x = case x of
  IClaferDecl clafer -> IClaferDecl $ optimizeClafer (1, ExIntegerNum 1) clafer
  IConstDecl constraint  -> x


optimizeClafer :: Interval -> IClafer -> IClafer
optimizeClafer interval clafer = clafer {glCard = glCard',
  elements = map (optimizeElement glCard') $ elements clafer}
  where
  glCard' = optimizeCard (fromJust $ card clafer) interval


optimizeCard :: Interval -> Interval -> Interval
optimizeCard (m, n) (m', n') = (min m m', maxEx n n')
  where
  maxEx ExIntegerAst _ = ExIntegerAst
  maxEx _ ExIntegerAst = ExIntegerAst
  maxEx (ExIntegerNum m) (ExIntegerNum n) = ExIntegerNum $ max m n


optimizeElement :: Interval -> IElement -> IElement
optimizeElement interval x = case x of
  ISubclafer clafer  -> ISubclafer $ optimizeClafer interval clafer
  ISubconstraint constraint  -> x


remUnusedAbs :: IModule -> IModule
remUnusedAbs declarations = declarations \\ unusedAbs
  where
  unusedAbs = map IClaferDecl $ findUnusedAbs clafers $ map uid $
              filter (not.isAbstract) clafers
  clafers   = toClafers declarations


findUnusedAbs :: [IClafer] -> [String] -> [IClafer]
findUnusedAbs maybeUsed [] = maybeUsed
findUnusedAbs [] _   = []
findUnusedAbs maybeUsed used = findUnusedAbs maybeUsed' $ getUniqExtended used'
  where
  (used', maybeUsed') = partition (\c -> uid c `elem` used) maybeUsed


getUniqExtended used = nub $ used >>= getExtended


getExtended :: IClafer -> [String]
getExtended clafer =
  sName ++ ((getSubclafers $ elements clafer) >>= getExtended)
  where
  sName = if not $ isOverlapping $ super clafer then [getSuper clafer] else []