module Optimizer.Optimizer where

import Data.Maybe

import Front.Absclafer
import Intermediate.Intclafer

optimizeModule :: IModule -> IModule
optimizeModule = map optimizeDeclaration


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