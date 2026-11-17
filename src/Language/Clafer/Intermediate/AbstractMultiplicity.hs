{-
 Copyright (C) 2026 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
{- | The multiplicity of an abstract clafer (gsdlab/clafer#129, kbak/clafer-semantics#193): an
     authored multiplicity bounds the number of all the instances of the abstract clafer, of all
     its subclafers together. For a top-level abstract clafer, the count is global, across all the
     actual parents; for a nested one, it is per instance of its declared parent. In a temporal
     model, the bound holds in every state. Without a multiplicity, the number is unrestricted.

     The rich IR keeps the multiplicity as written. The core has the bound as a constraint, next
     to the abstract clafer, e.g., @[ (#Tools >= 3) && (#Tools <= 6) ]@ for @abstract Tools 3..6@,
     and the abstract clafer is unrestricted (@0..*@).

     Only the authored multiplicity is a bound, not one that the optimizer gives an abstract clafer
     that nothing extends (@0..0@), nor a scope. The authored multiplicities come from the AST,
     since the optimizer changes the ones of the IR.
-}
module Language.Clafer.Intermediate.AbstractMultiplicity
  ( AuthoredBounds
  , authoredBounds
  , withAuthoredBounds
  , lowerAbstractBounds
  ) where

import Control.Lens.Plated (transformOn, universeOnOf)
import Data.Data.Lens (biplate, uniplate)
import qualified Data.Map as Map
import Language.Clafer.Common
import Language.Clafer.Front.AbsClafer
import Language.Clafer.Intermediate.Desugarer (desugarCard)
import Language.Clafer.Intermediate.Intclafer

-- | The multiplicities written on the abstract clafers, by the positions of the clafers.
type AuthoredBounds = Map.Map Span Interval

authoredBounds :: Module -> AuthoredBounds
authoredBounds ast' = Map.fromList
  [ (s, i)
  | Clafer s (Abstract _) _ _ _ _ _ crd _ _ _ <- universeOnOf biplate uniplate ast' :: [Clafer]
  , Just i <- [desugarCard crd] ]

-- | The module with the multiplicities of the abstract clafers as written, unrestricted without
--   one: the rich IR.
withAuthoredBounds :: AuthoredBounds -> IModule -> IModule
withAuthoredBounds bounds = transformOn biplate authored
  where
  authored c
    | _isAbstract c = c{_card = Just $ Map.findWithDefault unrestricted (_cinPos c) bounds}
    | otherwise = c

unrestricted :: Interval
unrestricted = (0, -1)

-- | The module with the bound of each abstract clafer as a constraint next to it: of the module
--   for a top-level abstract clafer, of its parent for a nested one. The abstract clafer is then
--   unrestricted, unless the optimizer gave it no instances (@0..0@), which a backend may need:
--   in Alloy, an abstract signature that nothing extends has atoms of its own.
lowerAbstractBounds :: AuthoredBounds -> IModule -> IModule
lowerAbstractBounds bounds imodule = imodule{_mDecls = lowerElements $ _mDecls imodule}
  where
  lowerElements = concatMap lowerElement
  lowerElement (IEClafer c) = IEClafer c'{_elements = lowerElements $ _elements c'} : constraints
    where
    (c', constraints) = case Map.lookup (_cinPos c) bounds of
      Just b | _isAbstract c, b /= unrestricted ->
        -- the optimizer changed the multiplicity of a clafer that nothing extends: it has no
        -- instances, which meets a bound without a lower bound
        let optimized = _card c /= Just b
        in ( if optimized then c else c{_card = Just unrestricted}
           , [ IEConstraint True p | not optimized || fst b > 0, Just p <- [boundOf c b] ] )
      _ -> (c, [])
  lowerElement e = [e]

-- | The constraint of the bound on the number of instances of the abstract clafer, in the context
--   of its parent: @#A@ at the top level, @#this.A@ in the parent.
boundOf :: IClafer -> Interval -> Maybe PExp
boundOf c (low, high) = case [ cmp op' n | (op', n, required) <- comparisons, required ] of
    [] -> Nothing
    ps -> Just $ foldr1 (\a b -> bool iAnd [a, b]) ps
  where
  pos' = _cinPos c
  uid' = _uid c
  comparisons
    | low == high = [ (iEq, low, True) ]
    | otherwise   = [ (iGte, low, low > 0), (iLte, high, high >= 0) ]
  cmp op' n = bool op' [ count, PExp (Just TInteger) "" pos' $ IInt n ]
  count = PExp (Just TInteger) "" pos' $ IFunExp iCSet [ instances ]
  instances
    | isTopLevel c = PExp (Just $ TClafer [uid']) "" pos' $ IClaferId "" uid' True (GlobalBind uid')
    | otherwise = PExp (Just $ TClafer [uid']) "" pos' $ IFunExp iJoin
        [ PExp (Just $ TClafer [_parentUID c]) "" pos' $ IClaferId "" thisIdent True (GlobalBind $ _parentUID c)
        , PExp (Just $ TClafer [uid']) "" pos' $ IClaferId "" uid' False (GlobalBind uid') ]
  bool op' = PExp (Just TBoolean) "" pos' . IFunExp op'
