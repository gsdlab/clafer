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

     The IR keeps the multiplicity as written: no pass changes the multiplicity of an abstract
     clafer (the optimizer does not give one that nothing extends @0..0@; that is a backend's
     choice, "Language.Clafer.Optimizer.Optimizer.zeroUnusedAbstracts").

     The explicit core keeps the multiplicity of a nested abstract clafer, which is an ordinary
     per-parent multiplicity over the instances of its subclafers
     (@AbstractMultiplicity.nested@, @valid_iff_global@ in the semantics), and lowers the one of a
     top-level abstract clafer, a global count, to a constraint next to it, e.g.,
     @[ (#Tools >= 3) && (#Tools <= 6) ]@ for @abstract Tools 3..6@, which is then @0..*@. The
     backends of this compiler read the multiplicity of each clafer as the number of its own
     instances, so they get every bound as a constraint, @#this.Rack@ in the parent of a nested
     one.
-}
module Language.Clafer.Intermediate.AbstractMultiplicity
  ( Bounds (..)
  , lowerAbstractBounds
  ) where

import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer

-- | Which multiplicities of abstract clafers become constraints.
data Bounds
  = TopLevelBounds  -- ^ of the top-level abstract clafers: the explicit core
  | AllBounds       -- ^ of all the abstract clafers: the core for the backends
  deriving (Eq, Show)

unrestricted :: Interval
unrestricted = (0, -1)

-- | The module with the bound of each abstract clafer that the choice lowers as a constraint
--   next to it: of the module for a top-level abstract clafer, of its parent for a nested one.
--   The abstract clafer is then unrestricted.
lowerAbstractBounds :: Bounds -> IModule -> IModule
lowerAbstractBounds which imodule = imodule{_mDecls = lowerElements $ _mDecls imodule}
  where
  lowerElements = concatMap lowerElement
  lowerElement (IEClafer c) = IEClafer c'{_elements = lowerElements $ _elements c'} : constraints
    where
    (c', constraints) = case _card c of
      Just b | _isAbstract c, b /= unrestricted, which == AllBounds || isTopLevel c ->
        ( c{_card = Just unrestricted}
        , [ IEConstraint' True p (Just $ Origin "abstract multiplicity" $ _cinPos c) | Just p <- [boundOf c b] ] )
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
