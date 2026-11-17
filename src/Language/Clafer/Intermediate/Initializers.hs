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
{- | The meaning of the initializers ('IEInitializer'), which the IR keeps as written (the rich
     explicit model); "Language.Clafer.Intermediate.Core" lowers them to constraints for the
     explicit core model and the backends.

     * @x -> T = e@ is @[ some x => x.dref = e ]@ in the context of the parent; in a temporal
       model, it holds in every state.
     * @x -> T := e@ is the initial value of the reference (kbak/clafer-semantics#164). In a
       static model, which has a single state, it is the same as @=@. In a temporal model,
       every lifetime of @x@ starts with the value: @[ initially (this.dref = e') ]@ in the
       context of @x@, where @e'@ is @e@ with @this.parent@ for @this@, the parent instance.
       A value with temporal operators keeps its meaning only in the context of the parent
       (gsdlab/clafer#123), where an instance appears when it was not there in the previous
       state (gsdlab/clafer#127): @[ all c : this.x | (not previous (c in this.x)) => (c.dref = e) ]@
       in the context of the parent, which holds in every state of the parent.
     * A set initializer, @xs -> T * := e@, constrains the instances under the parent when the
       parent is born: @[ initially (some xs => xs.dref = e) ]@ in the context of the parent.
     * The written clocks choose between the two, whatever the multiplicity
       (kbak/clafer-semantics#194): @:= each e@ is per instance and @:= together e@ a set
       initializer. On a concrete clafer with more than one instance under a parent, @:= each e@
       constrains each instance on its own, also in a static model:
       @[ all c : xs | c.dref = e ]@ in the context of the parent, not @xs.dref = e@, which the
       instances satisfy together, e.g., with the values @1@ and @2@ for @:= each 1, 2@.
-}
module Language.Clafer.Intermediate.Initializers
  ( Semantics (..)
  , lowerInitializers
  , initializedClafer
  , initializerValue
  ) where

import Control.Lens.Plated (transformOn, universeOn)
import Data.Data.Lens (biplate)
import Data.List (find)
import Data.Maybe (fromMaybe)
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer

-- | How a backend reads the initializers.
data Semantics
  = Static     -- ^ a single state: @:=@ is @=@ (static Alloy, Choco)
  | Temporal   -- ^ traces: @:=@ gives the value of each lifetime of an instance (temporal Alloy)
  deriving (Eq, Show)

-- | The module with the initializers that the backend does not interpret replaced by
--   constraints of the parents, right after their clafers.
lowerInitializers :: Semantics -> IModule -> IModule
lowerInitializers sem imodule = imodule{_mDecls = lowerElements sem taken $ _mDecls imodule}
  where
  -- the names that a local variable must not shadow
  taken = concat [ [_uid c, _ident c] | c <- universeOn biplate imodule :: [IClafer] ]
       ++ concat [ concatMap _decls ds | PExp{_exp = IDeclPExp _ ds _} <- universeOn biplate imodule :: [PExp] ]

lowerElements :: Semantics -> [String] -> [IElement] -> [IElement]
lowerElements sem taken = concatMap lowerElement
  where
  lowerElement (IEClafer c) = IEClafer c{_elements = kept} : parentConstraints
    where
    elements' = lowerElements sem taken $ _elements c
    kept = [ own e | e <- elements', not (lowered e) ]
    -- the initializers of c, lowered to constraints of its parent, next to c
    parentConstraints = [ IEConstraint' True (asConstraint c e) (Just $ origin c e) | e <- elements', lowered e ]
    -- the per-instance := of a temporal model, in the context of the clafer
    own e@(IEInitializer False False _ eq) | not (hasTemporal $ initializerValue eq) = IEConstraint' True (initialValue c eq) (Just $ origin c e)
    own e = e
  lowerElement e = [e]
  -- the initializer of the clafer, @=@, @:=@, or @:=@ with its written clock, for --record-provenance
  origin c e = Origin (case e of
    IEInitializer{_isConstant = True} -> "="
    IEInitializer{_isExplicitClock = True, _isSetInit = True} -> ":= together"
    IEInitializer{_isExplicitClock = True} -> ":= each"
    _ -> ":=") (_cinPos c)
  -- lowered to a constraint of the parent: all but the per-instance := of a temporal model
  -- whose value has no temporal operators, which becomes a constraint of the clafer
  lowered (IEInitializer k s _ eq) = sem == Static || k || s || hasTemporal (initializerValue eq)
  lowered _ = False
  asConstraint x (IEInitializer k s _ eq)
    | sem == Temporal && not k && s = bool iInitially [ implied ]
    | sem == Temporal && not k = appearing taken x eq
    | not k && not s && plural x = eachInstance taken x eq
    | otherwise = implied
    where
    implied = bool iImpl [ PExp (Just TBoolean) (_pid eq) (_inPos eq) $ IDeclPExp ISome [] $ initializedClafer eq, eq ]
    bool op' = PExp (Just TBoolean) (_pid eq) (_inPos eq) . IFunExp op'
  asConstraint _ e = error $ "[bug] Initializers.asConstraint: not an initializer: " ++ show e
  -- a concrete clafer with more than one instance under a parent, whose per-instance := is
  -- @:= each@: without the clock, its multiplicity makes := a set initializer
  plural x = not (_isAbstract x) && maybe False (\(_, m) -> m /= 0 && m /= 1) (_card x)

-- | The per-instance value of the clafer @x@ in a static model, for each instance on its own,
--   in the context of the parent: @[ all c : this.x | c.dref = e ]@. The local variable has a
--   name that no clafer and no other local variable has, e.g., @x_1@.
eachInstance :: [String] -> IClafer -> PExp -> PExp
eachInstance taken x eq@PExp{_exp = IFunExp op' [lhs, value]} =
    bool $ IDeclPExp IAll [IDecl False [v] xs] eq{_exp = IFunExp op' [ownRef lhs, value]}
  where
  pos' = _inPos eq
  bool = PExp (Just TBoolean) (_pid eq) pos'
  xs = initializedClafer eq
  v = localName taken x
  -- a local variable, which the backends write as it is (as the name resolver gives it)
  c = PExp (_iType xs) "" pos' $ IClaferId "" v True (LocalBind v)
  -- c.dref for this.x.dref (x.dref at the top level)
  ownRef p@PExp{_exp = IFunExp j [_, dref]} | j == iJoin = p{_exp = IFunExp j [c, dref]}
  ownRef p = p
eachInstance _ _ eq = error $ "[bug] Initializers.eachInstance: not an equation: " ++ show eq

-- | A name for a local variable over the instances of @x@ that no clafer and no other local
--   variable has, e.g., @x_1@.
localName :: [String] -> IClafer -> String
localName taken x = fromMaybe (_ident x) $ find (`notElem` taken) [ _ident x ++ "_" ++ show k | k <- [1 :: Int ..] ]

-- | The per-instance initial value of the clafer @x@ whose value has temporal operators, in the
--   context of the parent, where the value is written (gsdlab/clafer#123): each instance of @x@
--   that appears, i.e., that was not an instance of @x@ under this parent in the previous state
--   of its lifetime, has the value, @[ all c : this.x | (not previous (c in this.x)) => (c.dref = e) ]@
--   (gsdlab/clafer#127). The constraint holds in every state of the parent. The local variable has
--   a name that no clafer and no other local variable has, e.g., @x_1@.
appearing :: [String] -> IClafer -> PExp -> PExp
appearing taken x eq@PExp{_exp = IFunExp op' [lhs, value]} =
    bool $ IDeclPExp IAll [IDecl False [v] xs] $ bool $ IFunExp iImpl
      [ bool $ IFunExp iNot [bool $ IFunExp iPrevious [bool $ IFunExp iIn [c, xs]]]
      , eq{_exp = IFunExp op' [ownRef lhs, value]} ]
  where
  pos' = _inPos eq
  bool = PExp (Just TBoolean) (_pid eq) pos'
  xs = initializedClafer eq
  v = localName taken x
  c = PExp (_iType xs) "" pos' $ IClaferId "" v False (LocalBind v)
  -- c.dref for this.x.dref (x.dref at the top level)
  ownRef p@PExp{_exp = IFunExp j [_, dref]} | j == iJoin = p{_exp = IFunExp j [c, dref]}
  ownRef p = p
appearing _ _ eq = error $ "[bug] Initializers.appearing: not an equation: " ++ show eq

-- | The per-instance initial value of the clafer @c@, @initially (this.dref = e')@ in its context,
--   from the equation @x.dref = e@ in the context of the parent.
initialValue :: IClafer -> PExp -> PExp
initialValue c eq@PExp{_exp = IFunExp op' [lhs, value]} =
    bool iInitially [ eq{_exp = IFunExp op' [ownRef lhs, fromParent value]} ]
  where
  bool o = PExp (Just TBoolean) (_pid eq) (_inPos eq) . IFunExp o
  pos' = _inPos eq
  thisX t = PExp t "" pos' $ IClaferId "" thisIdent True (GlobalBind $ _uid c)
  -- this.dref for x.dref
  ownRef p@PExp{_exp = IFunExp j [x, dref]} | j == iJoin = p{_exp = IFunExp j [thisX (_iType x), dref]}
  ownRef p = p
  -- this, the parent instance, is this.parent, or the root at the top level
  fromParent = transformOn biplate fromThis
  fromThis p@PExp{_iType = t, _exp = IClaferId{_sident = s}} | s == thisIdent =
    if _parentUID c /= rootIdent && _parentUID c /= baseClafer
    then p{_exp = IFunExp iJoin [ thisX (Just $ TClafer [_uid c])
                                , PExp t "" pos' $ IClaferId "" parentIdent False (GlobalBind $ _parentUID c) ]}
    else p{_exp = IClaferId "" rootIdent True (GlobalBind rootIdent)}
  fromThis p = p
initialValue _ eq = error $ "[bug] Initializers.initialValue: not an equation: " ++ show eq

-- | Whether the expression has temporal operators.
hasTemporal :: PExp -> Bool
hasTemporal pexp = or [ op' `elem` (ltlOps ++ richTemporalOps) | IFunExp op' _ <- universeOn biplate pexp ]

-- | The instances of the clafer of an initializer, @this.x@ (or @x@ at the top level), from its
--   equation @x.dref = e@ in the context of the parent.
initializedClafer :: PExp -> PExp
initializedClafer PExp{_exp = IFunExp _ [lhs, _]} = withoutDref lhs
  where
  withoutDref PExp{_exp = IFunExp op' [x, PExp{_exp = IClaferId{_sident = s}}]} | op' == iJoin && s == drefIdent = x
  withoutDref x = x
initializedClafer pexp = error $ "[bug] Initializers.initializedClafer: not an equation: " ++ show pexp

-- | The value of an initializer, from its equation @x.dref = e@ in the context of the parent.
initializerValue :: PExp -> PExp
initializerValue PExp{_exp = IFunExp _ [_, value]} = value
initializerValue pexp = error $ "[bug] Initializers.initializerValue: not an equation: " ++ show pexp
