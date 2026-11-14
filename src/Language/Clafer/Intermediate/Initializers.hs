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
       (gsdlab/clafer#123), which the core cannot write: that initializer stays, and the
       temporal generator interprets it (see "Language.Clafer.Generator.AlloyLtl").
     * A set initializer, @xs -> T * := e@, constrains the instances under the parent when the
       parent is born: @[ initially (some xs => xs.dref = e) ]@ in the context of the parent.
-}
module Language.Clafer.Intermediate.Initializers
  ( Semantics (..)
  , lowerInitializers
  , initializedClafer
  , initializerValue
  ) where

import Control.Lens.Plated (transformOn, universeOn)
import Data.Data.Lens (biplate)
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
lowerInitializers sem imodule = imodule{_mDecls = lowerElements sem $ _mDecls imodule}

lowerElements :: Semantics -> [IElement] -> [IElement]
lowerElements sem = concatMap lowerElement
  where
  lowerElement (IEClafer c) = IEClafer c{_elements = kept} : parentConstraints
    where
    elements' = lowerElements sem $ _elements c
    kept = [ own e | e <- elements', not (lowered e) ]
    parentConstraints = [ IEConstraint True $ asConstraint e | e <- elements', lowered e ]
    -- the per-instance := of a temporal model, in the context of the clafer
    own (IEInitializer False False eq) | not (hasTemporal $ initializerValue eq) = IEConstraint True $ initialValue c eq
    own e = e
  lowerElement e = [e]
  lowered (IEInitializer k s _) = sem == Static || k || s
  lowered _ = False
  asConstraint (IEInitializer k s eq)
    | sem == Temporal && not k && s = bool iInitially [ implied ]
    | otherwise = implied
    where
    implied = bool iImpl [ PExp (Just TBoolean) (_pid eq) (_inPos eq) $ IDeclPExp ISome [] $ initializedClafer eq, eq ]
    bool op' = PExp (Just TBoolean) (_pid eq) (_inPos eq) . IFunExp op'
  asConstraint e = error $ "[bug] Initializers.asConstraint: not an initializer: " ++ show e

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
