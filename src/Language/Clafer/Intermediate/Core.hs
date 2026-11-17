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
{- | The core of a model: the IR keeps the modeling intent of the enumerations, the initializers,
     the behavioral patterns and the transitions (the rich explicit model, @clafer -m clafer@);
     this module lowers them to the core language (the explicit core model, @clafer -m clafer
     --core@), which every backend gets.

     * An enumeration is an abstract clafer with a concrete clafer for each literal.
     * The initializers are constraints ("Language.Clafer.Intermediate.Initializers").
     * The finality modifiers are constraints ("Language.Clafer.Intermediate.Finality").
     * The patterns are the LTL formulas of Dwyer et al.'s catalogue, Patterns in Property
       Specifications for Finite-State Verification (ICSE 1999), for the scopes globally,
       before r, after q, between q and r, and after q until r.
     * The transitions are as in Juodisius et al., Clafer: Lightweight Modeling of Structure,
       Behaviour, and Variability (2019), section 6.1: if the precondition holds in a state,
       the postcondition holds in the next state (@-->@), or the precondition and the context
       instance last until the postcondition holds (@-->>@); a guard strengthens the
       precondition. A chain of transitions is a sequence, e.g., a scenario
       @[ initially (green --> yellow --> red) ]@; only its first precondition is a condition,
       so @a --> b --> c@ is @a => X (b && X c)@, not @a => X (b => X c)@.
-}
module Language.Clafer.Intermediate.Core
  ( Semantics (..)
  , lowerToCore
  , lowerPExp
  ) where

import Control.Lens (over)
import Control.Lens.Plated (plate, transformOn)
import Data.Data.Lens (biplate)
import Language.Clafer.Common
import Language.Clafer.Intermediate.Finality (lowerFinality, lowerInitial)
import Language.Clafer.Intermediate.Initializers (Semantics (..), lowerInitializers)
import Language.Clafer.Intermediate.Intclafer

-- | The core of the module, for a backend that reads it with the given semantics.
lowerToCore :: Semantics -> IModule -> IModule
lowerToCore sem = lowerInitial . lowerFinality . lowerEnums . over biplate lowerPExp . lowerInitializers sem

-- | The clafers of the enumerations are ordinary clafers.
lowerEnums :: IModule -> IModule
lowerEnums = transformOn biplate unmark
  where
  unmark c = c{_modifiers = (_modifiers c){_enum = False}}

-- | The expression with its patterns and transitions in LTL.
lowerPExp :: PExp -> PExp
lowerPExp p@PExp{_exp = IFunExp op' args}
  | op' `elem` transitionOps = transition p op' args
  | Just (kind, scope) <- patternOf op' = pattern p kind scope $ map lowerPExp args
lowerPExp p = over plate lowerPExp p

-- | A transition: if the precondition holds, the step follows.
transition :: PExp -> String -> [PExp] -> PExp
transition p op' args = let (pre, stp) = transitionParts p op' args in mk p iImpl [pre, stp]

-- | The precondition and the step of a transition, whose target is a sequence.
transitionParts :: PExp -> String -> [PExp] -> (PExp, PExp)
transitionParts p op' args = case (op', map lowerPExp args, args) of
    (_, [a, _], [_, b0])       | op' == iTrans            -> (a, next b0)
    (_, [a, g, _], [_, _, b0]) | op' == iTransGuarded     -> (mk p iAnd [a, g], next b0)
    (_, [a, _], [_, b0])       | op' == iTransSync        -> (a, mk p iU [a, sequence' b0])
    (_, [a, _, t], [_, b0, _]) | op' == iTransSync        -> (a, mk p iU [mk p iAnd [t, a], sequence' b0])
    (_, [a, g, _], [_, _, b0]) | op' == iTransSyncGuarded -> (mk p iAnd [a, g], mk p iU [a, sequence' b0])
    (_, [a, g, _, t], [_, _, b0, _]) | op' == iTransSyncGuarded -> (mk p iAnd [a, g], mk p iU [mk p iAnd [t, a], sequence' b0])
    _ -> error $ "[bug] Core.transitionParts: " ++ op' ++ " with " ++ show (length args) ++ " arguments"
  where
  next b0 = mk p iX [sequence' b0]

-- | The target of a transition: in a chain, the states follow each other.
sequence' :: PExp -> PExp
sequence' p@PExp{_exp = IFunExp op' args} | op' `elem` transitionOps =
  let (pre, stp) = transitionParts p op' args in mk p iAnd [pre, stp]
sequence' p = lowerPExp p

-- | A pattern in a scope, with its arguments in LTL.
pattern :: PExp -> String -> String -> [PExp] -> PExp
pattern pe kind scope args = case (kind, scope, args) of
  ("never", "", [p])                -> g $ not' p
  ("never", "before", [p, r])       -> f r ==> (not' p `u` r)
  ("never", "after", [p, q])        -> g (q ==> g (not' p))
  ("never", "between", [p, q, r])   -> g ((q .& not' r .& f r) ==> (not' p `u` r))
  ("never", "after until", [p, q, r]) -> g ((q .& not' r) ==> (not' p `w` r))

  ("sometime", "", [p])                -> f p
  ("sometime", "before", [p, r])       -> not' r `w` (p .& not' r)
  ("sometime", "after", [p, q])        -> g (not' q) .| f (q .& f p)
  ("sometime", "between", [p, q, r])   -> g ((q .& not' r) ==> (not' r `w` (p .& not' r)))
  ("sometime", "after until", [p, q, r]) -> g ((q .& not' r) ==> (not' r `u` (p .& not' r)))

  -- (!P W (P W []!P))
  ("lonce", "", [p])                -> not' p `w` (p `w` g (not' p))
  -- <> R -> ((!P & !R) U ((R | (P & !R)) U ( R | (!P U R))))
  ("lonce", "before", [p, r])       -> f r ==> ((not' p .& not' r) `u` (r .| ((p .& not' r) `u` (r .| (not' p `u` r)))))
  -- <>Q -> (!Q U (Q & (!P W (P W []!P))))
  ("lonce", "after", [p, q])        -> f q ==> (not' q `u` (q .& (not' p `w` (p `w` g (not' p)))))
  -- []((Q & <>R) -> ((!P & !R) U (R | ((P & !R) U (R | (!P U R))))))
  ("lonce", "between", [p, q, r])   -> g ((q .& f r) ==> ((not' p .& not' r) `u` (r .| ((p .& not' r) `u` (r .| (not' p `u` r))))))
  -- [](Q -> ((!P & !R) U (R | ((P & !R) U (R | (!P W R) | []P)))))
  ("lonce", "after until", [p, q, r]) -> g (q ==> ((not' p .& not' r) `u` (r .| ((p .& not' r) `u` (r .| (not' p `w` r) .| g p)))))

  ("always", "", [p])                -> g p
  ("always", "before", [p, r])       -> f r ==> (p `u` r)
  ("always", "after", [p, q])        -> g (q ==> g p)
  ("always", "between", [p, q, r])   -> g ((q .& not' r .& f r) ==> (p `u` r))
  ("always", "after until", [p, q, r]) -> g ((q .& not' r) ==> (p `w` r))

  ("precede", "", [s, p])                -> not' p `w` s
  ("precede", "before", [s, p, r])       -> f r ==> (not' p `u` (s .| r))
  -- from the first q: Dwyer's []!Q | <>(Q & (!P W S)) may pick a later q
  ("precede", "after", [s, p, q])        -> f q ==> (not' q `u` (q .& (not' p `w` s)))
  ("precede", "between", [s, p, q, r])   -> g ((q .& not' r .& f r) ==> (not' p `u` (s .| r)))
  ("precede", "after until", [s, p, q, r]) -> g ((q .& not' r) ==> (not' p `w` (s .| r)))

  ("follow", "", [s, p])                -> g (p ==> f s)
  ("follow", "before", [s, p, r])       -> f r ==> ((p ==> (not' r `u` (s .& not' r))) `u` r)
  ("follow", "after", [s, p, q])        -> g (q ==> g (p ==> f s))
  -- every p up to r: []((Q & !R & <>R) -> ((P -> (!R U (S & !R))) U R))
  ("follow", "between", [s, p, q, r])   -> g ((q .& not' r .& f r) ==> ((p ==> (not' r `u` (s .& not' r))) `u` r))
  ("follow", "after until", [s, p, q, r]) -> g ((q .& not' r) ==> ((p ==> (not' r `u` (s .& not' r))) `w` r))

  _ -> error $ "[bug] Core.pattern: " ++ patternOp kind scope ++ " with " ++ show (length args) ++ " arguments"
  where
  infixr 4 `u`
  infixr 4 `w`
  infixl 3 .&
  infixl 2 .|
  infixr 1 ==>
  u a b = mk pe iU [a, b]
  w a b = mk pe iW [a, b]
  a ==> b = mk pe iImpl [a, b]
  a .& b = mk pe iAnd [a, b]
  a .| b = mk pe iOr [a, b]
  f a = mk pe iF [a]
  g a = mk pe iG [a]
  -- !(some x) is no x, as the desugarer writes it
  not' PExp{_exp = IDeclPExp ISome [] x} = PExp (Just TBoolean) (_pid pe) (_inPos pe) (IDeclPExp INo [] x)
  not' a = mk pe iNot [a]

-- | A formula at the place of the expression @p@.
mk :: PExp -> String -> [PExp] -> PExp
mk p op' args = PExp (Just TBoolean) (_pid p) (_inPos p) (IFunExp op' args)
