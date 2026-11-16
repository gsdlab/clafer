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
{-# LANGUAGE NamedFieldPuns #-}
{- | The forms of the initializers on which their lowering to core is undefined, and the
     initializers that no instance can satisfy (gsdlab/clafer#126, kbak/clafer-semantics#170).

     The errors are the support limits of the contract: on these forms, the clocks of @:=@
     ("Language.Clafer.Intermediate.Initializers") have no meaning. They are reported before
     any output, so that every mode, also the rich explicit model, gets only supported forms.

     * A per-instance @:=@ of an abstract clafer needs a value with at most one element
       ('unsupportedInitialValues'), e.g., @abstract Val -> integer := 1, 2@ is rejected.
     * On a top-level abstract clafer with @:=@, a written multiplicity other than @*@ (or @0..*@) has
       no meaning ('unsupportedInitializerBounds'), e.g., @abstract Val -> integer ? := 1@.

     The warning is for a well-formed conflict: a single reference with an initializer of
     several values, e.g., @x -> integer ? := 1, 2@, has no instance ('severalValues').
-}
module Language.Clafer.Intermediate.InitializerChecks
  ( atMostOne
  , unsupportedInitialValues
  , unsupportedInitializerBounds
  , severalValues
  ) where

import Control.Lens.Plated (universeOn)
import Data.Data.Lens (biplate)
import Data.List (isPrefixOf, nub)
import Data.Maybe (mapMaybe)
import Language.Clafer.Common
import Language.Clafer.Front.AbsClafer
import Language.Clafer.Front.PrintClafer (Print, printTree)
import Language.Clafer.Intermediate.Desugarer (desugarCard, sugarExp)
import Language.Clafer.Intermediate.Intclafer
import Language.ClaferT (CErr (..))

-- | Whether the value has at most one element, established from the declarations and from
--   simple, sound rules on the expression, without solving constraints. 'False' means that
--   the bound could not be established, not that the value has several elements:
--
--   * a literal, @this@ and @parent@;
--   * a top-level concrete clafer with at most one instance, e.g., @seed@ with @seed ?@;
--   * a navigation to a clafer with at most one instance under each parent, to @dref@ or to
--     @parent@, from a value with at most one element, e.g., @seed.dref@;
--   * a count, a sum, a product, a minimum and a maximum of a set;
--   * arithmetic and @-@ on values with at most one element, e.g., @1 / 0@;
--   * an intersection with, and a difference from, a value with at most one element, e.g.,
--     @pool.dref ** 1@;
--   * a union of the same value, e.g., @1, 1@, and @if c then a else b@ of two such values.
--
--   The constraints of the model are not used: @pool.dref@ of @pool ->> integer *@ is not
--   admitted, also with @[ #pool <= 1 ]@.
atMostOne :: UIDIClaferMap -> PExp -> Bool
atMostOne uidIClaferMap' = go
  where
  go PExp{_exp} = case _exp of
    IInt _ -> True
    IDecimal _ -> True
    IReal _ -> True
    IDouble _ -> True
    IStr _ -> True
    IClaferId{_sident, _binding}
      | _sident `elem` [thisIdent, parentIdent] -> True
      | GlobalBind u <- _binding -> maybe False (\c -> isTopLevel c && single c) $ findIClafer uidIClaferMap' u
    IFunExp fun [a]
      | fun `elem` [iCSet, iSumSet, iProdSet, iMaximum, iMinimum] -> True
      | fun == iMin -> go a
    IFunExp fun [a, b]
      | fun == iJoin -> go a && step b
      | fun == iUnion -> go a && go b && sameValue a b
      | fun == iIntersection -> go a || go b
      | fun == iDifference -> go a
      | fun `elem` arithBinOps -> go a && go b
    IFunExp fun [_, a, b]
      | fun == iIfThenElse -> go a && go b
    _ -> False
  -- a navigation step from at most one instance
  step PExp{_exp = IClaferId{_sident, _binding}}
    | _sident `elem` [drefIdent, parentIdent] = True
    | GlobalBind u <- _binding = maybe False single $ findIClafer uidIClaferMap' u
  step _ = False
  -- at most one instance under each parent (the instances of a top-level clafer)
  single c = not (_isAbstract c) && case _card c of
    Just (_, m) -> m == 0 || m == 1
    Nothing -> False

-- | Whether two expressions are the same, apart from their positions.
sameValue :: PExp -> PExp -> Bool
sameValue a b = printTree (sugarExp a) == printTree (sugarExp b)

-- | An expression or a multiplicity as written, e.g., @pool.dref@ and @1..*@, without the
--   spaces that 'printTree' puts around @.@ and @..@.
written :: Print a => a -> String
written = replace " .. " ".." . replace " . " "." . printTree
  where
  replace old new = go
    where
    go [] = []
    go str@(x : rest)
      | old `isPrefixOf` str = new ++ go (drop (length old) str)
      | otherwise = x : go rest

-- | The errors for the per-instance initializers @:=@ of abstract clafers whose value has no
--   established at-most-one bound ('atMostOne'), at the positions of the values. The module is
--   resolved and not optimized yet, since the optimizer removes the abstract clafers that
--   nothing extends, which have the same restriction.
unsupportedInitialValues :: IModule -> [CErr Span]
unsupportedInitialValues iModule =
  [ SemanticErr (_inPos value) $
      "The initializer ':=' of the abstract clafer " ++ _ident c ++ " gives each instance of "
      ++ _ident c ++ " its initial value, which must have at most one element, but that could not"
      ++ " be established for '" ++ written (sugarExp value) ++ "' from the declarations (literals,"
      ++ " clafers with at most one instance, and the operators that keep one element)."
      ++ " To initialize all the instances of " ++ _ident c ++ " together, write the multiplicity *:"
      ++ " abstract " ++ _ident c ++ " -> ... * := ..."
  | c <- universeOn biplate iModule :: [IClafer]
  , _isAbstract c
  , IEInitializer False False PExp{_exp = IFunExp _ [_, value]} <- _elements c
  , not $ atMostOne uidIClaferMap' value ]
  where
  uidIClaferMap' = createUidIClaferMap iModule

-- | The errors for the top-level abstract clafers with an initializer @:=@ and a written
--   multiplicity other than @*@ or @0..*@, at the positions of the multiplicities. On a
--   top-level abstract clafer, which has no parent, @*@ makes @:=@ initialize all its instances
--   at time zero, and other multiplicities have no meaning yet (kbak/clafer-semantics#170): the
--   bound is neither dropped nor read per parent. The contract classifies only the top-level
--   abstract clafers: on a nested one, @*@ makes @:=@ a set initializer under the parent, as for
--   a concrete clafer (the meaning of the multiplicity of an abstract clafer as a bound on the
--   number of instances is gsdlab/clafer#129). The multiplicity is
--   the written one, which only the AST has.
unsupportedInitializerBounds :: Module -> [CErr Span]
unsupportedInitializerBounds (Module _ declarations) =
  mapMaybe boundErr [ c | ElementDecl _ (Subclafer _ c) <- declarations ]
  where
  boundErr (Clafer _ (Abstract _) _ _ (PosIdent (_, name)) _ _ crd (InitSome _ (InitDefault _) _) _ _)
    | Just bound <- desugarCard crd, bound /= (0, -1) =
        Just $ SemanticErr (getSpan crd) $
          "The multiplicity " ++ written crd ++ " of the abstract clafer " ++ name
          ++ " with an initializer ':=' is not supported. Without a multiplicity, ':=' initializes"
          ++ " each instance of " ++ name ++ ", and with * (or 0..*), all the instances of " ++ name
          ++ " together at time zero; other multiplicities have no meaning. For a number of"
          ++ " instances, write a constraint, e.g., [ G (#" ++ name ++ " = 2) ]."
  boundErr _ = Nothing

-- | The initializers of single references whose value has several different literals, e.g.,
--   @x -> integer ? := 1, 2@, with whether they are @=@: no instance can satisfy them, since a
--   single reference cannot equal several targets. Such a model is well-formed, so this is a
--   warning. The initializers of abstract clafers are not single references: @=@ there is a
--   constraint on all instances together, and @:=@ is an error ('unsupportedInitialValues').
severalValues :: IModule -> [(IClafer, PExp, Bool)]
severalValues iModule =
  [ (c, value, constant)
  | c <- universeOn biplate iModule :: [IClafer]
  , not $ _isAbstract c
  , IEInitializer constant False PExp{_exp = IFunExp _ [_, value]} <- _elements c
  , Just literals <- [unionOfLiterals value]
  , length (nub $ map fst literals) == 1
  , length (nub literals) > 1 ]

-- | The literals of a union of literals, e.g., @1, 2, -3@, if it is one, each with its kind:
--   literals of different kinds, e.g., @1@ and @1.0@, may be equal.
unionOfLiterals :: PExp -> Maybe [(String, String)]
unionOfLiterals p@PExp{_exp} = case _exp of
  IFunExp fun [a, b] | fun == iUnion -> (++) <$> unionOfLiterals a <*> unionOfLiterals b
  IFunExp fun [PExp{_exp = IInt _}] | fun == iMin -> literal "integer"
  IInt _ -> literal "integer"
  IDecimal _ -> literal "decimal"
  IReal _ -> literal "real"
  IDouble _ -> literal "double"
  IStr _ -> literal "string"
  _ -> Nothing
  where
  literal kind = Just [(kind, printTree $ sugarExp p)]
