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
{- | The finality modifiers, lowered to constraints of the core (gsdlab/clafer#127,
     kbak/clafer-semantics#192). Each modifier keeps a set from one state to the next while the
     parent of the clafer exists, without additions and without losses. The constraints are in the
     context of the clafer @x@, where the obligations of @X@ and @previous@ last while the parent
     exists, in its current lifetime, and a quantifier captures the instance, which @this@ is not
     in a state in which the instance does not exist:

     * @final x@, the instances of @x@ under the parent:
       @[ all c : this | X (c in parent.x) ]@ and
       @[ all c : this | previous (some parent) => previous (c in parent.x) ]@;
     * @final x -> T@ and @finalref x -> T@, the target of each instance, which it has while it exists:
       @[ all c : this | all t : c.dref | X ((some c.dref) => (t in c.dref)) ]@, also for a reference
       that @x@ inherits;
     * @finaltarget x -> T@, the set of the targets of the instances of @x@ under the parent:
       @[ all t : this.dref | X (t in parent.x.dref) ]@ and
       @[ all t : this.dref | previous (some parent) => previous (t in parent.x.dref) ]@.

     At the top level, @parent.x@ is @x@, and the obligations last forever. A backend may still
     encode the finality of the rich IR directly when it agrees with these constraints, e.g., the
     temporal Alloy generator declares the relations of the clafers that are final with all their
     ancestors without @var@ ('staticClafers').
-}
module Language.Clafer.Intermediate.Finality
  ( lowerFinality
  , staticClafers
  ) where

import Control.Lens.Plated (transformOn, universeOn)
import Data.Data.Lens (biplate)
import Data.List (find)
import Data.Maybe (fromMaybe, isJust, listToMaybe)
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer

-- | The module with the finality modifiers as constraints of the clafers.
lowerFinality :: IModule -> IModule
lowerFinality imodule = unmark $ transformOn biplate lowerClafer imodule
  where
  uidIClaferMap' = createUidIClaferMap imodule
  taken = concat [ [_uid c, _ident c] | c <- universeOn biplate imodule :: [IClafer] ]
       ++ concat [ concatMap _decls ds | PExp{_exp = IDeclPExp _ ds _} <- universeOn biplate imodule :: [PExp] ]
  lowerClafer c
    | isRoot c = c
    | otherwise = c{_elements = _elements c ++ map (IEConstraint True) (finality uidIClaferMap' taken c)}
  -- no modifier is left
  unmark = transformOn biplate $ \c -> c
    { _modifiers = (_modifiers c){_final = False, _finalReferences = []}
    , _reference = (\r -> r{_refModifiers = []}) <$> _reference c }

-- | The constraints of the finality modifiers of the clafer, in its context.
finality :: UIDIClaferMap -> [String] -> IClafer -> [PExp]
finality uidIClaferMap' taken x =
  [ p | _isFinal x, not (_isAbstract x), p <- heads ]
  ++ [ p | fixesEach, Just _ <- [targetType], p <- eachTarget ]
  ++ [ p | fixesTargets, Just _ <- [targetType], p <- targets ]
  where
  uid' = _uid x
  pos' = _cinPos x
  parentUid = _parentUID x
  topLevel = isTopLevel x
  -- the reference of x: its own, or the one that it inherits, with its modifiers
  own = _reference x
  inheritedFrom = listToMaybe [ (s, r) | s <- drop 1 $ findHierarchy getSuper uidIClaferMap' x, Just r <- [_reference s] ]
  inherited = snd <$> inheritedFrom
  -- the clafer that declares the reference, which the type of dref names
  owner = maybe uid' (_uid . fst) (if isJust own then Nothing else inheritedFrom)
  inheritedFixed = maybe False (any (`elem` [FinalRefTarget, FinalRef]) . _refModifiers) inherited
  fixesEach = case own of
    Just r -> _isFinal x || any (`elem` [FinalRefTarget, FinalRef]) (_refModifiers r)
    -- unless the modifier of the inherited reference fixes it already, in the super clafer
    Nothing -> (_isFinal x || FinalRef `elem` _finalReferences (_modifiers x)) && not inheritedFixed
  fixesTargets = case own of
    Just r -> FinalTarget `elem` _refModifiers r
    Nothing -> FinalTarget `elem` _finalReferences (_modifiers x)
  targetType = _iType . _ref =<< maybe inherited Just own
  -- fresh names of the local variables
  fresh avoid base = fromMaybe base $ find (`notElem` avoid) [ base ++ "_" ++ show k | k <- [1 :: Int ..] ]
  vc = fresh taken (_ident x)
  vt = fresh (vc : taken) (_ident x)

  -- the expressions
  typed t = PExp (Just t) "" pos'
  bool = typed TBoolean
  clafer u = TClafer [u]
  thisX = typed (clafer uid') $ IClaferId "" thisIdent True (GlobalBind uid')
  local v t = typed t $ IClaferId "" v True (LocalBind v)
  join' t a b = typed t $ IFunExp iJoin [a, b]
  rootX = typed (clafer rootIdent) $ IClaferId "" rootIdent True (GlobalBind rootIdent)
  -- the parent: this.parent, which is the root at the top level
  parentOfThis
    | topLevel = rootX
    | otherwise = join' (clafer parentUid) thisX $ typed (clafer parentUid) $ IClaferId "" parentIdent True (GlobalBind parentUid)
  -- the instances of x under the parent: parent.x, or root.x at the top level
  siblings
    | topLevel = join' (clafer uid') rootX (typed (clafer uid') $ IClaferId "" uid' True (GlobalBind uid'))
    | otherwise = join' (clafer uid') parentOfThis (typed (clafer uid') $ IClaferId "" uid' False (GlobalBind uid'))
  dref of' = join' (fromMaybe TInteger targetType) of' $ typed (TMap (clafer owner) (fromMaybe TInteger targetType)) $
    IClaferId "" drefIdent True (GlobalBind uid')
  c = local vc (clafer uid')
  tv = local vt (fromMaybe TInteger targetType)
  fun op' args = bool $ IFunExp op' args
  forAll v set' body' = bool $ IDeclPExp IAll [IDecl False [v] set'] body'
  some' set' = bool $ IDeclPExp ISome [] set'
  -- previous (some parent) => previous a: unless the parent was born now, or the trace begins
  since' a = fun iPrevious [some' parentOfThis] `implies` fun iPrevious [a]
  implies a b = fun iImpl [a, b]

  heads =
    [ forAll vc thisX $ fun iX [fun iIn [c, siblings]]
    , forAll vc thisX $ since' (fun iIn [c, siblings]) ]
  eachTarget =
    [ forAll vc thisX $ forAll vt (dref c) $ fun iX [some' (dref c) `implies` fun iIn [tv, dref c]] ]
  targets =
    [ forAll vt (dref thisX) $ fun iX [fun iIn [tv, dref siblings]]
    , forAll vt (dref thisX) $ since' (fun iIn [tv, dref siblings]) ]

isRoot :: IClafer -> Bool
isRoot c = _uid c == rootIdent

-- | The clafers that are final with all their ancestors in the rich IR, whose relations do not
--   change, and of them, those whose own references do not change either: a backend may encode
--   them without change, which the constraints of 'lowerFinality' allow.
staticClafers :: IModule -> ([UID], [UID])
staticClafers imodule = (map _uid statics, [ _uid c | c <- statics, Just r <- [_reference c], not (null (_refModifiers r)) ])
  where
  uidIClaferMap' = createUidIClaferMap imodule
  clafers = universeOn biplate imodule :: [IClafer]
  statics = filter static clafers
  static c
    | isRoot c = True
    | otherwise = _isFinal c && maybe True static (findIClafer uidIClaferMap' (_parentUID c))
