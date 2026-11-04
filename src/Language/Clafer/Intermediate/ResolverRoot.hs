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
-- | The synthetic root (#112). The root is the parent of the instances of the top-level
--   concrete clafers, but it has no instance in the outputs: a navigation from it is a
--   navigation from the top level (@root.a@ is @a@), which the generators translate. Here,
--   after the types are resolved:
--
--   This applies to static models: in temporal models, the root is a signature.
--
--   * the root as a value is a constant: @some root@, @one root@ and @lone root@ hold, @no root@
--     does not, and @#root@ is 1; any other use of it as a value is an error;
--   * the parent of a set of instances of top-level clafers is the root when the set is not
--     empty: @some a.parent@ is @some a@, @#a.parent@ is 1 or 0, a navigation from it is a
--     navigation from the root when @a@ exists, and @a.parent@ is the root when @a@ always
--     exists;
--   * a constraint of a top-level abstract clafer that takes the parent of @this@, when some of
--     its subclafers are at the top level and some nested, is split on @this@: for the
--     instances of the top-level subclafers, the parent is the root.
module Language.Clafer.Intermediate.ResolverRoot (resolveRootModule) where

import Control.Monad
import Control.Monad.Except
import qualified Data.StringMap as SMap

import Language.ClaferT
import Language.Clafer.Front.AbsClafer (noSpan)
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.TypeSystem (rootTClafer)

type Resolve = Either ClaferSErr

-- | Whether the parent of @this@ is the root, in one part of a split constraint.
data ThisParent = Unsplit | RootParent | NestedParent IClafer

resolveRootModule :: (IModule, GEnv) -> Resolve IModule
resolveRootModule (imodule, _)
  -- the temporal generator has a root signature, and the parent of an instance of a top-level
  -- abstract clafer is the root for those of its top-level subclafers there
  | isDynamicModule imodule = return imodule
  | otherwise = do
    decls' <- mapM (rootElement Nothing) $ _mDecls imodule
    return imodule{_mDecls = decls'}
  where
  uidMap = createUidIClaferMap imodule

  rootElement :: Maybe IClafer -> IElement -> Resolve IElement
  rootElement _ (IEClafer c) = do
    elements' <- mapM (rootElement $ Just c) $ _elements c
    return $ IEClafer c{_elements = elements'}
  rootElement ctx (IEConstraint isHard' pexp) = IEConstraint isHard' <$> rootConstraint ctx pexp
  rootElement ctx (IEGoal isMaximize' pexp) = IEGoal isMaximize' <$> rootPExp ctx Unsplit pexp

  rootConstraint :: Maybe IClafer -> PExp -> Resolve PExp
  rootConstraint ctx@(Just c) pexp
    | ParentMixed tops nested <- parentKind (_uid c), takesParentOfThis pexp = do
      onTop <- rootPExp ctx RootParent pexp
      onNested <- mapM (\n -> rootPExp ctx (NestedParent n) pexp) nested
      let bool = PExp (Just TBoolean) "" noSpan
          implies cs e = bool $ IFunExp iImpl [bool $ IFunExp iIn [thisOf c, unionOf cs], e]
      return pexp{_exp = _exp $ foldl1 (\l r -> bool $ IFunExp iAnd [l, r]) $
        implies tops onTop : zipWith (\n e -> implies [n] e) nested onNested}
  rootConstraint ctx pexp = rootPExp ctx Unsplit pexp

  -- the concrete subclafers of a clafer, at the top level and nested
  parentKind :: UID -> ParentKind
  parentKind uid'
    | null tops = ParentReal
    | null nested = ParentRoot
    | otherwise = ParentMixed tops nested
    where
    subs = [ c' | c' <- SMap.elems uidMap, not (_isAbstract c'), _uid c' /= rootIdent
                , uid' `elem` map _uid (tail $ findHierarchy getSuper uidMap c') ]
    (tops, nested) = (filter isRootChild subs, filter (not . isRootChild) subs)

  isRootChild c' = _parentUID c' == rootIdent && not (_isAbstract c')

  thisOf c = PExp (Just $ TClafer [_uid c]) "" noSpan $ IClaferId "" thisIdent True (GlobalBind $ _uid c)
  -- all the instances of the clafers, a nested one by its path from the top level, e.g., g.f2
  unionOf cs = foldl1 (\l r -> PExp (Just $ TClafer []) "" noSpan $ IFunExp iUnion [l, r]) $ map instancesOf cs
  instancesOf c' = foldl1 (\l r -> PExp (_iType r) "" noSpan $ IFunExp iJoin [l, r])
    [ PExp (Just $ TClafer [_uid a]) "" noSpan $ IClaferId "" (_uid a) (isTopLevel a) (GlobalBind $ _uid a) | a <- reverse $ ancestors c' ]
  ancestors c' = c' : case findIClafer uidMap $ _parentUID c' of
    Just p | not (isTopLevel c'), _uid p /= rootIdent -> ancestors p
    _ -> []

  rootPExp :: Maybe IClafer -> ThisParent -> PExp -> Resolve PExp
  rootPExp ctx split pexp@PExp{_inPos = pos', _exp = exp'} = case exp' of
    IFunExp op' [l, r@PExp{_exp = IClaferId{_sident = s}}] | op' == iJoin, s == parentIdent -> do
      l' <- rootPExp ctx split l
      case parentKindOf l' of
        Just ParentRoot | isSingle l' || alwaysExists l' -> return $ toRoot pexp
        Just (ParentMixed _ _) | isThis l', RootParent <- split -> return $ toRoot pexp
        -- this as an instance of one nested subclafer, whose parent Choco can take: that of
        -- the abstract clafer, or of a union of clafers, it cannot
        Just (ParentMixed _ _) | isThis l', NestedParent n <- split ->
          return pexp{_exp = IFunExp op' [l'{_exp = IFunExp iIntersection [l', unionOf [n]]}, r]}
        Just ParentRoot -> throwError $ SemanticErr pos' $
          "The parent of " ++ claferNames l' ++ " is the root when an instance exists, and nothing otherwise: it can be navigated from, quantified or counted, e.g., `" ++ claferNames l' ++ ".parent.a`, `some " ++ claferNames l' ++ ".parent` or `#" ++ claferNames l' ++ ".parent`"
        Just (ParentMixed tops _) -> throwError $ SemanticErr pos' $
          "The parent of an instance of " ++ claferNames l' ++ " is the root for its top-level subclafers (" ++ unwords (map _ident tops) ++ ") and an instance for the others: take the parent of `this` in a constraint of " ++ claferNames l'
        _ -> return pexp{_exp = IFunExp op' [l', r]}
    -- a navigation from the parent of a set of instances of top-level clafers, e.g.,
    -- extra.parent.a for extra ?, is the navigation from the root when an instance exists:
    -- if some extra then a else a -- a, since the IR has no empty set
    IFunExp op' [PExp{_exp = IFunExp op'' [l, PExp{_exp = IClaferId{_sident = s}}]}, r]
      | op' == iJoin, op'' == iJoin, s == parentIdent, Just ParentRoot <- parentKindOf l, not (isSingle l || alwaysExists l) -> do
      l' <- rootPExp ctx split l
      r' <- rootPExp ctx split r
      let nav = pexp{_pid = "", _exp = IFunExp iJoin [toRoot l', r']}
      return pexp{_exp = IFunExp iIfThenElse [exists l', nav, nav{_exp = IFunExp iDifference [nav, nav]}]}
    IFunExp op' [l, r] | op' == iJoin -> do
      l' <- rootPExp ctx split l
      r' <- rootPExp ctx split r
      when (isRoot r') $ throwError $ SemanticErr pos' "The root is not a child of any clafer"
      return pexp{_exp = IFunExp op' [l', r']}
    IFunExp op' [PExp{_exp = IFunExp op'' [l, PExp{_exp = IClaferId{_sident = s}}]}]
      | op' == iCSet, op'' == iJoin, s == parentIdent, Just ParentRoot <- parentKindOf l, not (isSingle l || alwaysExists l) -> do
      l' <- rootPExp ctx split l
      let int n = PExp (Just TInteger) "" noSpan $ IInt n
      return pexp{_iType = Just TInteger, _exp = IFunExp iIfThenElse [exists l', int 1, int 0]}
    IFunExp op' [e] | op' == iCSet -> do
      e' <- rootPExp ctx split e
      return $ if isRoot e' then pexp{_iType = Just TInteger, _exp = IInt 1} else pexp{_exp = IFunExp op' [e']}
    IFunExp op' es -> do
      es' <- mapM (rootPExp ctx split) es
      when (any isRoot es') $ throwError $ SemanticErr pos' $ rootAsValue op'
      return $ case (lookup op' comparisons, es') of
        -- e.g., #this.parent = 1, which is 1 = 1 now; the comparisons of the model stay
        (Just cmp, [PExp{_exp = IInt m}, PExp{_exp = IInt n}]) | or (zipWith becameInt es es') ->
          pexp{_iType = Just TBoolean, _exp = constant $ cmp m n}
        _ -> pexp{_exp = IFunExp op' es'}
    -- the parent of a set of instances of top-level clafers exists when an instance does
    IDeclPExp q [] PExp{_exp = IFunExp op' [l, PExp{_exp = IClaferId{_sident = s}}]}
      | op' == iJoin, s == parentIdent, Just ParentRoot <- parentKindOf l, not (isSingle l || alwaysExists l) -> do
      l' <- rootPExp ctx split l
      return $ case q of
        ILone -> pexp{_iType = Just TBoolean, _exp = constant True}
        INo -> pexp{_exp = IDeclPExp INo [] l'}
        _ -> pexp{_exp = IDeclPExp ISome [] l'}
    IDeclPExp q [] e -> do
      e' <- rootPExp ctx split e
      return $ if isRoot e'
        then pexp{_iType = Just TBoolean, _exp = constant (q /= INo)}
        else pexp{_exp = IDeclPExp q [] e'}
    IDeclPExp q ds e -> do
      ds' <- forM ds $ \d -> do
        body' <- rootPExp ctx split $ _body d
        when (isRoot body') $ throwError $ SemanticErr pos' "A variable cannot range over the root, which has no instance"
        return d{_body = body'}
      e' <- rootPExp ctx split e
      return pexp{_exp = IDeclPExp q ds' e'}
    _ -> return pexp
    where
    toRoot p = p{_iType = Just rootTClafer, _exp = IClaferId "" rootIdent True (GlobalBind rootIdent)}
    exists l' = PExp (Just TBoolean) "" noSpan $ IDeclPExp ISome [] l'

  parentKindOf :: PExp -> Maybe ParentKind
  parentKindOf p = case _iType p of
    Just (TClafer uids@(_:_)) | Just cs <- mapM (findIClafer uidMap) uids, all isRootChild cs -> Just ParentRoot
    Just (TClafer [uid']) | Just c <- findIClafer uidMap uid', isTopLevel c, _isAbstract c -> Just $ parentKind uid'
    _ -> Nothing

  -- a concrete top-level clafer that has an instance in every instance of the model
  alwaysExists :: PExp -> Bool
  alwaysExists PExp{_exp = IClaferId{_sident = s, _binding = GlobalBind _}}
    | Just c <- findIClafer uidMap s, isRootChild c, Just (lower, _) <- _card c = lower >= 1
  alwaysExists _ = False

  claferNames p = case _iType p of
    Just (TClafer uids) -> unwords $ map (\u -> maybe u _ident $ findIClafer uidMap u) uids
    _ -> "the expression"

  -- whether the constraint takes the parent of @this@, which the split decides
  takesParentOfThis :: PExp -> Bool
  takesParentOfThis PExp{_exp = exp'} = case exp' of
    IFunExp op' [l, PExp{_exp = IClaferId{_sident = s}}] | op' == iJoin, s == parentIdent, isThis l -> True
    IFunExp _ es -> any takesParentOfThis es
    IDeclPExp _ ds e -> any (takesParentOfThis . _body) ds || takesParentOfThis e
    _ -> False

-- | The parent of the instances of a top-level clafer: the root for a concrete one, and, for an
--   abstract one, an instance, when its concrete subclafers are nested, the root, when they are
--   at the top level, or, when they are both, the root for the top-level ones and an instance
--   for the nested ones
data ParentKind = ParentReal | ParentRoot | ParentMixed [IClafer] [IClafer]

isRoot :: PExp -> Bool
isRoot PExp{_exp = IClaferId{_sident = s}} = s == rootIdent
isRoot _ = False

isThis :: PExp -> Bool
isThis PExp{_exp = IClaferId{_sident = s}} = s == thisIdent
isThis _ = False

-- | @this@ or a variable: one instance, whose parent always exists
isSingle :: PExp -> Bool
isSingle PExp{_exp = IClaferId{_binding = LocalBind _}} = True
isSingle p = isThis p

-- | True as @0 < 1@, false as @1 < 0@: the IR has no boolean constants, and Alloy warns that
--   @0 = 0@ is redundant.
constant :: Bool -> IExp
constant b = IFunExp iLt $ if b then [int 0, int 1] else [int 1, int 0]
  where
  int n = PExp (Just TInteger) "" noSpan $ IInt n

becameInt :: PExp -> PExp -> Bool
becameInt PExp{_exp = IInt _} _ = False
becameInt _ PExp{_exp = IInt _} = True
becameInt _ _ = False

comparisons :: [(String, Integer -> Integer -> Bool)]
comparisons = [(iEq, (==)), (iNeq, (/=)), (iLt, (<)), (iGt, (>)), (iLte, (<=)), (iGte, (>=))]

rootAsValue :: String -> String
rootAsValue op' = "The root has no instance: `root` can be navigated from, e.g., `root.a`, counted (`#root` is 1) and quantified (`some root` holds), but not used in '" ++ op' ++ "'"
