{-
 Copyright (C) 2012 Jimmy Liang, Kacper Bak, Michal Antkiewicz <http://gsd.uwaterloo.ca>

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

-- | Common methods for analyzing Clafer model
module Language.Clafer.Intermediate.Analysis where

import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.Desugarer
import Language.Clafer.Front.PrintClafer
import Language.Clafer.Common

import Control.Applicative
import Control.Monad.List
import Debug.Trace

type Info = UIDIClaferMap

claferWithUid :: (Monad m) => Info -> String -> m IClafer
claferWithUid uidIClaferMap' u = case findIClafer uidIClaferMap' u of
  Just c -> return c
  Nothing -> fail $ traceId $ "Analysis.claferWithUid: " ++ u ++ " not found!"

parentOf :: (Monad m) => Info -> UID -> m UID
parentOf uidIClaferMap' c = case _parentUID <$> findIClafer uidIClaferMap' c of
  Just u -> return u
  Nothing -> fail $ traceId $ "Analysis.parentOf: " ++ c ++ " not found!"

refUid :: Monad m => IClafer -> m String
refUid clafer =
  case getReference clafer of
    [u] -> return u
    _   -> fail $ traceId ("Analysis.refUID: No ref uid for " ++ _uid clafer)

refOf :: (Monad m) => Info -> UID -> m UID
refOf uidIClaferMap' c = do
  case getReference <$> findIClafer uidIClaferMap' c of
    Just [r] -> return r
    _        -> fail $ traceId ("Analysis.refOf: No ref uid for " ++ show c)

hierarchy :: (Monad m) => Info -> UID -> m [IClafer]
hierarchy uidIClaferMap' c = (case findIClafer uidIClaferMap' c of
      Nothing -> fail $ traceId $ "Analysis.hierarchy: clafer " ++ c ++ "not found!"
      Just clafer -> return $ findHierarchy getSuper uidIClaferMap' clafer)

{-
 - C is an direct child of B.
 -
 -  abstract A
 -    C      // C - child
 -  B : A    // B - parent
 -}
isIndirectChild :: (Monad m) => Info -> UID -> UID -> m Bool
isIndirectChild info child parent = do
  (_:allSupers) <- hierarchy info parent
  childOfSupers <- mapM ((isChild info child)._uid) $ filter (\c -> (_uid c) /= baseClafer) allSupers
  return $ or childOfSupers

isChild :: (Monad m) => Info -> UID -> UID -> m Bool
isChild uidIClaferMap' child parent =
    (case findIClafer uidIClaferMap' child of
            Nothing -> return False
            Just childIClafer -> do
                let directChild = (parent == _parentUID childIClafer)
                indirectChild <- isIndirectChild uidIClaferMap' child parent
                return $ directChild || indirectChild
            )

gatherInfo :: IModule -> Info
gatherInfo imodule = createUidIClaferMap imodule

{-
 -
 - Utility functions
 -
 -}

liftList :: Monad m => [a] -> ListT m a
liftList = ListT . return

foreachM :: Monad m => [a] -> ListT m a
foreachM = ListT . return

mapLeft :: (t -> a) -> Either t b -> Either a b
mapLeft f (Left l)  = Left $ f l
mapLeft _ (Right r) = Right r

comparing :: Ord b => (a -> b) -> a -> a -> Ordering
comparing f a b = f a `compare` f b

syntaxOf :: PExp -> String
syntaxOf = printTree . sugarExp

-- Returns true iff the left and right expressions are syntactically identical
sameAs :: PExp -> PExp -> Bool
sameAs e1 e2 = syntaxOf e1 == syntaxOf e2 -- Not very efficient but hopefully correct
