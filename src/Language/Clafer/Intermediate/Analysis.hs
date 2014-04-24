{-# LANGUAGE NamedFieldPuns, FlexibleContexts, FlexibleInstances, UndecidableInstances, GeneralizedNewtypeDeriving, StandaloneDeriving #-}

{-
 Copyright (C) 2012 Jimmy Liang, Kacper Bak <http://gsd.uwaterloo.ca>

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

{-
 - Common methods for analyzing Clafer model.
 -}
module Language.Clafer.Intermediate.Analysis where

import Language.Clafer.Front.Absclafer hiding (Path)
import qualified Language.Clafer.Intermediate.Intclafer as I
import Language.Clafer.Intermediate.Desugarer
import Language.Clafer.Front.Printclafer
import Control.Applicative
import Control.Monad.LPMonad.Supply
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.List
import Control.Monad.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Either
import Data.List
import Data.Maybe



newtype AnalysisT m a = AnalysisT (ReaderT Info m a)
  deriving (Monad, Functor, MonadReader Info, MonadState s, MonadTrans, MonadPlus, MonadError e, Applicative)
  
type Analysis = AnalysisT Identity

class (Monad m, Functor m) => MonadAnalysis m where
  clafers :: m [SClafer]
  withClafers :: [SClafer] -> m a -> m a
  
withExtraClafers :: MonadAnalysis m => [SClafer] -> m a -> m a
withExtraClafers cs a =
    do
        c <- clafers
        withClafers (cs ++ c) a
  
instance (Monad m, Functor m) => MonadAnalysis (AnalysisT m) where
  clafers = AnalysisT $ asks sclafers
  withClafers cs = local (const $ Info cs)
    
instance (Error e, MonadAnalysis m) => MonadAnalysis (ErrorT e m) where
  clafers = lift clafers
  withClafers = mapErrorT . withClafers
  
instance MonadAnalysis m => MonadAnalysis (ListT m) where
  clafers = lift clafers
  withClafers = mapListT . withClafers

instance MonadAnalysis m => MonadAnalysis (MaybeT m) where
  clafers = lift clafers
  withClafers = mapMaybeT . withClafers

instance MonadAnalysis m => MonadAnalysis (ReaderT r m) where
  clafers = lift clafers
  withClafers = mapReaderT . withClafers

instance (Monoid w, MonadAnalysis m) => MonadAnalysis (WriterT w m) where
  clafers = lift clafers
  withClafers = mapWriterT . withClafers
  
instance MonadAnalysis m => MonadAnalysis (VSupplyT m) where
  clafers = lift clafers
  withClafers = mapVSupplyT . withClafers
  
isConcrete :: SClafer -> Bool
isConcrete = not . isAbstract

isBase :: SClafer -> Bool
isBase = (`elem` ["clafer", "string", "real", "int", "integer", "boolean"]) . uid

isDerived :: SClafer -> Bool
isDerived = not . isBase
 

data SSuper = Ref String | Colon String deriving Show
-- | Easier to work with. IClafers have links from parents to children. SClafers have links from children to parent.
data SClafer = SClafer {uid::String, origUid::String, isAbstract::Bool, low::Integer, high::Integer, groupLow::Integer, groupHigh::Integer, parent::Maybe String, super::Maybe SSuper, constraints::[I.PExp]} deriving Show
  
data Info = Info{sclafers :: [SClafer]} deriving Show 

runAnalysis :: Analysis a -> Info -> a
runAnalysis r info = runIdentity $ runAnalysisT r info

runAnalysisT :: AnalysisT m a -> Info -> m a
runAnalysisT (AnalysisT r) info = runReaderT r info

claferWithUid :: MonadAnalysis m => String -> m SClafer
claferWithUid u =
  do
    c <- clafers
    case find ((==) u . uid) c of
      Just c' -> return c'
      Nothing -> error $ "claferWithUid: Unknown uid " ++ u
      
parentUid :: Monad m => SClafer -> m String
parentUid clafer =
  case parent clafer of
    Just p  -> return p
    Nothing -> fail $ "No parent uid for " ++ show clafer
    
parentOf :: (Uidable c, MonadAnalysis m) => c -> m c
parentOf clafer = fromUid =<< parentUid =<< toClafer clafer

parentsOf :: (Uidable c, MonadAnalysis m) => c -> m [c]
parentsOf clafer =
  do
    r <- runMaybeT $ parentOf clafer
    case r of
         Just r' -> (r' :) <$> parentsOf r'
         Nothing -> return []

ancestorsOf :: (Uidable c, MonadAnalysis m) => c -> m [c]
ancestorsOf clafer = (clafer :) <$> parentsOf clafer

directChildrenOf :: (Uidable c, MonadAnalysis m) => c -> m [c]
directChildrenOf c =
  do
    cs <- (anything |^ c) `select` fst
    mapM fromClafer cs

directDescendantsOf :: (Uidable c, MonadAnalysis m) => c -> m [c]
directDescendantsOf c =
  do
    cs <- (anything |^ c) `select` fst
    css <- mapM directDescendantsOf cs
    mapM fromClafer $ cs ++ concat css

topNonRootAncestor :: (Uidable c, MonadAnalysis m) => c -> m c
topNonRootAncestor clafer =
  do
    uid' <- toUid clafer
    when (uid' == rootUid) $ error "Root does not have a non root ancestor."
    (head . tail . reverse) <$> ancestorsOf clafer

refUid :: Monad m => SClafer -> m String
refUid clafer =
  case super clafer of
    Just (Ref u)  -> return u
    _             -> fail $ "No ref uid for " ++ show clafer

refOf :: (Uidable c, MonadAnalysis m) => c -> m c
refOf clafer = fromUid =<< refUid =<< toClafer clafer

refsOf :: (Uidable c, MonadAnalysis m) => c -> m [c]
refsOf clafer =
  do
    r <- runMaybeT $ refOf clafer
    case r of
         Just r' -> (r' :) <$> refsOf r'
         Nothing -> return []

colonUid :: (Uidable c, MonadAnalysis m) => c -> m String
colonUid c =
  do
    clafer <- toClafer c
    case super clafer of
      Just (Colon u)  -> return u
      _               -> fail $ "No colon uid for " ++ show clafer

colonOf :: (Uidable c, MonadAnalysis m) => c -> m c
colonOf clafer = fromUid =<< colonUid =<< toClafer clafer

colonsOf :: (Uidable c, MonadAnalysis m) => c -> m [c]
colonsOf clafer =
  do
    r <- runMaybeT $ colonOf clafer
    case r of
         Just r' -> (r' :) <$> colonsOf r'
         Nothing -> return []

-- "subclafers"
colonsTo :: (Uidable c, MonadAnalysis m) => c -> m [c]
colonsTo clafer =
    runListT $ do
        (sub, _) <- foreach $ anything |: clafer
        fromClafer =<< (return sub `mplus` foreach ( colonsTo sub))

    

hierarchy :: (Uidable c, MonadAnalysis m) => c -> m [c]
hierarchy t = (t :) <$> colonsOf t

{-
 - C is a direct child of B.
 -
 -  B
 -    C
 -}
isDirectChild :: (Uidable c, MonadAnalysis m) => c -> c -> m Bool
isDirectChild c p = (not . null) <$> (c |^ p)
 
{-
 - C is an direct child of B.
 -
 -  abstract A
 -    C
 -  B : A
 -}
isIndirectChild :: (Uidable c, MonadAnalysis m) => c -> c -> m Bool
isIndirectChild c p =
  fromMaybeT False $ do
    child <- toClafer c
    parent <- toClafer p
    s <- colonOf parent
    when (uid s == "clafer") mzero
    isChild child s

isChild :: (Uidable c, MonadAnalysis m) => c -> c -> m Bool
isChild child parent =
  liftM2 (||) (isDirectChild child parent) (isIndirectChild child parent)
  
class Matchable c => Uidable c where
  toClafer :: MonadAnalysis m => c -> m SClafer
  fromClafer :: MonadAnalysis m => SClafer -> m c
  toUid :: MonadAnalysis m => c -> m String
  fromUid :: MonadAnalysis m => String -> m c
  
instance Uidable SClafer where
  toClafer = return
  fromClafer = return
  toUid = return . uid
  fromUid = claferWithUid
  
instance Uidable String where
  toClafer = claferWithUid
  fromClafer = return . uid
  toUid = return
  fromUid = return

data Anything = Anything

class Matchable u where
  matches :: u -> SClafer -> Bool
  
instance Matchable String where
  matches s c = s == uid c
  
instance Matchable Anything where
  matches _ _ = True
  
instance Matchable SClafer where
  matches c1 c2 = uid c1 == uid c2

anything :: Anything
anything = Anything


-- a is a child of b
(|^) :: (MonadAnalysis m, Matchable a, Matchable b) => a -> b -> m [(SClafer, SClafer)]
lower |^ upper = runListT $ do
    clafer <- foreach clafers
    guard $ matches lower clafer
    parent <- parentOf clafer
    guard $ matches upper parent
    return (clafer , parent) 

-- a -> b    
(|->) :: (MonadAnalysis m, Matchable a, Matchable b) => a -> b -> m [(SClafer, SClafer)]
lower |-> upper = runListT $ do
    clafer <- foreach clafers
    guard $ matches lower clafer
    super  <- refOf clafer
    guard $ matches upper super
    return (clafer, super) 

-- a : b
(|:) :: (MonadAnalysis m, Matchable a, Matchable b) => a -> b -> m [(SClafer, SClafer)]
lower |: upper = runListT $ do
    clafer <- foreach clafers
    guard $ matches lower clafer
    super  <- colonOf clafer
    guard $ matches upper super
    return (clafer, super) 

-- constraints under
constraintsUnder :: (MonadAnalysis m, Matchable a) => a -> m [(SClafer, I.PExp)]
constraintsUnder under =
  do
    clafers' <- filter (matches under) <$> clafers
    return [(clafer, constraint) | clafer <- clafers', constraint <- constraints clafer]


rootUid :: String
rootUid = "_root"


-- Converts IClafer to SClafer
convertClafer :: I.IClafer -> [SClafer]
convertClafer = 
  convertClafer' Nothing
  where
  convertElement' parent (I.IEClafer clafer) = Just $ Left $ convertClafer' parent clafer
  convertElement' _ (I.IEConstraint _ pexp)   = Just $ Right $ pexp
  convertElement' _ _ = Nothing
  
  convertClafer' parent clafer =
    sclafer : concat children
    where
    sclafer
      | maybe 1 groupLow parent == 0 && maybe 1 groupHigh parent /= -1 =
          SClafer (I._uid clafer) (I._uid clafer) (I._isAbstract clafer) 1   high gLow gHigh (uid <$> parent) super constraints
      | otherwise =
          SClafer (I._uid clafer) (I._uid clafer) (I._isAbstract clafer) low high gLow gHigh (uid <$> parent) super constraints
    (children, constraints) = partitionEithers $ mapMaybe (convertElement' $ Just $ sclafer) (I._elements clafer)
    
    Just (low, high) = I._card clafer
    (gLow, gHigh) =
      case I._gcard clafer of
        Nothing -> (0, -1)
        -- TODO: Bug w/ keywords?
        Just (I.IGCard True _) -> (0, 1)
        Just (I.IGCard _ i)    -> i
    super =
      case I._super clafer of
        I.ISuper True [I.PExp{I._exp = I.IClaferId{I._sident = superUid}}]  -> Just $ Ref superUid
        I.ISuper False [I.PExp{I._exp = I.IClaferId{I._sident = superUid}}] ->
          if superUid `elem` ["string", "real", "int", "integer", "boolean"]
            then Just $ Ref superUid
            else Just $ Colon superUid
        _ -> Nothing

gatherInfo :: I.IModule -> Info
gatherInfo imodule =
  Info $ sClafer : sInteger : sInt : sReal : sString : sBoolean : convertClafer root
  where
  sClafer = SClafer "clafer" "clafer" False 0 (-1) 0 (-1) Nothing Nothing []
  sInteger = SClafer "integer" "integer" False 0 (-1) 0 (-1) Nothing Nothing []
  sInt     = SClafer "int" "int" False 0 (-1) 0 (-1) Nothing Nothing []
  sReal    = SClafer "real" "real" False 0 (-1) 0 (-1) Nothing Nothing []
  sString  = SClafer "string" "string" False 0 (-1) 0 (-1) Nothing Nothing []
  sBoolean = SClafer "boolean" "boolean" False 0 (-1) 0 (-1) Nothing Nothing []
  
  root = I.IClafer noSpan False Nothing rootUid rootUid (I.ISuper False [I.PExp Nothing "" noSpan $ I.IClaferId "clafer" "clafer" True]) (Just (1, 1)) (0, 0) $ I._mDecls imodule





{-
 -
 - Utility functions
 -
 -}
liftMaybe :: Monad m => Maybe a -> MaybeT m a
liftMaybe = MaybeT . return

liftList :: Monad m => [a] -> ListT m a
liftList = ListT . return
 
runListT_ :: Monad m => ListT m a -> m ()
runListT_ l = runListT l >> return ()

foreach :: m[a] -> ListT m a
foreach = ListT

foreachM :: Monad m => [a] -> ListT m a
foreachM = ListT . return

subClafers :: (a, b) -> a
subClafers = fst

superClafers :: (a, b) -> b
superClafers = snd

findAll :: Monad m => m a -> ListT m a
findAll = lift

select :: Monad m => m [a] -> (a -> b) -> m [b]
select from f = from >>= return . map f

suchThat :: Monad m => m [a] -> (a -> Bool) -> m [a]
suchThat = flip $ liftM . filter

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f l = concat `liftM` mapM f l

whenM :: Monad m => m Bool -> m () -> m ()
whenM a b = a >>= (`when` b)

unlessM :: Monad m => m Bool -> m() -> m()
unlessM a b = a >>= (`unless` b)

fromMaybeT :: Monad m => a -> MaybeT m a -> m a
fromMaybeT def m = fromMaybe def `liftM` runMaybeT m

mapMaybeT :: (m1 (Maybe a1) -> m (Maybe a)) -> MaybeT m1 a1 -> MaybeT m a
mapMaybeT f = MaybeT . f . runMaybeT

mapVSupplyT :: (Monad m, Monad m1) => (m1 a1 -> m a) -> VSupplyT m1 a1 -> VSupplyT m a
mapVSupplyT f = lift . f . runVSupplyT

mapLeft :: (t -> a) -> Either t b -> Either a b
mapLeft f (Left l)  = Left $ f l
mapLeft _ (Right r) = Right r

mapRight :: (t -> b) -> Either a t -> Either a b
mapRight _ (Left l)  = Left l
mapRight f (Right r) = Right $ f r

(<:>) :: Monad m => m a -> m [a] -> m [a]
(<:>) = liftM2 (:)

testing :: Eq b => (a -> b) -> a -> a -> Bool
testing f a b = f a == f b

comparing :: Ord b => (a -> b) -> a -> a -> Ordering
comparing f a b = f a `compare` f b

syntaxOf :: I.PExp -> String
syntaxOf = printTree . sugarExp

-- http://stackoverflow.com/questions/1714006/haskell-grouping-problem
combine :: Ord a => [(a, b)] -> [(a, [b])]
combine =
    map mergeGroup . groupBy (testing fst) . sortBy (comparing fst)
    where
    mergeGroup ((a, b):xs) = (a, b : map snd xs)
    mergeGroup [] = error "Function mergeGroup from Analysis expected a non empty list, but was given an empty one"

-- Returns true iff the left and right expressions are syntactically identical
sameAs :: I.PExp -> I.PExp -> Bool
sameAs e1 e2 = syntaxOf e1 == syntaxOf e2 -- Not very efficient but hopefully correct
