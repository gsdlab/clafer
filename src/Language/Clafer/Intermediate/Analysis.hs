{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances, GeneralizedNewtypeDeriving, StandaloneDeriving #-}

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

import Control.Applicative
import Control.Monad.LPMonad.Supply
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.List
import Control.Monad.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.List
import Data.Maybe



newtype AnalysisT m a = AnalysisT (ReaderT Info m a)
  deriving (Monad, Functor, MonadReader Info, MonadState s, MonadTrans, MonadPlus, MonadError e, Applicative)
  
type Analysis = AnalysisT Identity

class (Monad m, Functor m) => MonadAnalysis m where
  clafers :: m [SClafer]
  withExtraClafers :: [SClafer] -> m a -> m a
  
instance (Monad m, Functor m) => MonadAnalysis (AnalysisT m) where
  clafers = AnalysisT $ asks sclafers
  withExtraClafers extra = local addInfo
    where
    addInfo (Info c) = Info $ extra ++ c
    
instance (Error e, MonadAnalysis m) => MonadAnalysis (ErrorT e m) where
  clafers = lift clafers
  withExtraClafers = mapErrorT . withExtraClafers
  
instance MonadAnalysis m => MonadAnalysis (ListT m) where
  clafers = lift clafers
  withExtraClafers = mapListT . withExtraClafers

instance MonadAnalysis m => MonadAnalysis (MaybeT m) where
  clafers = lift clafers
  withExtraClafers = mapMaybeT . withExtraClafers
  
instance MonadAnalysis m => MonadAnalysis (VSupplyT m) where
  clafers = lift clafers
  withExtraClafers = mapVSupplyT . withExtraClafers
  
isConcrete :: SClafer -> Bool
isConcrete = not . isAbstract

isBase :: SClafer -> Bool
isBase = (`elem` ["clafer", "string", "real", "int", "integer", "boolean"]) . uid

isDerived :: SClafer -> Bool
isDerived = not . isBase
 

data SSuper = Ref String | Colon String deriving Show
-- Easier to work with. IClafers have links from parents to children. SClafers have links from children to parent.
data SClafer = SClafer {uid::String, isAbstract::Bool, low::Integer, high::Integer, parent::Maybe String, super::Maybe SSuper, constraints::[I.PExp]} deriving Show
  
data Info = Info{sclafers :: [SClafer]} deriving Show 

runAnalysis r info = runIdentity $ runAnalysisT r info

runAnalysisT :: AnalysisT m a -> Info -> m a
runAnalysisT (AnalysisT r) info = runReaderT r info

claferWithUid :: MonadAnalysis m => String -> m SClafer
claferWithUid u =
  do
    c <- clafers
    case find ((==) u . uid) c of
      Just c' -> return $ c'
      Nothing -> error $ "claferWithUid: Unknown uid " ++ u
      
parentUid :: Monad m => SClafer -> m String
parentUid clafer =
  case parent clafer of
    Just p  -> return p
    Nothing -> fail $ "No parent uid for " ++ show clafer
    
parentOf :: (Uidable c, MonadAnalysis m) => c -> m c
parentOf clafer = fromClafer =<< claferWithUid =<< parentUid =<< toClafer clafer

refUid :: Monad m => SClafer -> m String
refUid clafer =
  case super clafer of
    Just (Ref u)  -> return u
    _             -> fail $ "No ref uid for " ++ show clafer

refOf :: (Uidable c, MonadAnalysis m) => c -> m c
refOf clafer = fromClafer =<< claferWithUid =<< refUid =<< toClafer clafer

refsOf :: (Uidable c, MonadAnalysis m) => c -> m [c]
refsOf clafer =
  runListT $ do
    r <- refOf clafer
    return r `mplus` ListT (refsOf r)

colonUid :: Monad m => SClafer -> m String
colonUid clafer =
  case super clafer of
    Just (Colon u)  -> return u
    _               -> fail $ "No colon uid for " ++ show clafer

colonOf :: (Uidable c, MonadAnalysis m) => c -> m c
colonOf clafer = fromClafer =<< claferWithUid =<< colonUid =<< toClafer clafer

colonsOf :: (Uidable c, MonadAnalysis m) => c -> m [c]
colonsOf clafer =
  runListT $ do
    r <- colonOf clafer
    return r `mplus` ListT (colonsOf r)

hierarchy :: (Uidable c, MonadAnalysis m) => c -> m [c]
hierarchy t = (t :) <$> colonsOf t

{-
 - C is a direct child of B.
 -
 -  B
 -    C
 -}
isDirectChild :: (Uidable c, MonadAnalysis m) => c -> c -> m Bool
isDirectChild c p =
  do
    child <- toClafer c
    parent <- toClafer p
    is (not . null) (child |^ parent)
 
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
  
class Uidable c where
  toClafer :: MonadAnalysis m => c -> m SClafer
  fromClafer :: MonadAnalysis m => SClafer -> m c
  
instance Uidable SClafer where
  toClafer = return
  fromClafer = return
  
instance Uidable String where
  toClafer = claferWithUid
  fromClafer = return . uid

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
lower |^ upper =
  runListT $ do
    clafer <- foreach clafers
    parent <- parentOf clafer
    when (not $ matches lower clafer) mzero
    when (not $ matches upper parent) mzero
    return (clafer , parent)

-- a -> b    
(|->) :: (MonadAnalysis m, Matchable a, Matchable b) => a -> b -> m [(SClafer, SClafer)]
lower |-> upper =
  runListT $ do
    clafer <- foreach clafers
    super  <- refOf clafer
    when (not $ matches lower clafer) mzero
    when (not $ matches upper super) mzero
    return (clafer, super)

-- a : b
(|:) :: (MonadAnalysis m, Matchable a, Matchable b) => a -> b -> m [(SClafer, SClafer)]
lower |: upper =
  runListT $ do
    clafer <- foreach clafers
    super  <- colonOf clafer
    when (not $ matches lower clafer) mzero
    when (not $ matches upper super) mzero
    return (clafer, super)

-- constraints under
constraintsUnder :: (MonadAnalysis m, Matchable a) => a -> m [(SClafer, I.PExp)]
constraintsUnder under =
  runListT $ do
    clafer <- foreach clafers
    when (not $ matches under clafer) mzero
    constraint <- foreachM $ constraints clafer
    return (clafer, constraint)


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
    SClafer (I.uid clafer) (I.isAbstract clafer) low high parent super constraints : concat children
    where
    (children, constraints) = partitionEithers $ mapMaybe (convertElement' $ Just $ I.uid clafer) (I.elements clafer)
    
    Just (low, high) = I.card clafer
    super =
      case I.super clafer of
        I.ISuper True [I.PExp{I.exp = I.IClaferId{I.sident = superUid}}]  -> Just $ Ref superUid
        I.ISuper False [I.PExp{I.exp = I.IClaferId{I.sident = superUid}}] ->
          if superUid `elem` ["string", "real", "int", "integer", "boolean"]
            then Just $ Ref superUid
            else Just $ Colon superUid
        _ -> Nothing

gatherInfo :: I.IModule -> Info
gatherInfo imodule =
  Info $ sClafer : sInteger : sInt : sReal : sString : sBoolean : convertClafer root
  where
  sClafer = SClafer "clafer" False 0 (-1) Nothing Nothing []
  sInteger = SClafer "integer" False 0 (-1) Nothing Nothing []
  sInt     = SClafer "int" False 0 (-1) Nothing Nothing []
  sReal    = SClafer "real" False 0 (-1) Nothing Nothing []
  sString  = SClafer "string" False 0 (-1) Nothing Nothing []
  sBoolean = SClafer "boolean" False 0 (-1) Nothing Nothing []
  
  root = I.IClafer noSpan True Nothing rootUid rootUid (I.ISuper False [I.PExp Nothing "" noSpan $ I.IClaferId "clafer" "clafer" True]) (Just (1, 1)) (0, 0) $ I.mDecls imodule





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

is :: Monad m => (a -> Bool) -> m a -> m Bool
is = liftM

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
