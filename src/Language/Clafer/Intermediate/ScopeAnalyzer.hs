{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
module Language.Clafer.Intermediate.ScopeAnalyzer (scopeAnalysis) where

import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import qualified Language.Clafer.Intermediate.Intclafer as I

import Prelude hiding (exp)
import Control.Monad
import Control.Monad.List
import Control.Monad.LPMonad
import Control.Monad.State
import Data.LinearProgram
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import System.IO.Unsafe

newtype Analysis a = Analysis (StateT (Info, Integer) (LPM String Double) a)
  deriving (Monad, Functor)

instance MonadState (LP String Double) Analysis where
  get = Analysis $ lift get
  put = Analysis . lift . put
  state = Analysis . lift . state

ask :: Analysis Info
ask = Analysis $ gets fst

asks :: (Info -> a) -> Analysis a
asks f = Analysis $ gets (f . fst)

-- Variables starting with "_aux_" are reserved for creating
-- new variables at runtime.
uniqNameSpace :: String
uniqNameSpace = "_aux_"

uniqVar :: Analysis String
uniqVar =
  do
    (i, c) <- Analysis get
    Analysis $ put (i, c + 1)
    return $ uniqNameSpace ++ show c

runAnalysis :: Analysis a -> Info -> LP String Double
runAnalysis (Analysis s) info = execLPM $ evalStateT s (info, 0)
  

-- a is a child of b
(|^) :: (Uidable a, Uidable b) => a -> b -> ListT Analysis (IClafer, IClafer)
lower |^ upper =
  ListT $ do
    m <- asks parentMap
    cm <- asks claferMap
    let find n = Map.findWithDefault (error $ "|^ No uid named " ++ n) n cm
    return [(find child, find parent) |
            (child, parent) <- m,
            matches (toUid lower) child,
            matches (toUid upper) parent]

-- a : b
(|:) :: (Uidable a, Uidable b) => a -> b -> ListT Analysis (IClafer, IClafer)
lower |: upper =
  ListT $ do
    m <- asks colonMap
    cm <- asks claferMap
    let find n = Map.findWithDefault (error $ "|: No uid named " ++ n) n cm
    return [(find sub, find sup) |
            (sub, sup) <- m,
            matches (toUid lower) sub,
            matches (toUid upper) sup]

-- a -> b    
(|->) :: (Uidable a, Uidable b) => a -> b -> ListT Analysis (IClafer, IClafer)
lower |-> upper =
  ListT $ do
    m <- asks refMap
    cm <- asks claferMap
    let find n = Map.findWithDefault (error $ "|-> No uid named " ++ n) n cm
    return [(find sub, find sup) |
            (sub, sup) <- m,
            matches (toUid lower) sub,
            matches (toUid upper) sup]
            
-- constraints under
constraintsUnder :: Uidable a => a -> ListT Analysis (IClafer, PExp)
constraintsUnder under =
  ListT $ do
    m <- asks constraintMap
    cm <- asks claferMap
    let find n = Map.findWithDefault (error $ "(constraintsUnder) No uid named " ++ n) n cm
    return [(find clafer, constraint) |
            (clafer, constraint) <- m,
            matches (toUid under) clafer]

data Info = Info
  {
    iclafers :: [IClafer],
    claferMap :: Map String IClafer,
    colonMap :: SuperMap,
    refMap :: SuperMap,
    parentMap :: ParentMap,
    constraintMap :: ConstraintMap
  } deriving Show 

type SuperMap = [(String, String)]
type ParentMap = [(String, String)]
type ConstraintMap = [(String, PExp)]

clafers :: ListT Analysis IClafer
clafers = ListT $ asks iclafers

clafers' :: (IClafer -> a) -> ListT Analysis a
clafers' f = f `fmap` clafers

data Uid = Uid {uidLiteral::String} | Any deriving Show

class Uidable u where
  toUid :: u -> Uid
  
instance Uidable Char where
  toUid c = Uid [c]
  
-- c == Char
instance Uidable c => Uidable [c] where
  toUid s = Uid $ concatMap uidLiteral $ map toUid s

instance Uidable Uid where
  toUid = id
  
instance Uidable IClafer where
  toUid = Uid . uid

anything :: Uid
anything = Any


rootUid :: String
rootUid = "_root"

scopeAnalysis :: IModule -> [(String, Integer)]
scopeAnalysis imodule =
  removeZeroes $ removeRoot $ removeAux $
    -- unsafePerformIO should be safe (?)
    -- We aren't modifying any global state.
    -- If we don't use unsafePerformIO, then we have to be inside the IO monad and
    -- makes things really ugly. Might as well contain the ugliness in here.
    case unsafePerformIO solution of
      (Success, Just (_, s)) -> Map.toList $ Map.map truncate s
      x -> [] -- No solution
  where
  solution = glpSolveVars mipDefaults{msgLev = MsgOff} $ runAnalysis setConstraints $ analyze imodule
  -- Any scope that is 0 will take the global scope of 1 instead.
  removeZeroes = filter ((/= 0) . snd)
  -- The root is implied and not and not part of the actual solution.
  removeRoot = filter ((/= rootUid) . fst)
  -- Auxilary variables are only part of the computation, not the solution.
  removeAux = filter (not . (uniqNameSpace `isPrefixOf`) . fst)

setConstraints :: Analysis ()
setConstraints =
  do
    optFormula
    colonConstraints
    refConstraints
    parentConstraints
    (var rootUid) `equalTo` 1
    

matches :: Uid -> String -> Bool
matches (Uid u1) u2 = u1 == u2
matches Any _ = True

analyze :: IModule -> Info
analyze imodule =
  Info clafers claferMap colonMap refMap parentMap constraintMap
  where
  root = IClafer noSpan True Nothing "_root" "_root" (ISuper False [PExp Nothing "" noSpan $ IClaferId "clafer" "clafer" True]) Nothing (0, 0) $ mDecls imodule
  
  clafers = analyzeClafers root
  claferMap = Map.fromList [(uid c, c) | c <- clafers]
  colonMap = toSuperMap $ filter (not . isOverlapping . super) clafers
  refMap = toSuperMap $ filter (isOverlapping . super) clafers
  parentMap = analyzePC root
  constraintMap = []
  
  extends IClafer{super = ISuper _ [PExp{I.exp = IClaferId{sident = superUid}}]} = superUid
  extends c@IClafer{super = s} = error $ show c
  toSuperMap clafers = [(uid c, extends c) | c <- clafers]

optFormula :: Analysis ()
optFormula =
  do
    setDirection Min
    c <- runListT clafers
    let concretes = [uid concrete | concrete <- c, not $ isAbstract concrete]
    setObjective $ varSum concretes

colonConstraints :: Analysis ()
colonConstraints =
  runListT_ $ do
    -- forall c in the set of clafers' uid ...
    c <- clafers' uid
    -- ... find all uids of any clafer that extends c (only colons) ...
    subs <- findAll (uid . subClafers) $ anything |: c
    when (not $ null subs) $
      -- ... then set the constraint scope_C = sum scope_subs
      var c `equal` varSum subs

refConstraints :: Analysis ()
refConstraints =
  runListT_ $ do
    -- for all uids of any clafer the refs another uid ...
    (sub, sup) <- anything |-> anything
    let Just (low, _) = card sub
    let usub = uid sub
    let usup = uid sup
    aux <- lift $ testPositive usub
    -- scope_sup >= low-card(sub)
    var usup `geq` (low *^ var aux)
      
parentConstraints :: Analysis ()
parentConstraints =
  runListT_ $ do
    -- forall child under parent ...
    (child, parent) <- anything |^ anything
    let Just (low, high) = card child
    let uchild = uid child
    let uparent = uid parent
    -- ... scope_this <= scope_parent * low-card(this) ...
    (var uchild) `geq` (low *^ var uparent)
    -- ... scope_this >= scope_parent * high-card(this) ...
    -- high == -1 implies high card is unbounded
    when (high /= -1) $ 
      (var uchild) `leq` (high *^ var uparent)

{-
 - Create a new variable "aux". If
 -   v == 0 -> aux == 0
 -   v > 0  -> aux == 1
 -
 - pre: v >= 0
 -}
testPositive :: String -> Analysis String
testPositive v =
  do
    aux <- uniqVar
    var aux `leq` var v
    var aux `geq` (smallM *^ var v)
    var aux `leqTo` 1
    setVarKind aux IntVar
    return aux

{-
 - smallM cannot be too small. For example, with glpk
 -   0.000001 * 9 = 0
 -}
smallM :: Double
smallM = 0.00001

findAll f = lift . runListT . fmap f
subClafers = fst
superClafers = snd

runListT_ :: Monad m => ListT m a -> m ()
runListT_ l = runListT l >> return ()


t = IModule {mName = "", mDecls = [IEClafer (IClafer {cinPos = Span (Pos 1 1) (Pos 2 4), isAbstract = False, gcard = Just (IGCard {isKeyword = False, interval = (0,-1)}), ident = "A", uid = "c1_A", super = ISuper {isOverlapping = False, supers = [PExp {iType = Just TClafer, pid = "", inPos = Span (Pos 1 3) (Pos 1 4), exp = IClaferId {modName = "", sident = "c3_C", isTop = True}}]}, card = Just (2,2), glCard = (1,1), elements = [IEClafer (IClafer {cinPos = Span (Pos 2 3) (Pos 2 4), isAbstract = False, gcard = Just (IGCard {isKeyword = False, interval = (0,-1)}), ident = "B", uid = "c2_B", super = ISuper {isOverlapping = False, supers = [PExp {iType = Just TClafer, pid = "", inPos = Span (Pos 0 0) (Pos 0 0), exp = IClaferId {modName = "", sident = "clafer", isTop = False}}]}, card = Just (1,1), glCard = (1,1), elements = []})]}),IEClafer (IClafer {cinPos = Span (Pos 3 1) (Pos 4 4), isAbstract = True, gcard = Just (IGCard {isKeyword = False, interval = (0,-1)}), ident = "C", uid = "c3_C", super = ISuper {isOverlapping = False, supers = [PExp {iType = Just TClafer, pid = "", inPos = Span (Pos 0 0) (Pos 0 0), exp = IClaferId {modName = "", sident = "clafer", isTop = False}}]}, card = Just (0,-1), glCard = (0,-1), elements = [IEClafer (IClafer {cinPos = Span (Pos 4 3) (Pos 4 4), isAbstract = False, gcard = Just (IGCard {isKeyword = False, interval = (0,-1)}), ident = "D", uid = "c4_D", super = ISuper {isOverlapping = False, supers = [PExp {iType = Just TClafer, pid = "", inPos = Span (Pos 0 0) (Pos 0 0), exp = IClaferId {modName = "", sident = "clafer", isTop = False}}]}, card = Just (1,1), glCard = (0,-1), elements = []})]})]}

-- analyzeClafers: finds all the IClafers
analyzeClafers :: IClafer -> [IClafer]
analyzeClafers c@IClafer{elements = elements} = c : concatMap analyzeElement elements
  where
  analyzeElement (IEClafer clafer) = analyzeClafers clafer
  analyzeElement _ = []

-- analyzePC: finds the map from children to parents
analyzePC :: IClafer -> ParentMap
analyzePC IClafer{uid = uid, elements = elements} = concatMap (analyzePCElement uid) elements
  where
  analyzePCElement :: String -> IElement -> [(String, String)]
  analyzePCElement parent (IEClafer clafer)    = analyzePCClafer parent clafer
  analyzePCElement _ _ = []

  analyzePCClafer :: String -> IClafer -> [(String, String)]
  analyzePCClafer parent IClafer{uid = uid, elements = elements} =
    (uid, parent) : concatMap (analyzePCElement uid) elements


-- Unfold joins
-- If the expression is a tree of only joins, then this function will flatten
-- the joins into a list.
-- Otherwise, returns an empty list.
unfoldJoins :: PExp -> [String]
unfoldJoins pexp =
    fromMaybe [] $ unfoldJoins' pexp
    where
    unfoldJoins' PExp{exp = (IFunExp "." args)} =
        return $ args >>= unfoldJoins
    unfoldJoins' PExp{exp = IClaferId{sident = sident}} =
        return $ [sident]
    unfoldJoins' _ =
        fail "not a join"
