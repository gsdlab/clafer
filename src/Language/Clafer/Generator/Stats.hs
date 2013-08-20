{-# LANGUAGE FlexibleContexts #-}
{-
 Copyright (C) 2012 Kacper Bak <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Generator.Stats where

import Control.Monad.State
import Language.Clafer.Intermediate.Intclafer

data Stats = Stats {
      naClafers :: Int,
      nrClafers :: Int,
      ncClafers :: Int,
      nConstraints :: Int,
      nGoals :: Int,
      sglCard :: Interval
    } deriving Show


statsModule :: IModule -> Stats
statsModule imodule =
  execState (mapM statsElement $ mDecls imodule) $ Stats 0 0 0 0 0 (1, 1)

statsClafer :: MonadState Stats m => IClafer -> m ()
statsClafer claf = do
  if isAbstract claf
    then modify (\e -> e {naClafers = naClafers e + 1})
    else
      if isOverlapping $ super claf
        then modify (\e -> e {nrClafers = nrClafers e + 1})
        else modify (\e -> e {ncClafers = ncClafers e + 1})
  sglCard' <- gets sglCard
  modify (\e -> e {sglCard = statsCard sglCard' $ glCard claf})
  mapM_ statsElement $ elements claf


statsCard :: Interval -> Interval -> Interval
statsCard (m1, n1) (m2, n2) = (max m1 m2, maxEx n1 n2)
  where
  maxEx m' n' = if m' == -1 || n' == -1 then -1 else max m' n'

statsElement :: MonadState Stats m => IElement -> m ()
statsElement x = case x of
  IEClafer clafer -> statsClafer clafer
  IEConstraint _ _ _ -> modify (\e -> e {nConstraints = nConstraints e + 1})
  IEGoal _ _ _ -> modify (\e -> e {nGoals = nGoals e + 1})