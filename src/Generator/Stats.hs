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
module Generator.Stats where

import Control.Monad.State

import Common
import Front.Absclafer
import Intermediate.Intclafer
import Optimizer.Optimizer

data Stats = Stats {
      naClafers :: Int,
      nrClafers :: Int,
      ncClafers :: Int,
      nConstraints :: Int,
      sglCard :: Interval
    } deriving Show


statsModule :: IModule -> Stats
statsModule imodule =
  execState (mapM statsElement $ mDecls imodule) $ Stats 0 0 0 0 (1, ExIntegerNum 1)


statsClafer clafer = do
  if isAbstract clafer
    then modify (\e -> e {naClafers = naClafers e + 1})
    else
      if isOverlapping $ super clafer
        then modify (\e -> e {nrClafers = nrClafers e + 1})
        else modify (\e -> e {ncClafers = ncClafers e + 1})
  sglCard' <- gets sglCard
  modify (\e -> e {sglCard = statsCard sglCard' $ glCard clafer})
  mapM_ statsElement $ elements clafer


statsCard :: Interval -> Interval -> Interval
statsCard (m, n) (m', n') = (max m m', maxEx n n')
  where
  maxEx ExIntegerAst _ = ExIntegerAst
  maxEx _ ExIntegerAst = ExIntegerAst
  maxEx (ExIntegerNum m) (ExIntegerNum n) = ExIntegerNum $ max m n


statsElement x = case x of
  IEClafer clafer -> statsClafer clafer
  IEConstraint _ _ -> modify (\e -> e {nConstraints = nConstraints e + 1})
