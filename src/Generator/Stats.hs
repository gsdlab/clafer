{-
 This file is part of the Clafer Translator (clafer).

 Copyright (C) 2010 Kacper Bak <http://gsd.uwaterloo.ca/kbak>

 clafer is free software: you can redistribute it and/or modify
 it under the terms of the GNU Lesser General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 clafer is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Lesser General Public License for more details.

 You should have received a copy of the GNU Lesser General Public License
 along with clafer. (See files COPYING and COPYING.LESSER.)  If not,
 see <http://www.gnu.org/licenses/>.
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
statsModule declarations =
  execState (mapM statsDeclaration declarations) $ Stats 0 0 0 0 (1, ExIntegerNum 1)


statsDeclaration x = case x of
  IClaferDecl clafer  -> statsClafer clafer
  IConstDecl constraint  -> modify (\e -> e {nConstraints = nConstraints e + 1})


statsClafer clafer = do
  if isAbstract clafer
    then modify (\e -> e {naClafers = naClafers e + 1})
    else
      if isOverlapping $ super clafer
        then modify (\e -> e {nrClafers = nrClafers e + 1})
        else modify (\e -> e {ncClafers = ncClafers e + 1})
  sglCard' <- gets sglCard
  modify (\e -> e {sglCard = optimizeCard sglCard' $ glCard clafer})
  mapM_ statsElement $ elements clafer


statsElement x = case x of
  ISubclafer clafer -> statsClafer clafer
  ISubconstraint ilexp -> modify (\e -> e {nConstraints = nConstraints e + 1})
