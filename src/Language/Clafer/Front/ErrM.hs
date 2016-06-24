-- BNF Converter: Error Monad
-- Copyright (C) 2004  Author:  Aarne Ranta

-- This file comes with NO WARRANTY and may be used FOR ANY PURPOSE.
module Language.Clafer.Front.ErrM where

-- the Error monad: like Maybe type with error msgs

import Control.Monad
import Control.Applicative
import Prelude

import Language.Clafer.Front.AbsClafer

data Err a = Ok a | Bad Pos String
  deriving (Read, Show, Eq, Ord)

instance Monad Err where
  return      = pure
  fail        = Bad noPos
  Ok a  >>= f = f a
  Bad p s >>= _ = Bad p s

instance Applicative Err where
  pure = Ok
  (Bad p s) <*> _ = Bad p s
  (Ok f) <*> o  = fmap f o


instance Functor Err where
  fmap = liftM

instance MonadPlus Err where
  mzero = Bad noPos "Err.mzero"
  mplus (Bad _ _) y = y
  mplus x       _ = x

instance Alternative Err where
  empty = mzero
  (<|>) = mplus
