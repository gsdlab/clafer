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
module Intermediate.StringAnalyzer where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

import Common
import Front.Absclafer
import Intermediate.Intclafer

astrModule :: IModule -> IModule
astrModule imodule =
  imodule{mDecls = evalState (mapM astrElement decls) $ Map.empty}
  where
  decls = mDecls imodule


astrClafer x = case x of
  IClafer isAbstract gcard ident uid super card gCard elements  ->
    IClafer isAbstract gcard ident uid super card gCard `liftM`
            mapM astrElement elements


-- astrs single subclafer
astrElement x = case x of
  IEClafer clafer -> IEClafer `liftM` astrClafer clafer
  IEConstraint isHard pexp -> IEConstraint isHard `liftM` astrPExp pexp


astrPExp x = case x of 
  PExp (Just (IString _)) pid exp ->
    PExp (Just $ INumeric $ Just IInteger) pid `liftM` astrIExp exp
  PExp t pid (IFunExp op exps) -> PExp t pid `liftM`
                              (IFunExp op `liftM` mapM astrPExp exps)
  _ -> return x

astrIExp x = case x of
  IFunExp op exps -> if op == iUnion
                     then astrIExp $ concatStrExp x else return x
  IStr str -> do
    modify (\e -> Map.insertWith const str (Map.size e) e)
    st <- get
    return $  (IInt $ toInteger $ (Map.!) st str)
  _ -> return x


concatStrExp :: IExp -> IExp
concatStrExp x = case x of
  IFunExp _ exps -> IStr $ s0 ++ s1 
    where
    ((IStr s0):(IStr s1):_) = map concatStrExp $ map (Intermediate.Intclafer.exp) exps
  IStr string -> x