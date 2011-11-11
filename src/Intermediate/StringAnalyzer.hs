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

import Front.Absclafer
import Intermediate.Intclafer

astrModule :: IModule -> IModule
astrModule imodule =
  imodule{mDecls = evalState (mapM astrDeclaration decls) $ Map.empty}
  where
  decls = mDecls imodule

astrDeclaration x = case x of
  IClaferDecl clafer -> IClaferDecl `liftM` astrClafer clafer
  IConstDecl lexp -> IConstDecl `liftM` astrPExp lexp


astrClafer x = case x of
  IClafer isAbstract gcard ident uid super card gCard elements  ->
    IClafer isAbstract gcard ident uid super card gCard `liftM`
            mapM astrElement elements


-- astrs single subclafer
astrElement x = case x of
  ISubclafer clafer -> ISubclafer `liftM` astrClafer clafer
  ISubconstraint pexp -> ISubconstraint `liftM` astrPExp pexp


astrPExp x = case x of 
  PExp (Just (IString _)) exp ->
    PExp (Just $ INumeric $ Just IInteger) `liftM` astrIExp exp
  PExp t (IFunExp op exps) -> PExp t `liftM`
                              (IFunExp op `liftM` mapM astrPExp exps)
  _ -> return x

astrIExp x = case x of
  IFunExp IUnion exps -> astrIExp $ concatStrExp x
  IStr str -> do
    modify (\e -> Map.insertWith const str (Map.size e) e)
    st <- get
    return $  (IInt $ toInteger $ (Map.!) st str)
  _ -> return x


concatStrExp :: IExp -> IExp
concatStrExp x = case x of
  IFunExp IUnion exps -> IStr $ s0 ++ s1
    where
    ((IStr s0):(IStr s1):_) = map concatStrExp $ map (Intermediate.Intclafer.exp) exps
  IStr string -> x