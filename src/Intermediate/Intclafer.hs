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
module Intermediate.Intclafer where

import Front.Absclafer

data EType = TAExp | TSExp | TSAExp
  deriving (Eq,Ord,Show)

type IModule = [IDeclaration]

data IDeclaration =
   IClaferDecl IClafer
 | IConstDecl ILExp
  deriving (Eq,Ord,Show)

data IClafer =
   IClafer {
      isAbstract :: Bool,
      gcard :: Maybe IGCard,
      ident :: String,
      uid :: String,
      super:: ISuper,
      card :: Maybe Interval,
      glCard :: Interval,
      elements :: [IElement]
    }
  deriving (Eq,Ord,Show)

data IElement =
   ISubclafer IClafer
 | ISubconstraint ILExp
  deriving (Eq,Ord,Show)

data ISuper =
   ISuper {
      isOverlapping :: Bool,
      supers :: [ISExp]
    }
  deriving (Eq,Ord,Show)

data IGCard =
  IGCard {
      isKeyword :: Bool,
      interval :: Interval
    }
  deriving (Eq,Ord,Show)

type Interval = (Integer, ExInteger)

data ILExp =
   IEIff ILExp ILExp
 | IEImpliesElse ILExp ILExp (Maybe ILExp)
 | IEOr ILExp ILExp
 | IEXor ILExp ILExp
 | IEAnd ILExp ILExp
 | IENeg ILExp
 | IETerm ITerm
  deriving (Eq,Ord,Show)

data ITerm =
   ITermCmpExp ICmpExp (Maybe EType)
 | ITermQuantSet Quant ISExp
 | ITermQuantDeclExp [IDecl] ILExp
  deriving (Eq,Ord,Show)

data ICmpExp =
   IELt IExp IExp
 | IEGt IExp IExp
 | IEREq IExp IExp
 | IEEq IExp IExp
 | IELte IExp IExp
 | IEGte IExp IExp
 | IENeq IExp IExp
 | IERNeq IExp IExp
 | IEIn IExp IExp
 | IENin IExp IExp
  deriving (Eq,Ord,Show)

data IExp =
   IENumExp IAExp
 | IEStrExp StrExp
  deriving (Eq,Ord,Show)

data ISExp =
   ISExpUnion ISExp ISExp
 | ISExpIntersection ISExp ISExp
 | ISExpDomain ISExp ISExp
 | ISExpRange ISExp ISExp
 | ISExpJoin ISExp ISExp
 | ISExpIdent {
      sident :: String,
      isTop :: Bool
    }
  deriving (Eq,Ord,Show)

data IDecl =
   IDecl {
      exquant :: ExQuant,
      isDisj :: Bool,
      decls :: [String],
      body :: ISExp
    }
  deriving (Eq,Ord,Show)

data IAExp =
   IEAdd IAExp IAExp
 | IESub IAExp IAExp
 | IEMul IAExp IAExp
 | IECSetExp ISExp
 | IEASetExp ISExp
 | IEInt Integer
  deriving (Eq,Ord,Show)
