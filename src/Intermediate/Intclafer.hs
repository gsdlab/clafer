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
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- Module is a list of top-level declarations
type IModule = [IDeclaration]

-- Declaration is either a Clafer of a global constraint
data IDeclaration =
   IClaferDecl IClafer
 | IConstDecl ILExp
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- Clafer has a list of fields that specify its properties. Some fields, marked as (o) are for generating optimized code
data IClafer =
   IClafer {
      isAbstract :: Bool,     -- determines whether it's abstract
      gcard :: Maybe IGCard,  -- group cardinality
      ident :: String,        -- name
      uid :: String,          -- (o) unique identifier
      super:: ISuper,         -- superclafers
      card :: Maybe Interval, -- cardinality
      glCard :: Interval,     -- (o) global cardinality
      elements :: [IElement]  -- subclafers or constraints specified in the context of given clafer
    }
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- Clafer's subelement is either a clafer of a constraint
data IElement =
   ISubclafer IClafer
 | ISubconstraint ILExp
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- A list of superclafers. The isOverlapping determines whether the clafer is overlapping or disjoint with other clafers extending given list of superclafers.
data ISuper =
   ISuper {
      isOverlapping :: Bool,
      supers :: [ISExp]
    }
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- Group cardinality is specified as an interval. It may also be given by a keyword.
data IGCard =
  IGCard {
      isKeyword :: Bool,
      interval :: Interval
    }
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- (Min, max) integer interval
type Interval = (Integer, ExInteger)

-- Logical expressions
data ILExp =
   IEIff ILExp ILExp                       -- equivalence
 | IEImpliesElse ILExp ILExp (Maybe ILExp) -- implication/if then else
 | IEOr ILExp ILExp                        -- disjunction
 | IEXor ILExp ILExp                       -- exclusive or
 | IEAnd ILExp ILExp                       -- conjunction
 | IENeg ILExp                             -- negation
 | IETerm ITerm                            -- term
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- definition of a term
data ITerm =
   ITermCmpExp ICmpExp (Maybe EType) -- relational expression (comparison)
 | ITermQuantSet Quant ISExp         -- quantified set
 | ITermQuantDeclExp [IDecl] ILExp   -- logical expression with local declarations
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- Relational expression
data ICmpExp =
   IELt IExp IExp   -- less than
 | IEGt IExp IExp   -- greater than
 | IEREq IExp IExp  -- referential equality
 | IEEq IExp IExp   -- equality
 | IELte IExp IExp  -- less than or equal
 | IEGte IExp IExp  -- greater then or equal
 | IENeq IExp IExp  -- inequality
 | IERNeq IExp IExp -- referential inequality
 | IEIn IExp IExp   -- belonging to a set/being a subset
 | IENin IExp IExp  -- not belonging to a set/not being a subset
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- Generic expression
data IExp =
   IENumExp IAExp  -- numeric expression
 | IEStrExp StrExp -- string expression
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- Set expression
data ISExp =
   ISExpUnion ISExp ISExp        -- set union
 | ISExpIntersection ISExp ISExp -- set intersection
 | ISExpDomain ISExp ISExp       -- domain restriction
 | ISExpRange ISExp ISExp        -- range restriction
 | ISExpJoin ISExp ISExp         -- relational join
 | ISExpIdent {                  -- identifier
      sident :: String,          -- name
      isTop :: Bool              -- indicates whether the identifier refers to a top-level definition
    }
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- Local declaration
data IDecl =
   IDecl {
      exquant :: ExQuant, -- extended quantifier
      isDisj :: Bool,     -- is disjunct
      decls :: [String],  -- a list of local names
      body :: ISExp       -- set to which local names refer to
    }
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- Arithmetic expression
data IAExp =
   IEAdd IAExp IAExp -- addition
 | IESub IAExp IAExp -- substraction
 | IEMul IAExp IAExp -- multiplication
 | IECSetExp ISExp   -- counting number of set elements
 | IEASetExp ISExp   -- using clafer as a number
 | IEInt Integer     -- integer
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT
