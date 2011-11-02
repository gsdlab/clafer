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

data PExp = PExp {
      eType :: Maybe EType,
      exp :: IExp
    }
  deriving (Eq,Ord,Show)

data IExp =
   IDeclPExp ExQuant [Decl] PExp        -- quantified expression with local declarations
 | IEIff PExp PExp                      -- equivalence
 | IEImpliesElse PExp PExp (Maybe PExp) -- implication/if then else
 | IEOr PExp PExp                       -- disjunction
 | IEXor PExp PExp                      -- exclusive or
 | IEAnd PExp PExp                      -- conjunction
 | IENeg PExp                           -- negation
 | IQuantPExp Quant PExp                -- quantified expression
 | IELt PExp PExp                       -- less than
 | IEGt PExp PExp                       -- greater than
 | IEEq PExp PExp                       -- equality
 | IELte PExp PExp                      -- less than or equal
 | IEGte PExp PExp                      -- greater than or equal
 | IENeq PExp PExp                      -- inequality
 | IEIn PExp PExp                       -- belonging to a set/being a subset
 | IENin PExp PExp                      -- not belonging to a set/not being a subset
 | IEAdd PExp PExp                      -- addition
 | IESub PExp PExp                      -- substraction
 | IEMul PExp PExp                      -- multiplication
 | IEDiv PExp PExp                      -- division
 | IECSetPExp PExp                      -- counting number of set elements
 | IEInt Integer                        -- integer number
 | IEStr String                         -- string
 | IUnion PExp PExp                     -- set union/string concatenation
 | IDifference PExp PExp                -- set difference
 | IIntersection PExp PExp              -- set intersection
 | IDomain PExp PExp                    -- domain restriction
 | IRange PExp PExp                     -- range restriction
 | IJoin PExp PExp                      -- relational join
 | IClaferId Name                       -- clafer name
  deriving (Eq,Ord,Show)

data IName = IName {
      modName :: String,
      sident :: String,          -- name
      isTop :: Bool              -- indicates whether the identifier refers to a top-level definition
    }
  deriving (Eq,Ord,Show)

-- Local declaration
data IDecl =
   IDecl {
      isDisj :: Bool,     -- is disjunct
      decls :: [String],  -- a list of local names
      body :: PExp       -- set to which local names refer to
    }
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT
