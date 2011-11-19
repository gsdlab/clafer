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

data IType = IBoolean
           | IString  (Maybe IStringSub)
           | INumeric (Maybe INumericSub)
           | ISet
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

data INumericSub = IInteger | IReal | ISetInteger | ISetReal
  deriving (Eq,Ord,Show)

data IStringSub = ILiteral | ISetString
  deriving (Eq,Ord,Show)

-- Module is a list of top-level declarations
data IModule = IModule {
      mName :: String,
      mDecls :: [IDeclaration]
    }
  deriving (Eq,Ord,Show)

-- Declaration is either a Clafer of a global constraint
data IDeclaration =
   IClaferDecl IClafer
 | IConstDecl PExp
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
 | ISubconstraint PExp
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

-- A list of superclafers. The isOverlapping determines whether the clafer is overlapping or disjoint with other clafers extending given list of superclafers.
data ISuper =
   ISuper {
      isOverlapping :: Bool,
      supers :: [PExp]
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
      iType :: Maybe IType,
      exp :: IExp
    }
  deriving (Eq,Ord,Show)

data Op =
-- unary operators
          INeg          -- negation
        | ICSet         -- set counting operator
-- binary operators
        | IIff          -- equivalence
        | IImpl         -- implication
        | IOr           -- disjunction
        | IXor          -- exclusive or
        | IAnd          -- conjunction
        | ILt           -- less than
        | IGt           -- greater than
        | IEq           -- equality
        | ILte          -- less than or equal
        | IGte          -- greater than or equal
        | INeq          -- inequality
        | IIn           -- belonging to a set/being a subset
        | INin          -- not belonging to a set/not being a subset
        | IPlus         -- addition/string concatenation
        | ISub          -- substraction
        | IMul          -- multiplication
        | IDiv          -- division
        | IUnion        -- set union
        | IDifference   -- set difference
        | IIntersection -- set intersection
        | IDomain       -- domain restriction
        | IRange        -- range restriction
        | IJoin         -- relational join
-- ternary operators
        | IIfThenElse   -- if then else
  deriving (Eq,Ord,Show,Enum)

data IExp = 
   IDeclPExp IQuant [IDecl] PExp      -- quantified expression with declarations
 | IFunExp {op :: Op, exps :: [PExp]}
 | IInt Integer                       -- integer number
 | IDouble Double                     -- real number
 | IStr String                        -- string
 | IClaferId {                        -- clafer name
      modName :: String,         -- module name
      sident :: String,          -- name
      isTop :: Bool              -- identifier refers to a top-level definition
    }
  deriving (Eq,Ord,Show)

-- Local declaration
data IDecl =
   IDecl {
      isDisj :: Bool,     -- is disjunct
      decls :: [String],  -- a list of local names
      body :: PExp        -- set to which local names refer to
    }
  deriving (Eq,Ord,Show)
  {-! derive : XmlContent !-}    -- this line is for DrIFT

data IQuant =
   INo
 | ILone
 | IOne
 | ISome
 | IAll
  deriving (Eq,Ord,Show)
