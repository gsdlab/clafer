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

data INumericSub = IInteger | IReal | ISetInteger | ISetReal
  deriving (Eq,Ord,Show)

data IStringSub = ILiteral | ISetString
  deriving (Eq,Ord,Show)

-- Module is a list of top-level declarations
data IModule = IModule {
      mName :: String,
      mDecls :: [IElement]
    }
  deriving (Eq,Ord,Show)

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

-- Clafer's subelement is either a clafer of a constraint
data IElement =
   IEClafer IClafer
 | IEConstraint PExp
  deriving (Eq,Ord,Show)

-- A list of superclafers. The isOverlapping determines whether the clafer is overlapping or disjoint with other clafers extending given list of superclafers.
data ISuper =
   ISuper {
      isOverlapping :: Bool,
      supers :: [PExp]
    }
  deriving (Eq,Ord,Show)

-- Group cardinality is specified as an interval. It may also be given by a keyword.
data IGCard =
  IGCard {
      isKeyword :: Bool,
      interval :: Interval
    }
  deriving (Eq,Ord,Show)

-- (Min, max) integer interval
type Interval = (Integer, ExInteger)

data PExp = PExp {
      iType :: Maybe IType,
      pid :: String,
      exp :: IExp
    }
  deriving (Eq,Ord,Show)

data IExp = 
   -- quantified expression with declarations
   IDeclPExp {quant :: IQuant, oDecls :: [IDecl], bpexp :: PExp}
 | IFunExp {op :: String, exps :: [PExp]}
 | IInt Integer                       -- integer number
 | IDouble Double                     -- real number
 | IStr String                        -- string
 | IClaferId {                        -- clafer name
      modName :: String,         -- module name
      sident :: String,          -- name
      isTop :: Bool              -- identifier refers to a top-level definition
    }
  deriving (Eq,Ord,Show)

{-
For IFunExp standard set of operators includes:
1. Unary operators:
        !          -- not
        #          -- set counting operator
        -          -- negation
2. Binary operators:
        <=>        -- equivalence
        =>         -- implication
        ||         -- disjunction
        xor        -- exclusive or
        &&         -- conjunction
        <          -- less than
        >          -- greater than
        =          -- equality
        <=         -- less than or equal
        >=         -- greater than or equal
        !=         -- inequality
        in         -- belonging to a set/being a subset
        nin        -- not belonging to a set/not being a subset
        +          -- addition/string concatenation
        -          -- substraction
        *          -- multiplication
        /          -- division
        ++         -- set union
        --         -- set difference
        &          -- set intersection
        <:         -- domain restriction
        :>         -- range restriction
        .          -- relational join
3. Ternary operators
        ifthenelse -- if then else
-}

-- Local declaration
data IDecl =
   IDecl {
      isDisj :: Bool,     -- is disjunct
      decls :: [String],  -- a list of local names
      body :: PExp        -- set to which local names refer to
    }
  deriving (Eq,Ord,Show)

data IQuant =
   INo
 | ILone
 | IOne
 | ISome
 | IAll
  deriving (Eq,Ord,Show)
