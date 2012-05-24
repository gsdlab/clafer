{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.Intclafer where

--import Language.Clafer.Front.Absclafer

data IType = TBoolean
           | TString
           | TInteger
           | TReal
           | TClafer
           | TRef IType  -- a reference to the type
  deriving (Eq,Ord,Show)

-- Module is a list of fragments
data IModule = IModule {
      mName :: String,
      mDecls :: [IElement]
--      fragments :: [IModuleFragment]
    }
  deriving (Eq,Ord,Show)

-- Fragment is a list of top-level declarations
{-data IModuleFragment = IModuleFragment {
      mDecls :: [IElement]
    }
  deriving (Eq,Ord,Show)
-}
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
 | IEConstraint {
      isHard :: Bool,
      cpexp :: PExp
    }
 | IEGoal {
   isMaximize :: Bool,
   cpexp :: PExp
   }
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

-- (Min, max) integer interval. -1 denotes *
type Interval = (Integer, Integer)

data PExp = PExp {
      iType :: Maybe IType,
      pid :: String,
      inPos :: Position,         -- position in the input Clafer file
      exp :: IExp
    }
  deriving (Eq,Ord,Show)

data IExp = 
   -- quantified expression with declarations
   IDeclPExp {quant :: IQuant, oDecls :: [IDecl], bpexp :: PExp}
 | IFunExp {op :: String, exps :: [PExp]}
 | IInt Integer                  -- integer number
 | IDouble Double                -- real number
 | IStr String                   -- string
 | IClaferId {                   -- clafer name
      modName :: String,         -- module name
      sident :: String,          -- name
      isTop :: Bool              -- identifier refers to a top-level definition
    }
  deriving (Eq,Ord,Show)

{-
For IFunExp standard set of operators includes:
1. Unary operators:
        !          -- not (logical)
        #          -- set counting operator
        -          -- negation (arithmetic)
        max        -- maximum (created for goals)
        min        -- minimum (created for goals)
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

type LineNo = Int
type ColNo  = Int

type Position = ((LineNo, ColNo), (LineNo, ColNo))
