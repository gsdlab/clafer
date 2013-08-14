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

import Language.Clafer.Front.Absclafer
import Data.Monoid
import Data.Foldable (foldMap)

data Ir =
  IRIModule IModule | 
  IRIElement IElement |
  IRIType IType |
  IRClafer IClafer |
  IRIExp IExp |
  IRPExp PExp |
  IRISuper ISuper |
  IRIQuant IQuant |
  IRIDecl IDecl |
  IRIGCard IGCard
  deriving (Eq, Show)

data IType = TBoolean
           | TString
           | TInteger
           | TReal
           | TClafer [String]
  deriving (Eq,Ord,Show)

-- each file contains exactly one mode. A module is a list of declarations
data IModule = IModule {
      mName :: String,    -- always empty for now because we don't have syntax for declaring modules
      mDecls :: [IElement]
    }
  deriving (Eq,Ord,Show)

-- Clafer has a list of fields that specify its properties. Some fields, marked as (o) are for generating optimized code
data IClafer =
   IClafer {
      getParent :: Maybe IClafer, -- Nothing => TopLevel, Just x => x is the parent of this clafer
      cinPos :: Span,             -- the position of the syntax in source code
      isAbstract :: Bool,         -- whether abstract or not (i.e., concrete)
      gcard :: Maybe IGCard,      -- group cardinality
      ident :: String,            -- name
      uid :: String,              -- (o) unique identifier
      super:: ISuper,             -- superclafers
      card :: Maybe Interval,     -- clafer cardinality
      glCard :: Interval,         -- (o) global cardinality
      elements :: [IElement]      -- nested declarations
    }

data IClaferInstace =                                          -- IClafer without the Parent,
  IClaferInstace Span Bool (Maybe IGCard) String String ISuper -- used to help derive instances
  (Maybe Interval) Interval [IElement] deriving (Eq,Ord,Show)  -- that will ignore the Parent.

instance Eq IClafer where
  (==) (IClafer _ cp ia g i u s c gc es) (IClafer _ cp' ia' g' i' u' s' c' gc' es') = 
    (IClaferInstace cp ia g i u s c gc es) == (IClaferInstace cp' ia' g' i' u' s' c' gc' es')

instance Ord IClafer where
  compare (IClafer _ cp ia g i u s c gc es) (IClafer _ cp' ia' g' i' u' s' c' gc' es') = 
    IClaferInstace cp ia g i u s c gc es `compare` IClaferInstace cp' ia' g' i' u' s' c' gc' es'

instance Show IClafer where
  show (IClafer _ cp ia g i u s c gc es) = show $ IClaferInstace cp ia g i u s c gc es


-- Clafer's subelement is either a clafer, a constraint, or a goal (objective)
-- This is a wrapper type needed to have polymorphic lists of elements
data IElement =
   IEClafer IClafer
 | IEConstraint {
      isHard :: Bool,     -- whether hard or not (soft)
      cpexp :: PExp       -- the expression
    }
 | IEGoal {
   isMaximize :: Bool,    -- whether maximize or minimize
   cpexp :: PExp          -- the expression
   }
  deriving (Eq,Ord,Show)

-- A list of superclafers.  
-- ->    -- overlaping unique (set)
-- ->>   -- overlapping non-unique (bag)
-- :     -- non overlapping (disjoint)
data ISuper =
   ISuper {
      isOverlapping :: Bool,  -- whether overlapping or disjoint with other clafers extending given list of superclafers
      supers :: [PExp]
    }
  deriving (Eq,Ord,Show)

-- Group cardinality is specified as an interval. It may also be given by a keyword.
-- xor  -- 1..1 isKeyword = True
-- 1..1 -- 1..1 isKeyword = False
data IGCard =
  IGCard {
      isKeyword :: Bool,    -- whether given by keyword: or, xor, mux
      interval :: Interval
    }
  deriving (Eq,Ord,Show)

-- (Min, Max) integer interval. -1 denotes *
type Interval = (Integer, Integer)

-- This is expression container (parent). It has meta information about an actual expression 'exp'
data PExp = PExp {
      iType :: Maybe IType,  
      pid :: String,         -- non-empy unique id for expressions with span, "" for noSpan
      inPos :: Span,         -- position in the input Clafer file
      exp :: IExp            -- the actual expression
    }
  deriving (Eq,Ord,Show)

data IExp = 
   -- quantified expression with declarations
   -- e.g., [ all x1; x2 : X | x1.ref != x2.ref ]
   IDeclPExp {quant :: IQuant, oDecls :: [IDecl], bpexp :: PExp}
   -- expression with a
   -- unary function, e.g., -1
   -- binary function, e.g., 2 + 3
   -- ternary function, e.g., if x then 4 else 5
 | IFunExp {op :: String, exps :: [PExp]}
 | IInt Integer                  -- integer number
 | IDouble Double                -- real number
 | IStr String                   -- string
 | IClaferId {                   -- clafer name
      modName :: String,         -- module name - currently not used and empty since we have no module system
      sident :: String,          -- name of the clafer being referred to
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
-- disj x1; x2 : X ++ Y
-- y1 : Y 
data IDecl =
   IDecl {
      isDisj :: Bool,     -- is disjunct
      decls :: [String],  -- a list of local names
      body :: PExp        -- set to which local names refer to
    }
  deriving (Eq,Ord,Show)

data IQuant =
   INo    -- does not exist
 | ILone  -- less than one
 | IOne   -- exactly one
 | ISome  -- at least one (i.e., exists)
 | IAll   -- for all
  deriving (Eq,Ord,Show)

type LineNo = Integer
type ColNo  = Integer


{-Ir Traverse Functions-}
-------------------------

mapIR :: (Ir -> Ir) -> IModule -> IModule -- fmap/map for IModule
mapIR f (IModule name decls') = 
  unWrapIModule $ f $ IRIModule $ IModule name $ map (unWrapIElement . iMap f . IRIElement) decls'

foldMapIR :: (Monoid m) => (Ir -> m) -> IModule -> m -- foldMap for IModule
foldMapIR f i@(IModule _ decls') = 
  (f $ IRIModule i) `mappend` foldMap (iFoldMap f . IRIElement) decls'

foldIR :: (Ir -> a -> a) -> a -> IModule -> a -- a basic fold for IModule
foldIR f e m = appEndo (foldMapIR (Endo . f) m) e

{-
Note: even though the above functions take an IModule, 
the functions they use take an Ir (wrapped version see top of module). 
Also the bellow functions are just helpers for the above, you may use
them if you wish to start from somewhere other than IModule.
-}

iMap :: (Ir -> Ir) -> Ir -> Ir 
iMap f (IRIElement (IEClafer c)) = 
  f $ IRIElement $ IEClafer $ unWrapIClafer $ iMap f $ IRClafer c
iMap f (IRIElement (IEConstraint h pexp)) =
  f $ IRIElement $ IEConstraint h $ unWrapPExp $ iMap f $ IRPExp pexp
iMap f (IRIElement (IEGoal m pexp)) =
  f $ IRIElement $ IEGoal m $ unWrapPExp $ iMap f $ IRPExp pexp 
iMap f (IRClafer (IClafer par p a (Just grc) i u s c goc elems)) =
  f $ IRClafer $ IClafer par p a (Just $ unWrapIGCard $ iMap f $ IRIGCard grc) i u (unWrapISuper $ iMap f $ IRISuper s) c goc $ map (unWrapIElement . iMap f . IRIElement) elems
iMap f (IRClafer (IClafer par p a Nothing i u s c goc elems)) =
  f $ IRClafer $ IClafer par p a Nothing i u (unWrapISuper $ iMap f $ IRISuper s) c goc $ map (unWrapIElement . iMap f . IRIElement) elems
iMap f (IRIExp (IDeclPExp q decs p)) =
  f $ IRIExp $ IDeclPExp (unWrapIQuant $ iMap f $ IRIQuant q) (map (unWrapIDecl . iMap f . IRIDecl) decs) $ unWrapPExp $ iMap f $ IRPExp p
iMap f (IRIExp (IFunExp o pexps)) = 
  f $ IRIExp $ IFunExp o $ map (unWrapPExp . iMap f . IRPExp) pexps
iMap f (IRPExp (PExp (Just iType') pID p iExp)) =
  f $ IRPExp $ PExp (Just $ unWrapIType $ iMap f $ IRIType iType') pID p $ unWrapIExp $ iMap f $ IRIExp iExp
iMap f (IRPExp (PExp Nothing pID p iExp)) =
  f $ IRPExp $ PExp Nothing pID p $ unWrapIExp $ iMap f $ IRIExp iExp
iMap f (IRISuper (ISuper o pexps)) =
  f $ IRISuper $ ISuper o $ map (unWrapPExp . iMap f . IRPExp) pexps
iMap f (IRIDecl (IDecl i d body')) = 
  f $ IRIDecl $ IDecl i d $ unWrapPExp $ iMap f $ IRPExp body'
iMap f i = f i

iFoldMap :: (Monoid m) => (Ir -> m) -> Ir -> m
iFoldMap f i@(IRIElement (IEConstraint _ pexp)) =
  f i `mappend` (iFoldMap f $ IRPExp pexp)
iFoldMap f i@(IRIElement (IEGoal _ pexp)) =
  f i `mappend` (iFoldMap f $ IRPExp pexp)
iFoldMap f i@(IRClafer (IClafer _ _ _ Nothing _ _ s _ _ elems)) =
  f i `mappend` (iFoldMap f $ IRISuper s) `mappend` foldMap (iFoldMap f . IRIElement) elems
iFoldMap f i@(IRClafer (IClafer _ _ _ (Just grc) _ _ s _ _ elems)) =
  f i `mappend` (iFoldMap f $ IRISuper s) `mappend` (iFoldMap f $ IRIGCard grc) `mappend` foldMap (iFoldMap f . IRIElement) elems
iFoldMap f i@(IRIExp (IDeclPExp q decs p)) =
  f i `mappend` (iFoldMap f $ IRIQuant q) `mappend` (iFoldMap f $ IRPExp p) `mappend` foldMap (iFoldMap f . IRIDecl) decs
iFoldMap f i@(IRIExp (IFunExp _ pexps)) = 
  f i `mappend` foldMap (iFoldMap f . IRPExp) pexps
iFoldMap f i@(IRPExp (PExp (Just iType') _ _ iExp)) =
  f i `mappend` (iFoldMap f $ IRIType iType') `mappend` (iFoldMap f $ IRIExp iExp)
iFoldMap f i@(IRPExp (PExp Nothing _ _ iExp)) =
  f i `mappend` (iFoldMap f $ IRIExp iExp)
iFoldMap f i@(IRISuper (ISuper _ pexps)) =
  f i `mappend` foldMap (iFoldMap f . IRPExp) pexps
iFoldMap f i@(IRIDecl (IDecl _ _ body')) = 
  f i `mappend` (iFoldMap f $ IRPExp body')
iFoldMap f (IRIElement (IEClafer c)) = iFoldMap f $ IRClafer c
iFoldMap f i = f i

iFold :: (Ir -> a -> a) -> a -> Ir -> a
iFold f e m = appEndo (iFoldMap (Endo . f) m) e


unWrapIModule :: Ir -> IModule
unWrapIModule (IRIModule x) = x
unWrapIModule x = error $ "Can't call unWarpIModule on " ++ show x
unWrapIElement :: Ir -> IElement
unWrapIElement (IRIElement x) = x
unWrapIElement x = error $ "Can't call unWarpIElement on " ++ show x
unWrapIType :: Ir -> IType
unWrapIType (IRIType x) = x
unWrapIType x = error $ "Can't call unWarpIType on " ++ show x
unWrapIClafer :: Ir -> IClafer
unWrapIClafer (IRClafer x) = x
unWrapIClafer x = error $ "Can't call unWarpIClafer on " ++ show x
unWrapIExp :: Ir -> IExp
unWrapIExp (IRIExp x) = x
unWrapIExp x = error $ "Can't call unWarpIExp on " ++ show x
unWrapPExp :: Ir -> PExp
unWrapPExp (IRPExp x) = x
unWrapPExp x = error $ "Can't call unWarpPExp on " ++ show x
unWrapISuper :: Ir -> ISuper
unWrapISuper (IRISuper x) = x
unWrapISuper x = error $ "Can't call unWarpISuper on " ++ show x
unWrapIQuant :: Ir -> IQuant
unWrapIQuant (IRIQuant x) = x
unWrapIQuant x = error $ "Can't call unWarpIQuant on " ++ show x
unWrapIDecl :: Ir -> IDecl
unWrapIDecl (IRIDecl x) = x
unWrapIDecl x = error $ "Can't call unWarpIDecl on " ++ show x
unWrapIGCard :: Ir -> IGCard
unWrapIGCard (IRIGCard x) = x
unWrapIGCard x = error $ "Can't call unWarpIGcard on " ++ show x