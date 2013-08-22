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
import Prelude hiding (exp)
import Data.Maybe
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
  IRIReference IReference |
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
      claferParent :: Maybe IClafer,  -- Nothing => TopLevel, Just x => x is the parent of this clafer
      cinPos :: Span,                 -- the position of the syntax in source code
      isAbstract :: Bool,             -- whether abstract or not (i.e., concrete)
      gcard :: Maybe IGCard,          -- group cardinality
      ident :: String,                -- name
      uid :: String,                  -- (o) unique identifier
      super :: ISuper,                -- superclafers
      reference :: IReference,        -- refrence types
      card :: Maybe Interval,         -- clafer cardinality
      glCard :: Interval,             -- (o) global cardinality
      elements :: [IElement]          -- nested declarations
    }

data IClaferInstance =                                          -- IClafer without the Parent,
  IClaferInstance Span Bool (Maybe IGCard) String String ISuper -- used to help derive instances
    IReference (Maybe Interval) Interval [IElement]             -- that will ignore the Parent.
      deriving (Eq,Ord)  

instance Eq IClafer where
  (==) (IClafer _ cp ia g i u s r c gc es) (IClafer _ cp' ia' g' i' u' s' r' c' gc' es') = 
    (IClaferInstance cp ia g i u s r c gc es) == (IClaferInstance cp' ia' g' i' u' s' r' c' gc' es')

instance Ord IClafer where
  compare (IClafer _ cp ia g i u s r c gc es) (IClafer _ cp' ia' g' i' u' s' r' c' gc' es') = 
    IClaferInstance cp ia g i u s r c gc es `compare` IClaferInstance cp' ia' g' i' u' s' r' c' gc' es'

instance Show IClafer where
  show (IClafer p cp ia g i u s r c gc es) = 
    "IClafer {claferParentIdent = " ++ 
      (if p == Nothing then "Nothing" else if (uid $ fromJust p) /= "" then (uid $ fromJust p) else ident $ fromJust p) 
        ++ " cinPos = " ++ show cp ++ " isAbstract = " ++ show ia ++ 
          " gcard = " ++ show g ++ " ident = " ++ show i ++ " uid " ++ 
            show u ++ " super = " ++ show s ++ " reference = " ++ show r 
              ++ " card = " ++ show c ++ " glCard = " ++ show gc ++ 
                " elements = " ++ show es


-- Clafer's subelement is either a clafer, a constraint, or a goal (objective)
-- This is a wrapper type needed to have polymorphic lists of elements
data IElement =
   IEClafer IClafer
 | IEConstraint {
      constraintParent :: Maybe IClafer,-- Nothing => TopLevel, Just x => x is the parent of this constraint
      isHard :: Bool,                   -- whether hard or not (soft)
      cpexp :: PExp                     -- the expression
    }
 | IEGoal {
   goalParent :: Maybe IClafer,-- Nothing => TopLevel, Just x => x is the parent of this goal
   isMaximize :: Bool,         -- whether maximize or minimize
   cpexp :: PExp               -- the expression
   }

data ElementInstance = ElementInstance Bool PExp deriving (Eq, Ord)

instance Eq IElement where
  (==) (IEClafer c) (IEClafer c') = c == c'
  (==) (IEConstraint _ b p) (IEConstraint _ b' p') = 
    (ElementInstance b p) == (ElementInstance b' p')
  (==) (IEGoal _ b p) (IEGoal _ b' p') =
    (ElementInstance b p) == (ElementInstance b' p')
  (==) _ _ = False

instance Ord IElement where
  compare (IEClafer c) (IEClafer c') = c `compare` c'
  compare (IEConstraint _ b p) (IEConstraint _ b' p') =
    (ElementInstance b p) `compare` (ElementInstance b' p')
  compare (IEGoal _ b p) (IEGoal _ b' p') =
    (ElementInstance b p) `compare` (ElementInstance b' p')
  compare (IEClafer _) (IEConstraint _ _ _) = LT
  compare  (IEConstraint _ _ _) (IEClafer _) = GT
  compare (IEConstraint _ _ _) (IEGoal _ _ _) = LT
  compare (IEGoal _ _ _) (IEConstraint _ _ _) = GT
  compare (IEClafer _) (IEGoal _ _ _) = LT
  compare (IEGoal _ _ _) (IEClafer _)  = GT

instance Show IElement where
  show (IEClafer c) = "IEClafer " ++ show c 
  show (IEConstraint cp b p) = 
    "IEConstraint {constraintParentIdent = " ++ 
      (if cp == Nothing then "Nothing" else ident $ fromJust cp) 
        ++ " isHard = " ++ show b ++ " cpexp = " ++ show p
  show (IEGoal gp b p) = 
     "IEConstraint {goalParnetIdent = " ++ 
      (if gp == Nothing then "Nothing" else ident $ fromJust gp) 
        ++ " isMaximize = " ++ show b ++ " cpexp = " ++ show p


-- A list of superclafers.  
-- :    -- non overlapping (disjoint)
data ISuper =
   ISuper {
      iSuperParent :: IClafer, 
      superKind :: SuperKind,
      supers :: [PExp]
    }

data SuperKind = TopLevel | Nested | Redefinition IClafer | RedefinitionFail String deriving Ord

instance Eq SuperKind where
  (==) TopLevel TopLevel = True
  (==) Nested Nested = True
  (==) (Redefinition c1) (Redefinition c2) = uid c1 == uid c2
  (==) (RedefinitionFail _) (RedefinitionFail _) = True
  (==) _ _ = False
instance Show SuperKind where
  show TopLevel = "TopLevel"
  show Nested = "Nested"
  show (Redefinition c) = "Redefinition: " ++ uid c
  show (RedefinitionFail msg) = "RedefinitionFail: " ++ msg

data ISuperInstance = ISuperInstance SuperKind [PExp] deriving (Eq, Ord)

instance Eq ISuper where
  (==) (ISuper _ sk ss) (ISuper _ sk' ss') = 
    (ISuperInstance sk ss) == (ISuperInstance sk' ss')

instance Ord ISuper where
  compare (ISuper _ sk ss) (ISuper _ sk' ss') = 
    (ISuperInstance sk ss) `compare` (ISuperInstance sk' ss')

instance Show ISuper where
  show (ISuper par sk ss) = 
    "ISuper {iSuperParentIdent = " ++ 
      (if (uid par) == "" then ident par else uid par) ++ 
        ", superKind = " ++ show sk ++ ", supers = " ++ show ss


getReDefClafer :: IClafer -> IClafer
getReDefClafer (IClafer{super = ISuper{superKind = Redefinition i}}) = i
getReDefClafer _ = error "Tried to get redefintion clafer from a clafer that is not redefined"

-- ->   -- overlapping unique (set) [isSet=True]
-- ->>  -- overlapping non-unique (bag) [isSet=False]
data IReference = 
  IReference {
    iReferenceParent :: IClafer,
    isSet :: Bool,  -- True - set reference clafer, False - bag reference clafer
    refs :: [PExp]
  }

data IReferenceInstance = IReferenceInstance Bool [PExp] deriving (Eq, Ord)

instance Eq IReference where
  (==) (IReference _ s r) (IReference _ s' r') = 
    (IReferenceInstance s r) == (IReferenceInstance s' r')

instance Ord IReference where
  compare (IReference _ s r) (IReference _ s' r') = 
    (IReferenceInstance s r) `compare` (IReferenceInstance s' r')

instance Show IReference where
  show (IReference par s r) = 
    "IReference {iReferenceParentIdent = " ++ 
      (if (uid par) == "" then ident par else uid par) ++ 
        " superKind = " ++ show s ++ " refs = " ++ show r

isOverlapping :: IClafer -> Bool
isOverlapping = ([]/=) . refs . reference


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
      pExpParent :: Maybe PExp, -- Nothing => TopLevel, Just x => x is the parent of this PExp
      iType :: Maybe IType,  
      pid :: String,            -- non-empy unique id for expressions with span, "" for noSpan
      inPos :: Span,            -- position in the input Clafer file
      exp :: IExp               -- the actual expression
    }

data PExpInstance = PExpInstance (Maybe IType) String Span IExp 
  deriving (Eq,Ord)

instance Eq PExp where
  (==) (PExp _ t p pos e) (PExp _ t' p' pos' e') = 
    (PExpInstance t p pos e) == (PExpInstance t' p' pos' e')

instance Ord PExp where
  compare (PExp _ t p pos e) (PExp _ t' p' pos' e') = 
    (PExpInstance t p pos e) `compare` (PExpInstance t' p' pos' e')

instance Show PExp where
  show (PExp par t p pos e) = 
    "PExp {pExpParentIdent = " ++ 
      (if par == Nothing then "Nothing" else if (pid $ fromJust par) /= "" then (pid $ fromJust par) else getPExpName $ fromJust par)
        ++ ", iType = " ++ show t ++ ", pid = " ++ show p ++ 
          ", inPos = " ++ show pos ++ ", exp = "  ++ show e

getPExpName :: PExp -> String
getPExpName PExp{exp = IClaferId _ id' _} = id'
getPExpName PExp{exp = IDeclPExp d _ _} = show d
getPExpName PExp{exp = IFunExp op' _} = op'
getPExpName PExp{exp = IInt i} = show i
getPExpName PExp{exp = IDouble d} = show d
getPExpName PExp{exp = IStr s} = s

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

forIR :: IModule -> (Ir -> Ir) -> IModule -- mapIR with arguments fliped
forIR = flip mapIR

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
iMap f (IRIElement (IEConstraint p h pexp)) =
  f $ IRIElement $ IEConstraint p h $ unWrapPExp $ iMap f $ IRPExp pexp
iMap f (IRIElement (IEGoal p m pexp)) =
  f $ IRIElement $ IEGoal p m $ unWrapPExp $ iMap f $ IRPExp pexp 
iMap f (IRClafer (IClafer par p a grc i u s r c goc elems)) =
  f $ IRClafer $ IClafer par p a (if grc==Nothing then grc else Just $ unWrapIGCard $ iMap f $ IRIGCard $ fromJust grc) i u (unWrapISuper $ iMap f $ IRISuper s) (unWrapIReference $ iMap f $ IRIReference r) c goc $ map (unWrapIElement . iMap f . IRIElement) elems
iMap f (IRIExp (IDeclPExp q decs p)) =
  f $ IRIExp $ IDeclPExp (unWrapIQuant $ iMap f $ IRIQuant q) (map (unWrapIDecl . iMap f . IRIDecl) decs) $ unWrapPExp $ iMap f $ IRPExp p
iMap f (IRIExp (IFunExp o pexps)) = 
  f $ IRIExp $ IFunExp o $ map (unWrapPExp . iMap f . IRPExp) pexps
iMap f (IRPExp (PExp par iType' pID p iExp)) =
  f $ IRPExp $ PExp par (if iType'==Nothing then iType' else Just $ unWrapIType $ iMap f $ IRIType $ fromJust iType') pID p $ unWrapIExp $ iMap f $ IRIExp iExp
iMap f (IRISuper (ISuper par r pexps)) =
  f $ IRISuper $ ISuper par r $ map (unWrapPExp . iMap f . IRPExp) pexps
iMap f (IRIReference (IReference par s pexps)) =
  f $ IRIReference $ IReference par s $ map (unWrapPExp . iMap f . IRPExp) pexps
iMap f (IRIDecl (IDecl i d body')) = 
  f $ IRIDecl $ IDecl i d $ unWrapPExp $ iMap f $ IRPExp body'
iMap f i = f i

iFor :: Ir -> (Ir -> Ir) -> Ir
iFor = flip iMap

iFoldMap :: (Monoid m) => (Ir -> m) -> Ir -> m
iFoldMap f i@(IRIElement (IEConstraint _ _ pexp)) =
  f i `mappend` (iFoldMap f $ IRPExp pexp)
iFoldMap f i@(IRIElement (IEGoal _ _ pexp)) =
  f i `mappend` (iFoldMap f $ IRPExp pexp)
iFoldMap f i@(IRClafer (IClafer _ _ _ grc _ _ s r _ _ elems)) =
  f i `mappend` (iFoldMap f $ IRISuper s) `mappend` (iFoldMap f $ IRIReference r) `mappend` (if grc==Nothing then mempty else (iFoldMap f $ IRIGCard $ fromJust grc)) `mappend` foldMap (iFoldMap f . IRIElement) elems
iFoldMap f i@(IRIExp (IDeclPExp q decs p)) =
  f i `mappend` (iFoldMap f $ IRIQuant q) `mappend` (iFoldMap f $ IRPExp p) `mappend` foldMap (iFoldMap f . IRIDecl) decs
iFoldMap f i@(IRIExp (IFunExp _ pexps)) = 
  f i `mappend` foldMap (iFoldMap f . IRPExp) pexps
iFoldMap f i@(IRPExp (PExp _ iType' _ _ iExp)) =
  f i `mappend` (if iType'==Nothing then mempty else iFoldMap f $ IRIType $ fromJust iType') `mappend` (iFoldMap f $ IRIExp iExp)
iFoldMap f i@(IRISuper (ISuper _ _ pexps)) =
  f i `mappend` foldMap (iFoldMap f . IRPExp) pexps
iFoldMap f i@(IRIReference (IReference _ _ pexps)) =
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
unWrapIReference :: Ir -> IReference
unWrapIReference (IRIReference x) = x
unWrapIReference x = error $ "Can't call unWarpIReference on " ++ show x
unWrapIQuant :: Ir -> IQuant
unWrapIQuant (IRIQuant x) = x
unWrapIQuant x = error $ "Can't call unWarpIQuant on " ++ show x
unWrapIDecl :: Ir -> IDecl
unWrapIDecl (IRIDecl x) = x
unWrapIDecl x = error $ "Can't call unWarpIDecl on " ++ show x
unWrapIGCard :: Ir -> IGCard
unWrapIGCard (IRIGCard x) = x
unWrapIGCard x = error $ "Can't call unWarpIGcard on " ++ show x