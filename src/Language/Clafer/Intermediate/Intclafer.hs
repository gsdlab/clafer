{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
{-
 Copyright (C) 2012-2015 Kacper Bak, Jimmy Liang, Michal Antkiewicz, Luke Michael Brown <http://gsd.uwaterloo.ca>

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
-- | Intermediate representation (IR) of a Clafer model
module Language.Clafer.Intermediate.Intclafer where

import Language.Clafer.Front.AbsClafer

import Control.Lens
import Data.Aeson
import Data.Aeson.TH
import Data.Data
import Data.Monoid
import Data.Foldable
import Prelude

-- | unique identifier of a clafer
type UID = String
-- | clafer name as declared in the source model
type CName = String
-- | file:// ftp:// or http:// prefixed URL
type URL = String

-- | A "supertype" of all IR types
data Ir
  = IRIModule IModule
  | IRIElement IElement
  | IRIType IType
  | IRClafer IClafer
  | IRIExp IExp
  | IRPExp PExp
  | IRIReference (Maybe IReference)
  | IRIQuant IQuant
  | IRIDecl IDecl
  | IRIGCard (Maybe IGCard)
  deriving (Eq, Show)

data IType
  = TBoolean
  | TString
  | TInteger
  | TDouble
  | TReal
  | TClafer
    { _hi :: [UID]          -- ^ [UID] represents an inheritance hierarchy obtained using @Common.findHierarchy
    }
  | TMap                      --  Represents a map from the src class to the target class
    { _so :: IType            -- ^ must only be a TClass
    , _ta :: IType            -- ^ must only be a TClass
    }
  | TUnion
    { _un :: [IType]          -- ^ [IType] is a list of basic types (not union types)
    }

  deriving (Eq,Ord,Show,Data,Typeable)

-- | each file contains exactly one mode. A module is a list of declarations
data IModule
  = IModule
    { _mName :: String -- ^ always empty (no syntax for declaring modules)
    , _mDecls :: [IElement] -- ^ List of top-level elements
    }
  deriving (Eq,Ord,Show,Data,Typeable)

-- | Clafer has a list of fields that specify its properties. Some fields, marked as (o) are for generating optimized code
data IClafer
  = IClafer
    { _cinPos :: Span         -- ^ the position of the syntax in source code
    , _isAbstract :: Bool     -- ^ whether abstract or not (i.e., concrete)
    , _gcard :: Maybe IGCard  -- ^ group cardinality
    , _ident :: CName         -- ^ name declared in the model
    , _uid :: UID             -- ^ a unique identifier
    , _parentUID :: UID       -- ^ "root" if top-level, "" if unresolved or for root clafer, otherwise UID of the parent clafer
    , _super :: Maybe PExp    -- ^ superclafer - only allowed PExp is IClaferId. Nothing = default super "clafer"
    , _reference :: Maybe IReference -- ^ reference type, bag or set
    , _card :: Maybe Interval -- ^ clafer cardinality
    , _glCard :: Interval     -- ^ (o) global cardinality
    , _elements :: [IElement] -- ^ nested elements
    }
  deriving (Eq,Ord,Show,Data,Typeable)

-- | Clafer's subelement is either a clafer, a constraint, or a goal (objective)
--   This is a wrapper type needed to have polymorphic lists of elements
data IElement
  = IEClafer
    { _iClafer :: IClafer  -- ^ the actual clafer
    }
  | IEConstraint
    { _isHard :: Bool      -- ^ whether hard constraint or assertion
    , _cpexp :: PExp       -- ^ the container of the actual expression
    }
  -- | Goal (optimization objective)
  | IEGoal
    { _isMaximize :: Bool     -- ^ whether maximize or minimize
    , _cpexp :: PExp          -- ^ the expression
    }
  deriving (Eq,Ord,Show,Data,Typeable)

-- | A type of reference.
--   ->    values unique (set)
--   ->>   values non-unique (bag)
data IReference
  = IReference
    { _isSet :: Bool -- ^ whether set or bag
    , _ref :: PExp  -- ^ the only allowed reference expressions are IClafer and set expr. (++, **, --s)
    }
  deriving (Eq,Ord,Show,Data,Typeable)

-- | Group cardinality is specified as an interval. It may also be given by a keyword.
--   xor    1..1 isKeyword = True
--   1..1   1..1 isKeyword = False
data IGCard
  = IGCard
    { _isKeyword :: Bool    -- ^ whether given by keyword: or, xor, mux
    , _interval :: Interval
    } deriving (Eq,Ord,Show,Data,Typeable)

-- | (Min, Max) integer interval. -1 denotes *
type Interval = (Integer, Integer)

-- | This is expression container (parent).
--   It has meta information about an actual expression 'exp'
data PExp
  = PExp
    { _iType :: Maybe IType   -- ^ the inferred type
    , _pid :: String          -- ^ non-empty unique id for expressions with span, \"\" for noSpan
    , _inPos :: Span          -- ^ position in the input Clafer file
    , _exp :: IExp            -- ^ the actual expression
    }
  deriving (Eq,Ord,Show,Data,Typeable)

-- | Embedes reference to a resolved Clafer
type ClaferBinding = Maybe UID

data IExp
    -- | quantified expression with declarations
    --   e.g., [ all x1; x2 : X | x1.ref != x2.ref ]
  = IDeclPExp
    { _quant :: IQuant
    , _oDecls :: [IDecl]
    , _bpexp :: PExp
    }
    -- | expression with a
    --   unary function, e.g., -1
    --   binary function, e.g., 2 + 3
    --   ternary function, e.g., if x then 4 else 5
  | IFunExp
    { _op :: String
    , _exps :: [PExp]
    }
    -- | integer number
  | IInt
    { _iint :: Integer
    }
    -- | real number
  | IReal
    { _ireal :: Double
    }
    -- | double-precision floating point number
  | IDouble
    { _idouble :: Double
    }
    -- | string
  | IStr
    { _istr :: String
    }
    -- | a reference to a clafer name
  | IClaferId
    { _modName :: String         -- ^ module name - currently not used and empty since we have no module system
    , _sident :: CName           -- ^ name of the clafer being referred to
    , _isTop :: Bool             -- ^ identifier refers to a top-level definition
    , _binding :: ClaferBinding  -- ^ the UID of the bound IClafer, if resolved
    }
  deriving (Eq,Ord,Show,Data,Typeable)

{- |
For IFunExp standard set of operators includes:
1. Unary operators:
        !          - not (logical)
        #          - set counting operator
        -          - negation (arithmetic)
        max        - maximum (created for goals)
        min        - minimum (created for goals)
2. Binary operators:
        \<=\>        - equivalence
        =\>         - implication
        ||         - disjunction
        xor        - exclusive or
        &&         - conjunction
        \<          - less than
        \>          - greater than
        =          - equality
        \<=         - less than or equal
        \>=         - greater than or equal
        !=         - inequality
        in         - belonging to a set/being a subset
        nin        - not belonging to a set/not being a subset
        +          - addition/string concatenation
        -          - substraction
        *          - multiplication
        /          - division
        ++         - set union
        \-\-         - set difference
        **          - set intersection
        \<:         - domain restriction
        :\>         - range restriction
        .          - relational join
3. Ternary operators
        ifthenelse -- if then else
-}

-- | Local declaration
--   disj x1; x2 : X ++ Y
--   y1 : Y
data IDecl
  = IDecl
    { _isDisj :: Bool    -- ^ is disjunct
    , _decls :: [CName]  -- ^ a list of local names
    , _body :: PExp      -- ^ set to which local names refer to
    }
  deriving (Eq,Ord,Show,Data,Typeable)

-- | quantifier
data IQuant
  = INo    -- ^ does not exist
  | ILone  -- ^ less than one
  | IOne   -- ^ exactly one
  | ISome  -- ^ at least one (i.e., exists)
  | IAll   -- ^ for all
  deriving (Eq,Ord,Show,Data,Typeable)

type LineNo = Integer
type ColNo  = Integer


{-Ir Traverse Functions-}
-------------------------

-- | map over IR
mapIR :: (Ir -> Ir) -> IModule -> IModule -- fmap/map for IModule
mapIR f (IModule name decls') =
  unWrapIModule $ f $ IRIModule $ IModule name $ map (unWrapIElement . iMap f . IRIElement) decls'

-- | foldMap over IR
foldMapIR :: (Monoid m) => (Ir -> m) -> IModule -> m -- foldMap for IModule
foldMapIR f i@(IModule _ decls') =
  (f $ IRIModule i) `mappend` foldMap (iFoldMap f . IRIElement) decls'

-- | fold the IR
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
iMap f (IRClafer (IClafer p a grc i u pu Nothing  r c goc elems)) =
  f $ IRClafer $ IClafer p a (unWrapIGCard $ iMap f $ IRIGCard grc) i u pu Nothing                            (unWrapIReference $ iMap f $ IRIReference r) c goc $ map (unWrapIElement . iMap f . IRIElement) elems
iMap f (IRClafer (IClafer p a grc i u pu (Just s) r c goc elems)) =
  f $ IRClafer $ IClafer p a (unWrapIGCard $ iMap f $ IRIGCard grc) i u pu (Just $ unWrapPExp $ iMap f $ IRPExp s) (unWrapIReference $ iMap f $ IRIReference r) c goc $ map (unWrapIElement . iMap f . IRIElement) elems
iMap f (IRIExp (IDeclPExp q decs p)) =
  f $ IRIExp $ IDeclPExp (unWrapIQuant $ iMap f $ IRIQuant q) (map (unWrapIDecl . iMap f . IRIDecl) decs) $ unWrapPExp $ iMap f $ IRPExp p
iMap f (IRIExp (IFunExp o pexps)) =
  f $ IRIExp $ IFunExp o $ map (unWrapPExp . iMap f . IRPExp) pexps
iMap f (IRPExp (PExp (Just iType') pID p iExp)) =
  f $ IRPExp $ PExp (Just $ unWrapIType $ iMap f $ IRIType iType') pID p $ unWrapIExp $ iMap f $ IRIExp iExp
iMap f (IRPExp (PExp Nothing pID p iExp)) =
  f $ IRPExp $ PExp Nothing pID p $ unWrapIExp $ iMap f $ IRIExp iExp
iMap _ x@(IRIReference Nothing) = x
iMap f (IRIReference (Just (IReference is ref))) =
 f $ IRIReference $ Just $ IReference is $ (unWrapPExp . iMap f . IRPExp) ref
iMap f (IRIDecl (IDecl i d body')) =
  f $ IRIDecl $ IDecl i d $ unWrapPExp $ iMap f $ IRPExp body'
iMap f i = f i

iFoldMap :: (Monoid m) => (Ir -> m) -> Ir -> m
iFoldMap f i@(IRIElement (IEConstraint _ pexp)) =
  f i `mappend` (iFoldMap f $ IRPExp pexp)
iFoldMap f i@(IRIElement (IEGoal _ pexp)) =
  f i `mappend` (iFoldMap f $ IRPExp pexp)
iFoldMap f i@(IRClafer (IClafer _ _ grc _ _ _ Nothing r _ _ elems)) =
  f i `mappend` (iFoldMap f $ IRIReference r) `mappend` (iFoldMap f $ IRIGCard grc) `mappend` foldMap (iFoldMap f . IRIElement) elems
iFoldMap f i@(IRClafer (IClafer _ _ grc _ _ _ (Just s) r _ _ elems)) =
  f i `mappend` (iFoldMap f $ IRPExp s) `mappend` (iFoldMap f $ IRIReference r) `mappend` (iFoldMap f $ IRIGCard grc) `mappend` foldMap (iFoldMap f . IRIElement) elems
iFoldMap f i@(IRIExp (IDeclPExp q decs p)) =
  f i `mappend` (iFoldMap f $ IRIQuant q) `mappend` (iFoldMap f $ IRPExp p) `mappend` foldMap (iFoldMap f . IRIDecl) decs
iFoldMap f i@(IRIExp (IFunExp _ pexps)) =
  f i `mappend` foldMap (iFoldMap f . IRPExp) pexps
iFoldMap f i@(IRPExp (PExp (Just iType') _ _ iExp)) =
  f i `mappend` (iFoldMap f $ IRIType iType') `mappend` (iFoldMap f $ IRIExp iExp)
iFoldMap f i@(IRPExp (PExp Nothing _ _ iExp)) =
  f i `mappend` (iFoldMap f $ IRIExp iExp)
iFoldMap f i@(IRIReference Nothing) = f i
iFoldMap f i@(IRIReference (Just (IReference _ ref))) =
  f i `mappend` (iFoldMap f . IRPExp) ref
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
unWrapIReference :: Ir -> Maybe IReference
unWrapIReference (IRIReference x) = x
unWrapIReference x = error $ "Can't call unWarpIReference on " ++ show x
unWrapIQuant :: Ir -> IQuant
unWrapIQuant (IRIQuant x) = x
unWrapIQuant x = error $ "Can't call unWarpIQuant on " ++ show x
unWrapIDecl :: Ir -> IDecl
unWrapIDecl (IRIDecl x) = x
unWrapIDecl x = error $ "Can't call unWarpIDecl on " ++ show x
unWrapIGCard :: Ir -> Maybe IGCard
unWrapIGCard (IRIGCard x) = x
unWrapIGCard x = error $ "Can't call unWarpIGcard on " ++ show x

instance Plated IModule
instance Plated IClafer
instance Plated PExp
instance Plated IExp

makeLenses ''IType

makeLenses ''IModule

makeLenses ''IClafer

makeLenses ''IElement

makeLenses ''IReference

makeLenses ''IGCard

makeLenses ''PExp

makeLenses ''IExp

makeLenses ''IDecl

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''IType)

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''IModule)

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''IClafer)

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''IElement)

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''IReference)

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''IGCard)

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''PExp)

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''IExp)

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''IDecl)

$(deriveToJSON defaultOptions{fieldLabelModifier = tail, omitNothingFields=True} ''IQuant)

instance ToJSON Span where
  toJSON _ = Null

instance ToJSON Pos where
  toJSON _ = Null

-- | Datatype used for JSON output. See Language.Clafer.gatherObjectivesAndAttributes
data ObjectivesAndAttributes
  = ObjectivesAndAttributes
    { _qualities :: [String]
    , _attributes :: [String]
    }

$(deriveToJSON defaultOptions{fieldLabelModifier = tail} ''ObjectivesAndAttributes)
