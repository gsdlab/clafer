{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, NamedFieldPuns #-}
{-
 Copyright (C) 2012-2014 Kacper Bak, Jimmy Liang, Michal Antkiewicz, Luke Michael Brown <http://gsd.uwaterloo.ca>

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

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import Language.Clafer.Front.Absclafer
import Control.Lens
import Data.Data

-- | readable unique identifier of a clafer, constraint, goal, pexpression, local declaration
type UID = String    
-- | clafer name as declared in the source model
type CName = String  
-- | Module-unique identifier used internally by the compiler
type MUID = Int 

-- | A "supertype" of IR types identifiable with MUID
data Ir 
  = IRIModule     IModule
  | IRIClafer     IClafer
  | IRIConstraint IConstraint
  | IRIGoal       IGoal
  | IRPExp        PExp
  | IRIDecl       IDecl
  | IRILocId      CName
  deriving (Eq, Show)

-- | A mapping from MUIDs to Ir elements
--   0-indexed, IModule always has index 0
type IRModuleMap = V.Vector Ir

newEmptyIRModuleMap :: IRModuleMap
newEmptyIRModuleMap = V.empty

-- | Construct the IRModuleMap from a list of elements. IModule must be first. 
newIRModuleMap :: [Ir]                        -> IRModuleMap
newIRModuleMap    irElements@((IRIModule _):_) = V.fromList irElements
newIRModuleMap    _                            = error "BUG: newIRModuleMap got a list of IR elements in which IRIModule was not the head."

getIRElement :: IRModuleMap -> MUID  -> Ir
getIRElement    irModuleMap    muid   = irModuleMap V.! muid

getLargestMUID :: IRModuleMap -> Int
getLargestMUID    irModuleMap =  (V.length irModuleMap)-1

-- | A mapping from MUID of an Ir element to a MUID of it's parent 
--   0-indexed, IModule's parent is always itself (MUID 0)
type IRParentMap = VU.Vector MUID

newEmptyIRParentMap :: IRParentMap
newEmptyIRParentMap = VU.empty

newIRParentMap :: [MUID]           -> IRParentMap
newIRParentMap    parentMUIDs@(0:_) = VU.fromList parentMUIDs
newIRParentMap    _                 = error "BUG: newIRParentMap got a list of MUIDs which does not begin with 0."

getIRParentMUID :: IRParentMap -> MUID  -> MUID
getIRParentMUID    irParentMap    muid   = irParentMap VU.! muid

-- | A mapping from MUID of an IR element to the Span of the original AST node
type MUIDSpanMap = V.Vector Span

getSpanForMUID :: MUIDSpanMap -> MUID  -> Span
getSpanForMUID    muidSpanMap    muid   = muidSpanMap V.! muid

newEmptyMUIDSpanMap :: MUIDSpanMap
newEmptyMUIDSpanMap = V.empty

newMUIDSpanMap :: [Span] -> MUIDSpanMap
newMUIDSpanMap    spans@((Span (Pos 1 1) _) :_) = V.fromList spans
newMUIDSpanMap    spans                         = error $ "BUG: newMUIDSpanMap got a list of Spans which does not begin with (Span (Pos 1 1) _).\n" ++ (show spans)

data IType 
  = TBoolean
  | TString
  | TInteger
  | TReal
  -- | the type is an intersection of the listed clafers
  --   supports having paths in the inheritance hierarchy
  --   supports multiple inheritance
  | TClafer [MUID]  
  deriving (Eq,Ord,Show,Data,Typeable)

-- | each file contains exactly one mode. A module is a list of declarations
data IModule 
  = IModule 
    { _mName  :: String     -- ^ always empty (no syntax for declaring modules)
    , _mDecls :: [IElement] -- ^ List of top-level elements
    } deriving (Eq,Ord,Show,Data,Typeable)

-- | The MUID of the IModule is always 0, since it is always the first top-level element in the IR
_imoduleMUID :: IModule -> MUID
_imoduleMUID    _        = 0

-- | Clafer has a list of fields that specify its properties. Some fields, marked as (o) are for generating optimized code
data IClafer 
  = IClafer 
    { _claferMUID :: !MUID          -- ^ module-unique identifier
    , _cinPos     :: Span           -- ^ the position of the syntax in source code
    , _isAbstract :: !Bool          -- ^ whether abstract or not (i.e., concrete)
    , _gcard      :: Maybe IGCard   -- ^ group cardinality
    , _ident      :: CName          -- ^ name declared in the model
    , _super      :: ISuper         -- ^ superclafers
    , _card       :: Maybe Interval -- ^ clafer cardinality
    , _glCard     :: Interval       -- ^ (o) global cardinality
    , _elements   :: [IElement]     -- ^ nested elements
    } deriving (Eq,Ord,Show,Data,Typeable)

_uid :: IClafer -> UID
_uid    IClafer{_ident, _claferMUID}  = concat [ "c", show _claferMUID, "_", _ident ]

data IConstraint 
  = IConstraint 
    { _constraintMUID :: !MUID -- ^ module-unique identifier
    , _isHard         :: !Bool -- ^ whether a hard constraint or an assertion
    , _cpexp          :: PExp  -- ^ the container of the actual expression
    } deriving (Eq,Ord,Show,Data,Typeable)

data IGoal 
  = IGoal 
    { _goalMUID   :: !MUID -- ^ module-unique identifier
    , _isMaximize :: !Bool -- ^ whether maximize or minimize
    , _gpexp      :: PExp  -- ^ the container of the actual expression
    } deriving (Eq,Ord,Show,Data,Typeable)

-- | Clafer's subelement is either a clafer, a constraint, or a goal (objective)
--   This is a wrapper type needed to have polymorphic lists of elements
data IElement 
  = IEClafer 
    { _iClafer :: IClafer -- ^ the actual clafer 
    }
  | IEConstraint 
    { _iConstraint :: IConstraint -- ^ the actual constraint
    }
  | IEGoal 
    { _iGoal :: IGoal -- ^ the actual goal (objective)
    } deriving (Eq,Ord,Show,Data,Typeable)

-- | A list of superclafers.  
--   ->    overlaping unique (set)
--   ->>   overlapping non-unique (bag)
--   :     non overlapping (disjoint)
data ISuper 
  = ISuper
    { _isOverlapping :: !Bool  -- ^ whether overlapping or disjoint with other clafers extending given list of superclafers
    , _supers :: [PExp]
    } deriving (Eq,Ord,Show,Data,Typeable)

-- | Group cardinality is specified as an interval. It may also be given by a keyword.
--   xor    1..1 isKeyword = True
--   1..1   1..1 isKeyword = False
data IGCard 
  = IGCard 
    { _isKeyword :: !Bool -- ^ whether given by keyword: or, xor, mux
    , _interval :: Interval
    } deriving (Eq,Ord,Show,Data,Typeable)

-- | (Min, Max) integer interval. -1 denotes *
type Interval = (Integer, Integer)

-- | This is expression container (parent). 
--   It has meta information about an actual expression 'exp'
data PExp 
  = PExp 
    { _pexpMUID :: !MUID        -- ^ module-unique identifier
    , _iType    :: Maybe IType  -- ^ the inferred type
    , _inPos    :: Span         -- ^ position in the input Clafer file
    , _exp      :: IExp         -- ^ the actual expression
    } deriving (Eq,Ord,Show,Data,Typeable)

_pid :: PExp -> String
_pid PExp { _pexpMUID } = "pexp" ++ (show _pexpMUID)

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
    { _op :: String -- ^ operator
    , _exps :: [PExp] -- ^ list of arguments containing 1, 2, or 3 elements 
    }
  -- | integer number
  | IInt 
    { _iint :: Integer }
  -- | real number
  | IDouble 
    { _idouble :: Double }
  -- | string
  | IStr 
    { _istr :: String }
  -- | a reference to a clafer name
  | IClaferId 
    { _modName  :: String -- ^ module name - empty since we have no module system
    , _sident   :: CName  -- ^ name of the clafer being referred to
    , _sMUID    :: MUID   -- ^ MUID of the clafer being referred to 
    , _isTop    :: Bool   -- ^ identifier refers to a top-level definition
    } deriving (Eq,Ord,Show,Data,Typeable)

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
        &          - set intersection
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
    { _declMUID :: !MUID    -- ^ module-unique identifier
    , _isDisj   :: Bool     -- ^ is disjoint
    , _decls    :: [(CName, MUID)]  -- ^ a list of local names, we need MUIDs to distinguish between ones with same names
    , _body     :: PExp     -- ^ set to which local names refer to
    } deriving (Eq,Ord,Show,Data,Typeable)

-- | quantifier
data IQuant
  -- | does not exist
  = INo    
  -- | less than one
  | ILone  
  -- | exactly one
  | IOne   
  -- | at least one (i.e., exists)
  | ISome  
  -- | for all
  | IAll   
  deriving (Eq,Ord,Show,Data,Typeable)

type LineNo = Integer
type ColNo  = Integer

unwrapIModule :: Ir -> IModule
unwrapIModule (IRIModule x) = x
unwrapIModule x = error $ "Can't call unwrapIModule on " ++ show x
unwrapIClafer :: Ir -> IClafer
unwrapIClafer (IRIClafer x) = x
unwrapIClafer x = error $ "Can't call unwrapIClafer on " ++ show x
unwrapIConstraint :: Ir -> IConstraint
unwrapIConstraint (IRIConstraint x) = x
unwrapIConstraint x = error $ "Can't call unwrapIClafer on " ++ show x
unwrapIGoal :: Ir -> IGoal
unwrapIGoal (IRIGoal x) = x
unwrapIGoal x = error $ "Can't call unwrapIClafer on " ++ show x
unwrapPExp :: Ir -> PExp
unwrapPExp (IRPExp x) = x
unwrapPExp x = error $ "Can't call unwrapPExp on " ++ show x
unwrapIDecl :: Ir -> IDecl
unwrapIDecl (IRIDecl x) = x
unwrapIDecl x = error $ "Can't call unwrapIDecl on " ++ show x
unwrapILocId :: Ir -> CName
unwrapILocId (IRILocId x) = x
unwrapILocId x = error $ "Can't call unwrapILocId on " ++ show x

instance Plated IClafer
instance Plated PExp
instance Plated IExp

makeLenses ''IModule

makeLenses ''IClafer

makeLenses ''IConstraint

makeLenses ''IGoal

makeLenses ''IElement

makeLenses ''ISuper

makeLenses ''IGCard

makeLenses ''PExp

makeLenses ''IExp

makeLenses ''IDecl