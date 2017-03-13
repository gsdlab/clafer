{-# LANGUAGE NamedFieldPuns #-}
{-
 Copyright (C) 2015-2017 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.TypeSystem where

import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer hiding (uid)

import Control.Applicative
import Control.Lens ((&), (<&>), (%~))
import Control.Monad (mplus, liftM)
import Data.List (nub)
import Data.Maybe
import Prelude hiding (exp)

{- | Example Clafer model used in the various test cases.

abstract Person
    DOB -> integer

abstract Student : Person
    StudentID -> string

abstract Employee : Person
    EmplID -> integer

Alice : Student
    [ this.DOB.dref = 1990 ]
    [ this.StudentID.dref = "123Alice" ]

Bob : Employee
    [ this.EmplID.dref = 345 ]

AliceAndBob -> Person
[ root.AliceAndBob.dref = Alice, Bob ]

AliceAndBob2 -> Alice ++ Bob
-}

{- $setup
>>> :m + Control.Monad.List

TClafer
>>> let tClaferPerson = TClafer [ "Person" ]
>>> let tClaferDOB = TClafer [ "DOB" ]
>>> let tClaferStudent = TClafer [ "Student", "Person" ]
>>> let tClaferStudentID = TClafer [ "StudentID" ]
>>> let tClaferEmployee = TClafer [ "Employee", "Person" ]
>>> let tClaferEmplID = TClafer [ "EmplID" ]
>>> let tClaferAlice = TClafer [ "Alice", "Student", "Person" ]
>>> let tClaferBob = TClafer [ "Bob", "Employee", "Person" ]
>>> let tClaferAliceAndBob = TClafer [ "AliceAndBob" ]
>>> let tClaferAliceAndBob2 = TClafer [ "AliceAndBob2" ]

TUnion
>>> let tUnionAliceBob = TUnion [ tClaferAlice, tClaferBob ]

TMap
>>> let tMapDOB = TMap tClaferPerson tClaferDOB
>>> let tDrefMapDOB = TMap tClaferDOB TInteger
>>> let tMapStudentID = TMap tClaferStudent tClaferStudentID
>>> let tDrefMapStudentID = TMap tClaferStudentID TString
>>> let tMapEmplID = TMap tClaferEmplID tClaferEmplID
>>> let tDrefMapEmplID = TMap tClaferEmplID TInteger
>>> let tDrefMapAliceAndBob = TMap tClaferAliceAndBob tClaferPerson
>>> let tDrefMapAliceAndBob2 = TMap tClaferAliceAndBob tUnionAliceBob

constants
>>> let t1990 = TInteger
>>> let t123Alice = TString
>>> let t345 = TInteger
-}

-- | Sing
rootTClafer :: IType
rootTClafer = TClafer ["root"]

-- | Obj
claferTClafer :: IType
claferTClafer = TClafer ["clafer"]

numeric :: IType     -> Bool
numeric TInteger     = True
numeric TReal        = True
numeric TDouble      = True
numeric (TMap _ ta') = numeric ta'
numeric (TUnion un') = any numeric un'
numeric _            = False

isTInteger :: IType    -> Bool
isTInteger TInteger     = True
isTInteger (TMap _ ta') = isTInteger ta'
isTInteger (TUnion un') = any isTInteger un'
isTInteger _            = False

isTString :: IType    -> Bool
isTString TString      = True
isTString (TMap _ ta') = isTString ta'
isTString (TUnion un') = any isTString un'
isTString _            = False

isTBoolean :: IType    -> Bool
isTBoolean TBoolean      = True
isTBoolean (TMap _ ta') = isTBoolean ta'
isTBoolean (TUnion un') = any isTBoolean un'
isTBoolean _            = False

-- | Get TClafer for a given Clafer
-- can only be called after inheritance resolver
getTClafer :: IClafer -> IType
getTClafer    iClafer' = case _uid iClafer' of
  "root"   -> rootTClafer
  "clafer" -> claferTClafer
  _        -> case _super iClafer' of
    Nothing     -> TClafer [ _uid iClafer']
    Just super' -> fromJust (_iType super') & hi %~ (:) (_uid iClafer')

-- | Get TClafer for a given Clafer by its UID
-- can only be called after inheritance resolver
getTClaferByUID :: UIDIClaferMap -> UID -> Maybe IType
getTClaferByUID    uidIClaferMap'   uid' = case uid' of
  "root"   -> Just rootTClafer
  "clafer" -> Just claferTClafer
  _        -> findIClafer uidIClaferMap' uid' <&> getTClafer

-- | Get TClafer for a given Clafer by its UID
-- can only be called after inheritance resolver
getTClaferFromIExp :: UIDIClaferMap -> IExp -> Maybe IType
getTClaferFromIExp    uidIClaferMap'   (IClaferId _ uid' _ _) = getTClaferByUID uidIClaferMap' uid'
getTClaferFromIExp    _                (IInt _)               = Just TInteger
getTClaferFromIExp    _                (IReal _)              = Just TReal
getTClaferFromIExp    _                (IDouble _)            = Just TDouble
getTClaferFromIExp    _                (IStr _)               = Just TString
getTClaferFromIExp    _                _                      = Nothing

-- | Get TMap for a given reference Clafer. Nothing for non-reference clafers.
-- can only be called after inheritance resolver
getDrefTMap :: IClafer -> Maybe IType
getDrefTMap    iClafer' = case _uid iClafer' of
  "root"   -> Nothing
  "clafer" -> Nothing
  _        -> TMap <$> (Just $ getTClafer iClafer') <*> (iClafer' & _reference <&> _ref >>= _iType)

-- | Get TMap for a given Clafer by its UID. Nothing for non-reference clafers.
-- can only be called after inheritance resolver
getDrefTMapByUID :: UIDIClaferMap -> UID -> Maybe IType
getDrefTMapByUID    uidIClaferMap'   uid' = case uid' of
  "root"   -> Nothing
  "clafer" -> Nothing
  _        -> findIClafer uidIClaferMap' uid' >>= getDrefTMap


hierarchy :: (Monad m) => UIDIClaferMap -> UID -> m [IClafer]
hierarchy uidIClaferMap' uid' = case findIClafer uidIClaferMap' uid' of
      Nothing -> fail $ "TypeSystem.hierarchy: clafer " ++ uid' ++ "not found!"
      Just clafer -> return $ findHierarchy getSuper uidIClaferMap' clafer

hierarchyMap :: (Monad m) => UIDIClaferMap -> (IClafer -> a) -> UID -> m [a]
hierarchyMap uidIClaferMap' f c = case findIClafer uidIClaferMap' c of
      Nothing -> fail $ "TypeSystem.hierarchyMap: clafer " ++ c ++ "not found!"
      Just clafer -> return $ mapHierarchy f getSuper uidIClaferMap' clafer


{- ---------------------------------------
 - Sums, Intersections, and Compositions -
 --------------------------------------- -}

unionType :: IType -> [String]
unionType TString  = [stringType]
unionType TReal    = [realType]
unionType TDouble  = [doubleType]
unionType TInteger = [integerType]
unionType TBoolean = [booleanType]
unionType (TClafer u) = u
unionType (TUnion types) = concatMap unionType types
unionType (TMap _ ta') = unionType ta'

fromUnionType :: [String] -> Maybe IType
fromUnionType u =
    case nub u of
        ["string"]  -> Just TString
        ["integer"] -> Just TInteger
        ["int"]     -> Just TInteger
        ["double"]  -> Just TDouble
        ["real"]    -> Just TReal
        ["root"]    -> Just rootTClafer
        ["clafer"]  -> Just claferTClafer
        []          -> Nothing
        u'          -> Just $ TClafer u'

{- | Union the two given types
>>> TString +++ TString
TString

Unions with only one type should be collapsed.
>>> TUnion [TString] +++ TString
TString

>>> TString +++ TInteger
TUnion {_un = [TString,TInteger]}

>>> TString +++ TUnion [TInteger]
TUnion {_un = [TString,TInteger]}

>>> TUnion [TString] +++ TInteger
TUnion {_un = [TString,TInteger]}

>>> TUnion [TString] +++ TUnion[TInteger]
TUnion {_un = [TString,TInteger]}

>>> TUnion [TString] +++ TUnion[TInteger] +++ TInteger +++ TString
TUnion {_un = [TString,TInteger]}

Should return TUnion {_un = [TClafer {_hi = ["Alice","Student","Person"]},TClafer {_hi = ["Bob","Employee","Person"]}]}
>>> tClaferAlice +++ tClaferBob
TClafer {_hi = ["Alice","Student","Person","Bob","Employee"]}

>>> tClaferAlice +++ tClaferAlice
TClafer {_hi = ["Alice","Student","Person"]}

>>> (TClafer {_hi = ["A", "X"]} +++ TClafer {_hi = ["B", "X"]}) +++ TClafer {_hi = ["C", "X"]}
TClafer {_hi = ["A","X","B","C"]}

>>> TClafer {_hi = ["A", "X"]} +++ (TClafer {_hi = ["B", "X"]} +++ TClafer {_hi = ["C", "X"]})
TClafer {_hi = ["A","X","B","C"]}
-}
(+++) :: IType -> IType -> IType
TBoolean        +++ TBoolean        = TBoolean
TString         +++ TString         = TString
TReal           +++ TReal           = TReal
TDouble         +++ TDouble         = TDouble
TInteger        +++ TInteger        = TInteger
t1@(TClafer u1) +++ t2@(TClafer u2) = if t1 == t2
                                      then t1
                                      else TClafer $ nub $ u1 ++ u2  -- should be TUnion [t1,t2]
(TMap so1 ta1)  +++ (TMap so2 ta2)  = TMap (so1 +++ so2) (ta1 +++ ta2)
(TUnion un1)    +++ (TUnion un2)    = collapseUnion (TUnion $ nub $ un1 ++ un2)
(TUnion un1)    +++ t2              = collapseUnion (TUnion $ nub $ un1 ++ [t2])
t1              +++ (TUnion un2)    = collapseUnion (TUnion $ nub $ t1:un2)
t1              +++ t2              = if t1 == t2
                                      then t1
                                      else TUnion [t1, t2]

collapseUnion :: IType    -> IType
collapseUnion (TUnion [t]) = t
collapseUnion t            = t

-- original version
-- (+++) :: IType -> IType -> IType
-- t1 +++ t2 = fromJust $ fromUnionType $ unionType t1 ++ unionType t2

{- | Intersection of two types.
>>> runListT $ intersection undefined TString TString
[Just TString]

>>> runListT $ intersection undefined TInteger TString
[Nothing]

>>> runListT $ intersection undefined TInteger TReal
[Just TReal]

>>> runListT $ intersection undefined tDrefMapDOB TInteger
[Just TInteger]

Cannot assign a TReal to a map to TInteger
>>> runListT $ intersection undefined tDrefMapDOB TReal
[Nothing]

Cannot assign a TReal to a map to TInteger
>>> runListT $ intersection undefined TReal tDrefMapDOB
[Nothing]

runListT $ intersection undefined TClafer {_hi = ["A","X","B","C"]} TClafer {_hi = ["X"]}
[ Just TClafer {_hi = ["X"]]
-}

intersection :: Monad m => UIDIClaferMap -> IType -> IType -> m (Maybe IType)
intersection _              TBoolean        TBoolean      = return $ Just TBoolean
intersection _              TString         TString       = return $ Just TString
intersection _              TReal           TReal         = return $ Just TReal
intersection _              TReal           TDouble       = return $ Just TReal
intersection _              TDouble         TReal         = return $ Just TReal
intersection _              TReal           TInteger      = return $ Just TReal
intersection _              TInteger        TReal         = return $ Just TReal
intersection _              TDouble         TDouble       = return $ Just TDouble
intersection _              TDouble         TInteger      = return $ Just TDouble
intersection _              TInteger        TDouble       = return $ Just TDouble
intersection _              TInteger        TInteger      = return $ Just TInteger
intersection _              t               (TClafer ["clafer"]) = return $ Just t
intersection _              (TClafer ["clafer"]) t               = return $ Just t
intersection uidIClaferMap' (TUnion t1s)    t2@(TClafer _) = do
  t1s' <- mapM (intersection uidIClaferMap' t2) t1s
  return $ case catMaybes t1s' of
    [] -> Nothing
    [t] -> Just t
    t1s'' -> Just $ TUnion t1s''
intersection uidIClaferMap' t1@(TClafer _)  (TUnion t2s) = do
  t2s' <- mapM (intersection uidIClaferMap' t1) t2s
  return $ case catMaybes t2s' of
    [] -> Nothing
    [t] -> Just t
    t2s'' -> Just $ TUnion t2s''
intersection uidIClaferMap' t@(TClafer ut1) (TClafer ut2) = if ut1 == ut2
  then return $ Just t
  else do
    h1 <- mapM (hierarchyMap uidIClaferMap' _uid) ut1
    h2 <- mapM (hierarchyMap uidIClaferMap' _uid) ut2
    return $ fromUnionType $ catMaybes [contains (head u1) u2 `mplus` contains (head u2) u1 | u1 <- h1, u2 <- h2 ]
  where
  contains i is = if i `elem` is then Just i else Nothing
intersection uidIClaferMap' (TMap _ ta1) (TMap _ ta2) = intersection uidIClaferMap' ta1 ta2
intersection uidIClaferMap' (TMap _ ta1) ot2          = do
  coercedType <- intersection uidIClaferMap' ta1 ot2
  -- that means ot2 was coerced to ta1, so it's safe
  return $ if Just ta1 == coercedType then coercedType else Nothing
intersection uidIClaferMap' ot1          (TMap _ ta2) = do
  coercedType <- intersection uidIClaferMap' ot1 ta2
  -- that means ot2 was coerced to ta1, so it's safe
  return $ if Just ta2 == coercedType then coercedType else Nothing
intersection _              _            _            = do
  -- traceM $ "(DEBUG) TypeSystem.intersection: cannot intersect incompatible types: '"
  --      ++ show t1
  --      ++ "'' and '"
  --      ++ show t2
  --      ++ "'"
  return Nothing

-- old version
-- intersection :: Monad m => UIDIClaferMap -> IType -> IType -> m (Maybe IType)
-- intersection uidIClaferMap' t1 t2 = do
--   h1 <- (mapM (hierarchyMap uidIClaferMap' _uid) $ unionType t1)
--   h2 <- (mapM (hierarchyMap uidIClaferMap' _uid) $ unionType t2)
--   return $ fromUnionType $ catMaybes [contains (head u1) u2 `mplus` contains (head u2) u1 | u1 <- h1, u2 <- h2 ]
--   where
--   contains i is = if i `elem` is then Just i else Nothing

-- | This function is similar to 'intersection', but takes into account more ancestors to be able to combine
-- clafers of different types, but with a common ancestor:
-- Inputs:
-- t1 is of type B
-- t2 is of type C
-- B : A
-- C : A
-- Outputs:
-- the resulting type is: A, and the type combination is valid
getIfThenElseType :: Monad m => UIDIClaferMap -> IType -> IType -> m (Maybe IType)
getIfThenElseType _              TBoolean        TBoolean      = return $ Just TBoolean
getIfThenElseType _              TString         TString       = return $ Just TString
getIfThenElseType _              TReal           TReal         = return $ Just TReal
getIfThenElseType _              TReal           TDouble       = return $ Just TReal
getIfThenElseType _              TDouble         TReal         = return $ Just TReal
getIfThenElseType _              TReal           TInteger      = return $ Just TReal
getIfThenElseType _              TInteger        TReal         = return $ Just TReal
getIfThenElseType _              TDouble         TDouble       = return $ Just TDouble
getIfThenElseType _              TDouble         TInteger      = return $ Just TDouble
getIfThenElseType _              TInteger        TDouble       = return $ Just TDouble
getIfThenElseType _              TInteger        TInteger      = return $ Just TInteger
getIfThenElseType uidIClaferMap' (TUnion t1s)    t2@(TClafer _) = undefined {- o
  t1s' <- mapM (getIfThenElseType uidIClaferMap' t2) t1s
  return $ case catMaybes t1s' of
    [] -> Nothing
    [t] -> Just t
    t1s'' -> Just $ TUnion t1s''  -}
getIfThenElseType uidIClaferMap' t1@(TClafer _)  (TUnion t2s) = undefined {- do
  t2s' <- mapM (getIfThenElseType uidIClaferMap' t1) t2s
  return $ case catMaybes t2s' of
    [] -> Nothing
    [t] -> Just t
    t2s'' -> Just $ TUnion t2s''  -}
getIfThenElseType uidIClaferMap' t@(TClafer ut1) (TClafer ut2) = if ut1 == ut2
  then return $ Just t
  else do
    h1 <- mapM (hierarchyMap uidIClaferMap' _uid) ut1
    h2 <- mapM (hierarchyMap uidIClaferMap' _uid) ut2
    let ut = catMaybes [commonHierarchy u1 u2 | u1 <- h1, u2 <- h2]
    return $ fromUnionType ut
    where
    commonHierarchy :: [UID] -> [UID] -> Maybe UID
    commonHierarchy h1 h2 = commonHierarchy' (reverse h1) (reverse h2) Nothing
    commonHierarchy' (x:xs) (y:ys) accumulator =
      if x == y
      then
        if null xs || null ys
        then Just x
        else commonHierarchy' xs ys $ Just x
      else accumulator
    commonHierarchy' _ _ _ = error "ResolverType.commonHierarchy' expects two non empty lists but was given at least one empty list!" -- Should never happen
getIfThenElseType _ _ _ = return Nothing


{- | Compute the type of sequential composition of two types
>>> runListT $ composition undefined TString TString
[Nothing]

>>> runListT $ composition undefined TInteger TString
[Nothing]

>>> runListT $ composition undefined TInteger TReal
[Nothing]

>>> runListT $ composition undefined tDrefMapDOB TInteger
[Just (TMap {_so = TClafer {_hi = ["DOB"]}, _ta = TInteger})]

Cannot assign a TReal to a map to TInteger, should return [Nothing]
>>> runListT $ composition undefined tDrefMapDOB TReal
[Just (TMap {_so = TClafer {_hi = ["DOB"]}, _ta = TReal})]

Cannot assign a TInteger to a map to TInteger
>>> runListT $ composition undefined TInteger tDrefMapDOB
[Nothing]

Cannot assign a TReal to a map to TInteger
>>> runListT $ composition undefined TReal tDrefMapDOB
[Nothing]

>>> runListT $ composition undefined tDrefMapDOB (TMap TReal TString)
[Just (TMap {_so = TClafer {_hi = ["DOB"]}, _ta = TString})]

The following should return [Nothing]
>>> runListT $ composition undefined (TMap TString TReal) (TMap TInteger TString)
[Just (TMap {_so = TString, _ta = TString})]
-}
composition :: Monad m => UIDIClaferMap -> IType -> IType -> m (Maybe IType)
composition uidIClaferMap' (TMap so1 ta1) (TMap so2 ta2) = do
    -- check whether we can compose?
    _ <- intersection uidIClaferMap' ta1 so2
    return $ Just $ TMap so1 ta2
composition uidIClaferMap' ot1          (TMap so2 ta2) = do
    ot1' <- intersection uidIClaferMap' ot1 so2
    return $ TMap <$> ot1' <*> Just ta2
composition uidIClaferMap' (TMap so1 ta1) ot2          = do
    ot2' <- intersection uidIClaferMap' ta1 ot2
    return $ TMap so1 <$> ot2'
composition _              _            _            = do
  -- traceM $ "(DEBUG) ResolverType.composition: cannot compose incompatible types: '"
  --      ++ show t1
  --      ++ "'' and '"
  --      ++ show t2
  --      ++ "'"
  return Nothing

addHierarchy :: UIDIClaferMap -> IType           -> IType
addHierarchy    uidIClaferMap'   (TClafer [uid']) = TClafer $ mapHierarchy _uid getSuper uidIClaferMap' $ fromJust $ findIClafer uidIClaferMap' uid'
addHierarchy    uidIClaferMap'   (TMap so' ta')   = TMap (addHierarchy uidIClaferMap' so') (addHierarchy uidIClaferMap' ta')
addHierarchy    uidIClaferMap'   (TUnion un')     = TUnion $ map (addHierarchy uidIClaferMap') un'
addHierarchy    _                x                = x

closure :: Monad m => UIDIClaferMap -> [String] -> m [String]
closure uidIClaferMap' ut = concat `liftM` mapM (hierarchyMap uidIClaferMap' _uid) ut

getTMaps :: UIDIClaferMap -> IType        -> [IType]
getTMaps    uidIClaferMap'   (TClafer hi') = catMaybes $ map (getDrefTMapByUID uidIClaferMap') hi'
getTMaps    uidIClaferMap'   (TMap _ ta')  = getTMaps uidIClaferMap' ta'
getTMaps    uidIClaferMap'   (TUnion un')  = concatMap (getTMaps uidIClaferMap') un'
getTMaps    _                _             = []

getTClafers :: UIDIClaferMap -> IType          -> [IType]
getTClafers    uidIClaferMap'   (TClafer hi')   = catMaybes $ map (getTClaferByUID uidIClaferMap') hi'
getTClafers    uidIClaferMap'   (TMap _ ta')    = getTClafers uidIClaferMap' ta'
getTClafers    uidIClaferMap'   (TUnion un')    = concatMap (getTClafers uidIClaferMap') un'
getTClafers    _                _               = []


{- Coersions
>>> coerce tDrefMapDOB tDrefMapDOB
TInteger
>>> coerce tDrefMapDOB TInteger
TInteger
>>> coerce tDrefMapDOB tDrefMapDOB
TInteger
-}

coerce :: IType -> IType -> IType
-- basic coersions
coerce TReal TReal       = TReal
coerce TReal TInteger    = TReal
coerce TInteger TReal    = TReal
coerce TReal TDouble     = TReal
coerce TDouble TReal     = TReal
coerce TDouble TDouble   = TDouble
coerce TDouble TInteger  = TDouble
coerce TInteger TDouble  = TDouble
coerce TInteger TInteger = TInteger
-- reduce complex types to simple ones
coerce (TMap _ t1) (TMap _ t2) = coerce t1 t2
coerce (TMap _ t1) t2          = coerce t1 t2
coerce t1          (TMap _ t2) = coerce t1 t2
coerce x y = error $ "TypeSystem.coerce: Cannot coerce not numeric: " ++ show x ++ " and " ++ show y


{- | Return the type if it's possible to coerce the right type

coerceRight TString TInteger
Nothing

>>> coerceRight TInteger TInteger
Just TInteger

>>> coerceRight TDouble TInteger
Just TDouble

>>> coerceRight TReal TDouble
Just TReal

>>> coerceRight TInteger TDouble
Nothing

>>> coerceRight TDouble TReal
Nothing
-}
coerceRight :: IType -> IType -> Maybe IType
coerceRight    lt       rt     = let
    coercedRType = coerce lt rt
  in
    if lt == coercedRType then Just lt else Nothing

{- Note about intersections and unions

Refinement Intersections
========================

http://cstheory.stackexchange.com/questions/20536/what-are-the-practical-issues-with-intersection-and-union-types
"the intersection/union of two types can be formed only if they refine the same archetype"

In Clafer, that means that for
abstract Person
abstract Student : Person
Alice : Student   -- AT = TClafer [ Alice, Student, Person ]
Bob : Person      -- BT = TClafer [ Bob, Person ]

then

AT +++ BT = TClafer [ Person ]
AT *** BT = TClafer [ Person ]


Unrestricted Intersections
==========================

http://www.cs.cmu.edu/~joshuad/papers/intcomp/Dunfield12_elaboration.pdf

Subtyping Union Types
http://www.pps.univ-paris-diderot.fr/~vouillon/publi/subtyping-csl.pdf
-}
