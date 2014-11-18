{-# LANGUAGE DeriveDataTypeable, RankNTypes, KindSignatures, FlexibleContexts #-}
{-
 Copyright (C) 2012-2014 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Common where

import Data.Tree
import Data.Maybe
import Data.Char
import Data.List
import qualified Data.Map as Map

import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer

-- -----------------------------------------------------------------------------
-- basic functions shared by desugarer, analyzer and code generator
type Result = String

transIdent :: PosIdent -> Result
transIdent (PosIdent (_, str)) = str

mkIdent :: String -> PosIdent
mkIdent str = PosIdent ((0, 0), str)

mkInteger :: Read a => PosInteger -> a
mkInteger (PosInteger (_, n)) = read n

getSuper :: IClafer -> String
getSuper = getSuperId._supers._super

getSuperNoArr :: IClafer -> String

getSuperNoArr clafer
  | _isOverlapping $ _super clafer = baseClafer
  | otherwise                    = getSuper clafer

getSuperId :: [PExp] -> String
getSuperId = _sident . _exp . head

isEqClaferId :: String -> IClafer -> Bool
isEqClaferId = flip $ (==)._uid

idToPExp :: MUID -> Span -> String -> UID -> MUID -> Bool  -> PExp
idToPExp    muid    pos     modids    id'    muid'   isTop' = PExp muid (Just $ TClafer [muid']) pos (IClaferId modids id' muid' isTop')

mkLClaferId :: UID -> MUID -> Bool -> IExp
mkLClaferId = IClaferId ""

mkPLClaferId :: UID -> MUID -> Bool  -> PExp
mkPLClaferId    id'    muid'   isTop' = pExpDefPidPos pseudoMUID $ mkLClaferId id' muid' isTop'

pExpDefPidPos :: MUID -> IExp -> PExp
pExpDefPidPos muid' = pExpDefPid muid' noSpan

pExpDefPid :: MUID -> Span -> IExp -> PExp
pExpDefPid muid' pos' iExp = PExp muid' Nothing pos' iExp

isParent :: PExp -> Bool
isParent (PExp _ _ _ (IClaferId _ id' _ _)) = id' == parentIdent
isParent _ = False

isClaferName :: PExp -> Bool
isClaferName (PExp _ _ _ (IClaferId _ id' _ _)) =
  id' `notElem` (specialNames ++ primitiveTypes)
isClaferName _ = False

-- -----------------------------------------------------------------------------
-- conversions
elemToClafer :: IElement -> Maybe IClafer
elemToClafer x = case x of
  IEClafer clafer  -> Just clafer
  _  -> Nothing

toClafers :: [IElement] -> [IClafer]
toClafers = mapMaybe elemToClafer

-- -----------------------------------------------------------------------------
-- finds hierarchy and transforms each element
mapHierarchy :: (IClafer -> b)
                -> (IClafer -> String)
                -> [IClafer]
                -> IClafer
                -> [b]
mapHierarchy f sf = (map f.).(findHierarchy sf)


-- returns inheritance hierarchy of a clafer

findHierarchy :: (IClafer -> String)
                            -> [IClafer]
                            -> IClafer
                            -> [IClafer]
findHierarchy sFun clafers clafer
  | sFun clafer == baseClafer    = [clafer]
  | otherwise                    = if clafer `elem` superClafers
                                   then error $ "Inheritance hierarchy contains a cycle: line " ++ (show $ _cinPos clafer)
                                   else clafer : superClafers
  where
  superClafers = unfoldr (\c -> find (isEqClaferId $ sFun c) clafers >>=
                          Just . (apply id)) clafer

-- -----------------------------------------------------------------------------
-- generic functions

apply :: forall t t1. (t -> t1) -> t -> (t, t1)
apply f x = (x, f x)

-- lists all nodes of a tree (BFS). Take a function to extract subforest
bfs :: forall b b1. (b1 -> (b, [b1])) -> [b1] -> [b]
bfs toNode seed = map rootLabel $ concat $ takeWhile (not.null) $
  iterate (concatMap subForest) $ unfoldForest toNode seed


toNodeShallow :: IClafer -> (IClafer, [IClafer])
toNodeShallow = apply (getSubclafers._elements)


getSubclafers :: [IElement] -> [IClafer]
getSubclafers = mapMaybe elemToClafer


bfsClafers :: [IClafer] -> [IClafer]
bfsClafers clafers = bfs toNodeShallow clafers

lurry :: forall t t1. ([t1] -> t) -> t1 -> t1 -> t
lurry f x y = f [x,y]

fst3 :: forall t t1 t2. (t, t1, t2) -> t
fst3 (a, _, _) = a
snd3 :: forall t t1 t2. (t, t1, t2) -> t1
snd3 (_, b, _) = b
trd3 :: forall t t1 t2. (t, t1, t2) -> t2
trd3 (_, _, c) = c

toMTriple :: forall t t1 t2. t -> (t1, t2) -> Maybe (t, t1, t2)
toMTriple a (b,c) = Just (a, b, c)

-- unary operators
iNot :: String
iNot          = "!"

iCSet :: String
iCSet         = "#"

iMin :: String
iMin          = "-"

iGMax :: String
iGMax         = "max"

iGMin :: String
iGMin         = "min"

iSumSet :: String
iSumSet       = "sum"

unOps :: [String]
unOps = [iNot, iCSet, iMin, iGMax, iGMin, iSumSet]

-- binary operators
iIff :: String
iIff          = "<=>"

iImpl :: String
iImpl         = "=>"

iOr :: String
iOr           = "||"

iXor :: String
iXor          = "xor"

iAnd :: String
iAnd          = "&&"

logBinOps :: [String]
logBinOps = [iIff, iImpl, iOr, iXor, iAnd]

iLt :: String
iLt           = "<"

iGt :: String
iGt           = ">"

iEq :: String
iEq           = "="

iLte :: String
iLte          = "<="

iGte :: String
iGte          = ">="

iNeq :: String
iNeq          = "!="

iIn :: String
iIn           = "in"

iNin :: String
iNin          = "not in"

relGenBinOps :: [String]
relGenBinOps = [iLt, iGt, iEq, iLte, iGte, iNeq]

relSetBinOps :: [String]
relSetBinOps = [iIn, iNin]

relBinOps :: [String]
relBinOps = relGenBinOps ++ relSetBinOps

iPlus :: String
iPlus         = "+"

iSub :: String
iSub          = "-"

iMul :: String
iMul          = "*"

iDiv :: String
iDiv          = "/"

iSumSet' :: String
iSumSet'      = "sum'"

arithBinOps :: [String]
arithBinOps = [iPlus, iSub, iMul, iDiv, iSumSet']

iUnion :: String
iUnion        = "++"

iDifference :: String
iDifference   = "--"

iIntersection :: String
iIntersection = "&"

iDomain :: String
iDomain       = "<:"

iRange :: String
iRange        = ":>"

iJoin :: String
iJoin         = "."

setBinOps :: [String]
setBinOps = [iUnion, iDifference, iIntersection, iDomain, iRange, iJoin]

binOps :: [String]
binOps = logBinOps ++ relBinOps ++ arithBinOps ++ setBinOps

-- ternary operators
iIfThenElse :: String
iIfThenElse   = "ifthenelse"

mkIFunExp :: MUID -> String -> [IExp] -> IExp
mkIFunExp    _       _         (x:[]) = x
mkIFunExp    muid    op'       xs = foldl1' (\x y -> IFunExp op' $ map (PExp muid (Just $ TClafer []) noSpan) [x,y]) xs

toLowerS :: String -> String
toLowerS "" = ""
toLowerS (s:ss) = toLower s : ss

-- -----------------------------------------------------------------------------
-- Constants

rootIdent :: String
rootIdent = "root"

rootMUID :: MUID
rootMUID = -1

thisIdent :: String
thisIdent = "this"

thisMUID :: MUID
thisMUID = -7

parentIdent :: String
parentIdent = "parent"

parentMUID :: MUID
parentMUID = -8

refIdent :: String
refIdent = "ref"

refMUID :: MUID
refMUID = -9

childrenIdent :: String
childrenIdent = "children"

childrenMUID :: MUID
childrenMUID = -10

specialNames :: [String]
specialNames = [thisIdent, parentIdent, refIdent, rootIdent, childrenIdent]

isSpecial :: String -> Bool
isSpecial = flip elem specialNames

getSpecialMUID :: String -> MUID
getSpecialMUID    i
  | i == rootIdent = rootMUID
  | i == thisIdent = thisMUID
  | i == parentIdent = parentMUID
  | i == refIdent = refMUID
  | i == childrenIdent = childrenMUID
  | otherwise = error "getSpecialMUID: requested MUID for a non-special identifier"

baseClafer :: String
baseClafer = "clafer"

baseClaferMUID :: MUID
baseClaferMUID = (-2)

integerType :: String
integerType = "integer"

integerMUID :: MUID
integerMUID = (-3)

stringType :: String
stringType = "string"

stringMUID :: MUID
stringMUID = (-4)

intType :: String
intType = "int"  -- synonym only

realType :: String
realType = "real"

realMUID :: MUID
realMUID = (-5)

booleanType :: String
booleanType = "boolean"

booleanMUID :: MUID
booleanMUID = (-6)

unresolvedMUID :: MUID
unresolvedMUID = (-99)  -- MUID used in desugared IClaferIds to indicate that they are unresolved yet

pseudoMUID :: MUID  -- pseudo MUID used for derived elements when cannot generate a real MUID
pseudoMUID = (-100)

modSep :: String
modSep = "\\"

primitiveTypes :: [String]
primitiveTypes = [stringType, intType, integerType, realType]

isPrimitive :: String -> Bool
isPrimitive = flip elem primitiveTypes

getPrimitiveMUID :: String -> MUID
getPrimitiveMUID    i
  | i == stringType = stringMUID
  | i == intType = integerMUID
  | i == integerType = integerMUID
  | i == realType = realMUID
  | otherwise = error "getPrimitiveMUID: requested MUID for a non-primitive type identifier"

-- | reserved keywords which cannot be used as clafer identifiers
keywordIdents :: [String]
keywordIdents = 
  specialNames ++ 
  primitiveTypes ++ 
  [ iGMax, iGMin, iSumSet ] ++                      -- unary operators
  [ iXor, iIn ] ++                                  -- binary operators
  [ "if", "then", "else" ] ++                       -- ternary operators
  [ "no", "not", "some", "one", "all", "disj" ] ++  -- quantifiers
  [ "opt", "mux", "or", "lone" ] ++                 -- group cardinalities
  [ "abstract", "enum" ]                            -- keywords

data GEnv = GEnv 
  { stable :: Map.Map UID [[UID]]  -- super clafer names of a given clafer
  , sClafers ::[IClafer]           -- all clafers (no going through references)
  } deriving (Eq, Show)