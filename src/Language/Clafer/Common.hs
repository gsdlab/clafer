{-# LANGUAGE DeriveDataTypeable, RankNTypes, KindSignatures, FlexibleContexts #-}
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
transIdent x = case x of
  PosIdent str  -> snd str

mkIdent :: String -> PosIdent
mkIdent str = PosIdent ((0, 0), str)

mkInteger :: Read a => PosInteger -> a
mkInteger (PosInteger (_, n)) = read n

type Ident = PosIdent

getSuper :: IClafer -> String
getSuper clafer' = 
  if ([] == (supers $ super clafer')) then 
    getSuperId $ refs $ reference clafer' else
      getSuperId $ supers $ super clafer'

getSuperNoArr :: IClafer -> String
getSuperNoArr clafer
  | isOverlapping clafer = "clafer"
  | otherwise            = getSuper clafer

getSuperId :: [PExp] -> String
getSuperId = sident . Language.Clafer.Intermediate.Intclafer.exp . head

isEqClaferId :: String -> IClafer -> Bool
isEqClaferId = flip $ (==).uid

idToPExp :: Maybe PExp -> String -> Span -> String -> String -> Bool -> PExp
idToPExp par' pid' pos modids id' isTop' = PExp par' (Just $ TClafer [id']) pid' pos (IClaferId modids id' isTop')

mkLClaferId :: String -> Bool -> IExp
mkLClaferId = IClaferId ""

mkPLClaferId :: String -> Bool -> PExp
mkPLClaferId id' isTop' = pExpDefPidPos $ mkLClaferId id' isTop'

pExpDefPidPos :: IExp -> PExp
pExpDefPidPos = pExpDefPid noSpan

pExpDefPid :: Span -> IExp -> PExp
pExpDefPid = pExpDef ""

pExpDef :: String -> Span -> IExp -> PExp
pExpDef = PExp Nothing Nothing

isParent :: PExp -> Bool
isParent (PExp _ _ _ _ (IClaferId _ id' _)) = id' == parent
isParent _ = False

isClaferName :: PExp -> Bool
isClaferName (PExp _ _ _ _ (IClaferId _ id' _)) =
  id' `notElem` ([this, parent, children] ++ primitiveTypes)
isClaferName _ = False

isClaferName' :: PExp -> Bool
isClaferName' (PExp _ _ _ _ (IClaferId _ _ _)) = True
isClaferName' _ = False

getClaferName :: PExp -> String
getClaferName (PExp _ _ _ _ (IClaferId _ id' _)) = id'
getClaferName _ = ""

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
  | sFun clafer == "clafer"      = [clafer]
  | otherwise                    = if clafer `elem` superClafers
                                   then error $ "Inheritance hierarchy contains a cycle: line " ++ (show $ cinPos clafer)
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
toNodeShallow = apply (getSubclafers.elements)


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


toTriple :: forall t t1 t2. t -> (t1, t2) -> (t, t1, t2)
toTriple a (b,c) = (a, b, c)

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
iIfThenElse   = "=>else"

mkIFunExp :: String -> [IExp] -> IExp
mkIFunExp _ (x:[]) = x
mkIFunExp op' xs = foldl1 (\x y -> IFunExp op' $ map (PExp Nothing (Just $ TClafer []) "" noSpan) [x,y]) xs

toLowerS :: String -> String
toLowerS "" = ""
toLowerS (s:ss) = toLower s : ss

-- -----------------------------------------------------------------------------
-- Constants

this :: String
this = "this"

parent :: String
parent = "parent"

children :: String
children = "children"

ref :: String
ref = "ref"

specialNames :: [String]
specialNames = [this, parent, children, ref]

strType :: String
strType = "string"

intType :: String
intType = "int"

integerType :: String
integerType = "integer"

baseClafer :: String
baseClafer = "clafer"

modSep :: String
modSep = "\\"

primitiveTypes :: [String]
primitiveTypes = [strType, intType, integerType]

isPrimitive :: String -> Bool
isPrimitive = flip elem primitiveTypes

data GEnv = GEnv {
  num :: Int,
  stable :: Map.Map String [[String]], -- super clafer names of a given clafer
  sClafers ::[IClafer] -- all clafers (no going through references)
  } deriving (Eq, Show)

voidf :: Monad m => m t -> m ()
voidf f = do
  _ <- f
  return ()
  
istop :: Span -> Bool
istop (Span (Pos _ 1) _) = True
istop (Span (PosPos _ _ 1) _) = True
istop (PosSpan _ (Pos _ 1) _) = True
istop (PosSpan _ (PosPos _ _ 1) _) = True
istop _ = False