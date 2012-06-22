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
{-# LANGUAGE DeriveDataTypeable #-}
module Common where

import Data.Tree
import Data.Maybe
import Data.Char
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import System.Console.CmdArgs
import Control.Monad.State

import Front.Absclafer
import Intermediate.Intclafer

-- -----------------------------------------------------------------------------
-- basic functions shared by desugarer, analyzer and code generator
type Result = String

transIdent :: PosIdent -> Result
transIdent x = case x of
  PosIdent str  -> snd str

mkIdent str = PosIdent ((0, 0), str)

mkInteger (PosInteger (_, n)) = read n

type Ident = PosIdent

getSuper = getSuperId.supers.super

getSuperNoArr clafer
  | isOverlapping $ super clafer = "clafer"
  | otherwise                    = getSuper clafer

getSuperId = sident . Intermediate.Intclafer.exp . head

isEqClaferId = flip $ (==).uid

idToPExp pid pos modids id isTop = PExp (Just TClafer) pid pos (IClaferId modids id isTop)

mkLClaferId = IClaferId ""

mkPLClaferId id isTop = pExpDefPidPos $ mkLClaferId id isTop

pExpDefPidPos = pExpDefPid noPos

pExpDefPid = pExpDef ""

pExpDef = PExp Nothing

isParent (PExp _ _ _ (IClaferId _ id _)) = id == parent
isParent _ = False

isClaferName (PExp _ _ _ (IClaferId _ id _)) =
  id `notElem` ([this, parent, children] ++ primitiveTypes)

isClaferName' (PExp _ _ _ (IClaferId _ id _)) = True
isClaferName' _ = False

getClaferName (PExp _ _ _ (IClaferId _ id _)) = id


-- -----------------------------------------------------------------------------
-- conversions
elemToClafer x = case x of
  IEClafer clafer  -> Just clafer
  _  -> Nothing

toClafers = mapMaybe elemToClafer

-- -----------------------------------------------------------------------------
-- finds hierarchy and transforms each element
mapHierarchy f sf = (map f.).(findHierarchy sf)


-- returns inheritance hierarchy of a clafer

findHierarchy sFun clafers clafer
  | sFun clafer == "clafer"      = [clafer]
  | otherwise                    = clafer : superClafers
  where
  superClafers = unfoldr (\c -> find (isEqClaferId $ sFun c) clafers >>=
                          Just . (apply id)) clafer


-- -----------------------------------------------------------------------------
-- generic functions

apply f x = (x, f x)

-- lists all nodes of a tree (BFS). Take a function to extract subforest
bfs toNode seed = map rootLabel $ concat $ takeWhile (not.null) $
  iterate (concatMap subForest) $ unfoldForest toNode seed


toNodeShallow = apply (getSubclafers.elements)


getSubclafers = mapMaybe elemToClafer


bfsClafers clafers = bfs toNodeShallow clafers


lurry f x y = f [x,y]


fst3 (a, _, _) = a
snd3 (_, b, _) = b
trd3 (_, _, c) = c

toTriple a (b,c) = (a, b, c)

toMTriple a (b,c) = Just (a, b, c)

-- unary operators
iNot          = "!"
iCSet         = "#"
iMin          = "-"
iGMax         = "max"
iGMin         = "min"
unOps = [iNot, iCSet, iMin, iGMax, iGMin]

-- binary operators
iIff          = "<=>"
iImpl         = "=>"
iOr           = "||"
iXor          = "xor"
iAnd          = "&&"

logBinOps = [iIff, iImpl, iOr, iXor, iAnd]

iLt           = "<"
iGt           = ">"
iEq           = "="
iLte          = "<="
iGte          = ">="
iNeq          = "!="
iIn           = "in"
iNin          = "not in"

relGenBinOps = [iLt, iGt, iEq, iLte, iGte, iNeq]

relSetBinOps = [iIn, iNin]

relBinOps = relGenBinOps ++ relSetBinOps

iPlus         = "+"
iSub          = "-"
iMul          = "*"
iDiv          = "/"

arithBinOps = [iPlus, iSub, iMul, iDiv]

iUnion        = "++"
iDifference   = "--"
iIntersection = "&"
iDomain       = "<:"
iRange        = ":>"
iJoin         = "."

setBinOps = [iUnion, iDifference, iIntersection, iDomain, iRange, iJoin]

binOps = logBinOps ++ relBinOps ++ arithBinOps ++ setBinOps

-- ternary operators
iIfThenElse   = "=>else"

mkIFunExp op (x:[]) = x
mkIFunExp op xs = foldl1 (\x y -> IFunExp op $ map (PExp (Just TClafer) "" noPos) [x,y]) xs

toLowerS "" = ""
toLowerS (s:ss) = toLower s : ss

-- -----------------------------------------------------------------------------
-- Constants

this = "this"

parent = "parent"

children = "children"

ref = "ref"

specialNames = [this, parent, children, ref]

strType = "string"

intType = "int"

integerType = "integer"

baseClafer = "clafer"

modSep = "\\"

primitiveTypes = [strType, intType, integerType]

isPrimitive = flip elem primitiveTypes

data GEnv = GEnv {
  num :: Int,
  stable :: Map.Map String [[String]], -- super clafer names of a given clafer
  sClafers ::[IClafer] -- all clafers (no going through references)
  } deriving (Eq, Show)

voidf f = do
  x <- f
  return ()

noPos = ((0, 0), (0, 0))