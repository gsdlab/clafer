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
module Language.Clafer.Common where

import Data.Tree
import Data.Maybe
import Data.Char
import Data.List
import qualified Data.Map as Map
--import System.Console.CmdArgs
--import Control.Monad.State

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
getSuper = getSuperId.supers.super

getSuperNoArr :: IClafer -> [Char]
getSuperNoArr clafer
  | isOverlapping $ super clafer = "clafer"
  | otherwise                    = getSuper clafer

getSuperId :: [PExp] -> String
getSuperId = sident . Language.Clafer.Intermediate.Intclafer.exp . head

isEqClaferId = flip $ (==).uid

idToPExp :: String -> Span -> String -> String -> Bool -> PExp
idToPExp pid pos modids id isTop = PExp (Just $ TClafer [id]) pid pos (IClaferId modids id isTop)

mkLClaferId :: String -> Bool -> IExp
mkLClaferId = IClaferId ""

mkPLClaferId :: String -> Bool -> PExp
mkPLClaferId id isTop = pExpDefPidPos $ mkLClaferId id isTop

pExpDefPidPos :: IExp -> PExp
pExpDefPidPos = pExpDefPid noSpan

pExpDefPid :: Span -> IExp -> PExp
pExpDefPid = pExpDef ""

pExpDef :: String -> Span -> IExp -> PExp
pExpDef = PExp Nothing

isParent (PExp _ _ _ (IClaferId _ id _)) = id == parent
isParent _ = False

isClaferName :: PExp -> Bool
isClaferName (PExp _ _ _ (IClaferId _ id _)) =
  id `notElem` ([this, parent, children] ++ primitiveTypes)

isClaferName' (PExp _ _ _ (IClaferId _ id _)) = True
isClaferName' _ = False

getClaferName :: PExp -> String
getClaferName (PExp _ _ _ (IClaferId _ id _)) = id


-- -----------------------------------------------------------------------------
-- conversions
elemToClafer x = case x of
  IEClafer clafer  -> Just clafer
  _  -> Nothing

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
  | otherwise                    = clafer : superClafers
  where
  superClafers = unfoldr (\c -> find (isEqClaferId $ sFun c) clafers >>=
                          Just . (apply id)) clafer


-- -----------------------------------------------------------------------------
-- generic functions

apply f x = (x, f x)

-- lists all nodes of a tree (BFS). Take a function to extract subforest
bfs :: (b1 -> (b, [b1])) -> [b1] -> [b]
bfs toNode seed = map rootLabel $ concat $ takeWhile (not.null) $
  iterate (concatMap subForest) $ unfoldForest toNode seed


toNodeShallow :: IClafer -> (IClafer, [IClafer])
toNodeShallow = apply (getSubclafers.elements)


getSubclafers :: [IElement] -> [IClafer]
getSubclafers = mapMaybe elemToClafer


bfsClafers :: [IClafer] -> [IClafer]
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
iSumSet       = "sum"
unOps = [iNot, iCSet, iMin, iGMax, iGMin, iSumSet]

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

relGenBinOps :: [[Char]]
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

binOps :: [[Char]]
binOps = logBinOps ++ relBinOps ++ arithBinOps ++ setBinOps

-- ternary operators
iIfThenElse   = "=>else"

mkIFunExp op (x:[]) = x
mkIFunExp op xs = foldl1 (\x y -> IFunExp op $ map (PExp (Just $ TClafer []) "" noSpan) [x,y]) xs

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

voidf :: Monad m => m t -> m ()
voidf f = do
  x <- f
  return ()
