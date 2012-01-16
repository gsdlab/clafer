{-
 This file is part of the Clafer Translator (clafer).

 Copyright (C) 2010 Kacper Bak <http://gsd.uwaterloo.ca/kbak>

 clafer is free software: you can redistribute it and/or modify
 it under the terms of the GNU Lesser General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 clafer is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Lesser General Public License for more details.

 You should have received a copy of the GNU Lesser General Public License
 along with clafer. (See files COPYING and COPYING.LESSER.)  If not,
 see <http://www.gnu.org/licenses/>.
-}
{-# LANGUAGE DeriveDataTypeable #-}
module Common where

import Data.Tree
import Data.Maybe
import Data.Char
import List
import Data.Map (Map)
import qualified Data.Map as Map
import System.Console.CmdArgs
import Control.Monad.State

import Front.Absclafer
import Intermediate.Intclafer

-- -----------------------------------------------------------------------------
-- basic functions shared by desugarer, analyzer and code generator
type Result = String


transIdent :: Ident -> Result
transIdent x = case x of
  Ident str  -> str


getSuper clafer = id
  where
  [PExp _ _ (IClaferId _ id _)] = supers $ super $ clafer


isEqClaferId = flip $ (==).uid

idToPExp pid modids id isTop = PExp (Just ISet) pid (IClaferId modids id isTop)

mkLClaferId = IClaferId ""

mkPLClaferId id isTop = PExp Nothing "" $ mkLClaferId id isTop

-- -----------------------------------------------------------------------------
-- conversions
elemToClafer x = case x of
  IEClafer clafer  -> Just clafer
  _  -> Nothing

toClafers = mapMaybe elemToClafer

-- -----------------------------------------------------------------------------
-- finds hierarchy and transforms each element
mapHierarchy f = (map f.).findHierarchy


-- returns inheritance hierarchy of a clafer
findHierarchy :: [IClafer] -> IClafer -> [IClafer]
findHierarchy clafers clafer
  | getSuper clafer == "clafer" = [clafer]
  | otherwise                   = clafer : superClafers
  where
  superClafers = unfoldr (\c -> find (isEqClaferId $ getSuper c) clafers >>=
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


filterNull = filter (not.null)


fst3 (a, _, _) = a
snd3 (_, b, _) = b
trd3 (_, _, c) = c

toTriple a (b,c) = (a, b, c)

toMTriple a (b,c) = Just (a, b, c)

-- unary operators
iNot          = "!"
iCSet         = "#"
iMin          = "-"
unOps = [iNot, iCSet, iMin]

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
mkIFunExp op xs = foldl1 (\x y -> IFunExp op $ map (PExp (Just ISet) "") [x,y]) xs

toLowerS "" = ""
toLowerS (s:ss) = toLower s : ss

-- -----------------------------------------------------------------------------
-- Constants

this = "this"

parent = "parent"

children = "children"

strType = "string"

intType = "int"

integerType = "integer"

baseClafer = "clafer"

modSep = "\\"

isPrimitive = flip elem [strType, intType, integerType]

data GEnv = GEnv {
  num :: Int,
  stable :: Map.Map String [[String]],
  sClafers ::[IClafer]
    }
  deriving (Eq, Show)

data ClaferMode = Alloy42 | Alloy | Xml | Clafer
  deriving (Eq, Show, Data, Typeable)

data ClaferArgs = ClaferArgs {
      mode :: ClaferMode,
      console_output :: Bool,
      flatten_inheritance :: Bool,
      file :: FilePath,
      timeout_analysis :: Int,
      no_layout :: Bool,
      new_layout :: Bool,
      check_duplicates :: Bool,
      force_resolver :: Bool,
      keep_unused :: Bool,
      no_stats :: Bool,
      schema :: Bool
    } deriving (Show, Data, Typeable)

