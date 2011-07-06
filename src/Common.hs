{-# LANGUAGE DeriveDataTypeable #-}
module Common where

import Data.Tree
import Data.Maybe
import List
import Data.Map (Map)
import qualified Data.Map as Map
import System.Console.CmdArgs

import Front.Absclafer
import Intermediate.Intclafer

-- -----------------------------------------------------------------------------
-- basic functions shared by desugarer, analyzer and code generator
type Result = String


transIdent :: Ident -> Result
transIdent x = case x of
  Ident str  -> str


transName :: Name -> (Maybe Result, Result)
transName x = case x of
  Name modids id  -> (Nothing, transIdent id)


getSuper clafer = id
  where
  [ISExpIdent id _] = supers $ super $ clafer


isEqClaferId = flip $ (==).uid


-- -----------------------------------------------------------------------------
-- conversions
elemToClafer x = case x of
  ISubclafer clafer  -> Just clafer
  _  -> Nothing

toClafers = mapMaybe declToClafer
  where
  declToClafer x = case x of
    IClaferDecl clafer  -> Just clafer
    otherwise  -> Nothing


-- -----------------------------------------------------------------------------
-- processes lists with a list of functions
multiProcess = (flip (foldr ($))).(map process)


-- processes each element of the list with passing state
process f xs = unfoldr run ([], xs)
  where
  run (ps, us) = listToMaybe us >> (Just $ apply (\x -> (x : ps, tail us)) 
    (f ps us))

-- -----------------------------------------------------------------------------
-- finds hierarchy and transforms each element
mapHierarchy f = (map f.).findHierarchy


-- returns inheritance hierarchy of a clafer
findHierarchy :: [IClafer] -> IClafer -> [IClafer]
findHierarchy clafers clafer = clafer : unfoldr 
  (\c -> find (isEqClaferId $ getSuper c) clafers -- searches for super
     >>= Just . (apply id)) clafer

-- -----------------------------------------------------------------------------
-- generic functions

apply f x = (x, f x)

upFst f (x, y) = (f x, y)

upSnd f (x, y) = (x, f y)

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

-- -----------------------------------------------------------------------------
-- Constants

this = "this"

parent = "parent"

children = "children"

strType = "string"

intType = "int"

integerType = "integer"

baseClafer = "clafer"

data GEnv = GEnv {
  num :: Int,
  stable :: Map.Map String [[String]],
  sClafers ::[IClafer]
    }
  deriving (Eq, Show)

data ClaferArgs = ClaferArgs {
      unroll_inheritance :: Bool,
      file :: FilePath
    } deriving (Show, Data, Typeable)

