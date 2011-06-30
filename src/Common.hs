module Common where

import Data.Tree
import Data.Maybe
import List

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
-- Finds the first element with certain property and returns
-- it. If no element is found, returns some default value.
-- Elements are sorted according to their hierarchy
findInHierarchy def pred declarations clafer =
  findInList def pred $ findHierarchy declarations clafer


findInList def pred xs = maybe def id $ find pred xs


-- finds hierarchy and transforms each element
mapHierarchy f = (map f.).findHierarchy


-- returns inheritance hierarchy of a clafer
findHierarchy :: [IClafer] -> IClafer -> [IClafer]
findHierarchy clafers clafer = clafer : unfoldr 
  (\c -> find (isEqClaferId $ getSuper c) (bfsClafers clafers) -- searches for super
     >>= Just . (apply id)) clafer

-- -----------------------------------------------------------------------------
-- generic functions

apply f x = (x, f x)

-- lists all nodes of a tree (BFS). Take a function to extract subforest
bfs toNode seed = map rootLabel $ concat $ takeWhile (not.null) $
  iterate (concatMap subForest) $ unfoldForest toNode seed


toNodeShallow = apply (getSubclafers.elements)


getSubclafers = mapMaybe elemToClafer


bfsClafers clafers = bfs toNodeShallow clafers

pairToList = uncurry ((.return).(:))

lurry f x y = f [x,y]

filterNull = filter (not.null)

-- -----------------------------------------------------------------------------
-- Constants

this = "this"

parent = "parent"

children = "children"

strType = "string"

intType = "int"

integerType = "integer"

baseClafer = "clafer"