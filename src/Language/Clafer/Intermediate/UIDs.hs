{-
 Copyright (C) 2026 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
{- | The UIDs of the clafers: the names, qualified only as much as needed.

The UID of a clafer is its least-partially-qualified name, with @__@ between the names: @size@
if no other clafer is named @size@; @x__size@ for the @size@ in @x@, if another @size@ exists
elsewhere; @root__size@ for a top-level @size@ that is also the end of another clafer's path
(@root@ is a keyword, so no path of names starts with it). A UID is an identifier of Clafer, so
an explicit model needs only unique names, and nothing has to parse a UID to get a clafer's name:
it is the clafer's @_ident@.

* An apostrophe is written @_prime@: @a'@ is @a_prime@.
* A UID that equals the UID of a clafer before it in the model (e.g., @a_prime@ next to @a'@,
  or two siblings with the same name) gets the first free suffix @__2@, @__3@, ...: no path of
  names has a part that starts with a digit, so a suffix never equals a qualified name.

The UIDs do not depend on the outputs: each generator writes them in the form its target
language allows, e.g., the Alloy generator renames a UID that is an Alloy keyword
("Language.Clafer.Generator.AlloyNames").
-}
module Language.Clafer.Intermediate.UIDs
  ( assignUIDs
  , uidSegment
  ) where

import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import qualified Data.Set as Set

import           Language.Clafer.Common
import           Language.Clafer.Intermediate.Intclafer (UID)

-- | The UIDs of the clafers with the given paths (the names of the clafer and its ancestors,
--   from the top level), in the same order. The paths are those of all clafers of a model.
assignUIDs :: [[String]] -> [UID]
assignUIDs paths = snd $ mapAccumL fresh Set.empty $ map candidate reversedPaths
  where
    reversedPaths = map reverse paths
    -- for each suffix of a path (reversed), the number of clafers whose paths end with it
    suffixCounts :: Map.Map [String] Int
    suffixCounts = Map.fromListWith (+) [ (s, 1) | rp <- reversedPaths, s <- nub $ tail $ inits rp ]
    endWith s = Map.findWithDefault 0 s suffixCounts
    candidate rp = case [ s | k <- [1 .. length rp], let s = take k rp, endWith s == 1 ] of
      (s : _) -> render s
      -- the full path is also the end of another clafer's path: from the root
      [] -> render (rp ++ [rootIdent])
    render = intercalate "__" . map uidSegment . reverse
    fresh used uid' = (Set.insert chosen used, chosen)
      where chosen = fromJust $ find (`Set.notMember` used) $ uid' : [ uid' ++ "__" ++ show n | n <- [2 :: Int ..] ]

-- | A name as a part of a UID: an apostrophe, which identifiers cannot contain, is _prime.
uidSegment :: String -> String
uidSegment = concatMap (\c -> if c == '\'' then "_prime" else [c])
