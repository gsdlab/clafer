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
{- | The names of the clafers in the Alloy outputs.

A clafer's Alloy name is its UID, unless the UID cannot be one: an Alloy keyword (e.g., @sig@), a
function of @util/integer@, which the outputs open (e.g., @max@), or a name that the generators
write (e.g., @show@). The generators also derive names from a clafer's name @u@: @r_u@ (the
relation from the parent), @u_ref@ (the reference), @alive_u@ and @p_u@ (temporal models), which
must differ from the names of all other clafers. A clafer whose UID cannot be its Alloy name gets
@u_1@, @u_2@, ..., the first that is free. Only those clafers are renamed; the UIDs, and all
other outputs, are unchanged.
-}
module Language.Clafer.Generator.AlloyNames
  ( alloyNames
  , toAlloyNames
  , fromAlloyName
  , alloyReserved
  ) where

import           Control.Lens (over)
import           Control.Lens.Plated
import           Data.Char (isDigit)
import           Data.Data.Lens
import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import qualified Data.Set as Set

import           Language.Clafer.Intermediate.Intclafer

-- | The Alloy names of the clafers whose UIDs cannot be their Alloy names, by UID.
alloyNames :: IModule -> Map.Map UID String
alloyNames imodule = Map.fromList renamed
  where
    uids = map _uid (universeOn biplate imodule :: [IClafer])
    allUids = Set.fromList uids
    -- the UIDs that can be Alloy names, in the order of the model, with the names they use
    (used, toRename) = foldl keep (Set.empty, []) uids
    keep (used', rest) u
      | u `Set.member` alloyReserved || looksGenerated u || any (`Set.member` used') (derived u) = (used', rest ++ [u])
      | otherwise = (foldr Set.insert used' (derived u), rest)
    renamed = snd $ mapAccumL rename used toRename
    rename used' u = (foldr Set.insert used' (derived name), (u, name))
      where
        name = fromJust $ find free [ u ++ "_" ++ show n | n <- [1 :: Int ..] ]
        free n = n `Set.notMember` allUids && all (`Set.notMember` used') (derived n)

-- | The UID of a clafer given its Alloy name.
fromAlloyName :: Map.Map UID String -> String -> UID
fromAlloyName names name = fromMaybe name $ lookup name [ (n, u) | (u, n) <- Map.toList names ]

-- | The names the generators derive from a clafer's name.
derived :: String -> [String]
derived u = [u, "r_" ++ u, u ++ "_ref", "alive_" ++ u, "p_" ++ u]

-- | Writes the clafers of a module with their Alloy names: their UIDs, their parents, the
--   clafers in the expressions and in the types.
toAlloyNames :: Map.Map UID String -> IModule -> IModule
toAlloyNames names imodule
  | Map.null names = imodule
  | otherwise = over biplate renameType $ transformOn biplate renameExp $ transformOn biplate renameClafer imodule
  where
    r u = Map.findWithDefault u u names
    renameClafer c = c{_uid = r (_uid c), _parentUID = r (_parentUID c)}
    renameExp e@IClaferId{_sident = s, _binding = b} = case b of
      LocalBind _  -> e
      GlobalBind u -> e{_sident = r s, _binding = GlobalBind (r u)}
      NoBind       -> e{_sident = r s}
    renameExp e = e
    renameType (TClafer hi') = TClafer (map r hi')
    renameType (TMap so' ta') = TMap (renameType so') (renameType ta')
    renameType (TUnion un') = TUnion (map renameType un')
    renameType t = t

-- | A name that the Alloy generator writes for an assertion, e.g., assertAt_3_5.
looksGenerated :: String -> Bool
looksGenerated n = case stripPrefix "assertAt_" n of
  Just rest -> case break (== '_') rest of
    (line, '_' : column) -> not (null line) && all isDigit line && not (null column) && all isDigit column
    _ -> False
  Nothing -> False

-- | The names that cannot be clafers' names in Alloy: the keywords of Alloy 6, the functions of
--   util/integer and the names the generators write.
alloyReserved :: Set.Set String
alloyReserved = Set.fromList $
  [ "abstract", "all", "and", "as", "assert", "but", "check", "disj", "else", "enum", "exactly"
  , "expect", "extends", "fact", "for", "fun", "iden", "iff", "implies", "in", "Int", "int", "let"
  , "lone", "module", "no", "none", "not", "one", "open", "or", "pred", "private", "run", "seq"
  , "set", "sig", "some", "String", "sum", "this", "univ", "var", "steps", "always", "eventually"
  , "after", "before", "historically", "once", "since", "until", "releases", "triggered" ] ++
  [ "add", "plus", "sub", "minus", "mul", "div", "rem", "negate", "eq", "gt", "lt", "gte", "lte"
  , "zero", "pos", "neg", "nonpos", "nonneg", "signum", "int2elem", "elem2int", "max", "min"
  , "next", "prev", "nexts", "prevs", "larger", "smaller" ] ++
  [ "show", "ref", "self_", "children", "integer", "util" ]
