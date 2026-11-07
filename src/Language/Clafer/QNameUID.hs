{-
 Copyright (C) 2014-2026 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
{- | Fully- and least-partially-qualified names of clafers, and the clafers that a name names.

The least-partially-qualified (LPQ) name of a clafer is its UID (see
"Language.Clafer.Intermediate.UIDs"): its name, qualified with the names of its ancestors only as
much as needed to be unique, with @__@ between the names, e.g., @size@, @x__size@ or
@root__size@. The fully-qualified name has all of them, from the root, e.g., @root__x__size@.

A name names the clafer whose UID it is; otherwise, split on @__@, all the clafers whose paths of
names end with it, e.g., @size@ names every clafer named @size@, @x__size@ every @size@ in an
@x@, and @root__size@ only a top-level @size@. The older form with @::@ is read too: @x::size@ is
@x__size@, and @::size@ is @root__size@.
-}
module Language.Clafer.QNameUID (
        QName,
        FQName,
        PQName,
        QNameMaps,
        UID,
        deriveQNameMaps,
        getUIDs,
        getFQName,
        getLPQName,
        getQNameUIDTriples
)

where

import Data.List
import Data.List.Split
import qualified Data.Map as Map

import Language.Clafer.Common (rootIdent)
import Language.Clafer.Intermediate.Intclafer

-- | a fully- or partially-qualified name
type QName = String

-- | fully-qualified name, from the root, e.g., `root__Person__name`
type FQName = String

-- | partially-qualified name, e.g., `Person__name`, `chair`
type PQName = String

-- | the clafers by UID, in the order of the model: the names of each clafer and its ancestors,
--   from the top level
data QNameMaps = QNameMaps [(UID, [String])] (Map.Map UID [String])

-- | the UIDs of the clafers that a name names: one for a UID, possibly many for a partially
--   qualified name
getUIDs :: QNameMaps -> QName -> [UID]
getUIDs (QNameMaps paths pathOf) qName
  | Map.member qName pathOf = [qName]
  | null names              = []
  | otherwise               = [ uid' | (uid', path) <- paths, if fromRoot then path == names else names `isSuffixOf` path ]
  where
    (fromRoot, names) = case qName of
      ':' : ':' : rest -> (True, splitOn "::" rest)
      _ | "::" `isInfixOf` qName -> (False, splitOn "::" qName)
      _ -> case splitOn "__" qName of
        (r : rest@(_ : _)) | r == rootIdent -> (True, rest)
        parts -> (False, parts)

-- | the fully-qualified name of a clafer given its UID
getFQName :: QNameMaps -> UID -> Maybe FQName
getFQName (QNameMaps _ pathOf) uid' = fqName <$> Map.lookup uid' pathOf

-- | the least-partially-qualified name of a clafer given its UID: the UID
getLPQName :: QNameMaps -> UID -> Maybe PQName
getLPQName (QNameMaps _ pathOf) uid' = if Map.member uid' pathOf then Just uid' else Nothing

fqName :: [String] -> FQName
fqName = intercalate "__" . (rootIdent :)

-- | derive the names of the clafers of a module
deriveQNameMaps :: IModule -> QNameMaps
deriveQNameMaps iModule = QNameMaps paths (Map.fromList paths)
  where
    paths = concatMap (claferPaths []) $ _mDecls iModule
    claferPaths path (IEClafer iClaf) = (_uid iClaf, path') : concatMap (claferPaths path') (_elements iClaf)
      where path' = path ++ [_ident iClaf]
    claferPaths _ _ = []

-- | the fully-qualified name, the least-partially-qualified name and the UID of each clafer
getQNameUIDTriples :: QNameMaps -> [(FQName, PQName, UID)]
getQNameUIDTriples (QNameMaps paths _) = [ (fqName path, uid', uid') | (uid', path) <- paths ]
