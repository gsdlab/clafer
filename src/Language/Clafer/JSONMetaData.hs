{-# LANGUAGE OverloadedStrings #-}
{-
 Copyright (C) 2014-2017 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
-- | Creates JSON outputs for different kinds of metadata.
module Language.Clafer.JSONMetaData (
  generateJSONnameUIDMap,
  generateJSONScopes,
  parseJSONScopes,
  writeCfrScopeFile,
  readCfrScopeFile
)

where

import Control.Lens hiding ((.=))
import Data.Aeson ((.=))
import Data.Aeson.Encoding (Encoding, encodingToLazyByteString, list, pairs)
import Data.Aeson.Lens
import qualified Data.List as List
import Data.Maybe
import Data.String.Conversions
import qualified Data.Text as T
import System.FilePath
import System.Directory

import Language.Clafer.QNameUID

-- | Generate a JSON list of triples containing a fully-qualified-, least-partially-qualified name, and unique id.
-- | Both the FQNames and UIDs are brittle. LPQNames are the least brittle.
generateJSONnameUIDMap :: QNameMaps -> String
generateJSONnameUIDMap    qNameMaps     =
    prettyPrintJSON $ convertString $ encodingToLazyByteString $ list generateQNameUIDArrayEntry sortedTriples
    where
      sortedTriples :: [(FQName, PQName, UID)]
      sortedTriples = List.sortBy (\(fqName1, _, _) (fqName2, _, _) -> compare fqName1 fqName2) $ getQNameUIDTriples qNameMaps

generateQNameUIDArrayEntry :: (FQName, PQName, UID) -> Encoding
generateQNameUIDArrayEntry    (fqName, lpqName, uid) =
    pairs $ mconcat [
        "fqName" .= fqName,
        "lpqName" .= lpqName,
        "uid" .= uid ]

-- | Generate a JSON list of tuples containing a least-partially-qualified name and a scope
generateJSONScopes :: QNameMaps -> [(UID, Integer)] -> String
generateJSONScopes    qNameMaps    scopes       =
    prettyPrintJSON $ convertString $ encodingToLazyByteString $ list generateLpqNameScopeArrayEntry sortedLpqNameScopeList
    where
      lpqNameScopeList = map (\(uid, scope) -> (fromMaybe uid $ getLPQName qNameMaps uid, scope)) scopes
      sortedLpqNameScopeList :: [(PQName, Integer)]
      sortedLpqNameScopeList = List.sortBy (\(lpqName1, _) (lpqName2, _) -> compare lpqName1 lpqName2) lpqNameScopeList


generateLpqNameScopeArrayEntry :: (PQName, Integer) -> Encoding
generateLpqNameScopeArrayEntry    (lpqName, scope) =
    pairs $ mconcat [
        "lpqName" .= lpqName,
        "scope" .= scope ]

-- insert a new line after  [, {, and ,
prettyPrintJSON :: String -> String
prettyPrintJSON ('[':line) = '[':'\n':prettyPrintJSON line
prettyPrintJSON ('{':line) = '{':'\n':prettyPrintJSON line
prettyPrintJSON (',':line) = ',':'\n':prettyPrintJSON line
-- insert a new line before ], }
prettyPrintJSON (']':line) = '\n':']':prettyPrintJSON line
prettyPrintJSON ('}':line) = '\n':'}':prettyPrintJSON line
-- just rewrite and continue
prettyPrintJSON (c:line) =  c:prettyPrintJSON line
prettyPrintJSON ""         = ""

-- | given the QNameMaps, parse the JSON scopes and return list of scopes.
-- | Only the entries {"lpqName": name, "scope": n} are clafer scopes; the others, e.g., chocosolver's
-- | {"int": [low, high]} or {"defaultScope": n}, are skipped.
parseJSONScopes :: QNameMaps -> String    -> [ (UID, Integer) ]
parseJSONScopes    qNameMaps    scopesJSON =
    foldl (\uidScopes qScope -> qNameToUIDs qScope ++ uidScopes) [] decodedScopes
    where
      --                  QName
      decodedScopes :: [ (T.Text, Integer) ]
      decodedScopes = mapMaybe claferScope $ scopesJSON ^.. _Array . traverse
      claferScope o = (,) <$> o ^? key "lpqName" . _String <*> o ^? key "scope" . _Integer
      -- a UID names its clafer; a QName may resolve to potentially multiple UIDs
      qNameToUIDs :: (T.Text, Integer) -> [ (UID, Integer) ]
      qNameToUIDs   (qName, scope)
        | T.null qName                       = [ ("", scope) ]
        | isJust $ getFQName qNameMaps name  = [ (name, scope) ]
        | otherwise                          = [ (uid, scope) | uid <- getUIDs qNameMaps name ]
        where
          name = convertString qName

-- | Write a .cfr-scope file
writeCfrScopeFile :: [ (UID, Integer) ] -> QNameMaps -> FilePath        -> IO ()
writeCfrScopeFile    uidScopes             qNameMaps    modelName = do
    let
        scopesInJSON = generateJSONScopes qNameMaps uidScopes
    writeFile (replaceExtension modelName ".cfr-scope") scopesInJSON

-- | Read a .cfr-scope file
readCfrScopeFile :: QNameMaps -> FilePath        -> IO (Maybe [ (UID, Integer) ])
readCfrScopeFile    qNameMaps    modelName = do
    let
        cfrScopeFileName = replaceExtension modelName ".cfr-scope"
    exists <- doesFileExist cfrScopeFileName
    if exists
    then do
        scopesInJSON <- readFile cfrScopeFileName
        return $ Just $ parseJSONScopes qNameMaps scopesInJSON
    else return Nothing
