{-
 Copyright (C) 2014 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer.QNameUID (
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

import Data.Maybe
import Data.List.Split
import qualified Data.Map as Map
import qualified Data.StringMap as SMap

import Language.Clafer.Intermediate.Intclafer

-- | a fully- or partially-qualified name
type QName = String

-- | fully-qualified name, must begin with ::
-- | e.g., `::Person::name`, `::Company::Department::chair`
type FQName = String

-- a reversed FQName used as a key in the FQNameUIDMap
type FQKey = String

-- | partially-qualified name, must not begin with ::
-- | e.g., `Person::name`, `chair`
type PQName = String    

-- a map from reversed FQName (Key) to UID (Value)
type FQNameUIDMap = SMap.StringMap UID

type UIDFqNameMap = Map.Map UID FQName
type UIDLpqNameMap = Map.Map UID PQName

-- | maps between fully-, least-partially-qualified names and UIDs
data QNameMaps =  QNameMaps FQNameUIDMap UIDFqNameMap UIDLpqNameMap

-- | get the UID of a clafer given a fully qualifed name or potentially many UIDs given a partially qualified name
getUIDs :: QNameMaps                 -> QName -> [UID]
getUIDs    (QNameMaps fqNameUIDMap _ _) qName = findUIDsByFQName fqNameUIDMap qName

-- | get the fully-qualified name of a clafer given its UID
getFQName :: QNameMaps                 -> UID -> Maybe FQName
getFQName    (QNameMaps _ uidFqNameMap _) uid' = Map.lookup uid' uidFqNameMap 

-- | get the least-partially-qualified name of a clafer given its UID
getLPQName :: QNameMaps                 -> UID -> Maybe PQName
getLPQName    (QNameMaps _ _ uidLpqNameMap) uid' = Map.lookup uid' uidLpqNameMap 

-- | derive maps between fully-, partially-qualified names, and UIDs
deriveQNameMaps :: IModule -> QNameMaps
deriveQNameMaps    iModule = 
    let
        (fqNameUIDMap, uidFqNameMap) = deriveFQNameUIDMaps iModule
        uidLpqNameMap = deriveUidLpqNameMap fqNameUIDMap
    in 
        QNameMaps fqNameUIDMap uidFqNameMap uidLpqNameMap

deriveFQNameUIDMaps :: IModule -> (FQNameUIDMap, UIDFqNameMap)
deriveFQNameUIDMaps    iModule = addElements ["::"] (mDecls iModule) (SMap.empty, Map.empty)

addElements :: [String] -> [IElement] -> (FQNameUIDMap, UIDFqNameMap) -> (FQNameUIDMap, UIDFqNameMap)
addElements    path        elems         maps                         = foldl (addClafer path) maps elems

addClafer :: [String] -> (FQNameUIDMap, UIDFqNameMap) -> IElement          -> (FQNameUIDMap, UIDFqNameMap)
addClafer    path        (fqNameUIDMap, uidFqNameMap)    (IEClafer iClafer) = 
    let 
        newPath = (ident iClafer) : path 
        fqKey :: FQKey
        fqKey = concat newPath
        fqName :: FQName
        fqName = getQNameFromKey fqKey
        fqNameUIDMap' = SMap.insert fqKey (uid iClafer) fqNameUIDMap
        uidFqNameMap' = Map.insert (uid iClafer) fqName uidFqNameMap
    in 
        addElements ("::" : newPath) (elements iClafer) (fqNameUIDMap', uidFqNameMap')
addClafer    _           maps                            _                  = maps

findUIDsByFQName :: FQNameUIDMap -> FQName            -> [ UID ]
findUIDsByFQName    fqNameUIDMap    fqName@(':':':':_) = SMap.lookup (getFQKey fqName) fqNameUIDMap
findUIDsByFQName    fqNameUIDMap    fqName             = SMap.prefixFind (getFQKey fqName) fqNameUIDMap 

reverseOnQualifier :: FQName -> FQName
reverseOnQualifier fqName = concat $ reverse $ split (onSublist "::") fqName

getFQKey :: FQName -> FQKey
getFQKey = reverseOnQualifier

getQNameFromKey :: FQKey -> QName
getQNameFromKey = reverseOnQualifier


deriveUidLpqNameMap :: FQNameUIDMap ->  UIDLpqNameMap
deriveUidLpqNameMap    fqNameUIDMap = 
    SMap.foldWithKey (generateUIDLpqMapEntry fqNameUIDMap) Map.empty fqNameUIDMap

generateUIDLpqMapEntry :: FQNameUIDMap ->  SMap.Key -> UID -> UIDLpqNameMap -> UIDLpqNameMap
generateUIDLpqMapEntry    fqNameUIDMap     fqKey       uid'   uidLpqNameMap = 
    Map.insert uid' lpqName uidLpqNameMap
    where
      -- need to reverse the key to get a fully qualified name
      fqName :: FQName
      fqName = getQNameFromKey fqKey

      -- name qualified just sufficiently to uniquely identify the clafer
      -- can be both FQName or PQName
      lpqName :: QName
      lpqName = findLeastQualifiedName fqName fqNameUIDMap

      findLeastQualifiedName :: String -> FQNameUIDMap -> String
      -- handle fully qualified name case
      findLeastQualifiedName fqName'@(':':':':pqName) fqNameUIDMap' =
          if (length (findUIDsByFQName fqNameUIDMap' pqName) > 1)
              then fqName'
              else findLeastQualifiedName pqName fqNameUIDMap'
      -- handle partially qualified name case
      findLeastQualifiedName pqName fqNameUIDMap' =
         let
            -- remove one segment of qualification 
            lessQName =  concat $ drop 2 $ split (onSublist "::") pqName
         in 
            if (length (findUIDsByFQName fqNameUIDMap' lessQName) > 1)
              then pqName
              else findLeastQualifiedName lessQName fqNameUIDMap'      

getQNameUIDTriples :: QNameMaps -> [(FQName, PQName, UID)]
getQNameUIDTriples qNameMaps@(QNameMaps _ uidFqNameMap _) =
    let
      uidFqNameList :: [(UID, FQName)]
      uidFqNameList = Map.toList uidFqNameMap
    in
      map (\(uid', fqName) -> (fqName, fromMaybe fqName $ getLPQName qNameMaps uid', uid')) uidFqNameList
