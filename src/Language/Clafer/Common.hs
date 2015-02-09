{-# LANGUAGE DeriveDataTypeable, RankNTypes, KindSignatures, FlexibleContexts #-}
{-
 Copyright (C) 2012-2014 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Common where

import           Control.Applicative ((<$>))
import           Control.Lens (universeOn)
import           Data.Char
import           Data.Data.Lens (biplate)
import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import           Data.StringMap (StringMap)
import qualified Data.StringMap as SMap
import           Data.Tree

import Language.Clafer.Front.AbsClafer
import Language.Clafer.Intermediate.Intclafer

-- -----------------------------------------------------------------------------
-- basic functions shared by desugarer, analyzer and code generator
type Result = String

transIdent :: PosIdent -> String
transIdent (PosIdent (_, str)) = str

mkIdent :: String -> PosIdent
mkIdent str = PosIdent ((0, 0), str)

mkInteger :: Read a => PosInteger -> a
mkInteger (PosInteger (_, n)) = read n

type Ident = PosIdent

-- | Returns only [] or [_]
getSuper :: IClafer -> [String]
getSuper claf = case getSuperId <$> _super claf of
    Nothing       -> []
    Just "clafer" -> error "Bug: The identifier 'clafer' should never be returned as super type"
    Just x        -> [x]

-- | Returns only [] or [_]
getReference :: IClafer -> [String]
getReference c = case getSuperId <$> _ref <$> _reference c of
    Nothing -> []
    Just x  -> [x]

-- | Returns only [] or [_] or [_, _]
getSuperAndReference :: IClafer -> [String]
getSuperAndReference c = (getSuper c) ++ (getReference c)

getSuperId :: PExp -> String
getSuperId (PExp _ _ _ (IClaferId{ _sident = s})) = s
getSuperId pexp' = error $ "Bug: getSuperId called not on '[PExp (IClaferId)]' but instead on '" ++ show pexp' ++ "'"

isEqClaferId :: String -> IClafer -> Bool
isEqClaferId    uid'      claf'    = _uid claf' == uid'

idToPExp :: String -> Span -> String -> String -> Bool -> PExp
idToPExp pid' pos modids id' isTop' = PExp (Just $ TClafer [id']) pid' pos (IClaferId modids id' isTop' Nothing)

mkPLClaferId :: CName -> Bool -> ClaferBinding -> PExp
mkPLClaferId id' isTop' bind' = pExpDefPidPos $ IClaferId "" id' isTop' bind'

pExpDefPidPos :: IExp -> PExp
pExpDefPidPos = pExpDefPid noSpan

pExpDefPid :: Span -> IExp -> PExp
pExpDefPid = pExpDef ""

pExpDef :: String -> Span -> IExp -> PExp
pExpDef = PExp Nothing

isParent :: PExp -> Bool
isParent (PExp _ _ _ (IClaferId _ id' _ _)) = id' == parentIdent
isParent _ = False

isClaferName :: PExp -> Bool
isClaferName (PExp _ _ _ (IClaferId _ id' _ _)) =
  id' `notElem` (specialNames ++ primitiveTypes)
isClaferName _ = False

isClaferName' :: PExp -> Bool
isClaferName' (PExp _ _ _ (IClaferId _ _ _ _)) = True
isClaferName' _ = False

getClaferName :: PExp -> String
getClaferName (PExp _ _ _ (IClaferId _ id' _ _)) = id'
getClaferName _ = ""

isTopLevel :: IClafer -> Bool
isTopLevel IClafer{_parentUID=puid} = puid == rootIdent  -- for concrete clafers
                                   || puid == baseClafer -- for abstract clafers

-- -----------------------------------------------------------------------------
-- conversions
elemToClafer :: IElement -> Maybe IClafer
elemToClafer x = case x of
  IEClafer clafer  -> Just clafer
  _  -> Nothing

toClafers :: [IElement] -> [IClafer]
toClafers = mapMaybe elemToClafer

-- -----------------------------------------------------------------------------
-- | Finds hierarchy and transforms each element
mapHierarchy :: (IClafer -> b)
                -> (IClafer -> [String])
                -> [IClafer]
                -> IClafer
                -> [b]
mapHierarchy f sf = (map f.).(findHierarchy sf)


-- | Returns inheritance hierarchy of a clafer
findHierarchy :: (IClafer -> [String])
                            -> [IClafer]
                            -> IClafer
                            -> [IClafer]
findHierarchy sFun clafers clafer = case sFun clafer of
  []           -> [clafer]  -- no super and no reference
  supersOrRefs -> let
                    superOrRefClafers = (concatMap findSuper supersOrRefs)
                  in
                    clafer : superOrRefClafers ++ concatMap (findHierarchy sFun clafers) superOrRefClafers
  where
    findSuper superUid = filter (\c -> _uid c == superUid) clafers

-- -----------------------------------------------------------------------------
-- UID -> IClafer map construction functions

createUidIClaferMap :: IModule -> StringMap IClafer
createUidIClaferMap    iModule  = foldl' (\accumMap' claf -> SMap.insert (_uid claf) claf accumMap') (SMap.singleton rootIdent rootClafer) allClafers
  where
    allClafers :: [ IClafer ]
    allClafers = universeOn biplate iModule
    rootClafer = IClafer noSpan False Nothing rootIdent rootIdent "" Nothing Nothing (Just (1, 1)) (1, 1) []

findIClafer :: StringMap IClafer -> UID -> Maybe IClafer
findIClafer    uidIClaferMap        uid' = SMap.lookup uid' uidIClaferMap

-- -----------------------------------------------------------------------------
-- functions using the UID -> IClafer map

-- | traverse the inheritance hierarchy upwards to find a clafer with the given uidToFind
findUIDinSupers :: StringMap IClafer -> UID    -> IClafer      -> Maybe IClafer
findUIDinSupers    uidIClaferMap        uidToFind currentClafer =
  if uidToFind == _uid currentClafer
  then return currentClafer
  else do
    superClaferUID <- getSuperId <$> _super currentClafer
    superClafer <- findIClafer uidIClaferMap superClaferUID
    findUIDinSupers uidIClaferMap uidToFind superClafer

data NestedInheritanceMatch
  = NestedInheritanceMatch
  { _headClafer :: IClafer               -- ^ the clafer for which the match is computed
  , _parentClafer :: IClafer             -- ^ parent of the head clafer
  , _parentsSuperClafer :: Maybe IClafer -- ^ parent of the super of the head clafer
  , _targetClafer :: Maybe IClafer       -- ^ target of the head clafer
  , _targetsSuperClafer :: Maybe IClafer -- ^ super of the target of the head clafer
  , _superClafer :: IClafer              -- ^ super of the head clafer (must exist, otherwise no match)
  , _superClafersParent :: IClafer       -- ^ parent of the super of the head clafer
  , _superClafersTarget :: Maybe IClafer -- ^ target of the super of the head clafer
  } deriving Show

-- | This represents a match of this shape
--
--    superClafersParent
--         /\           <>
--        ?1|             \*
-- parentsSuperClafer      \
--         /\    [=]   superClafer --*-> superClafersTarget
--         *|              /\                     /\
--    parentClafer          |                      |?2
--               <>        *|       [=]   targetsSuperClafer
--                *\        |                     /\
--                  \       |                     *|
--                   headClafer -----*-----> targetClafer
--
-- The clafers are obtained by navigating from the headClafer
-- by following the links marked by *
-- The link marked by ?1 is checked for correctness of nesting (isProperNesting):
-- - _uid parentsSuperClafer == _parentUID superClafer
-- The link marked by ?2 is checked for correctness of redefinition (isProperRefinement):
-- - proper subtyping, bag to set, proper cardinality restriction
-- Redefinition occurs when the name of headClafer is the same as the name of superClafer (isProperRedefinition):
-- - isProperNesting && isProperRefinement && (_ident headClafer) == (_ident superClafer)

isProperNesting :: StringMap IClafer -> Maybe NestedInheritanceMatch -> Bool
isProperNesting _ Nothing  = False
isProperNesting uidIClaferMap (Just m) = case (_parentsSuperClafer m) of
  Nothing                 -> (_uid $ _parentClafer m) == (_uid $ _superClafersParent m)
  Just parentsSuperClafer -> isJust $  findUIDinSupers uidIClaferMap (_parentUID $ _superClafer m) parentsSuperClafer

-- ^ assumes that isProperNesting m == True
isProperRefinement :: StringMap IClafer -> Maybe NestedInheritanceMatch
  -> (Bool,  Bool,  Bool)
isProperRefinement    _                    Nothing
  = ( False
    , False
    , False )
isProperRefinement    uidIClaferMap        (Just m)
  = ( properCardinalityRefinement m
    , properBagToSetRefinement m
    , properTargetSubtyping m )
  where
    properCardinalityRefinement NestedInheritanceMatch{_headClafer=hc, _superClafer=hcs}
      = case (_card hc, _card hcs) of
          (Just (hcl, hcu), Just (hcsl, hcsu)) -> hcl >= hcsl && (hcu <= hcsu || hcsu == -1)
          _ -> False
    properBagToSetRefinement NestedInheritanceMatch{_headClafer=hc, _superClafer=hcs}
      = case (_reference hc, _reference hcs) of
          (Just IReference{_isSet=headIsSet}, Just IReference{_isSet=superIsSet}) -> superIsSet <= headIsSet  -- set (True) implies set (True), bag (False) allows bag (False) or set (True)
          _ -> True -- covers 1) only one of them has a ref, and 2) none of them has a ref
    properTargetSubtyping NestedInheritanceMatch{_targetClafer=(Just targetClafer), _superClafersTarget=(Just superClafersTarget)}
      = isJust $ findUIDinSupers uidIClaferMap (_uid superClafersTarget) targetClafer
    properTargetSubtyping _
      = True -- covers 1) only one of the target clafers exists, and 2) none of the target clafers exist

-- ^ assumes that isProperNesting m == True and isProperRefinement m == True
isProperRedefinition :: Maybe NestedInheritanceMatch -> Bool -- ^ whether the name of headClafer is the same as superClafer
isProperRedefinition Nothing = False
isProperRedefinition (Just NestedInheritanceMatch{_headClafer=hc, _superClafer=hs})
  =  (_ident hc) == (_ident hs)



-- ^ try to match the nested inheritance pattern
-- ^ only available after the parentUIDs were computed
matchNestedInheritance :: StringMap IClafer -> IClafer
  -> Maybe NestedInheritanceMatch
matchNestedInheritance    _                    IClafer{_super=Nothing}    = Nothing
matchNestedInheritance    uidIClaferMap        headClafer                 = do
--  traceM $ "matching nested inheritance for " ++ _uid headClafer
  parentClafer       <- findIClafer uidIClaferMap $ _parentUID headClafer
--  traceM $ "matched parentClafer " ++ _uid parentClafer
  superClafer        <- (findIClafer uidIClaferMap) =<< (getSuperId <$> _super headClafer)
--  traceM $ "matched superClafer " ++ _uid superClafer
  superClafersParent <- findIClafer uidIClaferMap $ _parentUID superClafer
--  traceM $ "matched superClafersParent " ++ _uid superClafersParent
  let
    parentsSuperClafer :: Maybe IClafer
    parentsSuperClafer = findIClafer uidIClaferMap =<< getSuperId <$> _super parentClafer  -- safe to use fromJust becuase _super is not isNothing
    targetClafer :: Maybe IClafer
    targetClafer = findIClafer uidIClaferMap =<< getSuperId <$> _ref <$> _reference headClafer
    targetsSuperClafer :: Maybe IClafer
    targetsSuperClafer = findIClafer uidIClaferMap =<< getSuperId <$> (_super =<< targetClafer)
    superClafersTarget :: Maybe IClafer
    superClafersTarget = findIClafer uidIClaferMap =<< getSuperId <$> _ref <$> _reference superClafer
--  traceM $ "matched parentsSuperClafer " ++ show (_uid <$> parentsSuperClafer)
--  traceM $ "matched targetClafer " ++ show (_uid <$> targetClafer)
--  traceM $ "matched targetsSuperClafer " ++ show (_uid <$> targetsSuperClafer)
--  traceM $ "matched superClafersTarget " ++ show (_uid <$> superClafersTarget)
  return $ NestedInheritanceMatch
    { _headClafer = headClafer
    , _parentClafer = parentClafer
    , _parentsSuperClafer = parentsSuperClafer
    , _superClafer = superClafer
    , _superClafersParent = superClafersParent
    , _targetClafer = targetClafer
    , _targetsSuperClafer = targetsSuperClafer
    , _superClafersTarget = superClafersTarget
    }


-- -----------------------------------------------------------------------------
-- generic functions

apply :: forall t t1. (t -> t1) -> t -> (t, t1)
apply f x = (x, f x)

-- lists all nodes of a tree (BFS). Take a function to extract subforest
bfs :: forall b b1. (b1 -> (b, [b1])) -> [b1] -> [b]
bfs toNode seed = map rootLabel $ concat $ takeWhile (not.null) $
  iterate (concatMap subForest) $ unfoldForest toNode seed


toNodeShallow :: IClafer -> (IClafer, [IClafer])
toNodeShallow = apply (getSubclafers._elements)


getSubclafers :: [IElement] -> [IClafer]
getSubclafers = mapMaybe elemToClafer


bfsClafers :: [IClafer] -> [IClafer]
bfsClafers clafers = bfs toNodeShallow clafers

lurry :: forall t t1. ([t1] -> t) -> t1 -> t1 -> t
lurry f x y = f [x,y]

fst3 :: forall t t1 t2. (t, t1, t2) -> t
fst3 (a, _, _) = a
snd3 :: forall t t1 t2. (t, t1, t2) -> t1
snd3 (_, b, _) = b
trd3 :: forall t t1 t2. (t, t1, t2) -> t2
trd3 (_, _, c) = c


toTriple :: forall t t1 t2. t -> (t1, t2) -> (t, t1, t2)
toTriple a (b,c) = (a, b, c)

toMTriple :: forall t t1 t2. t -> (t1, t2) -> Maybe (t, t1, t2)
toMTriple a (b,c) = Just (a, b, c)

-- unary operators
iNot :: String
iNot          = "!"

iG :: String
iG          = "G"

iF :: String
iF          = "F"

iX :: String
iX          = "X"

iCSet :: String
iCSet         = "#"

iMin :: String
iMin          = "-"

iGMax :: String
iGMax         = "max"

iGMin :: String
iGMin         = "min"

iSumSet :: String
iSumSet       = "sum"

unOps :: [String]
unOps = [iNot, iCSet, iMin, iGMax, iGMin, iSumSet, iX, iF, iG]

-- binary operators
iIff :: String
iIff          = "<=>"

iImpl :: String
iImpl         = "=>"

iOr :: String
iOr           = "||"

iXor :: String
iXor          = "xor"

iAnd :: String
iAnd          = "&&"

iU :: String
iU          = "U"

iW :: String
iW          = "W"

logBinOps :: [String]
logBinOps = [iIff, iImpl, iOr, iXor, iAnd, iU, iW]

iLt :: String
iLt           = "<"

iGt :: String
iGt           = ">"

iEq :: String
iEq           = "="

iLte :: String
iLte          = "<="

iGte :: String
iGte          = ">="

iNeq :: String
iNeq          = "!="

iIn :: String
iIn           = "in"

iNin :: String
iNin          = "not in"

ltlOps :: [String]
ltlOps = [iW, iU, iX, iG, iF]

ltlBinOps :: [String]
ltlBinOps = [iW, iU]

ltlUnOps :: [String]
ltlUnOps = [iX, iG, iF]

relGenBinOps :: [String]
relGenBinOps = [iLt, iGt, iEq, iLte, iGte, iNeq]

relSetBinOps :: [String]
relSetBinOps = [iIn, iNin]

relBinOps :: [String]
relBinOps = relGenBinOps ++ relSetBinOps

iPlus :: String
iPlus         = "+"

iSub :: String
iSub          = "-"

iMul :: String
iMul          = "*"

iDiv :: String
iDiv          = "/"

iSumSet' :: String
iSumSet'      = "sum'"

arithBinOps :: [String]
arithBinOps = [iPlus, iSub, iMul, iDiv, iSumSet']

iUnion :: String
iUnion        = "++"

iDifference :: String
iDifference   = "--"

iIntersection :: String
iIntersection = "**"

iDomain :: String
iDomain       = "<:"

iRange :: String
iRange        = ":>"

iJoin :: String
iJoin         = "."

setBinOps :: [String]
setBinOps = [iUnion, iDifference, iIntersection, iDomain, iRange, iJoin]

binOps :: [String]
binOps = logBinOps ++ relBinOps ++ arithBinOps ++ setBinOps

-- temporal keywords and property patterns

temporalModifiers :: [String]
temporalModifiers = [ "final", "initial" ]

iLet :: String
iLet = "let"

propertyKeywords :: [String]
propertyKeywords =
  [ "never", "sometime", "lonce", "always"
  , "must", "precede", "follow"
  , "initially", "finally"
  , "until", "weakuntil", "eventually", "globally", "next"
  , "before", "after", "between", "and", "after"
  ]

-- ternary operators
iIfThenElse :: String
iIfThenElse   = "ifthenelse"

mkIFunExp :: String -> [IExp] -> IExp
mkIFunExp _ (x:[]) = x
mkIFunExp op' xs = foldl1 (\x y -> IFunExp op' $ map (PExp (Just $ TClafer []) "" noSpan) [x,y]) xs

toLowerS :: String -> String
toLowerS "" = ""
toLowerS (s:ss) = toLower s : ss

-- -----------------------------------------------------------------------------
-- Constants

rootIdent :: String
rootIdent = "root"

rootUID :: String
rootUID = "root"

thisIdent :: String
thisIdent = "this"

parentIdent :: String
parentIdent = "parent"

refIdent :: String
refIdent = "ref"

childrenIdent :: String
childrenIdent = "children"

specialNames :: [String]
specialNames = [thisIdent, parentIdent, refIdent, rootIdent, childrenIdent]

isSpecial :: String -> Bool
isSpecial = flip elem specialNames

stringType :: String
stringType = "string"

intType :: String
intType = "int"

integerType :: String
integerType = "integer"

realType :: String
realType = "real"

booleanType :: String
booleanType = "boolean"

baseClafer :: String
baseClafer = "clafer"

modSep :: String
modSep = "\\"

primitiveTypes :: [String]
primitiveTypes = [stringType, intType, integerType, realType]

isPrimitive :: String -> Bool
isPrimitive = flip elem primitiveTypes

-- | reserved keywords which cannot be used as clafer identifiers
keywordIdents :: [String]
keywordIdents =
  baseClafer :
  specialNames ++
  primitiveTypes ++
  [ iGMax, iGMin, iSumSet ] ++ -- unary operators
  [ iXor, iIn ] ++ -- binary operators
  [ "if", "then", "else" ] ++ -- ternary operators
  [ "no", "not", "some", "one", "all", "disj" ] ++ -- quantifiers
  [ "opt", "mux", "or", "lone" ] ++ -- group cardinalities
  [ "abstract", "enum" ] ++ -- keywords
  temporalModifiers ++ -- temporal
  ltlOps ++ -- LTL
  propertyKeywords ++ -- temp patterns
  [ iLet ]

data GEnv = GEnv {
  identCountMap :: Map.Map String Int,
  expCount :: Int,
  stable :: Map.Map UID [[UID]], -- super clafer names of a given clafer
  sClafers ::[IClafer] -- all clafers (no going through references)
  } deriving (Eq, Show)

voidf :: Monad m => m t -> m ()
voidf f = do
  _ <- f
  return ()

safeTail :: [a] -> [a]
safeTail [] = []
safeTail (_:xs) = xs
