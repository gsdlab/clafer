{-
 Copyright (C) 2012-2014 Jimmy Liang, Kacper Bak, Michał Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.SimpleScopeAnalyzer (simpleScopeAnalysis) where

import Control.Applicative ((<$>))
import Control.Lens hiding (elements, assign)
import Data.Graph
import Data.List
import Data.Data.Lens (biplate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.Ratio
import Prelude hiding (exp)

import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer

-- | Collects the global cardinality and hierarchy information into proper, not necessarily lower, bounds.
simpleScopeAnalysis :: IModule -> [(String, Integer)]
simpleScopeAnalysis iModule@IModule{_mDecls = decls'} =
    [(a, b) | (a, b) <- finalAnalysis, b /= 1]
    where
    uidClaferMap' = createUidIClaferMap iModule
    findClafer :: UID -> IClafer
    findClafer uid' = fromJust $ findIClafer uidClaferMap' uid'

    finalAnalysis = Map.toList $ foldl analyzeComponent supersAndRefsAnalysis connectedComponents

    upperCards u =
        Map.findWithDefault (error $ "No upper cardinality for clafer named \"" ++ u ++ "\".") u upperCardsMap
    upperCardsMap = Map.fromList [(_uid c, snd $ fromJust $ _card c) | c <- clafers]

    supersAnalysis = foldl (analyzeSupers uidClaferMap' clafers) Map.empty decls'
    supersAndRefsAnalysis = foldl (analyzeRefs uidClaferMap' clafers) supersAnalysis decls'
    constraintAnalysis = analyzeConstraints constraints upperCards
    (subclaferMap, parentMap) = analyzeHierarchy uidClaferMap' clafers
    connectedComponents = analyzeDependencies uidClaferMap' clafers
    clafers :: [ IClafer ]
    clafers = universeOn biplate iModule
    constraints = concatMap findConstraints decls'

    lowerOrUpperFixedCard analysis' clafer =
        maximum [cardLb, cardUb, lowFromConstraints, oneForStar, targetScopeForStar ]
        where
        Just (cardLb, cardUb) = _card clafer
        oneForStar = if (cardLb == 0 && cardUb == -1) then 1 else 0
        targetScopeForStar = if ((isJust $ _reference clafer) && cardUb == -1)
            then case getReference clafer of
                [ref'] -> Map.findWithDefault 1 (fromMaybe "unknown" $ _uid <$> findIClafer uidClaferMap' ref' ) analysis'
                _      -> 0
            else 0
        lowFromConstraints = Map.findWithDefault 0 (_uid clafer) constraintAnalysis

    analyzeComponent analysis' component =
        case flattenSCC component of
            [uid'] -> analyzeSingleton uid' analysis'
            uids  ->
                foldr analyzeSingleton assume uids
                where
                -- assume that each of the scopes in the component is 1 while solving
                assume = foldr (`Map.insert` 1) analysis' uids
        where
        analyzeSingleton uid' analysis'' = analyze analysis'' $ findClafer uid'

    analyze :: Map String Integer -> IClafer -> Map String Integer
    analyze analysis' clafer =
        -- Take the max between the supers and references analysis and this analysis
        Map.insertWith max (_uid clafer) scope analysis'
        where
        scope
            | _isAbstract clafer  = sum subclaferScopes
            | otherwise          = parentScope * (lowerOrUpperFixedCard analysis' clafer)

        subclaferScopes = map (findOrError " subclafer scope not found" analysis') subclafers
        parentScope  =
            case parentMaybe of
                Just parent'' -> findOrError " parent scope not found" analysis' parent''
                Nothing      -> rootScope
        subclafers = Map.findWithDefault [] (_uid clafer) subclaferMap
        parentMaybe = Map.lookup (_uid clafer) parentMap
        rootScope = 1
        findOrError message m key = Map.findWithDefault (error $ key ++ message) key m

analyzeSupers :: UIDIClaferMap -> [IClafer] -> Map String Integer -> IElement -> Map String Integer
analyzeSupers uidClaferMap' clafers analysis (IEClafer clafer) =
    foldl (analyzeSupers uidClaferMap' clafers) analysis' (_elements clafer)
    where
    (Just (cardLb, cardUb)) = _card clafer
    lowerOrFixedUpperBound = maximum [1, cardLb, cardUb ]
    analysis' = if (isJust $ _reference clafer)
                then analysis
                else case (directSuper uidClaferMap' clafer) of
                  (Just c) -> Map.alter (incLB lowerOrFixedUpperBound) (_uid c) analysis
                  Nothing -> analysis
    incLB lb' Nothing = Just lb'
    incLB lb' (Just lb) = Just (lb + lb')
analyzeSupers _ _ analysis _ = analysis

analyzeRefs :: UIDIClaferMap -> [IClafer] -> Map String Integer -> IElement -> Map String Integer
analyzeRefs uidClaferMap' clafers analysis (IEClafer clafer) =
    foldl (analyzeRefs uidClaferMap' clafers) analysis' (_elements clafer)
    where
    (Just (cardLb, cardUb)) = _card clafer
    lowerOrFixedUpperBound = maximum [1, cardLb, cardUb]
    analysis' = if (isJust $ _reference clafer)
                then case (directSuper uidClaferMap' clafer) of
                    (Just c) -> Map.alter (maxLB lowerOrFixedUpperBound) (_uid c) analysis
                    Nothing -> analysis
                else analysis
    maxLB lb' Nothing = Just lb'
    maxLB lb' (Just lb) = Just (max lb lb')
analyzeRefs _ _ analysis _ = analysis

analyzeConstraints :: [PExp] -> (String -> Integer) -> Map String Integer
analyzeConstraints constraints upperCards =
    foldr analyzeConstraint Map.empty $ filter isOneOrSomeConstraint constraints
    where
    isOneOrSomeConstraint PExp{_exp = IDeclPExp{_quant = quant'}} =
        -- Only these two quantifiers requires an increase in scope to satisfy.
        case quant' of
            IOne -> True
            ISome -> True
            _     -> False
    isOneOrSomeConstraint _ = False

    -- Only considers how quantifiers affect scope. Other types of constraints are not considered.
    -- Constraints of the type [some path1.path2] or [no path1.path2], etc.
    analyzeConstraint PExp{_exp = IDeclPExp{_oDecls = [], _bpexp = bpexp'}} analysis =
        foldr atLeastOne analysis path'
        where
        path' = dropThisAndParent $ unfoldJoins bpexp'
        atLeastOne = Map.insertWith max `flip` 1

    -- Constraints of the type [all disj a : path1.path2] or [some b : path3.path4], etc.
    analyzeConstraint PExp{_exp = IDeclPExp{_oDecls = decls'}} analysis =
        foldr analyzeDecl analysis decls'
    analyzeConstraint _ analysis = analysis

    analyzeDecl IDecl{_isDisj = isDisj', _decls = decls', _body = body'} analysis =
        foldr (uncurry insert') analysis $ zip path' scores
        where
        -- Take the first element in the path', and change its effective lower cardinality.
        -- Can overestimate the scope.
        path' = dropThisAndParent $ unfoldJoins body'
        -- "disj a;b;c" implies at least 3 whereas "a;b;c" implies at least one.
        minScope = if isDisj' then fromIntegral $ length decls' else 1
        insert' = Map.insertWith max

        scores = assign path' minScope

        {-
         - abstract Z
         -   C *
         -     D : integer *
         -
         - A : Z
         -   B : integer
         -   [some disj a;b;c;d : D | a = 1 && b = 2 && c = 3 && d = B]
         -}
         -- Need at least 4 D's per A.
         -- Either
         -- a) Make the effective lower cardinality of C=4 and D=1
         -- b) Make the effective lower cardinality of C=1 and D=4
         -- c) Some other combination.
         -- Choose b, a greedy algorithm that starts from the lowest child progressing upwards.

        {-
         - abstract Z
         -   C *
         -     D : integer 3..*
         -
         - A : Z
         -   B : integer
         -   [some disj a;b;c;d : D | a = 1 && b = 2 && c = 3 && d = B]
         -}
         -- The algorithm we do is greedy so it will chose D=3.
         -- However, it still needs more D's so it will choose C=2
         -- C=2, D=3
         -- This might not be optimum since now the scope allows for 6 D's.
         -- A better solution might be C=2, D=2.
         -- Well too bad, we are using the greedy algorithm.
    assign [] _ = [1]
    assign (p : ps) score =
        pScore : ps'
        where
        --upper = upperCards p
        ps' = assign ps score
        psScore = product $ ps'
        pDesireScore = ceiling (score % psScore)
        pMaxScore = upperCards p
        pScore = min' pDesireScore pMaxScore

    min' a b = if b == -1 then a else min a b

    -- The each child has at most one parent. No matter what the path in a quantifier
    -- looks like, we ignore the parent parts.
    dropThisAndParent = dropWhile (== "parent") . dropWhile (== "this")


analyzeDependencies :: UIDIClaferMap -> [IClafer] -> [SCC String]
analyzeDependencies uidClaferMap' clafers = connComponents
    where
    connComponents  = stronglyConnComp [(key, key, depends) | (key, depends) <- dependencyGraph]
    dependencies    = concatMap (dependency uidClaferMap') clafers
    dependencyGraph = Map.toList $ Map.fromListWith (++) [(a, [b]) | (a, b) <- dependencies]

dependency :: UIDIClaferMap -> IClafer -> [(String, String)]
dependency uidClaferMap' clafer =
    selfDependency : (maybeToList superDependency ++ childDependencies)
    where
     -- This is to make the "stronglyConnComp" from Data.Graph play nice. Otherwise,
     -- clafers with no dependencies will not appear in the result.
    selfDependency = (_uid clafer, _uid clafer)
    superDependency
        | isNothing $ _super clafer = Nothing
        | otherwise =
            do
                super' <- directSuper uidClaferMap' clafer
                -- Need to analyze clafer before its super
                return (_uid super', _uid clafer)
    -- Need to analyze clafer before its children
    childDependencies = [(_uid child, _uid clafer) | child <- childClafers clafer]


analyzeHierarchy :: UIDIClaferMap -> [IClafer] -> (Map String [String], Map String String)
analyzeHierarchy uidClaferMap' clafers =
    foldl hierarchy (Map.empty, Map.empty) clafers
    where
    hierarchy (subclaferMap, parentMap) clafer = (subclaferMap', parentMap')
        where
            subclaferMap' =
                case super' of
                    Just super'' -> Map.insertWith (++) (_uid super'') [_uid clafer] subclaferMap
                    Nothing     -> subclaferMap
            super' = directSuper uidClaferMap' clafer
            parentMap' = foldr (flip Map.insert $ _uid clafer) parentMap (map _uid $ childClafers clafer)

directSuper :: UIDIClaferMap -> IClafer -> Maybe IClafer
directSuper uidClaferMap' clafer =
    second $ findHierarchy getSuper uidClaferMap' clafer
    where
    second [] = Nothing
    second [_] = Nothing
    second (_:x:_) = Just x


-- Find all constraints
findConstraints :: IElement -> [PExp]
findConstraints IEConstraint{_cpexp = c} = [c]
findConstraints (IEClafer clafer) = concatMap findConstraints (_elements clafer)
findConstraints _ = []

-- Finds all the direct ancestors (ie. children)
childClafers :: IClafer -> [IClafer]
childClafers clafer = clafer ^.. elements.traversed.iClafer

-- Unfold joins
-- If the expression is a tree of only joins, then this function will flatten
-- the joins into a list.
-- Otherwise, returns an empty list.
unfoldJoins :: PExp -> [String]
unfoldJoins pexp =
    fromMaybe [] $ unfoldJoins' pexp
    where
    unfoldJoins' PExp{_exp = (IFunExp "." args)} =
        return $ args >>= unfoldJoins
    unfoldJoins' PExp{_exp = IClaferId{_sident = sident'}} =
        return $ [sident']
    unfoldJoins' _ =
        fail "not a join"
