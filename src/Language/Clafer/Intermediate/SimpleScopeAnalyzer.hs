{-
 Copyright (C) 2012-2017 Jimmy Liang, Kacper Bak, Michał Antkiewicz <http://gsd.uwaterloo.ca>

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

import Control.Applicative
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

    finalAnalysis = Map.toList $ withSetReferences $ foldl analyzeComponent supersAndRefsAnalysis connectedComponents

    -- The targets of a set reference (->) differ under each parent, so a set reference has at
    -- most as many instances under a parent as its target has in all, e.g., three for an
    -- enumeration with three literals, when the multiplicities bound the target, so that its
    -- scope is not a guess that a larger scope of the target would change. A bag reference (->>)
    -- has no such bound, nor an abstract clafer, whose subclafers may share targets (#125).
    withSetReferences analysis' = foldr capSetReference analysis' clafers
      where
      capSetReference c a = case (_reference c, getReference c) of
          (Just IReference{_isSet = True}, [target]) | not (_isAbstract c)
                                                    , Just t <- findIClafer uidClaferMap' target
                                                    , bounded t
                                                    , Just targetScope <- Map.lookup (_uid t) analysis'
              -> Map.adjust (min $ parentScopeOf c * targetScope) (_uid c) a
          _ -> a
      -- the multiplicities bound the number of instances of the clafer
      bounded c = boundedParent || boundedSuper
        where
        boundedParent = (_isAbstract c || maybe False ((>= 0) . snd) (_card c))
                        && maybe True (maybe False bounded . findIClafer uidClaferMap') (Map.lookup (_uid c) parentMap)
                        && (not (_isAbstract c) || all (maybe False bounded . findIClafer uidClaferMap') (Map.findWithDefault [] (_uid c) subclaferMap))
        boundedSuper = or [ maybe True (maybe False bounded . findIClafer uidClaferMap') (Map.lookup (_uid s) parentMap)
                          | s <- findHierarchy getSuper uidClaferMap' c, _isAbstract s, Just (_, u) <- [_card s], u > 0 ]
      parentScopeOf c = maybe 1 (\p -> Map.findWithDefault 1 p analysis') $ Map.lookup (_uid c) parentMap

    upperCards u =
        Map.findWithDefault (error $ "No upper cardinality for clafer named \"" ++ u ++ "\".") u upperCardsMap
    upperCardsMap = Map.fromList [(_uid c, snd $ fromJust $ _card c) | c <- clafers]

    supersAnalysis = foldl (analyzeSupers uidClaferMap' clafers) Map.empty decls'
    supersAndRefsAnalysis = foldl (analyzeRefs uidClaferMap' clafers) supersAnalysis decls'
    constraintAnalysis = analyzeConstraints constraints upperCards (`Map.member` upperCardsMap)
    (subclaferMap, parentMap) = analyzeHierarchy uidClaferMap' clafers
    connectedComponents = analyzeDependencies uidClaferMap' clafers
    clafers :: [ IClafer ]
    clafers = universeOn biplate iModule
    constraints = concatMap findConstraints decls'

    lowerOrUpperFixedCard analysis' clafer =
        maximum [cardLb, cardUb, lowFromConstraints, oneForStar, targetScopeForStar, lowFromGroupCard, lowFromAbstractSupers ]
        where
        (cardLb, cardUb) = case _card clafer of
            (Just c) -> c
            Nothing  -> (1, 1)
        oneForStar = if (cardLb == 0 && cardUb == -1) then 1 else 0
        targetScopeForStar = if ((isJust $ _reference clafer) && cardUb == -1)
            then case getReference clafer of
                [ref'] -> Map.findWithDefault 1 (maybe "unknown" _uid (findIClafer uidClaferMap' ref')) analysis'
                _      -> 0
            else 0
        lowFromConstraints = Map.findWithDefault 0 (_uid clafer) constraintAnalysis
        -- The group cardinality n..m of the parent requires at least n children,
        -- possibly all instances of this clafer.
        lowFromGroupCard = case _gcard =<< findIClafer uidClaferMap' =<< Map.lookup (_uid clafer) parentMap of
            Just (IGCard _ (groupLb, _)) | cardUb == -1 -> groupLb
                                         | otherwise    -> min groupLb cardUb
            Nothing -> 0
        -- The multiplicity of an abstract super clafer counts all its instances (#129), which
        -- this clafer may supply alone: up to its upper bound, or at least its lower bound when
        -- it has none, unless this clafer's own upper bound is smaller.
        lowFromAbstractSupers =
            let low = maximum (0 : [ if u > 0 then u else l | s <- findHierarchy getSuper uidClaferMap' clafer, _isAbstract s, Just (l, u) <- [_card s] ])
            in if cardUb == -1 then low else min low cardUb

    -- The number of instances that the upper bound of the abstract clafer allows in all: the
    -- bound at the top level, the bound times the scope of the parent otherwise, if it is known.
    -- The 0..0 that the optimizer gives an unused abstract clafer is not a bound.
    abstractCap analysis' c = case _card c of
        Just (_, u) | _isAbstract c, u > 0 -> case Map.lookup (_uid c) parentMap of
            Nothing      -> Just u
            Just parent' -> (u *) <$> Map.lookup parent' analysis'
        _ -> Nothing
    -- The instances of a clafer are instances of each of its abstract super clafers.
    abstractSupersBound analysis' c =
        case mapMaybe (abstractCap analysis') $ drop 1 $ findHierarchy getSuper uidClaferMap' c of
            [] -> Nothing
            bs -> Just $ minimum bs

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
        -- Take the max between the supers and references analysis and this analysis, within the
        -- upper bounds of the abstract clafers (#129): globally at the top level, per instance of
        -- the parent otherwise
        Map.adjust (maybe id min bound) (_uid clafer) $ Map.insertWith max (_uid clafer) scope analysis'
        where
        scope
            | _isAbstract clafer  = sum subclaferScopes
            | otherwise          = parentScope * (lowerOrUpperFixedCard analysis' clafer)
        bound
            | _isAbstract clafer  = abstractCap analysis' clafer
            | otherwise          = abstractSupersBound analysis' clafer

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
analyzeSupers uidClaferMap' clafers analysis (IEClafer clafer)
    -- a clafer without instances, e.g., an abstract clafer that no concrete clafer extends,
    -- adds none to its super, and neither do its children
    | cardUb == 0 = analysis
    | otherwise   = foldl (analyzeSupers uidClaferMap' clafers) analysis' (_elements clafer)
    where
    (cardLb, cardUb) = case _card clafer of
        (Just c) -> c
        Nothing  -> (1, 1)
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
    (cardLb, cardUb) = case _card clafer of
        (Just c) -> c
        Nothing  -> (1, 1)
    lowerOrFixedUpperBound = maximum [1, cardLb, cardUb]
    analysis' = if (isJust $ _reference clafer)
                then case (directSuper uidClaferMap' clafer) of
                    (Just c) -> Map.alter (maxLB lowerOrFixedUpperBound) (_uid c) analysis
                    Nothing -> analysis
                else analysis
    maxLB lb' Nothing = Just lb'
    maxLB lb' (Just lb) = Just (max lb lb')
analyzeRefs _ _ analysis _ = analysis

analyzeConstraints :: [PExp] -> (String -> Integer) -> (String -> Bool) -> Map String Integer
analyzeConstraints constraints upperCards isClafer =
    foldr analyzeCount (foldr analyzeConstraint Map.empty $ filter isOneOrSomeConstraint constraints) counts
    where
    -- Constraints that count the instances of a path from below, e.g., [ #Box.item = 10 ] or
    -- [ #this.item >= 3 ], also in a conjunction: the path needs at least that many instances.
    -- A path through a reference (#r.dref) counts its targets, not instances of clafers.
    counts = concatMap countsOf constraints
    countsOf PExp{_exp = IFunExp op' [a, b]}
        | op' == iAnd = countsOf a ++ countsOf b
        | op' `elem` [iEq, iGte], Just p <- countOf a, Just n <- intOf b = [(p, n)]
        | op' == iGt, Just p <- countOf a, Just n <- intOf b = [(p, n + 1)]
        | op' `elem` [iEq, iLte], Just n <- intOf a, Just p <- countOf b = [(p, n)]
        | op' == iLt, Just n <- intOf a, Just p <- countOf b = [(p, n + 1)]
    countsOf _ = []
    countOf PExp{_exp = IFunExp op' [p]} | op' == iCSet, path'@(_ : _) <- dropThisAndParent (unfoldJoins p), all isClafer path' = Just path'
    countOf _ = Nothing
    intOf PExp{_exp = IInt n} = Just n
    intOf _ = Nothing
    analyzeCount (path', n) analysis
        | n <= 0    = analysis
        | otherwise = foldr (uncurry $ Map.insertWith max) analysis $ zip path' $ assign path' n

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
    selfDependency : (maybeToList superDependency ++ childDependencies ++ targetDependencies)
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
    -- Need to analyze the target of a reference with an unbounded cardinality before
    -- the reference, whose scope uses the target's (targetScopeForStar)
    targetDependencies
        | (snd <$> _card clafer) /= Just (-1) = []
        | otherwise = [(_uid clafer, _uid target) | [ref'] <- [getReference clafer], Just target <- [findIClafer uidClaferMap' ref']]


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
findConstraints IEConstraint'{_cpexp = c} = [c]
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
