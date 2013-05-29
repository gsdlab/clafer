{-
 Copyright (C) 2012 Jimmy Liang, Kacper Bak <http://gsd.uwaterloo.ca>

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

import Language.Clafer.Common
import Data.Graph
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.Ratio
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import Prelude hiding (exp)
import Debug.Trace


isReference = isOverlapping . super
isConcrete = not . isReference
isSuperest clafers clafer = isNothing $ directSuper clafers clafer


-- Collects the global cardinality and hierarchy information into proper lower bounds.
-- If the model only has Clafers (ie. no constraints) then the lower bound is tight.
-- scopeAnalysis :: IModule -> Map IClafer Integer
simpleScopeAnalysis :: IModule -> [(String, Integer)]
simpleScopeAnalysis IModule{mDecls = decls} =
    [(a, b) | (a, b) <- finalAnalysis, isReferenceOrSuper a, b /= 0]
    where
    finalAnalysis = Map.toList $ foldl analyzeComponent referenceAnalysis connectedComponents
    
    isReferenceOrSuper uid =
        isReference clafer || isSuperest clafers clafer
        where
        clafer = findClafer uid
        
    isConcrete' uid = isConcrete $ findClafer uid
    
    upperCards u =
        Map.findWithDefault (error $ "No upper cardinality for clafer named \"" ++ u ++ "\".") u upperCardsMap
    upperCardsMap = Map.fromList [(uid c, snd $ fromJust $ card c) | c <- clafers]
    
    referenceAnalysis = foldl (analyzeReferences clafers) Map.empty decls
    constraintAnalysis = analyzeConstraints constraints upperCards
    (subclaferMap, parentMap) = analyzeHierarchy clafers
    connectedComponents = analyzeDependencies clafers
    clafers = concatMap findClafers decls
    constraints = concatMap findConstraints decls
    findClafer uid = fromJust $ find (isEqClaferId uid) clafers
    
    lowCard clafer =
        max low constraintLow
        where
        low = fst $ fromJust $ card clafer
        constraintLow = Map.findWithDefault 0 (uid clafer) constraintAnalysis
    
    analyzeComponent analysis component =
        case flattenSCC component of
            [uid] -> analyzeSingleton uid analysis
            uids  ->
                foldr analyzeSingleton assume uids
                where
                -- assume that each of the scopes in the component is 1 while solving
                assume = foldr (`Map.insert` 1) analysis uids
        where
        analyzeSingleton uid analysis = analyze analysis $ findClafer uid
    
    analyze :: Map String Integer -> IClafer -> Map String Integer
    analyze analysis clafer =
        -- Take the max between the reference analysis and this analysis
        Map.insertWith max (uid clafer) scope analysis
        where
        scope
            | isAbstract clafer  = sum subclaferScopes
            | otherwise          = parentScope * lowCard clafer
        
        subclaferScopes = map (findOrError " subclafer scope not found" analysis) $ filter isConcrete' subclafers
        parentScope  =
            case parent of
                Just parent' -> findOrError " parent scope not found" analysis parent'
                Nothing      -> rootScope
        subclafers = Map.findWithDefault [] (uid clafer) subclaferMap
        parent     = Map.lookup (uid clafer) parentMap
        rootScope = 1
        findOrError message map key = Map.findWithDefault (error $ key ++ message) key map
        
    
analyzeReferences clafers analysis (IEClafer clafer) =
    foldl (analyzeReferences clafers) analysis' (elements clafer)
    where
    lowerBound = fst (fromJust $ card clafer)
    analysis'
        | isReference clafer = Map.insert (uid $ fromJust $ directSuper clafers clafer) lowerBound analysis
        | otherwise          = analysis
analyzeReferences _ analysis _ = analysis


analyzeConstraints :: [PExp] -> (String -> Integer) -> Map String Integer
analyzeConstraints constraints upperCards =
    foldr analyzeConstraint Map.empty $ filter isOneOrSomeConstraint constraints
    where
    isOneOrSomeConstraint PExp{exp = IDeclPExp{quant = quant}} =
        -- Only these two quantifiers requires an increase in scope to satisfy.
        case quant of
            IOne -> True
            ISome -> True
            _     -> False
    isOneOrSomeConstraint _ = False
    
    -- Only considers how quantifiers affect scope. Other types of constraints are not considered.
    -- Constraints of the type [some path1.path2] or [no path1.path2], etc.
    analyzeConstraint PExp{exp = IDeclPExp{quant = quant, oDecls = [], bpexp = bpexp}} analysis =
        foldr atLeastOne analysis path
        where
        path = dropThisAndParent $ unfoldJoins bpexp
        atLeastOne = Map.insertWith max `flip` 1
        
    -- Constraints of the type [all disj a : path1.path2] or [some b : path3.path4], etc.
    analyzeConstraint PExp{exp = IDeclPExp{oDecls = decls}} analysis =
        foldr analyzeDecl analysis decls
    analyzeConstraint _ analysis = analysis

    analyzeDecl IDecl{isDisj = isDisj, decls = decls, body = body} analysis =
        foldr (uncurry insert) analysis $ zip path scores
        where
        -- Take the first element in the path, and change its effective lower cardinality.
        -- Can overestimate the scope.
        path = dropThisAndParent $ unfoldJoins body
        -- "disj a;b;c" implies at least 3 whereas "a;b;c" implies at least one.
        minScope = if isDisj then fromIntegral $ length decls else 1
        insert = Map.insertWith max
        
        scores = assign path minScope
        
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
        upper = upperCards p
        ps' = assign ps score
        psScore = product $ ps'
        pDesireScore = ceiling (score % psScore)
        pMaxScore = upperCards p
        pScore = min' pDesireScore pMaxScore
        
    min' a b = if b == -1 then a else min a b
        
    -- The each child has at most one parent. No matter what the path in a quantifier
    -- looks like, we ignore the parent parts.
    dropThisAndParent = dropWhile (== "parent") . dropWhile (== "this")


analyzeDependencies :: [IClafer] -> [SCC String]
analyzeDependencies clafers = connComponents
    where
    connComponents  = stronglyConnComp [(key, key, depends) | (key, depends) <- dependencyGraph]
    dependencies    = concatMap (dependency clafers) clafers
    dependencyGraph = Map.toList $ Map.fromListWith (++) [(a, [b]) | (a, b) <- dependencies]


dependency clafers clafer =
    selfDependency : (maybeToList superDependency ++ childDependencies)
    where
     -- This is to make the "stronglyConnComp" from Data.Graph play nice. Otherwise,
     -- clafers with no dependencies will not appear in the result.
    selfDependency = (uid clafer, uid clafer)
    superDependency
        | isReference clafer = Nothing
        | otherwise =
            do
                super <- directSuper clafers clafer
                -- Need to analyze clafer before its super
                return (uid super, uid clafer)
    -- Need to analyze clafer before its children
    childDependencies = [(uid child, uid clafer) | child <- childClafers clafer]
        

analyzeHierarchy :: [IClafer] -> (Map String [String], Map String String)
analyzeHierarchy clafers =
    foldl hierarchy (Map.empty, Map.empty) clafers
    where
    hierarchy (subclaferMap, parentMap) clafer = (subclaferMap', parentMap')
        where
            subclaferMap' = 
                case super of
                    Just super' -> Map.insertWith (++) (uid super') [uid clafer] subclaferMap
                    Nothing     -> subclaferMap
            super = directSuper clafers clafer
            parentMap' = foldr (flip Map.insert $ uid clafer) parentMap (map uid $ childClafers clafer)
    

directSuper clafers clafer =
    second $ findHierarchy getSuper clafers clafer
    where
    second [] = Nothing
    second [x] = Nothing
    second (x1:x2:xs) = Just x2
    

-- Finds all ancestors
findClafers :: IElement -> [IClafer]
findClafers (IEClafer clafer) = clafer : concatMap findClafers (elements clafer)
findClafers _ = []


-- Find all constraints
findConstraints :: IElement -> [PExp]
findConstraints IEConstraint{cpexp = c} = [c]
findConstraints (IEClafer clafer) = concatMap findConstraints (elements clafer)
findConstraints _ = []

-- Finds all the direct ancestors (ie. children)
childClafers clafer =
    mapMaybe asClafer (elements clafer)
    where
    asClafer (IEClafer clafer) = Just clafer
    asClafer _ = Nothing
    
    
-- Unfold joins
-- If the expression is a tree of only joins, then this function will flatten
-- the joins into a list.
-- Otherwise, returns an empty list.
unfoldJoins :: PExp -> [String]
unfoldJoins pexp =
    fromMaybe [] $ unfoldJoins' pexp
    where
    unfoldJoins' PExp{exp = (IFunExp "." args)} =
        return $ args >>= unfoldJoins
    unfoldJoins' PExp{exp = IClaferId{sident = sident}} =
        return $ [sident]
    unfoldJoins' _ =
        fail "not a join"
