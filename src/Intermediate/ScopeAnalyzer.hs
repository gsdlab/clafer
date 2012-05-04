module Intermediate.ScopeAnalyzer (scopeAnalysis) where

import Common
import Data.Graph
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Front.Absclafer
import Intermediate.Intclafer
import Prelude hiding (exp)
import Debug.Trace


isReference = isOverlapping . super
isConcrete = not . isReference
isSuperest clafers clafer = isNothing $ directSuper clafers clafer


-- Collects the global cardinality and hierarchy information into proper lower bounds.
-- If the model only has Clafers (ie. no constraints) then the lower bound is tight.
-- scopeAnalysis :: IModule -> Map IClafer Integer
scopeAnalysis IModule{mDecls = decls} =
    filter (isReferenceOrSuper . fst) finalAnalysis
    where
    finalAnalysis = Map.toList $ foldl analyzeComponent referenceAnalysis connectedComponents
    
    isReferenceOrSuper uid =
        isReference clafer || isSuperest clafers clafer
        where
        clafer = findClafer uid
        
    isConcrete' uid = isConcrete $ findClafer uid
    
    referenceAnalysis = foldl (analyzeReferences clafers) Map.empty decls
    constraintAnalysis = analyzeConstraints constraints
    (subclaferMap, parentMap) = analyzeHierarchy clafers
    connectedComponents = analyzeDependencies clafers
    clafers = concatMap findClafers decls
    constraints = concatMap findConstraints decls
    findClafer uid = fromJust $ find (isEqClaferId uid) clafers
    
    lowCard clafer =
        max low constraintLow'
        where
        low = fst $ fromJust $ card clafer
        constraintLow = Map.findWithDefault 0 (uid clafer) constraintAnalysis
        -- Don't exceed the stated maximum
        constraintLow' = min' constraintLow $ snd $ fromJust $ card clafer
        
        min' a (ExIntegerNum b) = min a b
        min' a ExIntegerAst = a
    
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


analyzeConstraints :: [PExp] -> Map String Integer
analyzeConstraints constraints =
    foldr analyzeConstraint Map.empty constraints
    where
    -- Only considers how quantifiers affect scope. Other types of constraints are not considered.
    -- Constraints of the type [some path1.path2] or [no path1.path2], etc.    
    analyzeConstraint PExp{exp = IDeclPExp{quant = quant, oDecls = [], bpexp = bpexp}} analysis =
        case quant of
            IOne  -> analysis'
            ISome -> analysis'
            _     -> analysis -- The other quantifiers allow zero so skip.
        where
        analysis' = foldr atLeastOne analysis (top : follow)
        top : follow = dropThisAndParent $ unfoldJoins bpexp
        atLeastOne = Map.insertWith max `flip` 1
        
    -- Constraints of the type [all disj a : path1.path2] or [some b : path3.path4], etc.
    analyzeConstraint PExp{exp = IDeclPExp{oDecls = decls}} analysis =
        foldr analyzeDecl analysis decls
    analyzeConstraint _ analysis = analysis

    analyzeDecl IDecl{isDisj = isDisj, decls = decls, body = body} analysis =
        insert minScope top $ foldr (insert 1) analysis follow
        where
        -- Take the first element in the path, and change its effective lower cardinality.
        -- Can overestimate the scope.
        top : follow = dropThisAndParent $ unfoldJoins body
        -- "disj a;b;c" implies at least 3 whereas "a;b;c" implies at least one.
        minScope = if isDisj then fromIntegral $ length decls else 1
        insert s = Map.insertWith max `flip` s
        
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
         -- Choose b.
         -- A greedy algorithm that starts from the lowest child progressing upwards.
         
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
