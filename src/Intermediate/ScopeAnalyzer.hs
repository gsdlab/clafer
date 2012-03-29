module Intermediate.ScopeAnalyzer (scopeAnalysis) where

import Common
import Data.Graph
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Intermediate.Intclafer
import Prelude hiding (exp)



isReference = isOverlapping . super
isConcrete = not . isReference
isSuperest clafers clafer = isNothing $ directSuper clafers clafer


-- Collects the global cardinality and hierarchy information into proper lower bounds.
-- If the model only has Clafers (ie. no constraints) then the lower bound is tight.
-- scopeAnalysis :: IModule -> Map IClafer Integer
scopeAnalysis IModule{mDecls = decls} =
    filter (isConcreteAndSuper . fst) finalAnalysis
    where
    finalAnalysis = Map.toList $ foldl analyzeComponent referenceAnalysis connectedComponents
    
    isConcreteAndSuper uid =
        isConcrete clafer && isSuperest clafers clafer
        where
        clafer = findClafer uid
    
    referenceAnalysis = foldl (analyzeReferences clafers) Map.empty decls
    (subclaferMap, parentMap) = analyzeHierarchy clafers
    connectedComponents = analyzeDependencies clafers
    clafers = concatMap findClafers decls
    findClafer uid = fromJust $ find (isEqClaferId uid) clafers
    
    analyzeComponent analysis component =
        case flattenSCC component of
            [uid] -> analyze analysis $ findClafer uid
            uids  -> error $ "TODO:" ++ show uids
    
    analyze :: Map String Integer -> IClafer -> Map String Integer
    analyze analysis clafer =
        -- Take the max between the reference analysis and this analysis
        Map.insertWith max (uid clafer) scope analysis
        where
        scope
            | isReference clafer = 0 -- Reference scopes are already handled in the analyzeReferences
            | isAbstract clafer  = sum subclaferScopes
            | otherwise          = parentScope * lowCard
        
        lowCard = fst $ fromJust $ card clafer
        subclaferScopes = map (findOrError " subclafer scope not found" analysis) subclafers
        parentScope  =
            case parent of
                Just parent' -> findOrError " parent scope not found" analysis parent'
                Nothing      -> rootScope
        subclafers = findOrError " subclafer not found" subclaferMap $ uid clafer
        parent     = Map.lookup (uid clafer) parentMap
        rootScope = 1
        findOrError message map key = Map.findWithDefault (error $ key ++ message) key map
        
    
analyzeReferences clafers analysis (IEClafer clafer) =
    foldl (analyzeReferences clafers) analysis' (elements clafer)
    where
    lowerBound = fst (fromJust $ card clafer)
    analysis'
        | isReference clafer = Map.insert (uid clafer) 0 $ Map.insert (uid $ fromJust $ directSuper clafers clafer) lowerBound analysis
        | otherwise          = analysis
analyzeReferences _ analysis _ = analysis


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
findClafers (IEClafer clafer) = clafer : concatMap findClafers (elements clafer)
findClafers _ = []


-- Finds all the direct ancestors (ie. children)
childClafers clafer =
    mapMaybe asClafer (elements clafer)
    where
    asClafer (IEClafer clafer) = Just clafer
    asClafer _ = Nothing
