module Intermediate.ScopeAnalyzer (scopeAnalysis) where

import Common
import Data.Map hiding (map)
import Data.Maybe
import Intermediate.Intclafer
import Prelude hiding (exp)



data Scope = Scope {subs::[Integer], references::[Integer]} deriving Show



emptyScope = Scope [] []


-- Collects the global cardinality and hierarchy information into proper lower bounds.
-- If the model only has Clafers (ie. no constraints) then the lower bound is tight.
-- scopeAnalysis :: IModule -> Map IClafer Integer
scopeAnalysis IModule{mDecls = decls} = toList $ combineAnalysis `fmap` analysis
    where
    analysis = foldl (resolveClafer clafers) empty clafers
    clafers  = concatMap findClafers decls
    
    
combineAnalysis (Scope subs references) = maximum $ sum subs : references


findClafers (IEClafer clafer) = clafer : concatMap findClafers (elements clafer)
findClafers _ = []


-- Does not handle multiple inheritance yet.
resolveClafer clafers analysis clafer =
    if isAbstract clafer then
        -- No changes to the analysis
        analysis
    else
        insertKey (uid $ superest clafers clafer) analysis
    where
    insertKey k m      = insertWith (const add) k (add emptyScope) m
    
    (low, _)           = glCard clafer
    isReference        = isOverlapping $ super clafer
    
    add                = if isReference then addReference else addSub
    addSub scope       = scope{subs = low : subs scope}
    addReference scope = scope{references = low : references scope}


superest clafers clafer = last $ findHierarchy getSuper clafers clafer
