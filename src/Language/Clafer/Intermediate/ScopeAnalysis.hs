{-
 Copyright (C) 2013-2017 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.ScopeAnalysis where

import Control.Lens (universeOn)
import Data.Data.Lens (biplate)
import Data.Maybe

import Language.Clafer.ClaferArgs
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.SimpleScopeAnalyzer

-- | Return an appropriate scope analysis for a given strategy
getScopeStrategy :: ScopeStrategy -> IModule -> [(String, Integer)]
getScopeStrategy Simple = simpleScopeAnalysis
getScopeStrategy _      = const []

-- | The scope above which a scope is large
largeScope :: Integer
largeScope = 100

-- | The references with an unbounded multiplicity to a clafer (`refs -> A *`) whose scopes are large,
-- with their targets. Such a reference may point to every instance of its target, so its scope is
-- the target's scope per parent; an upper bound in its multiplicity makes it smaller.
largeReferenceScopes :: IModule -> [(UID, Integer)] -> [(IClafer, Integer, IClafer, Integer)]
largeReferenceScopes iModule scopes =
    [ (c, scopeOf c, target, scopeOf target)
    | c <- universeOn biplate iModule
    , (snd <$> _card c) == Just (-1)
    , [ref'] <- [getReference c]
    , not $ isPrimitive ref'
    , Just target <- [findIClafer uidClaferMap' ref']
    , scopeOf c > largeScope
    ]
    where
    uidClaferMap' = createUidIClaferMap iModule
    -- a clafer without an inferred scope has the global scope, 1 by default
    scopeOf c' = fromMaybe 1 $ lookup (_uid c') scopes
