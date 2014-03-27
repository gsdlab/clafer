{-
 Copyright (C) 2012 Kacper Bak <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.Transformer where

import Control.Lens
import Data.Maybe
import Language.Clafer.Common
import qualified Language.Clafer.Intermediate.Intclafer as I (exp, elements, op)
import Language.Clafer.Intermediate.Intclafer hiding (exp, elements, op)
import Language.Clafer.Intermediate.Desugarer

transModule :: IModule -> IModule
transModule = mDecls . traversed %~ transElement

transElement :: IElement -> IElement
transElement (IEClafer clafer)           = IEClafer $ transClafer clafer
transElement (IEConstraint isHard' pexp) = IEConstraint isHard' $ transPExp False pexp
transElement (IEGoal isMaximize' pexp)   = IEGoal isMaximize' $ transPExp False pexp  

transClafer :: IClafer -> IClafer
transClafer = I.elements . traversed %~ transElement 

transPExp :: Bool -> PExp -> PExp
transPExp True  pexp' = desugarPath $ I.exp %~ transIExp (fromJust $ pexp' ^. iType) $ pexp'
transPExp False pexp' = pexp'

transIExp :: IType -> IExp -> IExp
transIExp t idpe@(IDeclPExp _ _ _) = bpexp            %~ transPExp False $ idpe
transIExp t ife@(IFunExp op' _)    = exps . traversed %~ transPExp cond  $ ife
  where
    cond = op' == iIfThenElse && 
           t `elem` [TBoolean, TClafer []]
transIExp _ x = x 


