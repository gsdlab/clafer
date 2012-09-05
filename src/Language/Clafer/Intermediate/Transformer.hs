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

import Data.Maybe
import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.Desugarer

transModule imodule = imodule{mDecls = map transElement $ mDecls imodule}

transElement :: IElement -> IElement
transElement x = case x of
  IEClafer clafer  -> IEClafer $ transClafer clafer
  IEConstraint isHard pexp  -> IEConstraint isHard $ transPExp False pexp
  IEGoal isMaximize pexp  -> IEGoal isMaximize $ transPExp False pexp  

transClafer :: IClafer -> IClafer
transClafer clafer = clafer{elements = map transElement $ elements clafer}

transPExp :: Bool -> PExp -> PExp
transPExp some (PExp t pid pos x) = trans $ PExp t pid pos $ transIExp (fromJust t) x
  where
  trans = if some then desugarPath else id

transIExp :: IType -> IExp -> IExp
transIExp t x = case x of
  IDeclPExp quant decls pexp -> IDeclPExp quant decls $ transPExp False pexp
  IFunExp op exps -> IFunExp op $ map (transPExp cond) exps
    where
    cond = op == iIfThenElse && t `elem` [TBoolean, TClafer []]
  _  -> x
