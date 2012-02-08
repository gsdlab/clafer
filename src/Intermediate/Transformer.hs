{-
 This file is part of the Clafer Translator (clafer).

 Copyright (C) 2010 Kacper Bak <http://gsd.uwaterloo.ca/kbak>

 clafer is free software: you can redistribute it and/or modify
 it under the terms of the GNU Lesser General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 clafer is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU Lesser General Public License for more details.

 You should have received a copy of the GNU Lesser General Public License
 along with clafer. (See files COPYING and COPYING.LESSER.)  If not,
 see <http://www.gnu.org/licenses/>.
-}
module Intermediate.Transformer where
import Data.Maybe
import Common
import Intermediate.Intclafer
import Intermediate.Desugarer

transModule imodule = imodule{mDecls = map transElement $ mDecls imodule}

transElement :: IElement -> IElement
transElement x = case x of
  IEClafer clafer  -> IEClafer $ transClafer clafer
  IEConstraint isHard pexp  -> IEConstraint isHard $ transPExp False pexp

transClafer :: IClafer -> IClafer
transClafer clafer = clafer{elements = map transElement $ elements clafer}

transPExp :: Bool -> PExp -> PExp
transPExp some (PExp t pid x) = trans $ PExp t pid $ transIExp (fromJust t) x
  where
  trans = if some then desugarPath else id

transIExp :: IType -> IExp -> IExp
transIExp t x = case x of
  IDeclPExp quant decls pexp -> IDeclPExp quant decls $ transPExp False pexp
  IFunExp op exps -> IFunExp op $ map (transPExp cond) exps
    where
    cond = op == iIfThenElse && t `elem` [TBoolean, TClafer]
  _  -> x
