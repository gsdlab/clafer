{-
 Copyright (C) 2012-2014 Kacper Bak, Jimmy Liang, Luke Brown <http://gsd.uwaterloo.ca>

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
module Language.Clafer.Intermediate.StringAnalyzer where

import Data.Tuple
import qualified Data.Map as Map
import Control.Monad.State

import Language.Clafer.Intermediate.Intclafer

-- | Convert all strings into ints for analysis
-- | Return an inverse map from ints back to strings
astrModule :: IModule -> (IModule, Map.Map Int String)
astrModule    imodule = (imodule{_mDecls = decls''}, flipMap strMap')
  where
    decls' = _mDecls imodule
    (decls'', strMap') = runState (mapM astrElement decls') Map.empty

    flipMap :: Map.Map String Int -> Map.Map Int String
    flipMap = Map.fromList . map swap . Map.toList

astrClafer :: IClafer -> State (Map.Map String Int) IClafer
astrClafer (IClafer muid s isAbs gcrd ident' super' crd gCard es) =
    IClafer muid s isAbs gcrd ident' super' crd gCard `liftM` mapM astrElement es

-- astrs single subclafer
astrElement :: IElement -> State (Map.Map String Int) IElement
astrElement x = case x of
  IEClafer clafer         -> IEClafer `liftM` astrClafer clafer
  IEConstraint constraint -> IEConstraint `liftM` astrConstraint constraint
  IEGoal goal             -> IEGoal `liftM` astrGoal goal

astrConstraint :: IConstraint -> State (Map.Map String Int) IConstraint
astrConstraint (IConstraint muid isHard' pexp) = IConstraint muid isHard' `liftM` astrPExp pexp

astrGoal :: IGoal -> State (Map.Map String Int) IGoal
astrGoal (IGoal muid isMaximize' pexp) = IGoal muid isMaximize' `liftM` astrPExp pexp

astrPExp :: PExp -> State (Map.Map String Int) PExp
astrPExp (PExp muid iType' pos' (IFunExp op' exps')) = PExp muid iType' pos' `liftM`
                              (IFunExp op' `liftM` mapM astrPExp exps')
astrPExp (PExp muid iType' pos' (IDeclPExp quant' oDecls' bpexp')) = PExp muid iType' pos' `liftM`
                              (IDeclPExp quant' oDecls' `liftM` (astrPExp bpexp'))
astrPExp x = return x

astrIExp :: IExp -> State (Map.Map String Int) IExp
astrIExp x = case x of
  IFunExp op' exps' -> IFunExp op' `liftM` mapM astrPExp exps'
  IStr str -> do
    modify (\e -> Map.insertWith (flip const) str (Map.size e) e)
    st <- get
    return $  (IInt $ toInteger $ (Map.!) st str)
  _ -> return x