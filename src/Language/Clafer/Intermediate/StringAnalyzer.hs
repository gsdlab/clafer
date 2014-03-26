{-# LANGUAGE RankNTypes, KindSignatures ,FlexibleContexts #-}
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

import Data.Map (Map)
import Data.Tuple
import qualified Data.Map as Map
import Control.Monad.State

import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer

-- | Convert all strings into ints for analysis
-- | Return an inverse map from ints back to strings
astrModule :: IModule -> (IModule, Map Int String)
astrModule imodule = (imodule{_mDecls = decls''}, flipMap strMap')
  where
    decls' = _mDecls imodule
    (decls'', strMap') = runState (mapM astrElement decls') Map.empty

    flipMap :: Map String Int -> Map Int String
    flipMap = Map.fromList . map swap . Map.toList


astrClafer :: MonadState (Map String Int) m => IClafer -> m IClafer
astrClafer (IClafer s isAbs gcrd ident' uid' super' crd gCard es) =
    IClafer s isAbs gcrd ident' uid' super' crd gCard `liftM` mapM astrElement es


-- astrs single subclafer
astrElement :: MonadState (Map String Int) m => IElement -> m IElement
astrElement x = case x of
  IEClafer clafer -> IEClafer `liftM` astrClafer clafer
  IEConstraint isHard' pexp -> IEConstraint isHard' `liftM` astrPExp pexp
  IEGoal isMaximize' pexp -> IEGoal isMaximize' `liftM` astrPExp pexp

astrPExp :: MonadState (Map String Int) m => PExp -> m PExp
astrPExp (PExp (Just TString) pid' pos' exp') =
    PExp (Just TInteger) pid' pos' `liftM` astrIExp exp'
astrPExp (PExp t pid' pos' (IFunExp op' exps')) = PExp t pid' pos' `liftM`
                              (IFunExp op' `liftM` mapM astrPExp exps')
astrPExp (PExp t pid' pos' (IDeclPExp quant' oDecls' bpexp')) = PExp t pid' pos' `liftM`
                              (IDeclPExp quant' oDecls' `liftM` (astrPExp bpexp'))
astrPExp x = return x

astrIExp :: MonadState (Map String Int) m => IExp -> m IExp
astrIExp x = case x of
  IFunExp op' _ -> if op' == iUnion
                     then astrIExp $ concatStrExp x else return x                    
  IStr str -> do
    modify (\e -> Map.insertWith (flip const) str (Map.size e) e)
    st <- get
    --lift $ tell $ Map.singleton (toInteger $ (Map.!) st str) str 
    return $  (IInt $ toInteger $ (Map.!) st str)
     
  _ -> return x


concatStrExp :: IExp -> IExp
concatStrExp x = case x of
  IFunExp _ exps' -> IStr $ s0 ++ s1 
    where
    ((IStr s0):(IStr s1):_) = map concatStrExp $ map (Language.Clafer.Intermediate.Intclafer._exp) exps'
  IStr _ -> x
  _ -> x