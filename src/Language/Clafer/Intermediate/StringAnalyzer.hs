{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

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
import Control.Monad.Writer

import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer

astrModule :: IModule -> Writer (Map Int String) IModule
--astrModule :: IModule -> IModule
astrModule imodule = do
  let elementsState = (mapM astrElement decls) 
  let strMap = execState elementsState $ Map.empty
  returnVal <- (return $ imodule{mDecls = evalState elementsState $ Map.empty}) :: Writer (Map Int String) IModule
  tell (flipMap $ strMap)
  return $ returnVal
  where
    flipMap :: (Map String Int) -> (Map Int String)
    flipMap = Map.fromList . map swap . Map.toList
    decls = mDecls imodule



--astrClafer :: MonadState (Map String Int) m => IClafer -> m IClafer
astrClafer x = case x of
  IClafer s isAbstract gcard ident uid super card gCard elements  ->
    IClafer s isAbstract gcard ident uid super card gCard `liftM`
            mapM astrElement elements


-- astrs single subclafer
--astrElement :: MonadState (Map String Int) m => IElement -> m IElement
astrElement x = case x of
  IEClafer clafer -> IEClafer `liftM` astrClafer clafer
  IEConstraint isHard pexp -> IEConstraint isHard `liftM` astrPExp pexp
  IEGoal isMaximize pexp -> IEGoal isMaximize `liftM` astrPExp pexp

--astrPExp :: MonadState (Map String Int) m => PExp -> m PExp
astrPExp x = case x of 
  PExp (Just TString) pid pos exp ->
    PExp (Just TInteger) pid pos `liftM` astrIExp exp
  PExp t pid pos (IFunExp op exps) -> PExp t pid pos `liftM`
                              (IFunExp op `liftM` mapM astrPExp exps)
  PExp t pid pos (IDeclPExp quant oDecls bpexp) -> PExp t pid pos `liftM`
                              (IDeclPExp quant oDecls `liftM` (astrPExp bpexp))
  _ -> return x

--astrIExp :: MonadState (Map String Int) m => IExp -> m IExp
astrIExp x = case x of
  IFunExp op exps -> if op == iUnion
                     then astrIExp $ concatStrExp x else return x                    
  IStr str -> do
    modify (\e -> Map.insertWith (flip const) str (Map.size e) e)
    st <- get
    --lift $ tell $ Map.singleton (toInteger $ (Map.!) st str) str 
    return $  (IInt $ toInteger $ (Map.!) st str)
     
  _ -> return x


concatStrExp :: IExp -> IExp
concatStrExp x = case x of
  IFunExp _ exps -> IStr $ s0 ++ s1 
    where
    ((IStr s0):(IStr s1):_) = map concatStrExp $ map (Language.Clafer.Intermediate.Intclafer.exp) exps
  IStr string -> x
  _ -> x