{-# LANGUAGE FlexibleContexts #-}
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
module Language.Clafer.Intermediate.Resolver where

import Data.Maybe
import Data.Monoid
import Data.List
import Data.Function (on)
import Data.Foldable (foldMap)
import Control.Monad
import Control.Monad.State
import qualified Data.Map as Map

import Language.ClaferT
import Language.Clafer.Common
import Language.Clafer.ClaferArgs
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.ResolverName
import Language.Clafer.Intermediate.ResolverType
import Language.Clafer.Intermediate.ResolverInheritance

resolveModule :: Map.Map Span IClafer -> ClaferArgs -> IModule -> Resolve (IModule, GEnv)
resolveModule pMap args' declarations =
  do
    let (iMod', genv') = nameModule (skip_resolver args') declarations
    let clafs = bfsClafers $ toClafers $ mDecls iMod'
    let iMod = forIR iMod' $ reDefAdd clafs pMap
    let failList = foldMapIR getFails iMod
    if (failList /= []) then 
      Left $ (ClaferErr $ unlines $ "Improper redefinition for cardinalities at," : failList :: ClaferSErr) 
        else resolveNamesModule args' =<< (rom' . rem') =<< 
          resolveNModule pMap (iMod, genv')
  where
  rem' :: (IModule, GEnv) -> (IModule, GEnv)
  rem' = if flatten_inheritance args' then resolveEModule else id
  rom' :: (IModule, GEnv) -> Resolve (IModule, GEnv)
  rom' = if skip_resolver args' then return . id else resolveOModule

  getFails :: Ir -> [String]
  getFails (IRClafer (IClafer{super = ISuper{superKind = RedefinitionFail str}})) = [str]
  getFails _ = mempty

  reDefAdd :: [IClafer] -> Map.Map Span IClafer -> Ir -> Ir
  reDefAdd clafs parMap i@(IRClafer claf) = 
    let ranks = flip foldMap clafs $ \x -> if (istop $ cinPos claf) then mempty else getReDefRank x x claf 
    in if (ranks==[]) then i else 
      let c = fst $ minimumBy (compare `on` snd) ranks
      in if (isSpecifiedCard c claf) then 
        IRClafer $ claf{super = ISuper (Redefinition c) [PExp (Just $ TClafer []) "" noSpan (IClaferId "" (ident c) $ istop $ cinPos c)]}
          else IRClafer $ claf{super = (super claf){superKind = (RedefinitionFail $ getErrMsg (cinPos claf) $ cinPos c)}} 
    where
      getReDefRank :: IClafer -> IClafer -> IClafer -> [(IClafer, Integer)]
      getReDefRank oClaf claf1 claf2 =
        let par1 = flip Map.lookup parMap $ cinPos claf1
            par2 = flip Map.lookup parMap $ cinPos claf2
        in if (par1==Nothing && par2==Nothing) then 
          (let depth = recursiveCheck 1 claf1 claf2
           in if (depth==0) then mempty else [(oClaf, depth)])
          else if (par1==Nothing || par2==Nothing) 
            then mempty else if (ident claf1 == ident claf2) 
              then getReDefRank oClaf (fromJust par1) $ fromJust par2
                else mempty
        where
        recursiveCheck :: Integer -> IClafer -> IClafer -> Integer
        recursiveCheck acc c1 c2 = 
          let match = flip find clafs $ (== getSuper c2) . ident
          in if (ident c1 == getSuper c2) then acc
            else if (match == Nothing) then 0
              else recursiveCheck (acc+1) c1 $ fromJust match
          
      isSpecifiedCard :: IClafer -> IClafer -> Bool
      isSpecifiedCard claf1 claf2 = 
        (card claf2 `withinCard` card claf1) && (gcard claf2 `withinGCard` gcard claf1)
        where
          withinCard (Just (x2,y2)) (Just (x1,y1)) = x1 `lt` x2 && y1 `gt` y2
          withinCard Nothing (Just (x1,y1)) = x1 `lt` 1 && y1 `gt` 1
          withinCard (Just (x2,y2)) Nothing = 1 `lt` x2 && 1 `gt` y2
          withinCard _ _ = True
          withinGCard (Just (IGCard _ (x2,y2))) (Just (IGCard _ (x1,y1))) = x1 `lt` x2 && y1 `gt` y2
          withinGCard Nothing (Just (IGCard _ (x1,y1))) = x1 `lt` 0 && y1 `gt` (-1)
          withinGCard (Just (IGCard _ (x2,y2))) Nothing = 0 `lt` x2 && (-1) `gt` y2
          withinGCard _ _ = True
          lt x y = if (x == -1) then (y == -1) else if (y == -1) then True else x <= y
          gt x y = (not $ x `lt` y) || x==y
      getErrMsg :: Span -> Span -> String
      getErrMsg (Span (Pos l1 c1) _) (Span (Pos l2 c2) _) = 
        "line " ++ show l1 ++ " coloum " ++ show c1 ++ " redefining the clafer at line " ++ show l2 ++ " coloum " ++ show c2
      getErrMsg s1 s2 = 
        "span " ++ show s1 ++" redefining the clafer at span " ++ show s2
  reDefAdd _ _ i = i


-- -----------------------------------------------------------------------------
nameModule :: Bool -> IModule -> (IModule, GEnv)
nameModule skipResolver imodule = (imodule{mDecls = decls'}, genv')
  where
  (decls', genv') = runState (mapM (nameElement skipResolver) $ mDecls imodule) $ GEnv 0 Map.empty []

nameElement :: MonadState GEnv m => Bool -> IElement -> m IElement
nameElement skipResolver x = case x of
  IEClafer claf -> IEClafer `liftM` (nameClafer skipResolver claf)
  IEConstraint isHard' pexp -> IEConstraint isHard' `liftM` (namePExp pexp)
  IEGoal isMaximize' pexp -> IEGoal isMaximize' `liftM` (namePExp pexp)


nameClafer :: MonadState GEnv m => Bool -> IClafer -> m IClafer
nameClafer skipResolver claf = do
  claf' <- if skipResolver then return claf{uid = ident claf} else (renameClafer (not skipResolver)) claf
  elements' <- mapM (nameElement skipResolver) $ elements claf
  return $ claf' {elements = elements'}


namePExp :: MonadState GEnv m => PExp -> m PExp
namePExp pexp@(PExp _ _ _ exp') = do
  pid' <- genId "exp"
  exp'' <- nameIExp exp'
  return $ pexp {pid = pid', Language.Clafer.Intermediate.Intclafer.exp = exp''}

nameIExp :: MonadState GEnv m => IExp -> m IExp
nameIExp x = case x of
  IDeclPExp quant' decls' pexp -> do
    decls'' <- mapM nameIDecl decls'
    pexp'  <- namePExp pexp
    return $ IDeclPExp quant' decls'' pexp'
  IFunExp op' pexps -> IFunExp op' `liftM` (mapM namePExp pexps)
  _ -> return x

nameIDecl :: MonadState GEnv m => IDecl -> m IDecl
nameIDecl (IDecl isDisj' dels body') = IDecl isDisj' dels `liftM` (namePExp body')

-- -----------------------------------------------------------------------------
resolveNamesModule :: ClaferArgs -> (IModule, GEnv) -> Resolve (IModule, GEnv)
resolveNamesModule args' (declarations, genv') =
  do
    res <- foldM (flip ($)) declarations $ map (\f -> flip (curry f) genv') funs
    return (res, genv')
  where
  funs :: [(IModule, GEnv) -> Resolve IModule]
  funs
    | skip_resolver args' = [return . analyzeModule, resolveTModule]
    | otherwise = [ return . analyzeModule, resolveModuleNames, resolveTModule]
