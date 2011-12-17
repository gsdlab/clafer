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
module Intermediate.ResolverName where

import List
import Monad
import Data.Maybe
import Control.Monad.State
import Data.Function
import Data.Map (Map)
import qualified Data.Map as Map

import Common
import Front.Absclafer
import Intermediate.Intclafer

data SEnv = SEnv {
  clafers :: [IClafer],
  context :: Maybe IClafer,
  subClafers :: [(IClafer, [IClafer])],
  ancClafers :: [(IClafer, [IClafer])],
  bindings :: [([String], [IClafer])],
  resPath :: [IClafer],
  genv :: GEnv,
  aClafers :: [(IClafer, [IClafer])],
  cClafers :: [(IClafer, [IClafer])]
  } deriving Show


data HowResolved = Special | TypeSpecial | Binding | Subclafers | Ancestor | AbsClafer | TopClafer
  deriving (Eq, Show)


defSEnv genv declarations = env {aClafers = rCl aClafers',
                                 cClafers = rCl cClafers'}
  where
  env = SEnv (toClafers declarations) Nothing [] [] [] [] genv [] []
  rCl cs = bfs toNodeDeep $ map (\c -> env{context = Just c, resPath = [c]}) cs
  (aClafers', cClafers') = partition isAbstract $ clafers env


resolveModuleNames :: (IModule, GEnv) -> IModule
resolveModuleNames (imodule, genv) =
  imodule{mDecls = map (resolveElement (defSEnv genv decls)) decls}
  where
  decls = mDecls imodule


resolveClafer :: SEnv -> IClafer -> IClafer
resolveClafer env clafer =
  clafer {elements = map (resolveElement env'{subClafers = subClafers',
                                              ancClafers = ancClafers'}) $
          elements clafer}
  where
  env' = env {context = Just clafer, resPath = clafer : resPath env}
  subClafers' = tail $ bfs toNodeDeep [env'{resPath = [clafer]}]
  ancestor = last $ resPath env'
  ancClafers' = bfs toNodeDeep
                [env{context = Just ancestor, resPath = [ancestor]}]


resolveElement :: SEnv -> IElement -> IElement
resolveElement env x = case x of
  IEClafer clafer  -> IEClafer $ resolveClafer env clafer
  IEConstraint isHard pexp  -> IEConstraint isHard $ resolvePExp env pexp


resolvePExp :: SEnv -> PExp -> PExp
resolvePExp env (PExp t pid exp) = PExp t pid $ resolveIExp env exp

resolveIExp :: SEnv -> IExp -> IExp
resolveIExp env x = case x of
  IDeclPExp quant decls pexp -> IDeclPExp quant decls' $ resolvePExp env' pexp
    where
    (decls', env') = runState (mapM processDecl decls) env
  IFunExp op exps -> if op == iJoin then resNav else IFunExp op $ map res exps
  IInt n -> x
  IDouble n -> x
  IStr str -> x
  IClaferId _ _ _ -> resNav
  where
  res = resolvePExp env
  resNav = fst $ resolveNav env x True


processDecl decl = do
  env <- get
  let (body', path) = resolveNav env (Intermediate.Intclafer.exp $ body decl) True
  modify (\e -> e { bindings = (decls decl, path) : bindings e })
  return $ decl {body = PExp Nothing "" body'}

resolveNav :: SEnv -> IExp -> Bool -> (IExp, [IClafer])
resolveNav env x isFirst = case x of
  IFunExp _ (pexp0:pexp:_)  ->
    (IFunExp iJoin [PExp Nothing (pid pexp0) exp0', PExp Nothing (pid pexp) exp'], path')
    where
    (exp0', path) = resolveNav env (Intermediate.Intclafer.exp pexp0) True
    (exp', path') = resolveNav env {context = listToMaybe path, resPath = path}
                    (Intermediate.Intclafer.exp pexp) False
  IClaferId modName id _ -> out 
    where
    out
      | isFirst   = mkPath env $ resolveName env id
      | otherwise = (IClaferId modName (snd3 ctx) False, trd3 ctx)
    ctx = resolveImmName env id


mkPath :: SEnv -> (HowResolved, String, [IClafer]) -> (IExp, [IClafer])
mkPath env (howResolved, id, path) = case howResolved of
  Binding -> (mkLClaferId id True, path)
  Special -> (mkLClaferId id True, path)
  TypeSpecial -> (mkLClaferId id True, path)
  Subclafers -> (toNav $ tail $ reverse $ map uid path, path)
  _ -> (toNav' $ reverse $ map uid path, path)
  where
  id'   = mkLClaferId id False
  toNav = foldl
          (\exp id -> IFunExp iJoin [PExp Nothing "" exp, mkPLClaferId id False])
          (mkLClaferId this True)
  toNav' p = (mkIFunExp iJoin $ map (\c -> mkLClaferId c False) p) :: IExp

mkNav (x:[]) = x
mkNav xs = foldl1 (\x y -> IFunExp iJoin $ map (PExp Nothing "") [x, y]) xs

-- -----------------------------------------------------------------------------

resolveName :: SEnv -> String -> (HowResolved, String, [IClafer])
resolveName env id = resolve env id
  [resolveSpecial, resolveBind, resolveSubclafers, resolveAncestor, resolveTopLevel, resolveNone]


resolveImmName :: SEnv -> String -> (HowResolved, String, [IClafer])
resolveImmName env id = resolve env id
  [resolveImmSubclafers, resolveNone]


resolve env id fs = fromJust $ foldr1 mplus $ map (\x -> x env id) fs


-- reports error if clafer not found
resolveNone env id = error $ id ++ " not found"
   -- within " ++ (show $ context env >>= (Just . ident)) ++ show env


-- checks if ident is one of special identifiers
resolveSpecial :: SEnv -> String -> Maybe (HowResolved, String, [IClafer])
resolveSpecial env id
  | id `elem` [this, children] =
      Just (Special, id, (fromJust $ context env) : resPath env)
  | id == parent = Just (Special, id, resPath env)
  | isPrimitive id = Just (TypeSpecial, id, [])
  | otherwise      = Nothing 


-- checks if ident is bound locally
resolveBind :: SEnv -> String -> Maybe (HowResolved, String, [IClafer])
resolveBind env id = find (\bs -> id `elem` fst bs) (bindings env) >>=
  (\x -> Just (Binding, id, snd x))


-- searches for a name in all subclafers (BFS)
resolveSubclafers :: SEnv -> String -> Maybe (HowResolved, String, [IClafer])
resolveSubclafers env id = -- if null (subClafers env) then error $ uid $  else
  (context env) >> (findUnique id $ subClafers env) >>= (toMTriple Subclafers)


-- searches for a name in immediate subclafers (BFS)
resolveImmSubclafers :: SEnv -> String -> Maybe (HowResolved, String, [IClafer])
resolveImmSubclafers env id =
  (context env) >> (findUnique id $ map (\x -> (x, [x,fromJust $ context env]))
                    $ allSubclafers env) >>= toMTriple Subclafers


resolveAncestor :: SEnv -> String -> Maybe (HowResolved, String, [IClafer])
resolveAncestor env id = context env >> (findUnique id $ ancClafers env) >>=
                         toMTriple Ancestor


-- searches for a feature starting from local root (BFS) and then continues with
-- other declarations
resolveTopLevel :: SEnv -> String -> Maybe (HowResolved, String, [IClafer])
resolveTopLevel env id = foldr1 mplus $ map
  (\(cs, hr) -> findUnique id cs >>= toMTriple hr)
  [(aClafers env, AbsClafer), (cClafers env, TopClafer)]


toNodeDeep env
  | length (clafer `elemIndices` resPath env) > 1 = (result, [])
  | otherwise = (result, map (\c -> env {context = Just c,
                                         resPath = c : resPath env}) $
                 allSubclafers env)
  where
  result = (clafer, resPath env)
  clafer = fromJust $ context env
  

allSubclafers env = getSubclafers $ concat $
                    mapHierarchy elements (sClafers $ genv env)
                    (fromJust $ context env)


findUnique :: String -> [(IClafer, [IClafer])] -> Maybe (String, [IClafer])
findUnique x xs =
  case filter (((==) x).ident.fst) xs of
    []     -> Nothing
    [elem] -> Just $ (uid $ fst elem, snd elem)
    _      -> error $ "element is not unique : " ++ show x ++ ". Available paths: " ++ ((filter (((==) x).ident.fst) xs) >>= (show.(map uid).snd))
