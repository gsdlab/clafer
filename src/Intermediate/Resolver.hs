module Intermediate.Resolver where

import List
import Monad
import Data.Maybe
import Control.Monad.State

import Common
import Front.Absclafer
import Intermediate.Intclafer



resolveModule :: IModule -> IModule
resolveModule declarations = resolveSuperModule $ nameModule declarations

-- -----------------------------------------------------------------------------
data NEnv = NEnv {num :: Int}

nameModule :: IModule -> IModule
nameModule declarations = evalState (mapM nameDeclaration declarations) (NEnv 0)


nameDeclaration x = case x of
  IClaferDecl clafer  -> IClaferDecl `liftM` (nameClafer clafer)
  IConstDecl constraint  -> return x


nameClafer clafer = do
  modify (\e -> e {num = 1 + num e})
  n <- gets num
  elements' <- mapM nameElement $ elements clafer
  return $ clafer
    {uid = concat ["cl", show n, "_",  ident clafer], elements = elements'}


nameElement x = case x of
  ISubclafer clafer -> ISubclafer `liftM` (nameClafer clafer)
  ISubconstraint ilexp -> return x


-- -----------------------------------------------------------------------------
resolveSuperModule :: IModule -> IModule
resolveSuperModule declarations =
  map (resolveSuperDeclaration declarations) declarations


resolveSuperDeclaration :: IModule -> IDeclaration -> IDeclaration
resolveSuperDeclaration declarations x = case x of
  IClaferDecl clafer  -> IClaferDecl $ resolveSuperClafer declarations clafer
  IConstDecl constraint  -> x


resolveSuperClafer :: IModule -> IClafer -> IClafer
resolveSuperClafer declarations clafer =
  clafer {super = resolveSuperSuper declarations $ super clafer,
          elements = map (resolveSuperElement declarations) $ elements clafer}


resolveSuperSuper :: IModule -> ISuper -> ISuper
resolveSuperSuper declarations x = case x of
  ISuper False [SExpIdent id] -> ISuper False [SExpIdent $ Ident id']
    where
    id' = case resolveSuper declarations $ transIdent id of
            Just a -> a
            _ -> error "No superclafer found"
  _ -> x


resolveSuperElement :: IModule -> IElement -> IElement
resolveSuperElement declarations x = case x of
  ISubclafer clafer  -> ISubclafer $ resolveSuperClafer declarations clafer
  ISubconstraint constraint  -> x


resolveSuper :: IModule -> String -> Maybe String
resolveSuper declarations id = findUnique id $ filter isAbstract $
  bfsClafers (toClafers declarations)


findUnique :: String -> [IClafer] -> Maybe String
findUnique x xs =
  case filter (((==) x).ident) xs of
    []     -> Nothing
    [elem] -> Just $ uid elem
    _      -> error $ "element is not unique : " ++ show x

-- -----------------------------------------------------------------------------
data SEnv = SEnv {
  clafers :: [IClafer],
  context :: Maybe IClafer,
  bindings :: [String]
  } deriving Show


toNodeDeep env = (clafer, map (\c -> env {context = Just c}) allClafers)
  where
  clafer     = fromJust $ context env
  allClafers = mapMaybe elemToClafer $ concat $
               mapHierarchy elements (clafers env) clafer


resolvePathModule :: IModule -> IModule
resolvePathModule declarations =
  map (resolvePathDeclaration declarations) declarations


resolvePathDeclaration = undefined

resolvePath :: SEnv -> String -> Maybe String
resolvePath env id = undefined


-- checks if ident is one of special identifiers
resolveSpecial :: SEnv -> String -> Maybe String
resolveSpecial _ id
  | id `elem` [this, strType, intType, parent, children] = Just id
  | otherwise                                            = Nothing 


-- checks if ident is bound locally
resolveBind :: SEnv -> String -> Maybe String
resolveBind env id = find (== id) (bindings env)


-- searches for a name in subclafers (BFS)
resolveSubclafers :: SEnv -> String -> Maybe String
resolveSubclafers env id =
  (context env) >> (findUnique id $ tail $ bfs toNodeDeep [env])
