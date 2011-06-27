module Intermediate.StringAnalyzer where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

import Front.Absclafer
import Intermediate.Intclafer

astrModule :: IModule -> IModule
astrModule declarations =
  evalState (mapM astrDeclaration declarations) $ Map.empty

astrDeclaration x = case x of
  IClaferDecl clafer -> IClaferDecl `liftM` astrClafer clafer
  IConstDecl lexp -> IConstDecl `liftM` astrLExp lexp


astrClafer x = case x of
  IClafer isAbstract gcard ident uid super card elements  ->
    IClafer isAbstract gcard ident uid super card `liftM`
            mapM astrElement elements


-- astrs single subclafer
astrElement x = case x of
  ISubclafer clafer -> ISubclafer `liftM` astrClafer clafer
  ISubconstraint lexp -> ISubconstraint `liftM` astrLExp lexp


astrLExp x = case x of
  IEIff lexp0 lexp  -> ale IEIff [lexp0, lexp]
  IEImpliesElse lexp0 lexp Nothing ->
    applyExps (\(l0:l:[]) -> IEImpliesElse l0 l Nothing) astrLExp [lexp0, lexp]
  IEImpliesElse lexp0 lexp1 (Just lexp)  ->
    applyExps (\(l0:l1:l:[]) -> IEImpliesElse l0 l1 $ Just l) astrLExp
                  [lexp0, lexp1, lexp]
  IEOr lexp0 lexp  -> ale IEOr [lexp0, lexp]
  IEXor lexp0 lexp  -> ale IEXor [lexp0, lexp]
  IEAnd lexp0 lexp  -> ale IEAnd [lexp0, lexp]
  IENeg lexp  -> IENeg `liftM` astrLExp lexp
  IETerm term  -> IETerm `liftM` astrTerm term
  where
  ale cons ls = applyExps (apply2 cons) astrLExp ls
  apply2 cons (x1:x2:[])    = cons x1 x2


applyExps f mf ls = f `liftM` mapM mf ls


astrTerm x = case x of
  ITermCmpExp cmpexp -> ITermCmpExp `liftM` astrCmpExp cmpexp
  ITermQuantDeclExp decls lexp -> ITermQuantDeclExp decls `liftM` astrLExp lexp 
  _ -> return x


astrCmpExp x = case x of
  ELt exp0 exp  -> ae ELt [exp0, exp]
  EGt exp0 exp  -> ae EGt [exp0, exp]
  EREq exp0 exp -> ae EREq [exp0, exp]
  EEq exp0 exp  -> ae EEq [exp0, exp]
  ELte exp0 exp  -> ae ELte [exp0, exp]
  EGte exp0 exp  -> ae EGte [exp0, exp]
  ENeq exp0 exp  -> ae ENeq [exp0, exp]
  ERNeq exp0 exp -> ae ERNeq [exp0, exp]
  EIn exp0 exp   -> ae EIn  [exp0, exp]
  ENin exp0 exp  -> ae ENin [exp0, exp]
  where
  ae cons ls = applyExps (apply2 cons) astrExp ls
  apply2 cons (x1:x2:[]) = cons x1 x2


astrExp x = case x of
  EStrExp (EStr string) -> do
    modify (\e -> Map.insertWith const string (Map.size e) e)
    st <- get
    return $ ENumExp $ EInt $ toInteger $ (Map.!) st string
  EStrExp conc -> astrExp $ EStrExp $ concatStrExp conc


concatStrExp :: StrExp -> StrExp
concatStrExp x = case x of
  EConc strexp0 strexp -> EStr $ str0 ++ str
    where
    EStr str0 = concatStrExp strexp0
    EStr str  = concatStrExp strexp
  EStr string -> x
