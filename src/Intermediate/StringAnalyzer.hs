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


applyExps f mf ls = f `liftM` mapM mf ls
apply2 cons (x1:x2:[]) = cons x1 x2

astrTerm x = case x of
  ITermCmpExp cmpexp -> ITermCmpExp `liftM` astrCmpExp cmpexp
  ITermQuantDeclExp decls lexp -> ITermQuantDeclExp decls `liftM` astrLExp lexp 
  _ -> return x


astrCmpExp x = case x of
  IELt exp0 exp  -> ae IELt [exp0, exp]
  IEGt exp0 exp  -> ae IEGt [exp0, exp]
  IEREq exp0 exp -> ae IEREq [exp0, exp]
  IEEq exp0 exp  -> ae IEEq [exp0, exp]
  IELte exp0 exp  -> ae IELte [exp0, exp]
  IEGte exp0 exp  -> ae IEGte [exp0, exp]
  IENeq exp0 exp  -> ae IENeq [exp0, exp]
  IERNeq exp0 exp -> ae IERNeq [exp0, exp]
  IEIn exp0 exp   -> ae IEIn  [exp0, exp]
  IENin exp0 exp  -> ae IENin [exp0, exp]
  where
  ae cons ls = applyExps (apply2 cons) astrExp ls


astrExp x = case x of
  IEStrExp (EStr string) -> do
    modify (\e -> Map.insertWith const string (Map.size e) e)
    st <- get
    return $ IENumExp $ IEInt $ toInteger $ (Map.!) st string
  IEStrExp conc -> astrExp $ IEStrExp $ concatStrExp conc
  _ -> return x


concatStrExp :: StrExp -> StrExp
concatStrExp x = case x of
  EConc strexp0 strexp -> EStr $ str0 ++ str
    where
    EStr str0 = concatStrExp strexp0
    EStr str  = concatStrExp strexp
  EStr string -> x
