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
module Intermediate.ResolverType where

import Data.Function

import Common
import Intermediate.Intclafer

resolveTModule :: (IModule, GEnv) -> IModule
resolveTModule (declarations, genv) =
  map (resolveTDeclaration (declarations, genv)) declarations


resolveTDeclaration :: (IModule, GEnv) -> IDeclaration -> IDeclaration
resolveTDeclaration _ x = case x of
  IClaferDecl clafer  -> IClaferDecl $ resolveTClafer clafer
  IConstDecl constraint  -> IConstDecl $ resolveTLExp constraint


resolveTClafer :: IClafer -> IClafer
resolveTClafer clafer =
  clafer {elements = map resolveTElement $ elements clafer}


resolveTElement :: IElement -> IElement
resolveTElement x = case x of
  ISubclafer clafer  -> ISubclafer $ resolveTClafer clafer
  ISubconstraint constraint  -> ISubconstraint $ resolveTLExp constraint


resolveTLExp :: ILExp -> ILExp
resolveTLExp x = case x of
  IEIff lexp0 lexp  -> on IEIff resolveTLExp lexp0 lexp
  IEImpliesElse lexp0 lexp Nothing  -> on (\l0 l -> IEImpliesElse l0 l Nothing)
                                       resolveTLExp lexp0 lexp
  IEImpliesElse lexp0 lexp1 (Just lexp)  ->
      on (\l0 l1 -> IEImpliesElse l0 l1 $ Just $ resolveTLExp lexp)
      resolveTLExp lexp0 lexp1
  IEOr lexp0 lexp  -> on IEOr resolveTLExp lexp0 lexp
  IEXor lexp0 lexp  -> on IEXor resolveTLExp lexp0 lexp
  IEAnd lexp0 lexp  -> on IEAnd resolveTLExp lexp0 lexp
  IENeg lexp  -> IENeg $ resolveTLExp lexp
  IETerm term  -> IETerm $ resolveTTerm term


resolveTTerm :: ITerm -> ITerm
resolveTTerm x = case x of
  ITermCmpExp cmpexp _ -> ITermCmpExp cmpexp $ Just $ resolveTCmpExp cmpexp
  ITermQuantSet quant sexp -> x
  ITermQuantDeclExp decls lexp -> ITermQuantDeclExp decls $ resolveTLExp lexp


resolveTCmpExp :: ICmpExp -> EType
resolveTCmpExp x = case x of
  IELt exp0 exp  -> on resolveT resolveTExp exp0 exp
  IEGt exp0 exp  -> on resolveT resolveTExp exp0 exp
  IEEq exp0 exp  -> on resolveT resolveTExp exp0 exp
  IEREq exp0 exp  -> on resolveT resolveTExp exp0 exp
  IELte exp0 exp  -> on resolveT resolveTExp exp0 exp
  IEGte exp0 exp  -> on resolveT resolveTExp exp0 exp
  IENeq exp0 exp  -> on resolveT resolveTExp exp0 exp
  IERNeq exp0 exp  -> on resolveT resolveTExp exp0 exp
  IEIn exp0 exp  -> on resolveT resolveTExp exp0 exp
  IENin exp0 exp  -> on resolveT resolveTExp exp0 exp


resolveT TAExp TAExp = TAExp
resolveT TSExp TSExp = TSExp
resolveT _ _ = TSAExp


resolveTExp :: IExp -> EType
resolveTExp x = case x of
  IESetExp sexp  -> TSExp
  IENumExp aexp -> TAExp
  IEStrExp strexp -> TAExp
