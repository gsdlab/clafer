module Intermediate.Intclafer where

import Front.Absclafer

type IModule = [IDeclaration]

data IDeclaration =
   IClaferDecl IClafer
 | IConstDecl ILExp
  deriving (Eq,Ord,Show)

data IClafer =
   IClafer {
      isAbstract :: Bool,
      gcard :: Maybe IGCard,
      ident :: String,
      uid :: String,
      super:: ISuper,
      card :: Maybe Interval,
      elements :: [IElement]
    }
  deriving (Eq,Ord,Show)

data IElement =
   ISubclafer IClafer
 | ISubconstraint ILExp
  deriving (Eq,Ord,Show)

data ISuper =
   ISuper {
      isOverlapping :: Bool,
      supers :: [SExp]
    }
  deriving (Eq,Ord,Show)

data IGCard =
  IGCard {
      isKeyword :: Bool,
      interval :: Interval
    }
  deriving (Eq,Ord,Show)

type Interval = (Integer, ExInteger)

data ILExp =
   IEIff ILExp ILExp
 | IEImpliesElse ILExp ILExp (Maybe ILExp)
 | IEOr ILExp ILExp
 | IEXor ILExp ILExp
 | IEAnd ILExp ILExp
 | IENeg ILExp
 | IETerm ITerm
  deriving (Eq,Ord,Show)

data ITerm =
   ITermCmpExp CmpExp
 | ITermQuantSet Quant SExp
 | ITermQuantDeclExp [Decl] ILExp
  deriving (Eq,Ord,Show)