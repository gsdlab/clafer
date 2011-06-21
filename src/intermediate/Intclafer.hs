module Intclafer where

import Absclafer

data IModule =
   IModule [IDeclaration]
  deriving (Eq,Ord,Show)

data IDeclaration =
   IClaferDecl IClafer
 | IConstDecl [ILExp]
  deriving (Eq,Ord,Show)

data IClafer =
   IClafer {
      isAbstract :: Bool,
      gcard :: Interval,
      ident :: String,
      super:: ISuper,
      card :: Interval,
      elements :: [IElement]
    }
  deriving (Eq,Ord,Show)

data IElement =
   Subclafer Clafer
 | Subconstraint [ILExp]
  deriving (Eq,Ord,Show)

data ISuper =
   ISuper {
      isOverlapping :: Bool,
      supers :: [SExp]
    }
  deriving (Eq,Ord,Show)

data Interval =
   Interval Integer ExInteger
  deriving (Eq,Ord,Show)

data ILExp =
   IEIff ILExp ILExp
 | IEImpliesElse ILExp ILExp ILExp
 | IEOr ILExp ILExp
 | IEXor ILExp ILExp
 | IEAnd ILExp ILExp
 | IENeg ILExp
 | ITerm Term
  deriving (Eq,Ord,Show)

data ITerm =
   ITermCmpExp CmpExp
 | ITermQuantSet Quant SExp
 | ITermQuantDeclExp [Decl] ILExp
  deriving (Eq,Ord,Show)