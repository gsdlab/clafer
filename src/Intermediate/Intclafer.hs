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
      supers :: [ISExp]
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
   ITermCmpExp ICmpExp
 | ITermQuantSet Quant ISExp
 | ITermQuantDeclExp [IDecl] ILExp
  deriving (Eq,Ord,Show)

data ICmpExp =
   IELt IExp IExp
 | IEGt IExp IExp
 | IEREq IExp IExp
 | IEEq IExp IExp
 | IELte IExp IExp
 | IEGte IExp IExp
 | IENeq IExp IExp
 | IERNeq IExp IExp
 | IEIn IExp IExp
 | IENin IExp IExp
  deriving (Eq,Ord,Show)

data IExp =
   IESetExp ISExp
 | IENumExp IAExp
 | IEStrExp StrExp
  deriving (Eq,Ord,Show)

data ISExp =
   ISExpUnion ISExp ISExp
 | ISExpIntersection ISExp ISExp
 | ISExpDomain ISExp ISExp
 | ISExpRange ISExp ISExp
 | ISExpJoin ISExp ISExp
 | ISExpIdent {
      sident :: String,
      isTop :: Bool
    }
  deriving (Eq,Ord,Show)

data IDecl =
   IDecl {
      exquant :: ExQuant,
      isDisj :: Bool,
      decls :: [String],
      body :: ISExp
    }
  deriving (Eq,Ord,Show)

data IAExp =
   IEAdd IAExp IAExp
 | IESub IAExp IAExp
 | IEMul IAExp IAExp
 | IEUmn IAExp
 | IECSetExp ISExp
 | IEInt Integer
  deriving (Eq,Ord,Show)
