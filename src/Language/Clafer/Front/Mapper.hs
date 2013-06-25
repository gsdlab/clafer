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
module Language.Clafer.Front.Mapper (mapModule, Mappable(..)) where

import Language.Clafer.Front.Absclafer


mapModule :: Module -> Module
mapModule = mapNode


(>-) :: Span -> Span -> Span
(>-) (Span (Pos 0 0) (Pos 0 0)) s = s
(>-) r (Span (Pos 0 0) (Pos 0 0)) = r
(>-) (Span m _) (Span _ p) = Span m p
(>-) _ _ = error "Function '>-' was not given (Span (Pos 0 0) (Pos 0 0)) as one of it's argumented expected one argument of (Span (Pos 0 0) (Pos 0 0))"

doMap :: Mappable n => (Span -> n -> t) -> n -> t
doMap f e =
  f (range e') e'
  where
  e' = mapNode e

doMapWithSpan :: Mappable n => (Span -> n -> t) -> Span -> n -> t
doMapWithSpan f s e = 
  f (s >- range e') e'
  where
  e' = mapNode e

doMap2 :: (Mappable n, Mappable n1) => (Span -> n -> n1 -> t) -> n -> n1 -> t
doMap2 f d e =
  f (range d' >- range e') d' e'
  where
  d' = mapNode d
  e' = mapNode e

doMap2WithSpan :: (Mappable n, Mappable n1) => (Span -> n -> n1 -> t) -> Span -> n -> n1 -> t
doMap2WithSpan f s d e =
  f (s >- range d' >- range e') d' e'
  where
  d' = mapNode d
  e' = mapNode e

doMap3 :: (Mappable n, Mappable n1, Mappable n2) => (Span -> n -> n1 -> n2 -> t) -> n -> n1 -> n2 -> t
doMap3 f c d e =
  f (range c' >- range d' >- range e') c' d' e'
  where
  c' = mapNode c
  d' = mapNode d
  e' = mapNode e

doMap3WithSpan :: (Mappable n, Mappable n1, Mappable n2) => (Span -> n -> n1 -> n2 -> t) -> Span -> n -> n1 -> n2 -> t
doMap3WithSpan f s c d e =
  f (s >- range c' >- range d' >- range e') c' d' e'
  where
  c' = mapNode c
  d' = mapNode d
  e' = mapNode e

doMap7 :: (Mappable n, Mappable n1, Mappable n2, Mappable n3, Mappable n4, Mappable n5, Mappable n6) => (Span -> n -> n1 -> n2 -> n3 -> n4 -> n5 -> n6 -> t) -> n -> n1 -> n2 -> n3 -> n4 -> n5 -> n6 -> t
doMap7 f t u v w x y z =
  f (range t' >- range u' >- range v' >- range w' >- range x' >- range y' >- range z') t' u' v' w' x' y' z'
  where
  t' = mapNode t
  u' = mapNode u
  v' = mapNode v
  w' = mapNode w
  x' = mapNode x
  y' = mapNode y
  z' = mapNode z


class Mappable n where
  mapNode :: n -> n
  range :: n -> Span
  
  
instance Mappable s => Mappable [s] where
  mapNode = map mapNode
  range = foldr (>-) noSpan . map range


instance Mappable Module where
  mapNode (Module d) = doMap PosModule d
  mapNode x = errMsgM "(Module d)" x 
  range (PosModule s _) = s
  range x = errMsgR "(PosModule s _)" x


instance Mappable Declaration where
  mapNode (PosEnumDecl s p e) = doMap2WithSpan PosEnumDecl s p e
  mapNode (ElementDecl e)     = doMap PosElementDecl e
  mapNode x = errMsgM "(PosEnumDecl s p e) or ElementDecl e)" x 
  range (PosEnumDecl s _ _)  = s
  range (PosElementDecl s _) = s
  range x = errMsgR "(PosEnumDecl s p e) or (PosElementDecl s e)" x


instance Mappable Elements where
  mapNode ElementsEmpty         = PosElementsEmpty noSpan
  -- The span is inaccurate for some apparent reason. Not sure why yet.
  mapNode (PosElementsList _ e) = doMap PosElementsList e --doMapWithSpan PosElementsList s e
  mapNode x = errMsgM "ElementsEmpty or (PosElementsList s e)" x
  range (PosElementsEmpty s)  = s
  range (PosElementsList s _) = s
  range x = errMsgR "(PosElementsEmpty s) or (PosElementsList s _)" x


instance Mappable Element where
  mapNode (Subclafer c)          = doMap PosSubclafer c
  mapNode (PosClaferUse s n c e) = doMap3WithSpan PosClaferUse s n c e
  mapNode (Subconstraint c)      = doMap PosSubconstraint c
  mapNode (Subgoal g)            = doMap PosSubgoal g
  mapNode (Subsoftconstraint c)  = doMap PosSubsoftconstraint c
  mapNode x = errMsgM "(Subclafer c), (PosClaferUse s n c e), (Subconstraint c), (Subgoal g), or (Subsoftconstraint c)" x
  range (PosSubclafer s _)         = s
  range (PosClaferUse s _ _ _)     = s
  range (PosSubconstraint s _)     = s
  range (PosSubgoal s _)           = s
  range (PosSubsoftconstraint s _) = s
  range x = errMsgR "(PosSubclafer s _), (PosClaferUse s _ _ _), (PosSubconstraint s _), (PosSubgoal s _), (PosSubsoftconstraint s _)" x
  
  
instance Mappable Clafer where
  mapNode (Clafer a b c d e f g) = doMap7 PosClafer a b c d e f g
  mapNode x = errMsgM "(Clafer a b c d e f g)" x
  range (PosClafer s _ _ _ _ _ _ _) = s
  range x = errMsgR "(PosClafer s _ _ _ _ _ _ _)" x
  
  
instance Mappable Constraint where
--  mapNode (PosConstraint s e) = doMapWithSpan PosConstraint s e
--  The span in the PosConstraint contains the span of the "[" after lexing.
--  However, we don't have the span of the "]". It doesn't make sense to include
--  one but not the other. Hence, ignore the "[" position and start with the first
--  expression in the constraint instead.
  mapNode (PosConstraint _ e) = doMap PosConstraint e
  mapNode x = errMsgM "(PosConstraint s e)" x
  range (PosConstraint s _) = s
  range x = errMsgR "(PosConstraint s _)" x


instance Mappable SoftConstraint where
  mapNode (PosSoftConstraint s e) = doMapWithSpan PosSoftConstraint s e
  mapNode x = errMsgM "(PosSoftConstraint s e)" x
  range (PosSoftConstraint s _) = s
  range x = errMsgR "(PosSoftConstraint s _)" x
  
  
instance Mappable Goal where
  mapNode (PosGoal s e) = doMapWithSpan PosGoal s e
  mapNode x = errMsgM "(PosGoal s e)" x
  range (PosGoal s _) = s
  range x = errMsgR "(PosGoal s _)" x
  
  
instance Mappable Abstract where
  mapNode AbstractEmpty   = PosAbstractEmpty noSpan
  mapNode x@PosAbstract{} = x
  mapNode x = errMsgM "AbstractEmpty or x@PosAbstract{}"x 
  range (PosAbstractEmpty s) = s
  range (PosAbstract s)      = s
  range x = errMsgR "(PosAbstractEmpty s) or (PosAbstract s)" x


instance Mappable Super where
  mapNode SuperEmpty          = PosSuperEmpty noSpan
  mapNode (SuperSome how exp'') = doMap2 PosSuperSome how exp''
  mapNode x = errMsgM "SuperEmpty or (SuperSome how exp')" x
  range (PosSuperEmpty s)    = s
  range (PosSuperSome s _ _) = s
  range x = errMsgR "(PosSuperEmpty s) or (PosSuperSome s _ _)" x


instance Mappable SuperHow where
  mapNode = id
  range (PosSuperColon s)   = s
  range (PosSuperArrow s)   = s
  range (PosSuperMArrow  s) = s
  range x = errMsgR "(PosSuperColon s), (PosSuperArrow s), or (PosSuperMArrow  s) " x


instance Mappable Init where
  mapNode InitEmpty          = PosInitEmpty noSpan
  mapNode (InitSome how exp'') = doMap2 PosInitSome how exp''
  mapNode x = errMsgM "InitEmpty or (InitSome how exp')" x
  range (PosInitEmpty s)    = s
  range (PosInitSome s _ _) = s
  range x = errMsgR "(PosInitEmpty s) or (PosInitSome s _ _)" x
  
  
instance Mappable InitHow where
  mapNode = id
  range (PosInitHow_1 s) = s
  range (PosInitHow_2 s) = s
  range x = errMsgR "(PosInitHow_1 s) or (PosInitHow_2 s)" x


instance Mappable Decl where
  mapNode (Decl l e) = doMap2 PosDecl l e
  mapNode x = errMsgM "(Decl l e)" x
  range (PosDecl s _ _) = s
  range x = errMsgR "(PosDecl s _ _)" x


instance Mappable Exp where
  mapNode (PosDeclAllDisj s decl exp')    = doMap2WithSpan PosDeclAllDisj s decl exp'
  mapNode (PosDeclAll s decl exp')        = doMap2WithSpan PosDeclAll s decl exp'
  mapNode (DeclQuantDisj quant decl exp') = doMap3 PosDeclQuantDisj quant decl exp'
  mapNode (DeclQuant quant decl exp')     = doMap3 PosDeclQuant quant decl exp'
  mapNode (PosEGMax s exp')               = doMapWithSpan PosEGMax s exp'
  mapNode (PosEGMin s exp')               = doMapWithSpan PosEGMin s exp'
  mapNode (EIff exp0 exp1)               = doMap2 PosEIff exp0 exp1
  mapNode (EImplies exp0 exp1)           = doMap2 PosEImplies exp0 exp1
  mapNode (EOr exp0 exp1)                = doMap2 PosEOr exp0 exp1
  mapNode (EXor exp0 exp1)               = doMap2 PosEXor exp0 exp1
  mapNode (EAnd exp0 exp1)               = doMap2 PosEAnd exp0 exp1
  mapNode (PosENeg s exp')                = doMapWithSpan PosENeg s exp'
  mapNode (ELt exp0 exp1)                = doMap2 PosELt exp0 exp1
  mapNode (EGt exp0 exp1)                = doMap2 PosEGt exp0 exp1
  mapNode (EEq exp0 exp1)                = doMap2 PosEEq exp0 exp1
  mapNode (ELte exp0 exp1)               = doMap2 PosELte exp0 exp1
  mapNode (EGte exp0 exp1)               = doMap2 PosEGte exp0 exp1
  mapNode (ENeq exp0 exp1)               = doMap2 PosENeq exp0 exp1
  mapNode (EIn exp0 exp1)                = doMap2 PosEIn exp0 exp1
  mapNode (ENin exp0 exp1)               = doMap2 PosENin exp0 exp1
  mapNode (QuantExp quant exp')           = doMap2 PosQuantExp quant exp'
  mapNode (EAdd exp0 exp1)               = doMap2 PosEAdd exp0 exp1
  mapNode (ESub exp0 exp1)               = doMap2 PosESub exp0 exp1
  mapNode (EMul exp0 exp1)               = doMap2 PosEMul exp0 exp1
  mapNode (EDiv exp0 exp1)               = doMap2 PosEDiv exp0 exp1
  mapNode (PosECSetExp s exp')            = doMapWithSpan PosECSetExp s exp'
  mapNode (PosEMinExp s exp')             = doMapWithSpan PosEMinExp s exp'  
  mapNode (PosESumSetExp s exp')             = doMapWithSpan PosESumSetExp s exp'
  mapNode (PosEImpliesElse s exp0 exp1 exp2) = doMap3WithSpan PosEImpliesElse s exp0 exp1 exp2
  mapNode (EInt posinteger)              = doMap PosEInt posinteger
  mapNode (EDouble posdouble)            = doMap PosEDouble posdouble
  mapNode (EStr posstring)               = doMap PosEStr posstring
  mapNode (ESetExp setexp)               = doMap PosESetExp setexp
  mapNode x = errMsgM "Exp" x
  range (PosDeclAllDisj s _ _)    = s
  range (PosDeclAll s _ _)        = s
  range (PosDeclQuantDisj s _ _ _) = s
  range (PosDeclQuant s _ _ _)    = s
  range (PosEGMax s _)            = s
  range (PosEGMin s _)            = s
  range (PosEIff s _ _)           = s
  range (PosEImplies s _ _)       = s
  range (PosEOr s _ _)            = s
  range (PosEXor s _ _)           = s
  range (PosEAnd s _ _)           = s
  range (PosENeg s _)             = s
  range (PosELt s _ _)            = s
  range (PosEGt s _ _)            = s
  range (PosEEq s _ _)            = s
  range (PosELte s _ _)           = s
  range (PosEGte s _ _)           = s
  range (PosENeq s _ _)           = s
  range (PosEIn s _ _)            = s
  range (PosENin s _ _)           = s
  range (PosQuantExp s _ _)       = s
  range (PosEAdd s _ _)           = s
  range (PosESub s _ _)           = s
  range (PosEMul s _ _)           = s
  range (PosEDiv s _ _)           = s
  range (PosECSetExp s _)         = s
  range (PosESumSetExp s _)         = s
  range (PosEMinExp s _)          = s
  range (PosEImpliesElse s _ _ _) = s
  range (PosEInt s _)             = s
  range (PosEDouble s _)          = s
  range (PosEStr s _)             = s
  range (PosESetExp s _)          = s
  range x = error $ "No position for Exp " ++ show x
  
  
instance Mappable SetExp where
  mapNode (Union e1 e2)        = doMap2 PosUnion e1 e2
  mapNode (UnionCom e1 e2)     = doMap2 PosUnionCom e1 e2
  mapNode (Difference e1 e2)   = doMap2 PosDifference e1 e2
  mapNode (Intersection e1 e2) = doMap2 PosIntersection e1 e2
  mapNode (Domain e1 e2)       = doMap2 PosDomain e1 e2
  mapNode (Range e1 e2)        = doMap2 PosRange e1 e2
  mapNode (Join e1 e2)         = doMap2 PosJoin e1 e2
  mapNode (ClaferId n)         = doMap PosClaferId n
  mapNode x = errMsgM "SetExp" x
  range (PosUnion s _ _)        = s
  range (PosUnionCom s _ _)     = s
  range (PosDifference s _ _)   = s
  range (PosIntersection s _ _) = s
  range (PosDomain s _ _)       = s
  range (PosRange s _ _)        = s
  range (PosJoin s _ _)         = s
  range (PosClaferId s _)       = s
  range x = errMsgR "SetExp" x
  

instance Mappable NCard where
  mapNode (NCard l h) = doMap2 PosNCard l h
  mapNode x = errMsgM "(NCard l h)" x
  range (PosNCard s _ _) = s
  range x = errMsgR "(PosNCard s _ _)" x
  
  
instance Mappable Card where
  mapNode CardEmpty        = PosCardEmpty noSpan
  mapNode x@PosCardLone{}  = x
  mapNode x@PosCardSome{}  = x
  mapNode x@PosCardAny{}   = x
  mapNode (CardNum i)      = doMap PosCardNum i 
  mapNode (CardInterval c) = doMap PosCardInterval c
  mapNode x = errMsgM "Card" x
  range (PosCardEmpty s) = s
  range (PosCardLone s)  = s
  range (PosCardSome s)  = s
  range (PosCardAny s)   = s
  range (PosCardNum s _) = s
  range (PosCardInterval s _) = s
  range x = errMsgR "Card" x
  
  
instance Mappable GCard where
  mapNode GCardEmpty        = PosGCardEmpty noSpan
  mapNode x@PosGCardXor{}   = x
  mapNode x@PosGCardOr{}    = x
  mapNode x@PosGCardMux{}   = x
  mapNode x@PosGCardOpt{}   = x
  mapNode (GCardInterval n) = doMap PosGCardInterval n
  mapNode x = errMsgM "GCard" x
  range (PosGCardEmpty s)      = s
  range (PosGCardXor s)        = s
  range (PosGCardOr s)         = s
  range (PosGCardMux s)        = s
  range (PosGCardOpt s)        = s
  range (PosGCardInterval s _) = s
  range x = errMsgR "GCard" x


instance Mappable Name where
  mapNode (Path m) = doMap PosPath m
  mapNode x = errMsgM "(Path m)" x
  range (PosPath s _) = s
  range x = errMsgR "(PosPath s _)" x
  

instance Mappable LocId where
  mapNode (LocIdIdent i) = doMap PosLocIdIdent i
  mapNode x = errMsgM "(LocIdIdent i)" x
  range (PosLocIdIdent s _) = s
  range x = errMsgR "(PosLocIdIdent s _)" x
  

instance Mappable ModId where
  mapNode (ModIdIdent i) = doMap PosModIdIdent i
  mapNode x = errMsgM "(ModIdIdent i)" x
  range (PosModIdIdent s _) = s
  range x = errMsgR "(PosModIdIdent s _)" x


instance Mappable EnumId where
  mapNode (EnumIdIdent i) = doMap PosEnumIdIdent i
  mapNode x = errMsgM "(EnumIdIdent i)" x
  range (PosEnumIdIdent s _) = s
  range x = errMsgR "(PosEnumIdIdent s _)" x
  
  
instance Mappable Quant where
  mapNode = id
  range (PosQuantNo s)   = s
  range (PosQuantLone s) = s
  range (PosQuantOne s)  = s
  range (PosQuantSome s) = s
  range x = errMsgR "(PosQuantNo s), (PosQuantLone s), (PosQuantOne s), or (PosQuantSome s)" x



instance Mappable ExInteger where
  mapNode x@PosExIntegerAst{} = x
  mapNode (ExIntegerNum i)    = doMap PosExIntegerNum i
  mapNode x = errMsgM "x@PosExIntegerAst{} or (ExIntegerNum i)" x
  range (PosExIntegerAst s)   = s
  range (PosExIntegerNum s _) = s  
  range x = errMsgR "(PosExIntegerAst s) or (PosExIntegerNum s _)" x


instance Mappable PosIdent where
  mapNode = id
  range (PosIdent ((c, l), lex')) =
    Span (Pos c' l') (Pos c' $ l' + len lex')
    where
    c' = toInteger c
    l' = toInteger l


instance Mappable PosString where
  mapNode = id
  range (PosString ((c, l), lex')) =
    Span (Pos c' l') (Pos c' $ l' + len lex')
    where
    c' = toInteger c
    l' = toInteger l

  
instance Mappable PosDouble where
  mapNode = id  
  range (PosDouble ((c, l), lex')) =
    Span (Pos c' l') (Pos c' $ l' + len lex')
    where
    c' = toInteger c
    l' = toInteger l

  
  
instance Mappable PosInteger where
  mapNode = id  
  range (PosInteger ((c, l), lex')) =
    Span (Pos c' l') (Pos c' $ l' + len lex')
    where
    c' = toInteger c
    l' = toInteger l


len :: [a] -> Integer
len = toInteger . length

errMsg :: Show a => [Char] -> [Char] -> a -> t
errMsg function expected actual = error $ "Error: Function '" ++ function ++ "' expected argument of type(s) " ++ expected ++ " got " ++ show actual
errMsgM :: Show a => [Char] -> a -> t
errMsgM e a = errMsg "mapNode" e a
errMsgR :: Show a => [Char] -> a -> t
errMsgR e a = errMsg "range" e a