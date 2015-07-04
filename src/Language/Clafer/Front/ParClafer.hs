{-# OPTIONS_GHC -w #-}
{-# OPTIONS -fglasgow-exts -cpp #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Language.Clafer.Front.ParClafer where
import Language.Clafer.Front.AbsClafer
import Language.Clafer.Front.LexClafer
import Language.Clafer.Front.ErrM
import qualified Data.Array as Happy_Data_Array
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.5

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn8 :: (PosInteger) -> (HappyAbsSyn )
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> (PosInteger)
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
happyIn9 :: (PosDouble) -> (HappyAbsSyn )
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> (PosDouble)
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
happyIn10 :: (PosString) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> (PosString)
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
happyIn11 :: (PosIdent) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> (PosIdent)
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: (Module) -> (HappyAbsSyn )
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> (Module)
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
happyIn13 :: (Declaration) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> (Declaration)
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: (Clafer) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> (Clafer)
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyIn15 :: (Constraint) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> (Constraint)
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyIn16 :: (SoftConstraint) -> (HappyAbsSyn )
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> (SoftConstraint)
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
happyIn17 :: (Goal) -> (HappyAbsSyn )
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> (Goal)
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
happyIn18 :: (Abstract) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> (Abstract)
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: (Elements) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> (Elements)
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: (Element) -> (HappyAbsSyn )
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> (Element)
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
happyIn21 :: (Super) -> (HappyAbsSyn )
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> (Super)
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyIn22 :: (Reference) -> (HappyAbsSyn )
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> (Reference)
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
happyIn23 :: (Init) -> (HappyAbsSyn )
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> (Init)
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
happyIn24 :: (InitHow) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> (InitHow)
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyIn25 :: (GCard) -> (HappyAbsSyn )
happyIn25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn ) -> (GCard)
happyOut25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut25 #-}
happyIn26 :: (Card) -> (HappyAbsSyn )
happyIn26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn ) -> (Card)
happyOut26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut26 #-}
happyIn27 :: (NCard) -> (HappyAbsSyn )
happyIn27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn ) -> (NCard)
happyOut27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut27 #-}
happyIn28 :: (ExInteger) -> (HappyAbsSyn )
happyIn28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn ) -> (ExInteger)
happyOut28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut28 #-}
happyIn29 :: (Name) -> (HappyAbsSyn )
happyIn29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn ) -> (Name)
happyOut29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut29 #-}
happyIn30 :: (Exp) -> (HappyAbsSyn )
happyIn30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn30 #-}
happyOut30 :: (HappyAbsSyn ) -> (Exp)
happyOut30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut30 #-}
happyIn31 :: (Exp) -> (HappyAbsSyn )
happyIn31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn31 #-}
happyOut31 :: (HappyAbsSyn ) -> (Exp)
happyOut31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut31 #-}
happyIn32 :: (Exp) -> (HappyAbsSyn )
happyIn32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn32 #-}
happyOut32 :: (HappyAbsSyn ) -> (Exp)
happyOut32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut32 #-}
happyIn33 :: (Exp) -> (HappyAbsSyn )
happyIn33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn33 #-}
happyOut33 :: (HappyAbsSyn ) -> (Exp)
happyOut33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut33 #-}
happyIn34 :: (Exp) -> (HappyAbsSyn )
happyIn34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn34 #-}
happyOut34 :: (HappyAbsSyn ) -> (Exp)
happyOut34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut34 #-}
happyIn35 :: (Exp) -> (HappyAbsSyn )
happyIn35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn35 #-}
happyOut35 :: (HappyAbsSyn ) -> (Exp)
happyOut35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut35 #-}
happyIn36 :: (Exp) -> (HappyAbsSyn )
happyIn36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn36 #-}
happyOut36 :: (HappyAbsSyn ) -> (Exp)
happyOut36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut36 #-}
happyIn37 :: (Exp) -> (HappyAbsSyn )
happyIn37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn37 #-}
happyOut37 :: (HappyAbsSyn ) -> (Exp)
happyOut37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut37 #-}
happyIn38 :: (Exp) -> (HappyAbsSyn )
happyIn38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn38 #-}
happyOut38 :: (HappyAbsSyn ) -> (Exp)
happyOut38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut38 #-}
happyIn39 :: (Exp) -> (HappyAbsSyn )
happyIn39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn39 #-}
happyOut39 :: (HappyAbsSyn ) -> (Exp)
happyOut39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut39 #-}
happyIn40 :: (Exp) -> (HappyAbsSyn )
happyIn40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn40 #-}
happyOut40 :: (HappyAbsSyn ) -> (Exp)
happyOut40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut40 #-}
happyIn41 :: (Exp) -> (HappyAbsSyn )
happyIn41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn41 #-}
happyOut41 :: (HappyAbsSyn ) -> (Exp)
happyOut41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut41 #-}
happyIn42 :: (Exp) -> (HappyAbsSyn )
happyIn42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn42 #-}
happyOut42 :: (HappyAbsSyn ) -> (Exp)
happyOut42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut42 #-}
happyIn43 :: (Exp) -> (HappyAbsSyn )
happyIn43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn43 #-}
happyOut43 :: (HappyAbsSyn ) -> (Exp)
happyOut43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut43 #-}
happyIn44 :: (Exp) -> (HappyAbsSyn )
happyIn44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn44 #-}
happyOut44 :: (HappyAbsSyn ) -> (Exp)
happyOut44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut44 #-}
happyIn45 :: (Exp) -> (HappyAbsSyn )
happyIn45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn45 #-}
happyOut45 :: (HappyAbsSyn ) -> (Exp)
happyOut45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut45 #-}
happyIn46 :: (Exp) -> (HappyAbsSyn )
happyIn46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn46 #-}
happyOut46 :: (HappyAbsSyn ) -> (Exp)
happyOut46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut46 #-}
happyIn47 :: (Exp) -> (HappyAbsSyn )
happyIn47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn47 #-}
happyOut47 :: (HappyAbsSyn ) -> (Exp)
happyOut47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut47 #-}
happyIn48 :: (Exp) -> (HappyAbsSyn )
happyIn48 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn48 #-}
happyOut48 :: (HappyAbsSyn ) -> (Exp)
happyOut48 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut48 #-}
happyIn49 :: (Exp) -> (HappyAbsSyn )
happyIn49 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn49 #-}
happyOut49 :: (HappyAbsSyn ) -> (Exp)
happyOut49 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut49 #-}
happyIn50 :: (Decl) -> (HappyAbsSyn )
happyIn50 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn50 #-}
happyOut50 :: (HappyAbsSyn ) -> (Decl)
happyOut50 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut50 #-}
happyIn51 :: (Quant) -> (HappyAbsSyn )
happyIn51 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn51 #-}
happyOut51 :: (HappyAbsSyn ) -> (Quant)
happyOut51 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut51 #-}
happyIn52 :: (EnumId) -> (HappyAbsSyn )
happyIn52 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn52 #-}
happyOut52 :: (HappyAbsSyn ) -> (EnumId)
happyOut52 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut52 #-}
happyIn53 :: (ModId) -> (HappyAbsSyn )
happyIn53 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn53 #-}
happyOut53 :: (HappyAbsSyn ) -> (ModId)
happyOut53 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut53 #-}
happyIn54 :: (LocId) -> (HappyAbsSyn )
happyIn54 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn54 #-}
happyOut54 :: (HappyAbsSyn ) -> (LocId)
happyOut54 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut54 #-}
happyIn55 :: ([Declaration]) -> (HappyAbsSyn )
happyIn55 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn55 #-}
happyOut55 :: (HappyAbsSyn ) -> ([Declaration])
happyOut55 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut55 #-}
happyIn56 :: ([EnumId]) -> (HappyAbsSyn )
happyIn56 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn56 #-}
happyOut56 :: (HappyAbsSyn ) -> ([EnumId])
happyOut56 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut56 #-}
happyIn57 :: ([Element]) -> (HappyAbsSyn )
happyIn57 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn57 #-}
happyOut57 :: (HappyAbsSyn ) -> ([Element])
happyOut57 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut57 #-}
happyIn58 :: ([Exp]) -> (HappyAbsSyn )
happyIn58 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn58 #-}
happyOut58 :: (HappyAbsSyn ) -> ([Exp])
happyOut58 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut58 #-}
happyIn59 :: ([LocId]) -> (HappyAbsSyn )
happyIn59 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn59 #-}
happyOut59 :: (HappyAbsSyn ) -> ([LocId])
happyOut59 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut59 #-}
happyIn60 :: ([ModId]) -> (HappyAbsSyn )
happyIn60 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn60 #-}
happyOut60 :: (HappyAbsSyn ) -> ([ModId])
happyOut60 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut60 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x00\x00\x33\x01\x36\x01\x2d\x01\x3b\x01\xf3\x00\x00\x00\x0d\x01\x00\x00\x0d\x01\x10\x01\x05\x01\x00\x00\x05\x01\x21\x01\x00\x00\x05\x01\x07\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x01\x08\x01\x1f\x01\xee\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x58\x00\x00\x00\x1e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x01\x0e\x01\xf1\x00\xef\x00\x25\x01\x00\x00\xe8\x05\x00\x00\x64\x00\x71\x00\x00\x00\x00\x00\xb0\x00\x19\x01\x15\x01\xed\x00\x06\x01\xf4\x00\x00\x00\xbe\x00\xd7\x00\x00\x00\xad\x00\x27\x00\x75\x00\x27\x00\x00\x00\xd7\xff\x27\x00\x00\x00\x92\x00\x92\x00\x00\x00\x00\x00\x00\x00\x27\x00\x00\x00\x27\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\xf0\x00\x0f\x00\xdd\x00\x1b\x00\xe7\x00\xaf\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa9\x00\x00\x00\x00\x00\x00\x00\x9c\x00\xfd\xff\x00\x00\x00\x00\x00\x00\xcc\x00\x27\x00\xcc\x00\xae\x00\x00\x00\xa5\x00\xc8\x00\xc9\x00\x9a\x00\x00\x00\xd4\x00\x00\x00\xe8\x05\x95\x00\x18\x00\x00\x00\x99\x00\x94\x00\xfd\xff\xfd\xff\xfd\xff\xfd\xff\xfd\xff\xfd\xff\xfd\xff\x06\x00\x06\x00\x06\x00\x06\x00\x06\x00\xad\x00\xad\x00\xad\x00\xad\x00\xad\x00\xad\x00\xad\x00\xa3\x00\x92\x00\x92\x00\x92\x00\x92\x00\x92\x00\xb2\x00\x8f\x00\x93\x00\xc3\x00\x00\x00\xad\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x71\x00\x71\x00\x00\x00\x00\x00\x00\x00\xb5\x00\xb5\x00\xb9\x00\xa7\x00\xa8\x00\xa4\x00\x00\x00\x7f\x00\x75\x00\x00\x00\x00\x00\x73\x00\xfd\xff\x5a\x00\x75\x00\x27\x00\x00\x00\x1b\x00\x27\x00\x27\x00\x00\x00\x50\x00\x00\x00\x00\x00\x00\x00\xf7\xff\x3f\x00\x00\x00\x00\x00\xf3\xff\x5f\x00\x00\x00\x00\x00\x8b\x00\x75\x00\x00\x00\x75\x00\x00\x00\x00\x00\x00\x00\xfd\xff\x41\x00\x75\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8b\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x09\x00\x0c\x00\x7a\x00\x6c\x00\x69\x00\x00\x00\x00\x00\x00\x00\x3a\x00\x00\x00\x00\x00\x00\x00\xf8\xff\x00\x00\xa1\x00\x00\x00\x00\x00\x7e\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x52\x00\x60\x00\x00\x00\x57\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x34\x02\xf0\xff\x34\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x73\x04\x00\x00\x00\x00\xa4\x03\xd2\x05\x06\x02\xb9\x05\x00\x00\xfb\x00\xa3\x05\x00\x00\xbe\x02\x90\x02\x00\x00\x00\x00\x00\x00\x8a\x05\x00\x00\x74\x05\x00\x00\x00\x00\x00\x00\xd8\x01\x00\x00\x07\x00\x05\x00\x00\x00\x5d\x00\x00\x00\x11\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9d\x00\x00\x00\x00\x00\x00\x00\x0a\x00\x1b\x06\x00\x00\x00\x00\x00\x00\x00\x00\x5b\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xfa\x00\x00\x00\x00\x00\x00\x00\x00\x00\x39\x00\x00\x00\x00\x00\x00\x00\x49\x00\x0c\x06\xbc\x05\xcf\x00\x15\x06\x06\x06\xec\x05\x9f\x04\xfd\x04\xe7\x04\xce\x04\xb8\x04\x8a\x04\x5c\x04\x45\x04\x2e\x04\x17\x04\x00\x04\xe9\x03\xd2\x03\x00\x00\x76\x03\x48\x03\x1a\x03\xec\x02\x62\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xbb\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xaa\x01\x00\x00\x00\x00\x00\x00\x8b\x03\x61\x00\x7c\x01\x45\x05\x00\x00\x15\x00\x2c\x05\x16\x05\x00\x00\x00\x00\x00\x00\x00\x00\xd5\xff\xab\x01\x77\x00\x00\x00\x00\x00\xfb\xff\x00\x00\x00\x00\x00\x00\x00\x00\x4e\x01\x00\x00\x20\x01\x00\x00\x00\x00\x00\x00\x5d\x03\x04\x00\xf2\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\x86\xff\xef\xff\x00\x00\x00\x00\x00\x00\x00\x00\xfa\xff\x00\x00\x80\xff\x00\x00\x00\x00\x00\x00\x80\xff\x00\x00\xdd\xff\xee\xff\x00\x00\xef\xff\x85\xff\xeb\xff\xe9\xff\xe7\xff\xe8\xff\xf4\xff\x00\x00\x00\x00\x00\x00\x00\x00\xd8\xff\xda\xff\xd9\xff\xdb\xff\xdc\xff\x00\x00\x80\xff\x00\x00\xa2\xff\xa1\xff\xa0\xff\x88\xff\x91\xff\x7f\xff\xc9\xff\xc5\xff\xc3\xff\xc1\xff\xbf\xff\xbd\xff\xbb\xff\xb2\xff\xb0\xff\xad\xff\xa9\xff\xa4\xff\x9f\xff\x9c\xff\x9a\xff\x98\xff\x96\xff\x94\xff\x92\xff\x00\x00\x7c\xff\xce\xff\x00\x00\x00\x00\x00\x00\x00\x00\xf0\xff\x00\x00\x00\x00\x8c\xff\x00\x00\x00\x00\x8e\xff\x8d\xff\x8b\xff\x00\x00\x8a\xff\x00\x00\xf9\xff\xf8\xff\xf7\xff\x00\x00\xf2\xff\xe6\xff\x00\x00\x00\x00\xd7\xff\xd3\xff\xed\xff\xd2\xff\xd4\xff\xd5\xff\xd6\xff\x00\x00\xcf\xff\xd1\xff\xd0\xff\xe4\xff\x00\x00\xf1\xff\xa8\xff\xa7\xff\xc7\xff\x00\x00\xc8\xff\x00\x00\x87\xff\x00\x00\x7e\xff\x00\x00\x00\x00\xa5\xff\x00\x00\xa6\xff\xbc\xff\x00\x00\x88\xff\xb1\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc6\xff\xc4\xff\xc2\xff\xc0\xff\xbe\xff\x00\x00\xb4\xff\xb6\xff\xb9\xff\xb8\xff\xb7\xff\xba\xff\xb5\xff\xae\xff\xaf\xff\xab\xff\xac\xff\xaa\xff\x9d\xff\x9e\xff\x9b\xff\x99\xff\x97\xff\x95\xff\x93\xff\x00\x00\x00\x00\x7b\xff\x90\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe5\xff\xd7\xff\x00\x00\x00\x00\x89\xff\x84\xff\xf5\xff\xea\xff\x82\xff\xef\xff\x00\x00\xe2\xff\xe3\xff\xe1\xff\x00\x00\xcc\xff\x7d\xff\x8f\xff\x00\x00\xca\xff\x00\x00\xb3\xff\xcb\xff\xcd\xff\x00\x00\xed\xff\x00\x00\xde\xff\xdf\xff\x83\xff\x81\xff\xec\xff\xe0\xff\xf3\xff\xa3\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x2a\x00\x01\x00\x06\x00\x03\x00\x00\x00\x31\x00\x06\x00\x15\x00\x03\x00\x0f\x00\x10\x00\x06\x00\x04\x00\x0d\x00\x0b\x00\x1d\x00\x1a\x00\x06\x00\x0d\x00\x0d\x00\x00\x00\x0a\x00\x08\x00\x0e\x00\x14\x00\x23\x00\x44\x00\x0b\x00\x26\x00\x27\x00\x01\x00\x29\x00\x03\x00\x32\x00\x08\x00\x06\x00\x0a\x00\x25\x00\x12\x00\x13\x00\x28\x00\x32\x00\x0d\x00\x14\x00\x06\x00\x2d\x00\x17\x00\x2f\x00\x30\x00\x31\x00\x2d\x00\x33\x00\x34\x00\x35\x00\x40\x00\x2f\x00\x38\x00\x39\x00\x3a\x00\x03\x00\x22\x00\x38\x00\x21\x00\x3a\x00\x44\x00\x41\x00\x42\x00\x43\x00\x44\x00\x28\x00\x41\x00\x42\x00\x43\x00\x44\x00\x2d\x00\x03\x00\x2f\x00\x30\x00\x31\x00\x41\x00\x33\x00\x34\x00\x35\x00\x2d\x00\x03\x00\x38\x00\x39\x00\x3a\x00\x01\x00\x03\x00\x03\x00\x41\x00\x00\x00\x06\x00\x41\x00\x42\x00\x43\x00\x44\x00\x03\x00\x03\x00\x0d\x00\x2d\x00\x15\x00\x41\x00\x42\x00\x43\x00\x44\x00\x32\x00\x34\x00\x0a\x00\x12\x00\x13\x00\x0d\x00\x09\x00\x2a\x00\x08\x00\x04\x00\x01\x00\x2e\x00\x03\x00\x08\x00\x03\x00\x06\x00\x33\x00\x25\x00\x3d\x00\x2d\x00\x28\x00\x07\x00\x0d\x00\x44\x00\x13\x00\x2d\x00\x34\x00\x2f\x00\x30\x00\x31\x00\x2b\x00\x33\x00\x34\x00\x35\x00\x3e\x00\x2e\x00\x38\x00\x39\x00\x3a\x00\x01\x00\x33\x00\x03\x00\x0b\x00\x0c\x00\x06\x00\x41\x00\x42\x00\x43\x00\x44\x00\x28\x00\x44\x00\x0d\x00\x03\x00\x00\x00\x2d\x00\x2c\x00\x2f\x00\x30\x00\x31\x00\x30\x00\x33\x00\x34\x00\x35\x00\x0f\x00\x10\x00\x38\x00\x39\x00\x3a\x00\x03\x00\x3e\x00\x11\x00\x06\x00\x13\x00\x11\x00\x41\x00\x42\x00\x43\x00\x44\x00\x0d\x00\x0b\x00\x0c\x00\x3e\x00\x16\x00\x2d\x00\x19\x00\x2f\x00\x09\x00\x0e\x00\x06\x00\x33\x00\x34\x00\x35\x00\x05\x00\x2c\x00\x38\x00\x39\x00\x3a\x00\x30\x00\x3f\x00\x3c\x00\x1e\x00\x2e\x00\x03\x00\x41\x00\x42\x00\x43\x00\x44\x00\x3e\x00\x44\x00\x44\x00\x2d\x00\x07\x00\x2f\x00\x14\x00\x44\x00\x17\x00\x33\x00\x34\x00\x35\x00\x3e\x00\x15\x00\x38\x00\x39\x00\x3a\x00\x2a\x00\x3b\x00\x1e\x00\x2d\x00\x3d\x00\x44\x00\x41\x00\x42\x00\x43\x00\x44\x00\x00\x00\x01\x00\x02\x00\x03\x00\x27\x00\x28\x00\x29\x00\x12\x00\x1d\x00\x24\x00\x2d\x00\x03\x00\x03\x00\x41\x00\x42\x00\x43\x00\x44\x00\x34\x00\x14\x00\x11\x00\x19\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x16\x00\x2b\x00\x09\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x2a\x00\x2a\x00\x34\x00\x0e\x00\x2e\x00\x2e\x00\x05\x00\x3c\x00\x1e\x00\x33\x00\x33\x00\x1c\x00\x3f\x00\x12\x00\x44\x00\x23\x00\x41\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x45\x00\x2b\x00\x44\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x45\x00\x32\x00\x34\x00\x1a\x00\x29\x00\x36\x00\x37\x00\x23\x00\x27\x00\xff\xff\xff\xff\x3c\x00\xff\xff\xff\xff\xff\xff\xff\xff\x41\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x05\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\xff\xff\x0c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\xff\xff\x0c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\xff\xff\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x1a\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x23\x00\xff\xff\xff\xff\x26\x00\x27\x00\x15\x00\x29\x00\xff\xff\xff\xff\x2c\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x45\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x03\x00\xff\xff\xff\xff\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x15\x00\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x15\x00\xff\xff\xff\xff\x03\x00\xff\xff\xff\xff\x34\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x15\x00\x2b\x00\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x15\x00\xff\xff\x00\x00\x01\x00\x02\x00\x03\x00\x34\x00\xff\xff\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\x15\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\x15\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\x15\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\x15\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\x15\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\x15\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\x15\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\x15\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x2b\x00\x15\x00\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\xff\xff\x15\x00\x2d\x00\x2e\x00\x03\x00\xff\xff\xff\xff\xff\xff\x33\x00\x34\x00\xff\xff\xff\xff\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x15\x00\xff\xff\xff\xff\x2d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x15\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x15\x00\xff\xff\x2d\x00\xff\xff\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x15\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x15\x00\xff\xff\x2d\x00\xff\xff\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x15\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x15\x00\xff\xff\x2d\x00\xff\xff\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x15\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x15\x00\xff\xff\x2d\x00\xff\xff\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x15\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x15\x00\xff\xff\x2d\x00\xff\xff\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x15\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x15\x00\xff\xff\x2d\x00\x15\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x28\x00\x29\x00\x2d\x00\x15\x00\xff\xff\x2d\x00\x02\x00\xff\xff\xff\xff\x34\x00\xff\xff\x03\x00\x34\x00\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x18\x00\x15\x00\xff\xff\x1b\x00\xff\xff\x1d\x00\x34\x00\x1f\x00\x20\x00\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x03\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2e\x00\xff\xff\x03\x00\x2d\x00\xff\xff\x15\x00\x34\x00\xff\xff\x03\x00\xff\xff\x34\x00\x15\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x15\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x15\x00\xff\xff\xff\xff\x2d\x00\xff\xff\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x34\x00\x26\x00\x27\x00\x28\x00\x29\x00\xff\xff\x34\x00\xff\xff\x2d\x00\xff\xff\x29\x00\xff\xff\xff\xff\xff\xff\x2d\x00\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x71\x00\x41\x00\x43\x00\x42\x00\x60\x00\xbe\x00\x43\x00\xd1\x00\x42\x00\xce\x00\xcf\x00\x43\x00\x10\x00\x44\x00\xd6\x00\xd2\x00\x09\x00\x0d\x00\x44\x00\x63\x00\x59\x00\x0e\x00\x63\x00\xb6\x00\x61\x00\x0d\x00\x53\x00\xbc\x00\x19\x00\x10\x00\x41\x00\x0b\x00\x42\x00\x53\x00\x5d\x00\x43\x00\x5e\x00\x66\x00\xc2\x00\x5b\x00\x46\x00\x21\x00\x44\x00\x87\xff\x43\x00\x47\x00\x87\xff\x48\x00\x49\x00\x4a\x00\x47\x00\x4b\x00\x4c\x00\x4d\x00\xd5\x00\x11\x00\x4e\x00\x4f\x00\x50\x00\x27\x00\x5f\x00\x4e\x00\x45\x00\x50\x00\x53\x00\x07\x00\x51\x00\x52\x00\x53\x00\x46\x00\x07\x00\x51\x00\x52\x00\x53\x00\x47\x00\x6c\x00\x48\x00\x49\x00\x4a\x00\x07\x00\x4b\x00\x4c\x00\x4d\x00\x47\x00\x27\x00\x4e\x00\x4f\x00\x50\x00\x41\x00\x55\x00\x42\x00\x07\x00\x59\x00\x43\x00\x07\x00\x51\x00\x52\x00\x53\x00\x57\x00\x6c\x00\x44\x00\x3e\x00\x58\x00\x07\x00\x51\x00\x52\x00\x53\x00\x23\x00\xae\x00\x85\x00\x5a\x00\x5b\x00\x86\x00\x07\x00\xac\x00\x09\x00\x82\x00\x41\x00\x6e\x00\x42\x00\x83\x00\xb9\x00\x43\x00\x6f\x00\x55\x00\xbe\x00\x3e\x00\x46\x00\x0b\x00\x44\x00\x53\x00\x84\x00\x47\x00\x3f\x00\x48\x00\x49\x00\x4a\x00\xce\x00\x4b\x00\x4c\x00\x4d\x00\xc0\x00\x6e\x00\x4e\x00\x4f\x00\x50\x00\x41\x00\xc5\x00\x42\x00\x80\x00\x81\x00\x43\x00\x07\x00\x51\x00\x52\x00\x53\x00\x46\x00\x53\x00\x44\x00\xb9\x00\x1a\x00\x47\x00\xba\x00\x48\x00\x49\x00\x4a\x00\xd2\x00\x4b\x00\x4c\x00\x4d\x00\xb8\x00\xb9\x00\x4e\x00\x4f\x00\x50\x00\x42\x00\xc8\x00\x1b\x00\x43\x00\x1c\x00\x7b\x00\x07\x00\x51\x00\x52\x00\x53\x00\x44\x00\x80\x00\x81\x00\xca\x00\x7c\x00\x47\x00\x7d\x00\x48\x00\x7e\x00\x7f\x00\x43\x00\x4b\x00\x4c\x00\x4d\x00\x8f\x00\xba\x00\x4e\x00\x4f\x00\x50\x00\xbb\x00\x91\x00\x90\x00\x92\x00\x99\x00\x27\x00\x07\x00\x51\x00\x52\x00\x53\x00\xae\x00\x53\x00\x53\x00\x47\x00\xb0\x00\x48\x00\xb2\x00\x53\x00\xb3\x00\x4b\x00\x4c\x00\x4d\x00\xb4\x00\x28\x00\x4e\x00\x4f\x00\x50\x00\x7a\x00\xb5\x00\x92\x00\x47\x00\xbe\x00\x53\x00\x07\x00\x51\x00\x52\x00\x53\x00\x24\x00\x25\x00\x26\x00\x27\x00\xa9\x00\x3b\x00\x3c\x00\x57\x00\x60\x00\x76\x00\x3e\x00\x6c\x00\x6c\x00\x07\x00\x51\x00\x52\x00\x53\x00\x3f\x00\x65\x00\x7b\x00\x7d\x00\x28\x00\xd5\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x7c\x00\x3d\x00\x7e\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\xb0\x00\x6d\x00\x3f\x00\x7f\x00\x6e\x00\x6e\x00\x8f\x00\x90\x00\x92\x00\x6f\x00\x6f\x00\x93\x00\x91\x00\x57\x00\x53\x00\x23\x00\x07\x00\x28\x00\xcb\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\xff\xff\x3d\x00\x53\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\xff\xff\x1e\x00\x3f\x00\x09\x00\x0b\x00\x1f\x00\x20\x00\x0d\x00\x10\x00\x00\x00\x00\x00\x21\x00\x00\x00\x00\x00\x00\x00\x00\x00\x07\x00\x28\x00\xcc\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x3d\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x0e\x00\x00\x00\x17\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\xc4\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x3d\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x13\x00\x14\x00\x15\x00\x16\x00\x0e\x00\x00\x00\xd3\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\xc8\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x3d\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x3d\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\x72\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x3d\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x3d\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\x00\x00\x00\x00\x93\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\x00\x00\x00\x00\x68\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\x00\x00\x00\x00\x6a\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\x00\x00\x00\x00\x00\x00\x94\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x09\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0d\x00\x00\x00\x00\x00\x19\x00\x10\x00\x28\x00\x0b\x00\x00\x00\x00\x00\x1a\x00\x95\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\xf6\xff\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\x00\x00\x00\x00\x27\x00\x00\x00\x00\x00\x96\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x28\x00\x69\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\xd7\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x28\x00\x00\x00\x00\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x97\x00\x30\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x28\x00\x69\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\xc6\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x28\x00\x00\x00\x24\x00\x25\x00\x26\x00\x27\x00\x3f\x00\x00\x00\x74\x00\x31\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x28\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\xca\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x28\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x99\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x28\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x9a\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x28\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x9b\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x28\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x9c\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x28\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x9d\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x28\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x9e\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x28\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x76\x00\x00\x00\x00\x00\x3f\x00\x9f\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x69\x00\x28\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x77\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x78\x00\x00\x00\x28\x00\x3e\x00\x6e\x00\x27\x00\x00\x00\x00\x00\x00\x00\x6f\x00\x3f\x00\x00\x00\x00\x00\xa0\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x28\x00\x00\x00\x00\x00\x3e\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa5\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x28\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa1\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x28\x00\x00\x00\x3e\x00\x00\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\xa2\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x28\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa3\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x28\x00\x00\x00\x3e\x00\x00\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\xa4\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x28\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x28\x00\x00\x00\x3e\x00\x00\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\xc1\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x28\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc3\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x28\x00\x00\x00\x3e\x00\x00\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x77\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x28\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x66\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x28\x00\x00\x00\x3e\x00\x00\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x67\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x28\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x27\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6b\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x28\x00\x00\x00\x3e\x00\x28\x00\x24\x00\x25\x00\x26\x00\x27\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x71\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\xaa\x00\x3c\x00\x3e\x00\x28\x00\x00\x00\x3e\x00\x87\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x27\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x73\x00\x36\x00\x37\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x88\x00\x28\x00\x00\x00\x89\x00\x00\x00\x8a\x00\x3f\x00\x8b\x00\x8c\x00\x27\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x27\x00\xa6\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x8d\x00\x00\x00\x27\x00\x3e\x00\x00\x00\x28\x00\x8e\x00\x00\x00\x27\x00\x00\x00\x3f\x00\x28\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\xa7\x00\x39\x00\x3a\x00\x3b\x00\x3c\x00\x28\x00\x00\x00\x00\x00\x3e\x00\x00\x00\xab\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x3f\x00\xa8\x00\x3a\x00\x3b\x00\x3c\x00\x00\x00\x3f\x00\x00\x00\x3e\x00\x00\x00\xb5\x00\x00\x00\x00\x00\x00\x00\x3e\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (5, 132) [
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66),
	(67 , happyReduce_67),
	(68 , happyReduce_68),
	(69 , happyReduce_69),
	(70 , happyReduce_70),
	(71 , happyReduce_71),
	(72 , happyReduce_72),
	(73 , happyReduce_73),
	(74 , happyReduce_74),
	(75 , happyReduce_75),
	(76 , happyReduce_76),
	(77 , happyReduce_77),
	(78 , happyReduce_78),
	(79 , happyReduce_79),
	(80 , happyReduce_80),
	(81 , happyReduce_81),
	(82 , happyReduce_82),
	(83 , happyReduce_83),
	(84 , happyReduce_84),
	(85 , happyReduce_85),
	(86 , happyReduce_86),
	(87 , happyReduce_87),
	(88 , happyReduce_88),
	(89 , happyReduce_89),
	(90 , happyReduce_90),
	(91 , happyReduce_91),
	(92 , happyReduce_92),
	(93 , happyReduce_93),
	(94 , happyReduce_94),
	(95 , happyReduce_95),
	(96 , happyReduce_96),
	(97 , happyReduce_97),
	(98 , happyReduce_98),
	(99 , happyReduce_99),
	(100 , happyReduce_100),
	(101 , happyReduce_101),
	(102 , happyReduce_102),
	(103 , happyReduce_103),
	(104 , happyReduce_104),
	(105 , happyReduce_105),
	(106 , happyReduce_106),
	(107 , happyReduce_107),
	(108 , happyReduce_108),
	(109 , happyReduce_109),
	(110 , happyReduce_110),
	(111 , happyReduce_111),
	(112 , happyReduce_112),
	(113 , happyReduce_113),
	(114 , happyReduce_114),
	(115 , happyReduce_115),
	(116 , happyReduce_116),
	(117 , happyReduce_117),
	(118 , happyReduce_118),
	(119 , happyReduce_119),
	(120 , happyReduce_120),
	(121 , happyReduce_121),
	(122 , happyReduce_122),
	(123 , happyReduce_123),
	(124 , happyReduce_124),
	(125 , happyReduce_125),
	(126 , happyReduce_126),
	(127 , happyReduce_127),
	(128 , happyReduce_128),
	(129 , happyReduce_129),
	(130 , happyReduce_130),
	(131 , happyReduce_131),
	(132 , happyReduce_132)
	]

happy_n_terms = 70 :: Int
happy_n_nonterms = 53 :: Int

happyReduce_5 = happySpecReduce_1  0# happyReduction_5
happyReduction_5 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn8
		 (PosInteger (mkPosToken happy_var_1)
	)}

happyReduce_6 = happySpecReduce_1  1# happyReduction_6
happyReduction_6 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn9
		 (PosDouble (mkPosToken happy_var_1)
	)}

happyReduce_7 = happySpecReduce_1  2# happyReduction_7
happyReduction_7 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn10
		 (PosString (mkPosToken happy_var_1)
	)}

happyReduce_8 = happySpecReduce_1  3# happyReduction_8
happyReduction_8 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn11
		 (PosIdent (mkPosToken happy_var_1)
	)}

happyReduce_9 = happySpecReduce_1  4# happyReduction_9
happyReduction_9 happy_x_1
	 =  case happyOut55 happy_x_1 of { happy_var_1 -> 
	happyIn12
		 (Module ((mkCatSpan happy_var_1)) (reverse happy_var_1)
	)}

happyReduce_10 = happyReduce 4# 5# happyReduction_10
happyReduction_10 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut11 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { happy_var_3 -> 
	case happyOut56 happy_x_4 of { happy_var_4 -> 
	happyIn13
		 (EnumDecl ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2) >- (mkTokenSpan happy_var_3) >- (mkCatSpan happy_var_4)) happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}}

happyReduce_11 = happySpecReduce_1  5# happyReduction_11
happyReduction_11 happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (ElementDecl ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_12 = happyReduce 8# 6# happyReduction_12
happyReduction_12 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut18 happy_x_1 of { happy_var_1 -> 
	case happyOut25 happy_x_2 of { happy_var_2 -> 
	case happyOut11 happy_x_3 of { happy_var_3 -> 
	case happyOut21 happy_x_4 of { happy_var_4 -> 
	case happyOut22 happy_x_5 of { happy_var_5 -> 
	case happyOut26 happy_x_6 of { happy_var_6 -> 
	case happyOut23 happy_x_7 of { happy_var_7 -> 
	case happyOut19 happy_x_8 of { happy_var_8 -> 
	happyIn14
		 (Clafer ((mkCatSpan happy_var_1) >- (mkCatSpan happy_var_2) >- (mkCatSpan happy_var_3) >- (mkCatSpan happy_var_4) >- (mkCatSpan happy_var_5) >- (mkCatSpan happy_var_6) >- (mkCatSpan happy_var_7) >- (mkCatSpan happy_var_8)) happy_var_1 happy_var_2 happy_var_3 happy_var_4 happy_var_5 happy_var_6 happy_var_7 happy_var_8
	) `HappyStk` happyRest}}}}}}}}

happyReduce_13 = happySpecReduce_3  7# happyReduction_13
happyReduction_13 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut58 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { happy_var_3 -> 
	happyIn15
		 (Constraint ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2) >- (mkTokenSpan happy_var_3)) (reverse happy_var_2)
	)}}}

happyReduce_14 = happyReduce 4# 8# happyReduction_14
happyReduction_14 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut58 happy_x_3 of { happy_var_3 -> 
	case happyOutTok happy_x_4 of { happy_var_4 -> 
	happyIn16
		 (SoftConstraint ((mkTokenSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3) >- (mkTokenSpan happy_var_4)) (reverse happy_var_3)
	) `HappyStk` happyRest}}}}

happyReduce_15 = happySpecReduce_3  9# happyReduction_15
happyReduction_15 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut58 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { happy_var_3 -> 
	happyIn17
		 (Goal ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2) >- (mkTokenSpan happy_var_3)) (reverse happy_var_2)
	)}}}

happyReduce_16 = happySpecReduce_0  10# happyReduction_16
happyReduction_16  =  happyIn18
		 (AbstractEmpty noSpan
	)

happyReduce_17 = happySpecReduce_1  10# happyReduction_17
happyReduction_17 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn18
		 (Abstract ((mkTokenSpan happy_var_1))
	)}

happyReduce_18 = happySpecReduce_0  11# happyReduction_18
happyReduction_18  =  happyIn19
		 (ElementsEmpty noSpan
	)

happyReduce_19 = happySpecReduce_3  11# happyReduction_19
happyReduction_19 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut57 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { happy_var_3 -> 
	happyIn19
		 (ElementsList ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2) >- (mkTokenSpan happy_var_3)) (reverse happy_var_2)
	)}}}

happyReduce_20 = happySpecReduce_1  12# happyReduction_20
happyReduction_20 happy_x_1
	 =  case happyOut14 happy_x_1 of { happy_var_1 -> 
	happyIn20
		 (Subclafer ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_21 = happyReduce 4# 12# happyReduction_21
happyReduction_21 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_2 of { happy_var_2 -> 
	case happyOut26 happy_x_3 of { happy_var_3 -> 
	case happyOut19 happy_x_4 of { happy_var_4 -> 
	happyIn20
		 (ClaferUse ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2) >- (mkCatSpan happy_var_3) >- (mkCatSpan happy_var_4)) happy_var_2 happy_var_3 happy_var_4
	) `HappyStk` happyRest}}}}

happyReduce_22 = happySpecReduce_1  12# happyReduction_22
happyReduction_22 happy_x_1
	 =  case happyOut15 happy_x_1 of { happy_var_1 -> 
	happyIn20
		 (Subconstraint ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_23 = happySpecReduce_1  12# happyReduction_23
happyReduction_23 happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	happyIn20
		 (Subgoal ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_24 = happySpecReduce_1  12# happyReduction_24
happyReduction_24 happy_x_1
	 =  case happyOut16 happy_x_1 of { happy_var_1 -> 
	happyIn20
		 (Subsoftconstraint ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_25 = happySpecReduce_0  13# happyReduction_25
happyReduction_25  =  happyIn21
		 (SuperEmpty noSpan
	)

happyReduce_26 = happySpecReduce_2  13# happyReduction_26
happyReduction_26 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut49 happy_x_2 of { happy_var_2 -> 
	happyIn21
		 (SuperSome ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_27 = happySpecReduce_0  14# happyReduction_27
happyReduction_27  =  happyIn22
		 (ReferenceEmpty noSpan
	)

happyReduce_28 = happySpecReduce_2  14# happyReduction_28
happyReduction_28 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_2 of { happy_var_2 -> 
	happyIn22
		 (ReferenceSet ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_29 = happySpecReduce_2  14# happyReduction_29
happyReduction_29 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_2 of { happy_var_2 -> 
	happyIn22
		 (ReferenceBag ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_30 = happySpecReduce_0  15# happyReduction_30
happyReduction_30  =  happyIn23
		 (InitEmpty noSpan
	)

happyReduce_31 = happySpecReduce_2  15# happyReduction_31
happyReduction_31 happy_x_2
	happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	case happyOut30 happy_x_2 of { happy_var_2 -> 
	happyIn23
		 (InitSome ((mkCatSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_1 happy_var_2
	)}}

happyReduce_32 = happySpecReduce_1  16# happyReduction_32
happyReduction_32 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn24
		 (InitConstant ((mkTokenSpan happy_var_1))
	)}

happyReduce_33 = happySpecReduce_1  16# happyReduction_33
happyReduction_33 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn24
		 (InitDefault ((mkTokenSpan happy_var_1))
	)}

happyReduce_34 = happySpecReduce_0  17# happyReduction_34
happyReduction_34  =  happyIn25
		 (GCardEmpty noSpan
	)

happyReduce_35 = happySpecReduce_1  17# happyReduction_35
happyReduction_35 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (GCardXor ((mkTokenSpan happy_var_1))
	)}

happyReduce_36 = happySpecReduce_1  17# happyReduction_36
happyReduction_36 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (GCardOr ((mkTokenSpan happy_var_1))
	)}

happyReduce_37 = happySpecReduce_1  17# happyReduction_37
happyReduction_37 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (GCardMux ((mkTokenSpan happy_var_1))
	)}

happyReduce_38 = happySpecReduce_1  17# happyReduction_38
happyReduction_38 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (GCardOpt ((mkTokenSpan happy_var_1))
	)}

happyReduce_39 = happySpecReduce_1  17# happyReduction_39
happyReduction_39 happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (GCardInterval ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_40 = happySpecReduce_0  18# happyReduction_40
happyReduction_40  =  happyIn26
		 (CardEmpty noSpan
	)

happyReduce_41 = happySpecReduce_1  18# happyReduction_41
happyReduction_41 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (CardLone ((mkTokenSpan happy_var_1))
	)}

happyReduce_42 = happySpecReduce_1  18# happyReduction_42
happyReduction_42 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (CardSome ((mkTokenSpan happy_var_1))
	)}

happyReduce_43 = happySpecReduce_1  18# happyReduction_43
happyReduction_43 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (CardAny ((mkTokenSpan happy_var_1))
	)}

happyReduce_44 = happySpecReduce_1  18# happyReduction_44
happyReduction_44 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (CardNum ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_45 = happySpecReduce_1  18# happyReduction_45
happyReduction_45 happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (CardInterval ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_46 = happySpecReduce_3  19# happyReduction_46
happyReduction_46 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut28 happy_x_3 of { happy_var_3 -> 
	happyIn27
		 (NCard ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_47 = happySpecReduce_1  20# happyReduction_47
happyReduction_47 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn28
		 (ExIntegerAst ((mkTokenSpan happy_var_1))
	)}

happyReduce_48 = happySpecReduce_1  20# happyReduction_48
happyReduction_48 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn28
		 (ExIntegerNum ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_49 = happySpecReduce_1  21# happyReduction_49
happyReduction_49 happy_x_1
	 =  case happyOut60 happy_x_1 of { happy_var_1 -> 
	happyIn29
		 (Path ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_50 = happyReduce 5# 22# happyReduction_50
happyReduction_50 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut50 happy_x_3 of { happy_var_3 -> 
	case happyOutTok happy_x_4 of { happy_var_4 -> 
	case happyOut30 happy_x_5 of { happy_var_5 -> 
	happyIn30
		 (EDeclAllDisj ((mkTokenSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3) >- (mkTokenSpan happy_var_4) >- (mkCatSpan happy_var_5)) happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}}}

happyReduce_51 = happyReduce 4# 22# happyReduction_51
happyReduction_51 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut50 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { happy_var_3 -> 
	case happyOut30 happy_x_4 of { happy_var_4 -> 
	happyIn30
		 (EDeclAll ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2) >- (mkTokenSpan happy_var_3) >- (mkCatSpan happy_var_4)) happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}}

happyReduce_52 = happyReduce 5# 22# happyReduction_52
happyReduction_52 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut51 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut50 happy_x_3 of { happy_var_3 -> 
	case happyOutTok happy_x_4 of { happy_var_4 -> 
	case happyOut30 happy_x_5 of { happy_var_5 -> 
	happyIn30
		 (EDeclQuantDisj ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3) >- (mkTokenSpan happy_var_4) >- (mkCatSpan happy_var_5)) happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}}}

happyReduce_53 = happyReduce 4# 22# happyReduction_53
happyReduction_53 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut51 happy_x_1 of { happy_var_1 -> 
	case happyOut50 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { happy_var_3 -> 
	case happyOut30 happy_x_4 of { happy_var_4 -> 
	happyIn30
		 (EDeclQuant ((mkCatSpan happy_var_1) >- (mkCatSpan happy_var_2) >- (mkTokenSpan happy_var_3) >- (mkCatSpan happy_var_4)) happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}}

happyReduce_54 = happySpecReduce_1  22# happyReduction_54
happyReduction_54 happy_x_1
	 =  case happyOut31 happy_x_1 of { happy_var_1 -> 
	happyIn30
		 (happy_var_1
	)}

happyReduce_55 = happySpecReduce_2  23# happyReduction_55
happyReduction_55 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut32 happy_x_2 of { happy_var_2 -> 
	happyIn31
		 (EGMax ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_56 = happySpecReduce_2  23# happyReduction_56
happyReduction_56 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut32 happy_x_2 of { happy_var_2 -> 
	happyIn31
		 (EGMin ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_57 = happySpecReduce_3  23# happyReduction_57
happyReduction_57 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut31 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut32 happy_x_3 of { happy_var_3 -> 
	happyIn31
		 (EIff ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_58 = happySpecReduce_1  23# happyReduction_58
happyReduction_58 happy_x_1
	 =  case happyOut32 happy_x_1 of { happy_var_1 -> 
	happyIn31
		 (happy_var_1
	)}

happyReduce_59 = happySpecReduce_3  24# happyReduction_59
happyReduction_59 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut32 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut33 happy_x_3 of { happy_var_3 -> 
	happyIn32
		 (EImplies ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_60 = happySpecReduce_1  24# happyReduction_60
happyReduction_60 happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (happy_var_1
	)}

happyReduce_61 = happySpecReduce_3  25# happyReduction_61
happyReduction_61 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut34 happy_x_3 of { happy_var_3 -> 
	happyIn33
		 (EOr ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_62 = happySpecReduce_1  25# happyReduction_62
happyReduction_62 happy_x_1
	 =  case happyOut34 happy_x_1 of { happy_var_1 -> 
	happyIn33
		 (happy_var_1
	)}

happyReduce_63 = happySpecReduce_3  26# happyReduction_63
happyReduction_63 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut34 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut35 happy_x_3 of { happy_var_3 -> 
	happyIn34
		 (EXor ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_64 = happySpecReduce_1  26# happyReduction_64
happyReduction_64 happy_x_1
	 =  case happyOut35 happy_x_1 of { happy_var_1 -> 
	happyIn34
		 (happy_var_1
	)}

happyReduce_65 = happySpecReduce_3  27# happyReduction_65
happyReduction_65 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut35 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut36 happy_x_3 of { happy_var_3 -> 
	happyIn35
		 (EAnd ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_66 = happySpecReduce_1  27# happyReduction_66
happyReduction_66 happy_x_1
	 =  case happyOut36 happy_x_1 of { happy_var_1 -> 
	happyIn35
		 (happy_var_1
	)}

happyReduce_67 = happySpecReduce_2  28# happyReduction_67
happyReduction_67 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut37 happy_x_2 of { happy_var_2 -> 
	happyIn36
		 (ENeg ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_68 = happySpecReduce_1  28# happyReduction_68
happyReduction_68 happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	happyIn36
		 (happy_var_1
	)}

happyReduce_69 = happySpecReduce_3  29# happyReduction_69
happyReduction_69 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut38 happy_x_3 of { happy_var_3 -> 
	happyIn37
		 (ELt ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_70 = happySpecReduce_3  29# happyReduction_70
happyReduction_70 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut38 happy_x_3 of { happy_var_3 -> 
	happyIn37
		 (EGt ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_71 = happySpecReduce_3  29# happyReduction_71
happyReduction_71 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut38 happy_x_3 of { happy_var_3 -> 
	happyIn37
		 (EEq ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_72 = happySpecReduce_3  29# happyReduction_72
happyReduction_72 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut38 happy_x_3 of { happy_var_3 -> 
	happyIn37
		 (ELte ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_73 = happySpecReduce_3  29# happyReduction_73
happyReduction_73 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut38 happy_x_3 of { happy_var_3 -> 
	happyIn37
		 (EGte ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_74 = happySpecReduce_3  29# happyReduction_74
happyReduction_74 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut38 happy_x_3 of { happy_var_3 -> 
	happyIn37
		 (ENeq ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_75 = happySpecReduce_3  29# happyReduction_75
happyReduction_75 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut38 happy_x_3 of { happy_var_3 -> 
	happyIn37
		 (EIn ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_76 = happyReduce 4# 29# happyReduction_76
happyReduction_76 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { happy_var_3 -> 
	case happyOut38 happy_x_4 of { happy_var_4 -> 
	happyIn37
		 (ENin ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkTokenSpan happy_var_3) >- (mkCatSpan happy_var_4)) happy_var_1 happy_var_4
	) `HappyStk` happyRest}}}}

happyReduce_77 = happySpecReduce_1  29# happyReduction_77
happyReduction_77 happy_x_1
	 =  case happyOut38 happy_x_1 of { happy_var_1 -> 
	happyIn37
		 (happy_var_1
	)}

happyReduce_78 = happySpecReduce_2  30# happyReduction_78
happyReduction_78 happy_x_2
	happy_x_1
	 =  case happyOut51 happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_2 of { happy_var_2 -> 
	happyIn38
		 (EQuantExp ((mkCatSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_1 happy_var_2
	)}}

happyReduce_79 = happySpecReduce_1  30# happyReduction_79
happyReduction_79 happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	happyIn38
		 (happy_var_1
	)}

happyReduce_80 = happySpecReduce_3  31# happyReduction_80
happyReduction_80 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut40 happy_x_3 of { happy_var_3 -> 
	happyIn39
		 (EAdd ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_81 = happySpecReduce_3  31# happyReduction_81
happyReduction_81 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut40 happy_x_3 of { happy_var_3 -> 
	happyIn39
		 (ESub ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_82 = happySpecReduce_1  31# happyReduction_82
happyReduction_82 happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (happy_var_1
	)}

happyReduce_83 = happySpecReduce_3  32# happyReduction_83
happyReduction_83 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut41 happy_x_3 of { happy_var_3 -> 
	happyIn40
		 (EMul ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_84 = happySpecReduce_3  32# happyReduction_84
happyReduction_84 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut41 happy_x_3 of { happy_var_3 -> 
	happyIn40
		 (EDiv ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_85 = happySpecReduce_3  32# happyReduction_85
happyReduction_85 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut41 happy_x_3 of { happy_var_3 -> 
	happyIn40
		 (ERem ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_86 = happySpecReduce_1  32# happyReduction_86
happyReduction_86 happy_x_1
	 =  case happyOut41 happy_x_1 of { happy_var_1 -> 
	happyIn40
		 (happy_var_1
	)}

happyReduce_87 = happySpecReduce_2  33# happyReduction_87
happyReduction_87 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_2 of { happy_var_2 -> 
	happyIn41
		 (ESum ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_88 = happySpecReduce_2  33# happyReduction_88
happyReduction_88 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_2 of { happy_var_2 -> 
	happyIn41
		 (EProd ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_89 = happySpecReduce_2  33# happyReduction_89
happyReduction_89 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_2 of { happy_var_2 -> 
	happyIn41
		 (ECard ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_90 = happySpecReduce_2  33# happyReduction_90
happyReduction_90 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_2 of { happy_var_2 -> 
	happyIn41
		 (EMinExp ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2)) happy_var_2
	)}}

happyReduce_91 = happySpecReduce_1  33# happyReduction_91
happyReduction_91 happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	happyIn41
		 (happy_var_1
	)}

happyReduce_92 = happyReduce 6# 34# happyReduction_92
happyReduction_92 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { happy_var_1 -> 
	case happyOut42 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { happy_var_3 -> 
	case happyOut42 happy_x_4 of { happy_var_4 -> 
	case happyOutTok happy_x_5 of { happy_var_5 -> 
	case happyOut43 happy_x_6 of { happy_var_6 -> 
	happyIn42
		 (EImpliesElse ((mkTokenSpan happy_var_1) >- (mkCatSpan happy_var_2) >- (mkTokenSpan happy_var_3) >- (mkCatSpan happy_var_4) >- (mkTokenSpan happy_var_5) >- (mkCatSpan happy_var_6)) happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}}}}

happyReduce_93 = happySpecReduce_1  34# happyReduction_93
happyReduction_93 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn42
		 (EInt ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_94 = happySpecReduce_1  34# happyReduction_94
happyReduction_94 happy_x_1
	 =  case happyOut9 happy_x_1 of { happy_var_1 -> 
	happyIn42
		 (EDouble ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_95 = happySpecReduce_1  34# happyReduction_95
happyReduction_95 happy_x_1
	 =  case happyOut10 happy_x_1 of { happy_var_1 -> 
	happyIn42
		 (EStr ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_96 = happySpecReduce_1  34# happyReduction_96
happyReduction_96 happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	happyIn42
		 (happy_var_1
	)}

happyReduce_97 = happySpecReduce_3  35# happyReduction_97
happyReduction_97 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn43
		 (EUnion ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_98 = happySpecReduce_3  35# happyReduction_98
happyReduction_98 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn43
		 (EUnionCom ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_99 = happySpecReduce_1  35# happyReduction_99
happyReduction_99 happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	happyIn43
		 (happy_var_1
	)}

happyReduce_100 = happySpecReduce_3  36# happyReduction_100
happyReduction_100 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut45 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (EDifference ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_101 = happySpecReduce_1  36# happyReduction_101
happyReduction_101 happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	happyIn44
		 (happy_var_1
	)}

happyReduce_102 = happySpecReduce_3  37# happyReduction_102
happyReduction_102 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut46 happy_x_3 of { happy_var_3 -> 
	happyIn45
		 (EIntersection ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_103 = happySpecReduce_1  37# happyReduction_103
happyReduction_103 happy_x_1
	 =  case happyOut46 happy_x_1 of { happy_var_1 -> 
	happyIn45
		 (happy_var_1
	)}

happyReduce_104 = happySpecReduce_3  38# happyReduction_104
happyReduction_104 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut46 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut47 happy_x_3 of { happy_var_3 -> 
	happyIn46
		 (EDomain ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_105 = happySpecReduce_1  38# happyReduction_105
happyReduction_105 happy_x_1
	 =  case happyOut47 happy_x_1 of { happy_var_1 -> 
	happyIn46
		 (happy_var_1
	)}

happyReduce_106 = happySpecReduce_3  39# happyReduction_106
happyReduction_106 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut47 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut48 happy_x_3 of { happy_var_3 -> 
	happyIn47
		 (ERange ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_107 = happySpecReduce_1  39# happyReduction_107
happyReduction_107 happy_x_1
	 =  case happyOut48 happy_x_1 of { happy_var_1 -> 
	happyIn47
		 (happy_var_1
	)}

happyReduce_108 = happySpecReduce_3  40# happyReduction_108
happyReduction_108 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut48 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut49 happy_x_3 of { happy_var_3 -> 
	happyIn48
		 (EJoin ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_109 = happySpecReduce_1  40# happyReduction_109
happyReduction_109 happy_x_1
	 =  case happyOut49 happy_x_1 of { happy_var_1 -> 
	happyIn48
		 (happy_var_1
	)}

happyReduce_110 = happySpecReduce_1  41# happyReduction_110
happyReduction_110 happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	happyIn49
		 (ClaferId ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_111 = happySpecReduce_3  41# happyReduction_111
happyReduction_111 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_2 of { happy_var_2 -> 
	happyIn49
		 (happy_var_2
	)}

happyReduce_112 = happySpecReduce_3  42# happyReduction_112
happyReduction_112 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut59 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { happy_var_2 -> 
	case happyOut43 happy_x_3 of { happy_var_3 -> 
	happyIn50
		 (Decl ((mkCatSpan happy_var_1) >- (mkTokenSpan happy_var_2) >- (mkCatSpan happy_var_3)) happy_var_1 happy_var_3
	)}}}

happyReduce_113 = happySpecReduce_1  43# happyReduction_113
happyReduction_113 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn51
		 (QuantNo ((mkTokenSpan happy_var_1))
	)}

happyReduce_114 = happySpecReduce_1  43# happyReduction_114
happyReduction_114 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn51
		 (QuantNot ((mkTokenSpan happy_var_1))
	)}

happyReduce_115 = happySpecReduce_1  43# happyReduction_115
happyReduction_115 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn51
		 (QuantLone ((mkTokenSpan happy_var_1))
	)}

happyReduce_116 = happySpecReduce_1  43# happyReduction_116
happyReduction_116 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn51
		 (QuantOne ((mkTokenSpan happy_var_1))
	)}

happyReduce_117 = happySpecReduce_1  43# happyReduction_117
happyReduction_117 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn51
		 (QuantSome ((mkTokenSpan happy_var_1))
	)}

happyReduce_118 = happySpecReduce_1  44# happyReduction_118
happyReduction_118 happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	happyIn52
		 (EnumIdIdent ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_119 = happySpecReduce_1  45# happyReduction_119
happyReduction_119 happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	happyIn53
		 (ModIdIdent ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_120 = happySpecReduce_1  46# happyReduction_120
happyReduction_120 happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	happyIn54
		 (LocIdIdent ((mkCatSpan happy_var_1)) happy_var_1
	)}

happyReduce_121 = happySpecReduce_0  47# happyReduction_121
happyReduction_121  =  happyIn55
		 ([]
	)

happyReduce_122 = happySpecReduce_2  47# happyReduction_122
happyReduction_122 happy_x_2
	happy_x_1
	 =  case happyOut55 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_2 of { happy_var_2 -> 
	happyIn55
		 (flip (:)  happy_var_1 happy_var_2
	)}}

happyReduce_123 = happySpecReduce_1  48# happyReduction_123
happyReduction_123 happy_x_1
	 =  case happyOut52 happy_x_1 of { happy_var_1 -> 
	happyIn56
		 ((:[])  happy_var_1
	)}

happyReduce_124 = happySpecReduce_3  48# happyReduction_124
happyReduction_124 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut52 happy_x_1 of { happy_var_1 -> 
	case happyOut56 happy_x_3 of { happy_var_3 -> 
	happyIn56
		 ((:)  happy_var_1 happy_var_3
	)}}

happyReduce_125 = happySpecReduce_0  49# happyReduction_125
happyReduction_125  =  happyIn57
		 ([]
	)

happyReduce_126 = happySpecReduce_2  49# happyReduction_126
happyReduction_126 happy_x_2
	happy_x_1
	 =  case happyOut57 happy_x_1 of { happy_var_1 -> 
	case happyOut20 happy_x_2 of { happy_var_2 -> 
	happyIn57
		 (flip (:)  happy_var_1 happy_var_2
	)}}

happyReduce_127 = happySpecReduce_0  50# happyReduction_127
happyReduction_127  =  happyIn58
		 ([]
	)

happyReduce_128 = happySpecReduce_2  50# happyReduction_128
happyReduction_128 happy_x_2
	happy_x_1
	 =  case happyOut58 happy_x_1 of { happy_var_1 -> 
	case happyOut30 happy_x_2 of { happy_var_2 -> 
	happyIn58
		 (flip (:)  happy_var_1 happy_var_2
	)}}

happyReduce_129 = happySpecReduce_1  51# happyReduction_129
happyReduction_129 happy_x_1
	 =  case happyOut54 happy_x_1 of { happy_var_1 -> 
	happyIn59
		 ((:[])  happy_var_1
	)}

happyReduce_130 = happySpecReduce_3  51# happyReduction_130
happyReduction_130 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut54 happy_x_1 of { happy_var_1 -> 
	case happyOut59 happy_x_3 of { happy_var_3 -> 
	happyIn59
		 ((:)  happy_var_1 happy_var_3
	)}}

happyReduce_131 = happySpecReduce_1  52# happyReduction_131
happyReduction_131 happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	happyIn60
		 ((:[])  happy_var_1
	)}

happyReduce_132 = happySpecReduce_3  52# happyReduction_132
happyReduction_132 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	case happyOut60 happy_x_3 of { happy_var_3 -> 
	happyIn60
		 ((:)  happy_var_1 happy_var_3
	)}}

happyNewToken action sts stk [] =
	happyDoAction 69# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TS _ 12) -> cont 12#;
	PT _ (TS _ 13) -> cont 13#;
	PT _ (TS _ 14) -> cont 14#;
	PT _ (TS _ 15) -> cont 15#;
	PT _ (TS _ 16) -> cont 16#;
	PT _ (TS _ 17) -> cont 17#;
	PT _ (TS _ 18) -> cont 18#;
	PT _ (TS _ 19) -> cont 19#;
	PT _ (TS _ 20) -> cont 20#;
	PT _ (TS _ 21) -> cont 21#;
	PT _ (TS _ 22) -> cont 22#;
	PT _ (TS _ 23) -> cont 23#;
	PT _ (TS _ 24) -> cont 24#;
	PT _ (TS _ 25) -> cont 25#;
	PT _ (TS _ 26) -> cont 26#;
	PT _ (TS _ 27) -> cont 27#;
	PT _ (TS _ 28) -> cont 28#;
	PT _ (TS _ 29) -> cont 29#;
	PT _ (TS _ 30) -> cont 30#;
	PT _ (TS _ 31) -> cont 31#;
	PT _ (TS _ 32) -> cont 32#;
	PT _ (TS _ 33) -> cont 33#;
	PT _ (TS _ 34) -> cont 34#;
	PT _ (TS _ 35) -> cont 35#;
	PT _ (TS _ 36) -> cont 36#;
	PT _ (TS _ 37) -> cont 37#;
	PT _ (TS _ 38) -> cont 38#;
	PT _ (TS _ 39) -> cont 39#;
	PT _ (TS _ 40) -> cont 40#;
	PT _ (TS _ 41) -> cont 41#;
	PT _ (TS _ 42) -> cont 42#;
	PT _ (TS _ 43) -> cont 43#;
	PT _ (TS _ 44) -> cont 44#;
	PT _ (TS _ 45) -> cont 45#;
	PT _ (TS _ 46) -> cont 46#;
	PT _ (TS _ 47) -> cont 47#;
	PT _ (TS _ 48) -> cont 48#;
	PT _ (TS _ 49) -> cont 49#;
	PT _ (TS _ 50) -> cont 50#;
	PT _ (TS _ 51) -> cont 51#;
	PT _ (TS _ 52) -> cont 52#;
	PT _ (TS _ 53) -> cont 53#;
	PT _ (TS _ 54) -> cont 54#;
	PT _ (TS _ 55) -> cont 55#;
	PT _ (TS _ 56) -> cont 56#;
	PT _ (TS _ 57) -> cont 57#;
	PT _ (TS _ 58) -> cont 58#;
	PT _ (TS _ 59) -> cont 59#;
	PT _ (TS _ 60) -> cont 60#;
	PT _ (TS _ 61) -> cont 61#;
	PT _ (TS _ 62) -> cont 62#;
	PT _ (TS _ 63) -> cont 63#;
	PT _ (TS _ 64) -> cont 64#;
	PT _ (T_PosInteger _) -> cont 65#;
	PT _ (T_PosDouble _) -> cont 66#;
	PT _ (T_PosString _) -> cont 67#;
	PT _ (T_PosIdent _) -> cont 68#;
	_ -> happyError' (tk:tks)
	}

happyError_ 69# tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = (thenM)
happyReturn :: () => a -> Err a
happyReturn = (returnM)
happyThen1 m k tks = (thenM) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (returnM) a
happyError' :: () => [(Token)] -> Err a
happyError' = happyError

pModule tks = happySomeParser where
  happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (happyOut12 x))

pClafer tks = happySomeParser where
  happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (happyOut14 x))

pConstraint tks = happySomeParser where
  happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (happyOut15 x))

pSoftConstraint tks = happySomeParser where
  happySomeParser = happyThen (happyParse 3# tks) (\x -> happyReturn (happyOut16 x))

pGoal tks = happySomeParser where
  happySomeParser = happyThen (happyParse 4# tks) (\x -> happyReturn (happyOut17 x))

happySeq = happyDontSeq


returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad (pp ts) $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens

gp x@(PT (Pn _ l c) _) = Span (Pos (toInteger l) (toInteger c)) (Pos (toInteger l) (toInteger c + toInteger (length $ prToken x)))
pp (PT (Pn _ l c) _ :_) = Pos (toInteger l) (toInteger c)
pp (Err (Pn _ l c) :_) = Pos (toInteger l) (toInteger c)
pp _ = error "EOF"

mkCatSpan :: (Spannable c) => c -> Span
mkCatSpan = getSpan

mkTokenSpan :: Token -> Span
mkTokenSpan = gp
{-# LINE 1 "templates\GenericTemplate.hs" #-}
{-# LINE 1 "templates\\GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 9 "<command-line>" #-}
{-# LINE 1 "C:\\dev\\MinGHC-7.10.1\\ghc-7.10.1\\lib/include\\ghcversion.h" #-}

















{-# LINE 9 "<command-line>" #-}
{-# LINE 1 "templates\\GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 13 "templates\\GenericTemplate.hs" #-}





-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif
{-# LINE 46 "templates\\GenericTemplate.hs" #-}


data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList





{-# LINE 67 "templates\\GenericTemplate.hs" #-}

{-# LINE 77 "templates\\GenericTemplate.hs" #-}

{-# LINE 86 "templates\\GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is 0#, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}


          case action of
                0#           -> {- nothing -}
                                     happyFail i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}

                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}


                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = indexShortOffAddr happyActOffsets st
         off_i  = (off Happy_GHC_Exts.+# i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else False
         action
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st


indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#





data HappyAddr = HappyA# Happy_GHC_Exts.Addr#




-----------------------------------------------------------------------------
-- HappyState data type (not arrays)

{-# LINE 170 "templates\\GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = indexShortOffAddr happyGotoOffsets st1
             off_i = (off Happy_GHC_Exts.+# nt)
             new_state = indexShortOffAddr happyTable off_i



          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = indexShortOffAddr happyGotoOffsets st
         off_i = (off Happy_GHC_Exts.+# nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        happyDoAction 0# tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ( (Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
