{-# OPTIONS_GHC -w #-}
{-# OPTIONS -fglasgow-exts -cpp #-}
{-# OPTIONS -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Parclafer where
import Absclafer
import Lexclafer
import ErrM
import qualified Data.Array as Happy_Data_Array
import qualified GHC.Exts as Happy_GHC_Exts

-- parser produced by Happy Version 1.18.6

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn4 :: (Ident) -> (HappyAbsSyn )
happyIn4 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn4 #-}
happyOut4 :: (HappyAbsSyn ) -> (Ident)
happyOut4 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut4 #-}
happyIn5 :: (Integer) -> (HappyAbsSyn )
happyIn5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn5 #-}
happyOut5 :: (HappyAbsSyn ) -> (Integer)
happyOut5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut5 #-}
happyIn6 :: (String) -> (HappyAbsSyn )
happyIn6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn6 #-}
happyOut6 :: (HappyAbsSyn ) -> (String)
happyOut6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut6 #-}
happyIn7 :: (Module) -> (HappyAbsSyn )
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn ) -> (Module)
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
happyIn8 :: (Declaration) -> (HappyAbsSyn )
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> (Declaration)
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
happyIn9 :: (Clafer) -> (HappyAbsSyn )
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> (Clafer)
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
happyIn10 :: (Constraint) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> (Constraint)
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
happyIn11 :: (Abstract) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> (Abstract)
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: (Elements) -> (HappyAbsSyn )
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> (Elements)
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
happyIn13 :: (ElementCl) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> (ElementCl)
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: (Super) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> (Super)
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyIn15 :: (GCard) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> (GCard)
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyIn16 :: (Card) -> (HappyAbsSyn )
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> (Card)
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
happyIn17 :: (GNCard) -> (HappyAbsSyn )
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> (GNCard)
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
happyIn18 :: (NCard) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> (NCard)
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: (ExInteger) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> (ExInteger)
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: (Name) -> (HappyAbsSyn )
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> (Name)
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
happyIn21 :: (Exp) -> (HappyAbsSyn )
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> (Exp)
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyIn22 :: (Exp) -> (HappyAbsSyn )
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> (Exp)
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
happyIn23 :: (Exp) -> (HappyAbsSyn )
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> (Exp)
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
happyIn24 :: (Exp) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> (Exp)
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyIn25 :: (Exp) -> (HappyAbsSyn )
happyIn25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn ) -> (Exp)
happyOut25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut25 #-}
happyIn26 :: (Exp) -> (HappyAbsSyn )
happyIn26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn ) -> (Exp)
happyOut26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut26 #-}
happyIn27 :: (Exp) -> (HappyAbsSyn )
happyIn27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn ) -> (Exp)
happyOut27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut27 #-}
happyIn28 :: (Exp) -> (HappyAbsSyn )
happyIn28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn ) -> (Exp)
happyOut28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut28 #-}
happyIn29 :: (Exp) -> (HappyAbsSyn )
happyIn29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn ) -> (Exp)
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
happyIn38 :: (Decl) -> (HappyAbsSyn )
happyIn38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn38 #-}
happyOut38 :: (HappyAbsSyn ) -> (Decl)
happyOut38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut38 #-}
happyIn39 :: (Disj) -> (HappyAbsSyn )
happyIn39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn39 #-}
happyOut39 :: (HappyAbsSyn ) -> (Disj)
happyOut39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut39 #-}
happyIn40 :: (Quant) -> (HappyAbsSyn )
happyIn40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn40 #-}
happyOut40 :: (HappyAbsSyn ) -> (Quant)
happyOut40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut40 #-}
happyIn41 :: (ExQuant) -> (HappyAbsSyn )
happyIn41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn41 #-}
happyOut41 :: (HappyAbsSyn ) -> (ExQuant)
happyOut41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut41 #-}
happyIn42 :: (EnumId) -> (HappyAbsSyn )
happyIn42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn42 #-}
happyOut42 :: (HappyAbsSyn ) -> (EnumId)
happyOut42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut42 #-}
happyIn43 :: (ModId) -> (HappyAbsSyn )
happyIn43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn43 #-}
happyOut43 :: (HappyAbsSyn ) -> (ModId)
happyOut43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut43 #-}
happyIn44 :: (LocId) -> (HappyAbsSyn )
happyIn44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn44 #-}
happyOut44 :: (HappyAbsSyn ) -> (LocId)
happyOut44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut44 #-}
happyIn45 :: ([Declaration]) -> (HappyAbsSyn )
happyIn45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn45 #-}
happyOut45 :: (HappyAbsSyn ) -> ([Declaration])
happyOut45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut45 #-}
happyIn46 :: ([EnumId]) -> (HappyAbsSyn )
happyIn46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn46 #-}
happyOut46 :: (HappyAbsSyn ) -> ([EnumId])
happyOut46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut46 #-}
happyIn47 :: ([ElementCl]) -> (HappyAbsSyn )
happyIn47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn47 #-}
happyOut47 :: (HappyAbsSyn ) -> ([ElementCl])
happyOut47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut47 #-}
happyIn48 :: ([Exp]) -> (HappyAbsSyn )
happyIn48 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn48 #-}
happyOut48 :: (HappyAbsSyn ) -> ([Exp])
happyOut48 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut48 #-}
happyIn49 :: ([Decl]) -> (HappyAbsSyn )
happyIn49 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn49 #-}
happyOut49 :: (HappyAbsSyn ) -> ([Decl])
happyOut49 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut49 #-}
happyIn50 :: ([LocId]) -> (HappyAbsSyn )
happyIn50 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn50 #-}
happyOut50 :: (HappyAbsSyn ) -> ([LocId])
happyOut50 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut50 #-}
happyIn51 :: ([ModId]) -> (HappyAbsSyn )
happyIn51 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn51 #-}
happyOut51 :: (HappyAbsSyn ) -> ([ModId])
happyOut51 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut51 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x00\x00\x17\x01\x00\x00\x11\x01\xff\xff\x00\x00\x00\x00\x00\x00\x57\x00\x00\x00\x00\x00\x13\x01\x46\x01\x04\x00\x0a\x01\x0c\x01\x00\x00\x00\x00\x00\x00\x00\x00\x30\x01\x23\x01\x00\x00\xfc\xff\x09\x01\x00\x00\x00\x00\x00\x00\x00\x00\x1d\x01\x16\x01\x14\x01\xf5\x00\x12\x01\x00\x00\xf0\x03\x50\x00\x95\x00\x00\x00\xf0\xff\x03\x01\x04\x01\x00\x01\xf7\x00\x00\x00\x3d\x02\xef\x00\xe3\x00\xd1\x00\x00\x00\x3d\x02\xe3\xff\xf4\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd1\x00\x00\x00\xf3\x00\x00\x00\xdd\x00\xf0\xff\xf0\x03\x3d\x02\x00\x00\xcb\x00\xd9\x00\xc3\x00\xe7\x00\x00\x00\xf0\x03\xe3\xff\xe3\xff\xe3\xff\xe3\xff\xe3\xff\xe3\xff\xc4\x01\xc4\x01\xc4\x01\xc4\x01\xc4\x01\xc4\x01\xc4\x01\xc4\x01\xc4\x01\xc4\x01\xc4\x01\xc4\x00\x03\x04\x03\x04\x03\x04\x03\x04\x03\x04\xfd\xff\xb9\x00\xf4\x03\xb9\x00\x00\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xce\x00\xd4\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb4\x00\xf2\xff\x9b\x00\x9e\x00\x00\x00\xc4\x01\x50\x00\x50\x00\x50\x00\x50\x00\x50\x00\x50\x00\x50\x00\x95\x00\x95\x00\x00\x00\x00\x00\x96\x00\x96\x00\x92\x00\x90\x00\x89\x00\x00\x00\x03\x04\x00\x00\x86\x00\x98\x00\x63\x00\x00\x00\x00\x00\x00\x00\x4c\x00\x00\x00\x00\x00\xf4\x03\x4c\x00\x6e\x00\x50\x00\x03\x04\x00\x00\x00\x00\x18\x00\x00\x00\x11\x00\x67\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x2e\x00\xfd\xff\x5e\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x0c\x00\x00\x00\x00\x00\x00\x00\xf8\x00\x00\x00\x00\x00\x00\x00\x6b\x00\x35\x00\x00\x00\x5f\x00\x00\x00\xa4\x00\x59\x00\x9d\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x34\x02\x02\x01\x00\x00\x14\x00\x00\x00\x0c\x02\xb4\x03\x7c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x87\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe4\x01\x00\x00\x2b\x00\x00\x00\x58\x00\x00\x00\x00\x00\x00\x00\x70\x01\x99\x01\xde\x03\xcc\x03\xb9\x03\x02\x00\xa0\x03\x8b\x03\x76\x03\x60\x03\x4a\x03\x28\x03\x06\x03\xe4\x02\xc2\x02\xa0\x02\x7e\x02\x00\x00\xbc\x01\x94\x01\x6c\x01\x44\x01\xf4\x00\xc6\x00\x1a\x01\x54\x00\xf2\x00\x00\x00\x76\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x47\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x5c\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xcc\x00\x00\x00\x00\x00\x00\x00\xae\x00\x00\x00\x00\x00\x00\x00\x82\x00\x00\x00\x00\x00\x2c\x00\x2f\x00\x00\x00\x00\x00\x1c\x01\x00\x00\xe6\xff\x0d\x00\x00\x00\xd0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xca\x00\x0f\x00\x05\x00\x00\x00\x00\x00"#

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\x9d\xff\x00\x00\xfe\xff\x00\x00\xf5\xff\x9c\xff\xf9\xff\xf8\xff\xea\xff\x97\xff\xf4\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe7\xff\xe6\xff\xe8\xff\xe9\xff\x00\x00\x00\x00\xfd\xff\xee\xff\xdb\xff\xb9\xff\xb8\xff\xab\xff\x96\xff\xd8\xff\xd6\xff\xd3\xff\xd1\xff\xcf\xff\xcd\xff\xcb\xff\xc1\xff\xbe\xff\xbb\xff\xb7\xff\xb4\xff\xb2\xff\xb0\xff\xae\xff\xac\xff\xa1\xff\xa8\xff\x00\x00\x00\x00\xf6\xff\x00\x00\x00\x00\x00\x00\xa2\xff\xa5\xff\xa6\xff\xa4\xff\xa3\xff\xfc\xff\x00\x00\xa0\xff\x9b\xff\xfa\xff\x00\x00\xba\xff\xcc\xff\x00\x00\xda\xff\x00\x00\x95\xff\x00\x00\x00\x00\xa7\xff\xca\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe4\xff\x00\x00\x00\x00\x00\x00\xe5\xff\x00\x00\xdc\xff\xdf\xff\xdd\xff\xec\xff\xeb\xff\xed\xff\x00\x00\xf3\xff\xe0\xff\xe3\xff\xe2\xff\xe1\xff\xd7\xff\xd5\xff\xd2\xff\xd0\xff\xce\xff\x00\x00\xc3\xff\xc4\xff\xc5\xff\xc6\xff\xc8\xff\xc9\xff\xc7\xff\xbf\xff\xc0\xff\xbc\xff\xbd\xff\xb5\xff\xb6\xff\xb3\xff\xb1\xff\xaf\xff\xad\xff\x00\x00\x9e\xff\x93\xff\x00\x00\xa8\xff\x9f\xff\x90\xff\xaa\xff\x00\x00\x9a\xff\x94\xff\x00\x00\x00\x00\xd9\xff\xc2\xff\x00\x00\xf7\xff\x99\xff\x00\x00\xde\xff\xf5\xff\xd4\xff\x92\xff\xa9\xff\xf1\xff\xef\xff\x98\xff\xf2\xff\x00\x00\xe4\xff\xf3\xff\xf0\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x02\x00\x00\x00\x07\x00\x08\x00\x13\x00\x23\x00\x03\x00\x0b\x00\x0c\x00\x0d\x00\x1b\x00\x1c\x00\x08\x00\x01\x00\x03\x00\x01\x00\x2b\x00\x10\x00\x02\x00\x00\x00\x0a\x00\x05\x00\x06\x00\x35\x00\x15\x00\x28\x00\x0c\x00\x0f\x00\x0e\x00\x1a\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x25\x00\x0d\x00\x2a\x00\x23\x00\x29\x00\x27\x00\x26\x00\x00\x00\x00\x00\x01\x00\x02\x00\x00\x00\x2c\x00\x2f\x00\x2e\x00\x36\x00\x30\x00\x29\x00\x25\x00\x33\x00\x39\x00\x35\x00\x36\x00\x37\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x36\x00\x08\x00\x24\x00\x25\x00\x27\x00\x27\x00\x00\x00\x01\x00\x02\x00\x28\x00\x00\x00\x00\x00\x2f\x00\x2f\x00\x0c\x00\x2e\x00\x0e\x00\x00\x00\x09\x00\x2c\x00\x04\x00\x35\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x0b\x00\x01\x00\x24\x00\x25\x00\x13\x00\x27\x00\x00\x00\x01\x00\x02\x00\x11\x00\x28\x00\x35\x00\x00\x00\x2f\x00\x2d\x00\x0f\x00\x2e\x00\x00\x00\x31\x00\x32\x00\x27\x00\x34\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x01\x00\x07\x00\x24\x00\x25\x00\x0d\x00\x27\x00\x00\x00\x01\x00\x02\x00\x21\x00\x26\x00\x20\x00\x0d\x00\x2f\x00\x2a\x00\x26\x00\x19\x00\x1f\x00\x1e\x00\x2a\x00\x14\x00\x1d\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x12\x00\x01\x00\x24\x00\x25\x00\x00\x00\x27\x00\x00\x00\x01\x00\x02\x00\x34\x00\x22\x00\x23\x00\x0c\x00\x2f\x00\x0e\x00\x05\x00\x06\x00\x07\x00\x04\x00\x09\x00\x10\x00\x2d\x00\x10\x00\x0f\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x35\x00\x2b\x00\x24\x00\x27\x00\x00\x00\x27\x00\x00\x00\x01\x00\x02\x00\x10\x00\x35\x00\x2f\x00\x21\x00\x2f\x00\x04\x00\x05\x00\x06\x00\x07\x00\x35\x00\x24\x00\x10\x00\x10\x00\x10\x00\x22\x00\x35\x00\x13\x00\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x27\x00\x20\x00\x24\x00\x27\x00\x00\x00\x27\x00\x00\x00\x01\x00\x02\x00\x1f\x00\x1d\x00\x2f\x00\x1e\x00\x2f\x00\x22\x00\x23\x00\x14\x00\x13\x00\x12\x00\x34\x00\x10\x00\x22\x00\x10\x00\x0a\x00\x11\x00\x2d\x00\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x0e\x00\x35\x00\x24\x00\x27\x00\x36\x00\x27\x00\x00\x00\x01\x00\x02\x00\x01\x00\x35\x00\x2f\x00\x39\x00\x2f\x00\x35\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\x24\x00\xff\xff\xff\xff\x27\x00\x00\x00\x01\x00\x02\x00\xff\xff\x00\x00\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\x10\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\x24\x00\x21\x00\xff\xff\x27\x00\x00\x00\x01\x00\x02\x00\x27\x00\xff\xff\x00\x00\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\x24\x00\x20\x00\x21\x00\x27\x00\x00\x00\x01\x00\x02\x00\xff\xff\x27\x00\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x1a\x00\xff\xff\x24\x00\xff\xff\xff\xff\x27\x00\x00\x00\x01\x00\x02\x00\x23\x00\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\x35\x00\x36\x00\x37\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\x24\x00\xff\xff\xff\xff\x27\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\x24\x00\xff\xff\xff\xff\x27\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\x1a\x00\x24\x00\xff\xff\xff\xff\x27\x00\x00\x00\x01\x00\x02\x00\xff\xff\x23\x00\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2c\x00\xff\xff\x2e\x00\x10\x00\x30\x00\xff\xff\xff\xff\x33\x00\xff\xff\x35\x00\x36\x00\x37\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x27\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x27\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x27\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x27\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x27\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x27\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x27\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\x27\x00\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x2f\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\xff\xff\xff\xff\x10\x00\x27\x00\xff\xff\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\x2f\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\xff\xff\x10\x00\xff\xff\x27\x00\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x2f\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\xff\xff\x10\x00\xff\xff\x27\x00\xff\xff\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x2f\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\x10\x00\xff\xff\xff\xff\x27\x00\xff\xff\x10\x00\xff\xff\xff\xff\x00\x00\xff\xff\xff\xff\x2f\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x27\x00\x10\x00\xff\xff\x00\x00\xff\xff\x27\x00\xff\xff\xff\xff\x2f\x00\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\x1e\x00\x1f\x00\x20\x00\x21\x00\x10\x00\xff\xff\xff\xff\x01\x00\xff\xff\x27\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x09\x00\x0a\x00\x2f\x00\xff\xff\x1f\x00\x20\x00\x21\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x27\x00\x16\x00\x17\x00\x18\x00\x15\x00\xff\xff\xff\xff\xff\xff\x2f\x00\x1a\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x23\x00\x15\x00\xff\xff\x26\x00\x2b\x00\xff\xff\x1a\x00\xff\xff\x2f\x00\x2c\x00\xff\xff\x2e\x00\xff\xff\x30\x00\xff\xff\x23\x00\x33\x00\xff\xff\x35\x00\x36\x00\x37\x00\xff\xff\xff\xff\xff\xff\x2c\x00\xff\xff\x2e\x00\xff\xff\x30\x00\xff\xff\xff\xff\x33\x00\xff\xff\x35\x00\x36\x00\x37\x00\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x0a\x00\x18\x00\x63\x00\x64\x00\x5f\x00\x35\x00\x32\x00\x71\x00\x72\x00\x73\x00\x4f\x00\x50\x00\xa9\x00\x67\x00\x03\x00\x6d\x00\x9e\x00\x1b\x00\x0a\x00\x43\x00\x61\x00\xa6\x00\xa7\x00\x03\x00\x33\x00\x9a\x00\xa8\x00\x9d\x00\x6f\x00\x34\x00\x84\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x0b\x00\x6a\x00\x65\x00\x35\x00\x0c\x00\x2f\x00\x36\x00\x8f\x00\x18\x00\x19\x00\x1a\x00\x8b\x00\x37\x00\x30\x00\x38\x00\x17\x00\x39\x00\x04\x00\x0b\x00\x3a\x00\xfb\xff\x03\x00\x17\x00\x3b\x00\x1b\x00\xa1\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x17\x00\x9a\x00\x2d\x00\x2e\x00\x2f\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x8c\x00\x8b\x00\x17\x00\x90\x00\x30\x00\x53\x00\xa0\x00\x54\x00\x0c\x00\x10\x00\x0d\x00\x9c\x00\x03\x00\x1b\x00\x6b\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x0e\x00\x67\x00\x2d\x00\x2e\x00\x5f\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x61\x00\x8c\x00\x03\x00\x3c\x00\x30\x00\x11\x00\x68\x00\x8d\x00\x3c\x00\x12\x00\x13\x00\x49\x00\x14\x00\x1b\x00\x3f\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x14\x00\x96\x00\x2d\x00\x2e\x00\x51\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x97\x00\x3d\x00\x4b\x00\x15\x00\x30\x00\x93\x00\x3d\x00\x52\x00\x4c\x00\x4d\x00\x3e\x00\x5d\x00\x4e\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x60\x00\x6d\x00\x2d\x00\x2e\x00\x18\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x5e\x00\x45\x00\x46\x00\x6e\x00\x30\x00\x6f\x00\xa2\x00\xa3\x00\x08\x00\x9c\x00\xa4\x00\xa7\x00\x94\x00\x1b\x00\x9d\x00\x97\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x03\x00\x79\x00\x42\x00\x2f\x00\x18\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x8b\x00\x03\x00\x30\x00\x8f\x00\x30\x00\x05\x00\x06\x00\x07\x00\x08\x00\x03\x00\x92\x00\x6a\x00\x93\x00\x1b\x00\x45\x00\x03\x00\x73\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x49\x00\x4b\x00\x42\x00\x2f\x00\x18\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x4c\x00\x4e\x00\x30\x00\x4d\x00\x30\x00\x45\x00\x46\x00\x5d\x00\x5f\x00\x60\x00\x5e\x00\x6c\x00\x9f\xff\x1b\x00\x66\x00\x61\x00\x47\x00\x9f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x67\x00\x03\x00\x42\x00\x2f\x00\x17\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x3c\x00\x03\x00\x30\x00\xff\xff\x30\x00\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x74\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x18\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x75\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x42\x00\x89\x00\x00\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x2f\x00\x00\x00\x18\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x76\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x42\x00\x88\x00\x2c\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x77\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x34\x00\x00\x00\x42\x00\x00\x00\x00\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x35\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03\x00\x17\x00\x3b\x00\x49\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x41\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x42\x00\x00\x00\x00\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x49\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x34\x00\x42\x00\x00\x00\x00\x00\x2f\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x35\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x37\x00\x00\x00\x38\x00\x1b\x00\x39\x00\x00\x00\x00\x00\x3a\x00\x00\x00\x03\x00\x17\x00\x3b\x00\x98\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x79\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7a\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7b\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7c\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7d\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7e\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x18\x00\x19\x00\x1a\x00\x7f\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x18\x00\x19\x00\x1a\x00\x30\x00\x80\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x30\x00\x81\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x18\x00\x19\x00\x1a\x00\x00\x00\x00\x00\x30\x00\x82\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x2f\x00\x00\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x18\x00\x30\x00\x83\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x2f\x00\x00\x00\x1b\x00\x00\x00\x00\x00\x18\x00\x00\x00\x00\x00\x30\x00\x40\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x85\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2f\x00\x1b\x00\x00\x00\x18\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x30\x00\x00\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x86\x00\x2a\x00\x2b\x00\x2c\x00\x1b\x00\x00\x00\x00\x00\x55\x00\x00\x00\x2f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x56\x00\x57\x00\x30\x00\x00\x00\x87\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x2f\x00\x58\x00\x59\x00\x5a\x00\x33\x00\x00\x00\x00\x00\x00\x00\x30\x00\x34\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x35\x00\x33\x00\x00\x00\x36\x00\x5b\x00\x00\x00\x34\x00\x00\x00\x5c\x00\x37\x00\x00\x00\x38\x00\x00\x00\x39\x00\x00\x00\x35\x00\x3a\x00\x00\x00\x03\x00\x17\x00\x3b\x00\x00\x00\x00\x00\x00\x00\x37\x00\x00\x00\x38\x00\x00\x00\x39\x00\x00\x00\x00\x00\x3a\x00\x00\x00\x03\x00\x17\x00\x3b\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (1, 111) [
	(1 , happyReduce_1),
	(2 , happyReduce_2),
	(3 , happyReduce_3),
	(4 , happyReduce_4),
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
	(111 , happyReduce_111)
	]

happy_n_terms = 58 :: Int
happy_n_nonterms = 48 :: Int

happyReduce_1 = happySpecReduce_1  0# happyReduction_1
happyReduction_1 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TV happy_var_1)) -> 
	happyIn4
		 (Ident happy_var_1
	)}

happyReduce_2 = happySpecReduce_1  1# happyReduction_2
happyReduction_2 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TI happy_var_1)) -> 
	happyIn5
		 ((read happy_var_1) :: Integer
	)}

happyReduce_3 = happySpecReduce_1  2# happyReduction_3
happyReduction_3 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TL happy_var_1)) -> 
	happyIn6
		 (happy_var_1
	)}

happyReduce_4 = happySpecReduce_1  3# happyReduction_4
happyReduction_4 happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	happyIn7
		 (Module (reverse happy_var_1)
	)}

happyReduce_5 = happyReduce 4# 4# happyReduction_5
happyReduction_5 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut4 happy_x_2 of { happy_var_2 -> 
	case happyOut46 happy_x_4 of { happy_var_4 -> 
	happyIn8
		 (EnumDecl happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_6 = happySpecReduce_1  4# happyReduction_6
happyReduction_6 happy_x_1
	 =  case happyOut9 happy_x_1 of { happy_var_1 -> 
	happyIn8
		 (ClaferDecl happy_var_1
	)}

happyReduce_7 = happySpecReduce_1  4# happyReduction_7
happyReduction_7 happy_x_1
	 =  case happyOut10 happy_x_1 of { happy_var_1 -> 
	happyIn8
		 (ConstDecl happy_var_1
	)}

happyReduce_8 = happyReduce 6# 5# happyReduction_8
happyReduction_8 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut11 happy_x_1 of { happy_var_1 -> 
	case happyOut15 happy_x_2 of { happy_var_2 -> 
	case happyOut4 happy_x_3 of { happy_var_3 -> 
	case happyOut14 happy_x_4 of { happy_var_4 -> 
	case happyOut16 happy_x_5 of { happy_var_5 -> 
	case happyOut12 happy_x_6 of { happy_var_6 -> 
	happyIn9
		 (Clafer happy_var_1 happy_var_2 happy_var_3 happy_var_4 happy_var_5 happy_var_6
	) `HappyStk` happyRest}}}}}}

happyReduce_9 = happySpecReduce_3  6# happyReduction_9
happyReduction_9 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut48 happy_x_2 of { happy_var_2 -> 
	happyIn10
		 (Constraint (reverse happy_var_2)
	)}

happyReduce_10 = happySpecReduce_0  7# happyReduction_10
happyReduction_10  =  happyIn11
		 (AbstractEmpty
	)

happyReduce_11 = happySpecReduce_1  7# happyReduction_11
happyReduction_11 happy_x_1
	 =  happyIn11
		 (Abstract
	)

happyReduce_12 = happySpecReduce_0  8# happyReduction_12
happyReduction_12  =  happyIn12
		 (ElementsEmpty
	)

happyReduce_13 = happySpecReduce_3  8# happyReduction_13
happyReduction_13 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut47 happy_x_2 of { happy_var_2 -> 
	happyIn12
		 (ElementsList (reverse happy_var_2)
	)}

happyReduce_14 = happySpecReduce_1  9# happyReduction_14
happyReduction_14 happy_x_1
	 =  case happyOut9 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (Subclafer happy_var_1
	)}

happyReduce_15 = happyReduce 4# 9# happyReduction_15
happyReduction_15 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut20 happy_x_2 of { happy_var_2 -> 
	case happyOut16 happy_x_3 of { happy_var_3 -> 
	case happyOut12 happy_x_4 of { happy_var_4 -> 
	happyIn13
		 (ClaferUse happy_var_2 happy_var_3 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_16 = happySpecReduce_1  9# happyReduction_16
happyReduction_16 happy_x_1
	 =  case happyOut10 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (Subconstraint happy_var_1
	)}

happyReduce_17 = happySpecReduce_0  10# happyReduction_17
happyReduction_17  =  happyIn14
		 (SuperEmpty
	)

happyReduce_18 = happySpecReduce_2  10# happyReduction_18
happyReduction_18 happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_2 of { happy_var_2 -> 
	happyIn14
		 (SuperColon happy_var_2
	)}

happyReduce_19 = happySpecReduce_2  10# happyReduction_19
happyReduction_19 happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_2 of { happy_var_2 -> 
	happyIn14
		 (SuperExtends happy_var_2
	)}

happyReduce_20 = happySpecReduce_2  10# happyReduction_20
happyReduction_20 happy_x_2
	happy_x_1
	 =  case happyOut21 happy_x_2 of { happy_var_2 -> 
	happyIn14
		 (SuperArrow happy_var_2
	)}

happyReduce_21 = happySpecReduce_0  11# happyReduction_21
happyReduction_21  =  happyIn15
		 (GCardEmpty
	)

happyReduce_22 = happySpecReduce_1  11# happyReduction_22
happyReduction_22 happy_x_1
	 =  happyIn15
		 (GCardXor
	)

happyReduce_23 = happySpecReduce_1  11# happyReduction_23
happyReduction_23 happy_x_1
	 =  happyIn15
		 (GCardOr
	)

happyReduce_24 = happySpecReduce_1  11# happyReduction_24
happyReduction_24 happy_x_1
	 =  happyIn15
		 (GCardMux
	)

happyReduce_25 = happySpecReduce_1  11# happyReduction_25
happyReduction_25 happy_x_1
	 =  happyIn15
		 (GCardOpt
	)

happyReduce_26 = happySpecReduce_3  11# happyReduction_26
happyReduction_26 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_2 of { happy_var_2 -> 
	happyIn15
		 (GCardInterval happy_var_2
	)}

happyReduce_27 = happySpecReduce_0  12# happyReduction_27
happyReduction_27  =  happyIn16
		 (CardEmpty
	)

happyReduce_28 = happySpecReduce_1  12# happyReduction_28
happyReduction_28 happy_x_1
	 =  happyIn16
		 (CardLone
	)

happyReduce_29 = happySpecReduce_1  12# happyReduction_29
happyReduction_29 happy_x_1
	 =  happyIn16
		 (CardSome
	)

happyReduce_30 = happySpecReduce_1  12# happyReduction_30
happyReduction_30 happy_x_1
	 =  happyIn16
		 (CardAny
	)

happyReduce_31 = happySpecReduce_1  12# happyReduction_31
happyReduction_31 happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (CardInterval happy_var_1
	)}

happyReduce_32 = happySpecReduce_3  13# happyReduction_32
happyReduction_32 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut5 happy_x_1 of { happy_var_1 -> 
	case happyOut19 happy_x_3 of { happy_var_3 -> 
	happyIn17
		 (GNCard happy_var_1 happy_var_3
	)}}

happyReduce_33 = happySpecReduce_3  14# happyReduction_33
happyReduction_33 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut5 happy_x_1 of { happy_var_1 -> 
	case happyOut19 happy_x_3 of { happy_var_3 -> 
	happyIn18
		 (NCard happy_var_1 happy_var_3
	)}}

happyReduce_34 = happySpecReduce_1  15# happyReduction_34
happyReduction_34 happy_x_1
	 =  happyIn19
		 (ExIntegerAst
	)

happyReduce_35 = happySpecReduce_1  15# happyReduction_35
happyReduction_35 happy_x_1
	 =  case happyOut5 happy_x_1 of { happy_var_1 -> 
	happyIn19
		 (ExIntegerNum happy_var_1
	)}

happyReduce_36 = happySpecReduce_1  16# happyReduction_36
happyReduction_36 happy_x_1
	 =  case happyOut4 happy_x_1 of { happy_var_1 -> 
	happyIn20
		 (LocClafer happy_var_1
	)}

happyReduce_37 = happySpecReduce_2  16# happyReduction_37
happyReduction_37 happy_x_2
	happy_x_1
	 =  case happyOut51 happy_x_1 of { happy_var_1 -> 
	case happyOut4 happy_x_2 of { happy_var_2 -> 
	happyIn20
		 (ModClafer happy_var_1 happy_var_2
	)}}

happyReduce_38 = happyReduce 4# 17# happyReduction_38
happyReduction_38 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut41 happy_x_1 of { happy_var_1 -> 
	case happyOut49 happy_x_2 of { happy_var_2 -> 
	case happyOut22 happy_x_4 of { happy_var_4 -> 
	happyIn21
		 (DeclExp happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_39 = happySpecReduce_1  17# happyReduction_39
happyReduction_39 happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	happyIn21
		 (happy_var_1
	)}

happyReduce_40 = happySpecReduce_3  18# happyReduction_40
happyReduction_40 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	case happyOut23 happy_x_3 of { happy_var_3 -> 
	happyIn22
		 (EIff happy_var_1 happy_var_3
	)}}

happyReduce_41 = happySpecReduce_1  18# happyReduction_41
happyReduction_41 happy_x_1
	 =  case happyOut23 happy_x_1 of { happy_var_1 -> 
	happyIn22
		 (happy_var_1
	)}

happyReduce_42 = happySpecReduce_3  19# happyReduction_42
happyReduction_42 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut23 happy_x_1 of { happy_var_1 -> 
	case happyOut24 happy_x_3 of { happy_var_3 -> 
	happyIn23
		 (EImplies happy_var_1 happy_var_3
	)}}

happyReduce_43 = happyReduce 5# 19# happyReduction_43
happyReduction_43 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut23 happy_x_1 of { happy_var_1 -> 
	case happyOut24 happy_x_3 of { happy_var_3 -> 
	case happyOut24 happy_x_5 of { happy_var_5 -> 
	happyIn23
		 (EImpliesElse happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_44 = happySpecReduce_1  19# happyReduction_44
happyReduction_44 happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	happyIn23
		 (happy_var_1
	)}

happyReduce_45 = happySpecReduce_3  20# happyReduction_45
happyReduction_45 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	case happyOut25 happy_x_3 of { happy_var_3 -> 
	happyIn24
		 (EOr happy_var_1 happy_var_3
	)}}

happyReduce_46 = happySpecReduce_1  20# happyReduction_46
happyReduction_46 happy_x_1
	 =  case happyOut25 happy_x_1 of { happy_var_1 -> 
	happyIn24
		 (happy_var_1
	)}

happyReduce_47 = happySpecReduce_3  21# happyReduction_47
happyReduction_47 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut25 happy_x_1 of { happy_var_1 -> 
	case happyOut26 happy_x_3 of { happy_var_3 -> 
	happyIn25
		 (EXor happy_var_1 happy_var_3
	)}}

happyReduce_48 = happySpecReduce_1  21# happyReduction_48
happyReduction_48 happy_x_1
	 =  case happyOut26 happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (happy_var_1
	)}

happyReduce_49 = happySpecReduce_3  22# happyReduction_49
happyReduction_49 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut26 happy_x_1 of { happy_var_1 -> 
	case happyOut27 happy_x_3 of { happy_var_3 -> 
	happyIn26
		 (EAnd happy_var_1 happy_var_3
	)}}

happyReduce_50 = happySpecReduce_1  22# happyReduction_50
happyReduction_50 happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (happy_var_1
	)}

happyReduce_51 = happySpecReduce_2  23# happyReduction_51
happyReduction_51 happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_2 of { happy_var_2 -> 
	happyIn27
		 (ENeg happy_var_2
	)}

happyReduce_52 = happySpecReduce_1  23# happyReduction_52
happyReduction_52 happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	happyIn27
		 (happy_var_1
	)}

happyReduce_53 = happySpecReduce_2  24# happyReduction_53
happyReduction_53 happy_x_2
	happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	case happyOut28 happy_x_2 of { happy_var_2 -> 
	happyIn28
		 (QuantExp happy_var_1 happy_var_2
	)}}

happyReduce_54 = happySpecReduce_3  24# happyReduction_54
happyReduction_54 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (ELt happy_var_1 happy_var_3
	)}}

happyReduce_55 = happySpecReduce_3  24# happyReduction_55
happyReduction_55 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (EGt happy_var_1 happy_var_3
	)}}

happyReduce_56 = happySpecReduce_3  24# happyReduction_56
happyReduction_56 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (EEq happy_var_1 happy_var_3
	)}}

happyReduce_57 = happySpecReduce_3  24# happyReduction_57
happyReduction_57 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (ELte happy_var_1 happy_var_3
	)}}

happyReduce_58 = happySpecReduce_3  24# happyReduction_58
happyReduction_58 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (EGte happy_var_1 happy_var_3
	)}}

happyReduce_59 = happySpecReduce_3  24# happyReduction_59
happyReduction_59 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (ENeq happy_var_1 happy_var_3
	)}}

happyReduce_60 = happySpecReduce_3  24# happyReduction_60
happyReduction_60 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (EIn happy_var_1 happy_var_3
	)}}

happyReduce_61 = happyReduce 4# 24# happyReduction_61
happyReduction_61 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_4 of { happy_var_4 -> 
	happyIn28
		 (ENin happy_var_1 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_62 = happySpecReduce_1  24# happyReduction_62
happyReduction_62 happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	happyIn28
		 (happy_var_1
	)}

happyReduce_63 = happySpecReduce_3  25# happyReduction_63
happyReduction_63 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	case happyOut30 happy_x_3 of { happy_var_3 -> 
	happyIn29
		 (EAdd happy_var_1 happy_var_3
	)}}

happyReduce_64 = happySpecReduce_3  25# happyReduction_64
happyReduction_64 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	case happyOut30 happy_x_3 of { happy_var_3 -> 
	happyIn29
		 (ESub happy_var_1 happy_var_3
	)}}

happyReduce_65 = happySpecReduce_1  25# happyReduction_65
happyReduction_65 happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	happyIn29
		 (happy_var_1
	)}

happyReduce_66 = happySpecReduce_3  26# happyReduction_66
happyReduction_66 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	case happyOut31 happy_x_3 of { happy_var_3 -> 
	happyIn30
		 (EMul happy_var_1 happy_var_3
	)}}

happyReduce_67 = happySpecReduce_3  26# happyReduction_67
happyReduction_67 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	case happyOut31 happy_x_3 of { happy_var_3 -> 
	happyIn30
		 (EDiv happy_var_1 happy_var_3
	)}}

happyReduce_68 = happySpecReduce_1  26# happyReduction_68
happyReduction_68 happy_x_1
	 =  case happyOut31 happy_x_1 of { happy_var_1 -> 
	happyIn30
		 (happy_var_1
	)}

happyReduce_69 = happySpecReduce_2  27# happyReduction_69
happyReduction_69 happy_x_2
	happy_x_1
	 =  case happyOut32 happy_x_2 of { happy_var_2 -> 
	happyIn31
		 (ECSetExp happy_var_2
	)}

happyReduce_70 = happySpecReduce_1  27# happyReduction_70
happyReduction_70 happy_x_1
	 =  case happyOut5 happy_x_1 of { happy_var_1 -> 
	happyIn31
		 (EInt happy_var_1
	)}

happyReduce_71 = happySpecReduce_1  27# happyReduction_71
happyReduction_71 happy_x_1
	 =  case happyOut6 happy_x_1 of { happy_var_1 -> 
	happyIn31
		 (EStr happy_var_1
	)}

happyReduce_72 = happySpecReduce_1  27# happyReduction_72
happyReduction_72 happy_x_1
	 =  case happyOut32 happy_x_1 of { happy_var_1 -> 
	happyIn31
		 (happy_var_1
	)}

happyReduce_73 = happySpecReduce_3  28# happyReduction_73
happyReduction_73 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut32 happy_x_1 of { happy_var_1 -> 
	case happyOut33 happy_x_3 of { happy_var_3 -> 
	happyIn32
		 (Union happy_var_1 happy_var_3
	)}}

happyReduce_74 = happySpecReduce_3  28# happyReduction_74
happyReduction_74 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut32 happy_x_1 of { happy_var_1 -> 
	case happyOut33 happy_x_3 of { happy_var_3 -> 
	happyIn32
		 (Difference happy_var_1 happy_var_3
	)}}

happyReduce_75 = happySpecReduce_1  28# happyReduction_75
happyReduction_75 happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (happy_var_1
	)}

happyReduce_76 = happySpecReduce_3  29# happyReduction_76
happyReduction_76 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOut34 happy_x_3 of { happy_var_3 -> 
	happyIn33
		 (Intersection happy_var_1 happy_var_3
	)}}

happyReduce_77 = happySpecReduce_1  29# happyReduction_77
happyReduction_77 happy_x_1
	 =  case happyOut34 happy_x_1 of { happy_var_1 -> 
	happyIn33
		 (happy_var_1
	)}

happyReduce_78 = happySpecReduce_3  30# happyReduction_78
happyReduction_78 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut34 happy_x_1 of { happy_var_1 -> 
	case happyOut35 happy_x_3 of { happy_var_3 -> 
	happyIn34
		 (Domain happy_var_1 happy_var_3
	)}}

happyReduce_79 = happySpecReduce_1  30# happyReduction_79
happyReduction_79 happy_x_1
	 =  case happyOut35 happy_x_1 of { happy_var_1 -> 
	happyIn34
		 (happy_var_1
	)}

happyReduce_80 = happySpecReduce_3  31# happyReduction_80
happyReduction_80 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut35 happy_x_1 of { happy_var_1 -> 
	case happyOut36 happy_x_3 of { happy_var_3 -> 
	happyIn35
		 (Range happy_var_1 happy_var_3
	)}}

happyReduce_81 = happySpecReduce_1  31# happyReduction_81
happyReduction_81 happy_x_1
	 =  case happyOut36 happy_x_1 of { happy_var_1 -> 
	happyIn35
		 (happy_var_1
	)}

happyReduce_82 = happySpecReduce_3  32# happyReduction_82
happyReduction_82 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut36 happy_x_1 of { happy_var_1 -> 
	case happyOut37 happy_x_3 of { happy_var_3 -> 
	happyIn36
		 (Join happy_var_1 happy_var_3
	)}}

happyReduce_83 = happySpecReduce_1  32# happyReduction_83
happyReduction_83 happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	happyIn36
		 (happy_var_1
	)}

happyReduce_84 = happySpecReduce_1  33# happyReduction_84
happyReduction_84 happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	happyIn37
		 (ClaferId happy_var_1
	)}

happyReduce_85 = happySpecReduce_3  33# happyReduction_85
happyReduction_85 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut21 happy_x_2 of { happy_var_2 -> 
	happyIn37
		 (happy_var_2
	)}

happyReduce_86 = happyReduce 4# 34# happyReduction_86
happyReduction_86 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut39 happy_x_1 of { happy_var_1 -> 
	case happyOut50 happy_x_2 of { happy_var_2 -> 
	case happyOut21 happy_x_4 of { happy_var_4 -> 
	happyIn38
		 (Decl happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_87 = happySpecReduce_0  35# happyReduction_87
happyReduction_87  =  happyIn39
		 (DisjEmpty
	)

happyReduce_88 = happySpecReduce_1  35# happyReduction_88
happyReduction_88 happy_x_1
	 =  happyIn39
		 (Disj
	)

happyReduce_89 = happySpecReduce_1  36# happyReduction_89
happyReduction_89 happy_x_1
	 =  happyIn40
		 (QuantNo
	)

happyReduce_90 = happySpecReduce_1  36# happyReduction_90
happyReduction_90 happy_x_1
	 =  happyIn40
		 (QuantLone
	)

happyReduce_91 = happySpecReduce_1  36# happyReduction_91
happyReduction_91 happy_x_1
	 =  happyIn40
		 (QuantOne
	)

happyReduce_92 = happySpecReduce_1  36# happyReduction_92
happyReduction_92 happy_x_1
	 =  happyIn40
		 (QuantSome
	)

happyReduce_93 = happySpecReduce_1  37# happyReduction_93
happyReduction_93 happy_x_1
	 =  happyIn41
		 (ExQuantAll
	)

happyReduce_94 = happySpecReduce_1  37# happyReduction_94
happyReduction_94 happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	happyIn41
		 (ExQuantQuant happy_var_1
	)}

happyReduce_95 = happySpecReduce_1  38# happyReduction_95
happyReduction_95 happy_x_1
	 =  case happyOut4 happy_x_1 of { happy_var_1 -> 
	happyIn42
		 (EnumIdIdent happy_var_1
	)}

happyReduce_96 = happySpecReduce_1  39# happyReduction_96
happyReduction_96 happy_x_1
	 =  case happyOut4 happy_x_1 of { happy_var_1 -> 
	happyIn43
		 (ModIdIdent happy_var_1
	)}

happyReduce_97 = happySpecReduce_1  40# happyReduction_97
happyReduction_97 happy_x_1
	 =  case happyOut4 happy_x_1 of { happy_var_1 -> 
	happyIn44
		 (LocIdIdent happy_var_1
	)}

happyReduce_98 = happySpecReduce_0  41# happyReduction_98
happyReduction_98  =  happyIn45
		 ([]
	)

happyReduce_99 = happySpecReduce_2  41# happyReduction_99
happyReduction_99 happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	case happyOut8 happy_x_2 of { happy_var_2 -> 
	happyIn45
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_100 = happySpecReduce_1  42# happyReduction_100
happyReduction_100 happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	happyIn46
		 ((:[]) happy_var_1
	)}

happyReduce_101 = happySpecReduce_3  42# happyReduction_101
happyReduction_101 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	case happyOut46 happy_x_3 of { happy_var_3 -> 
	happyIn46
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_102 = happySpecReduce_0  43# happyReduction_102
happyReduction_102  =  happyIn47
		 ([]
	)

happyReduce_103 = happySpecReduce_2  43# happyReduction_103
happyReduction_103 happy_x_2
	happy_x_1
	 =  case happyOut47 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_2 of { happy_var_2 -> 
	happyIn47
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_104 = happySpecReduce_0  44# happyReduction_104
happyReduction_104  =  happyIn48
		 ([]
	)

happyReduce_105 = happySpecReduce_2  44# happyReduction_105
happyReduction_105 happy_x_2
	happy_x_1
	 =  case happyOut48 happy_x_1 of { happy_var_1 -> 
	case happyOut21 happy_x_2 of { happy_var_2 -> 
	happyIn48
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_106 = happySpecReduce_1  45# happyReduction_106
happyReduction_106 happy_x_1
	 =  case happyOut38 happy_x_1 of { happy_var_1 -> 
	happyIn49
		 ((:[]) happy_var_1
	)}

happyReduce_107 = happySpecReduce_3  45# happyReduction_107
happyReduction_107 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut38 happy_x_1 of { happy_var_1 -> 
	case happyOut49 happy_x_3 of { happy_var_3 -> 
	happyIn49
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_108 = happySpecReduce_1  46# happyReduction_108
happyReduction_108 happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	happyIn50
		 ((:[]) happy_var_1
	)}

happyReduce_109 = happySpecReduce_3  46# happyReduction_109
happyReduction_109 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut50 happy_x_3 of { happy_var_3 -> 
	happyIn50
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_110 = happySpecReduce_2  47# happyReduction_110
happyReduction_110 happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	happyIn51
		 ((:[]) happy_var_1
	)}

happyReduce_111 = happySpecReduce_3  47# happyReduction_111
happyReduction_111 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOut51 happy_x_3 of { happy_var_3 -> 
	happyIn51
		 ((:) happy_var_1 happy_var_3
	)}}

happyNewToken action sts stk [] =
	happyDoAction 57# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS "=") -> cont 1#;
	PT _ (TS "[") -> cont 2#;
	PT _ (TS "]") -> cont 3#;
	PT _ (TS "{") -> cont 4#;
	PT _ (TS "}") -> cont 5#;
	PT _ (TS "`") -> cont 6#;
	PT _ (TS ":") -> cont 7#;
	PT _ (TS "->") -> cont 8#;
	PT _ (TS "<") -> cont 9#;
	PT _ (TS ">") -> cont 10#;
	PT _ (TS "?") -> cont 11#;
	PT _ (TS "+") -> cont 12#;
	PT _ (TS "*") -> cont 13#;
	PT _ (TS "-") -> cont 14#;
	PT _ (TS "..") -> cont 15#;
	PT _ (TS "|") -> cont 16#;
	PT _ (TS "<=>") -> cont 17#;
	PT _ (TS "=>") -> cont 18#;
	PT _ (TS "||") -> cont 19#;
	PT _ (TS "&&") -> cont 20#;
	PT _ (TS "~") -> cont 21#;
	PT _ (TS "<=") -> cont 22#;
	PT _ (TS ">=") -> cont 23#;
	PT _ (TS "!=") -> cont 24#;
	PT _ (TS "/") -> cont 25#;
	PT _ (TS "#") -> cont 26#;
	PT _ (TS "++") -> cont 27#;
	PT _ (TS "--") -> cont 28#;
	PT _ (TS "&") -> cont 29#;
	PT _ (TS "<:") -> cont 30#;
	PT _ (TS ":>") -> cont 31#;
	PT _ (TS ".") -> cont 32#;
	PT _ (TS ",") -> cont 33#;
	PT _ (TS "\\") -> cont 34#;
	PT _ (TS "(") -> cont 35#;
	PT _ (TS ")") -> cont 36#;
	PT _ (TS "abstract") -> cont 37#;
	PT _ (TS "all") -> cont 38#;
	PT _ (TS "disj") -> cont 39#;
	PT _ (TS "else") -> cont 40#;
	PT _ (TS "enum") -> cont 41#;
	PT _ (TS "extends") -> cont 42#;
	PT _ (TS "in") -> cont 43#;
	PT _ (TS "lone") -> cont 44#;
	PT _ (TS "mux") -> cont 45#;
	PT _ (TS "no") -> cont 46#;
	PT _ (TS "not") -> cont 47#;
	PT _ (TS "one") -> cont 48#;
	PT _ (TS "opt") -> cont 49#;
	PT _ (TS "or") -> cont 50#;
	PT _ (TS "some") -> cont 51#;
	PT _ (TS "xor") -> cont 52#;
	PT _ (TV happy_dollar_dollar) -> cont 53#;
	PT _ (TI happy_dollar_dollar) -> cont 54#;
	PT _ (TL happy_dollar_dollar) -> cont 55#;
	_ -> cont 56#;
	_ -> happyError' (tk:tks)
	}

happyError_ tk tks = happyError' (tk:tks)

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
  happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (happyOut7 x))

happySeq = happyDontSeq


returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map prToken (take 4 ts))

myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 30 "templates/GenericTemplate.hs" #-}


data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList





{-# LINE 51 "templates/GenericTemplate.hs" #-}

{-# LINE 61 "templates/GenericTemplate.hs" #-}

{-# LINE 70 "templates/GenericTemplate.hs" #-}

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
		0#		  -> {- nothing -}
				     happyFail i tk st
		-1# 	  -> {- nothing -}
				     happyAccept i tk st
		n | (n Happy_GHC_Exts.<# (0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}

				     (happyReduceArr Happy_Data_Array.! rule) i tk st
				     where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
		n		  -> {- nothing -}


				     happyShift new_state i tk st
				     where (new_state) = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where (off)    = indexShortOffAddr happyActOffsets st
         (off_i)  = (off Happy_GHC_Exts.+# i)
	 check  = if (off_i Happy_GHC_Exts.>=# (0# :: Happy_GHC_Exts.Int#))
			then (indexShortOffAddr happyCheck off_i Happy_GHC_Exts.==#  i)
			else False
         (action)
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st

{-# LINE 130 "templates/GenericTemplate.hs" #-}


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

{-# LINE 163 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let (i) = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
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
        happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))
       where (sts1@((HappyCons (st1@(action)) (_)))) = happyDrop k (HappyCons (st) (sts))
             drop_stk = happyDropStk k stk

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
       happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))
       where (sts1@((HappyCons (st1@(action)) (_)))) = happyDrop k (HappyCons (st) (sts))
             drop_stk = happyDropStk k stk

             (off) = indexShortOffAddr happyGotoOffsets st1
             (off_i) = (off Happy_GHC_Exts.+# nt)
             (new_state) = indexShortOffAddr happyTable off_i




happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where (off) = indexShortOffAddr happyGotoOffsets st
         (off_i) = (off Happy_GHC_Exts.+# nt)
         (new_state) = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail  0# tk old_st _ stk =
--	trace "failing" $ 
    	happyError_ tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
						(saved_tok `HappyStk` _ `HappyStk` stk) =
--	trace ("discarding state, depth " ++ show (length stk))  $
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
--	happySeq = happyDoSeq
-- otherwise it emits
-- 	happySeq = happyDontSeq

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
