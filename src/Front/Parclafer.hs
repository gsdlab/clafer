{-# OPTIONS_GHC -w #-}
{-# OPTIONS -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Front.Parclafer where
import Front.Absclafer
import Front.Lexclafer
import Front.ErrM

-- parser produced by Happy Version 1.18.6

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn4 (Ident)
	| HappyAbsSyn5 (Integer)
	| HappyAbsSyn6 (Double)
	| HappyAbsSyn7 (String)
	| HappyAbsSyn8 (Module)
	| HappyAbsSyn9 (Declaration)
	| HappyAbsSyn10 (Clafer)
	| HappyAbsSyn11 (Constraint)
	| HappyAbsSyn12 (SoftConstraint)
	| HappyAbsSyn13 (Goal)
	| HappyAbsSyn14 (Abstract)
	| HappyAbsSyn15 (Elements)
	| HappyAbsSyn16 (Element)
	| HappyAbsSyn17 (Super)
	| HappyAbsSyn18 (SuperHow)
	| HappyAbsSyn19 (Init)
	| HappyAbsSyn20 (InitHow)
	| HappyAbsSyn21 (GCard)
	| HappyAbsSyn22 (Card)
	| HappyAbsSyn23 (NCard)
	| HappyAbsSyn24 (ExInteger)
	| HappyAbsSyn25 (Name)
	| HappyAbsSyn26 (Exp)
	| HappyAbsSyn40 (SetExp)
	| HappyAbsSyn47 (Decl)
	| HappyAbsSyn48 (Quant)
	| HappyAbsSyn49 (EnumId)
	| HappyAbsSyn50 (ModId)
	| HappyAbsSyn51 (LocId)
	| HappyAbsSyn52 ([Declaration])
	| HappyAbsSyn53 ([EnumId])
	| HappyAbsSyn54 ([Element])
	| HappyAbsSyn55 ([Exp])
	| HappyAbsSyn56 ([LocId])
	| HappyAbsSyn57 ([ModId])

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> m HappyAbsSyn
-}

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51,
 action_52,
 action_53,
 action_54,
 action_55,
 action_56,
 action_57,
 action_58,
 action_59,
 action_60,
 action_61,
 action_62,
 action_63,
 action_64,
 action_65,
 action_66,
 action_67,
 action_68,
 action_69,
 action_70,
 action_71,
 action_72,
 action_73,
 action_74,
 action_75,
 action_76,
 action_77,
 action_78,
 action_79,
 action_80,
 action_81,
 action_82,
 action_83,
 action_84,
 action_85,
 action_86,
 action_87,
 action_88,
 action_89,
 action_90,
 action_91,
 action_92,
 action_93,
 action_94,
 action_95,
 action_96,
 action_97,
 action_98,
 action_99,
 action_100,
 action_101,
 action_102,
 action_103,
 action_104,
 action_105,
 action_106,
 action_107,
 action_108,
 action_109,
 action_110,
 action_111,
 action_112,
 action_113,
 action_114,
 action_115,
 action_116,
 action_117,
 action_118,
 action_119,
 action_120,
 action_121,
 action_122,
 action_123,
 action_124,
 action_125,
 action_126,
 action_127,
 action_128,
 action_129,
 action_130,
 action_131,
 action_132,
 action_133,
 action_134,
 action_135,
 action_136,
 action_137,
 action_138,
 action_139,
 action_140,
 action_141,
 action_142,
 action_143,
 action_144,
 action_145,
 action_146,
 action_147,
 action_148,
 action_149,
 action_150,
 action_151,
 action_152,
 action_153,
 action_154,
 action_155,
 action_156,
 action_157,
 action_158,
 action_159,
 action_160,
 action_161,
 action_162,
 action_163,
 action_164,
 action_165,
 action_166,
 action_167,
 action_168,
 action_169,
 action_170,
 action_171,
 action_172,
 action_173,
 action_174,
 action_175,
 action_176,
 action_177,
 action_178,
 action_179,
 action_180,
 action_181,
 action_182,
 action_183,
 action_184,
 action_185,
 action_186,
 action_187,
 action_188,
 action_189,
 action_190,
 action_191,
 action_192,
 action_193,
 action_194,
 action_195,
 action_196,
 action_197,
 action_198,
 action_199,
 action_200,
 action_201,
 action_202,
 action_203 :: () => Int -> ({-HappyReduction (Err) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyReduce_1,
 happyReduce_2,
 happyReduce_3,
 happyReduce_4,
 happyReduce_5,
 happyReduce_6,
 happyReduce_7,
 happyReduce_8,
 happyReduce_9,
 happyReduce_10,
 happyReduce_11,
 happyReduce_12,
 happyReduce_13,
 happyReduce_14,
 happyReduce_15,
 happyReduce_16,
 happyReduce_17,
 happyReduce_18,
 happyReduce_19,
 happyReduce_20,
 happyReduce_21,
 happyReduce_22,
 happyReduce_23,
 happyReduce_24,
 happyReduce_25,
 happyReduce_26,
 happyReduce_27,
 happyReduce_28,
 happyReduce_29,
 happyReduce_30,
 happyReduce_31,
 happyReduce_32,
 happyReduce_33,
 happyReduce_34,
 happyReduce_35,
 happyReduce_36,
 happyReduce_37,
 happyReduce_38,
 happyReduce_39,
 happyReduce_40,
 happyReduce_41,
 happyReduce_42,
 happyReduce_43,
 happyReduce_44,
 happyReduce_45,
 happyReduce_46,
 happyReduce_47,
 happyReduce_48,
 happyReduce_49,
 happyReduce_50,
 happyReduce_51,
 happyReduce_52,
 happyReduce_53,
 happyReduce_54,
 happyReduce_55,
 happyReduce_56,
 happyReduce_57,
 happyReduce_58,
 happyReduce_59,
 happyReduce_60,
 happyReduce_61,
 happyReduce_62,
 happyReduce_63,
 happyReduce_64,
 happyReduce_65,
 happyReduce_66,
 happyReduce_67,
 happyReduce_68,
 happyReduce_69,
 happyReduce_70,
 happyReduce_71,
 happyReduce_72,
 happyReduce_73,
 happyReduce_74,
 happyReduce_75,
 happyReduce_76,
 happyReduce_77,
 happyReduce_78,
 happyReduce_79,
 happyReduce_80,
 happyReduce_81,
 happyReduce_82,
 happyReduce_83,
 happyReduce_84,
 happyReduce_85,
 happyReduce_86,
 happyReduce_87,
 happyReduce_88,
 happyReduce_89,
 happyReduce_90,
 happyReduce_91,
 happyReduce_92,
 happyReduce_93,
 happyReduce_94,
 happyReduce_95,
 happyReduce_96,
 happyReduce_97,
 happyReduce_98,
 happyReduce_99,
 happyReduce_100,
 happyReduce_101,
 happyReduce_102,
 happyReduce_103,
 happyReduce_104,
 happyReduce_105,
 happyReduce_106,
 happyReduce_107,
 happyReduce_108,
 happyReduce_109,
 happyReduce_110,
 happyReduce_111,
 happyReduce_112,
 happyReduce_113,
 happyReduce_114,
 happyReduce_115,
 happyReduce_116,
 happyReduce_117,
 happyReduce_118,
 happyReduce_119,
 happyReduce_120,
 happyReduce_121,
 happyReduce_122,
 happyReduce_123,
 happyReduce_124,
 happyReduce_125,
 happyReduce_126 :: () => ({-HappyReduction (Err) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

action_0 (8) = happyGoto action_3
action_0 (52) = happyGoto action_4
action_0 _ = happyReduce_115

action_1 (118) = happyShift action_2
action_1 _ = happyFail

action_2 _ = happyReduce_1

action_3 (123) = happyAccept
action_3 _ = happyFail

action_4 (63) = happyShift action_12
action_4 (81) = happyShift action_13
action_4 (90) = happyShift action_14
action_4 (93) = happyShift action_15
action_4 (94) = happyShift action_16
action_4 (98) = happyShift action_17
action_4 (123) = happyReduce_5
action_4 (9) = happyGoto action_5
action_4 (10) = happyGoto action_6
action_4 (11) = happyGoto action_7
action_4 (12) = happyGoto action_8
action_4 (13) = happyGoto action_9
action_4 (14) = happyGoto action_10
action_4 (16) = happyGoto action_11
action_4 _ = happyReduce_12

action_5 _ = happyReduce_116

action_6 _ = happyReduce_16

action_7 _ = happyReduce_18

action_8 _ = happyReduce_20

action_9 _ = happyReduce_19

action_10 (104) = happyShift action_29
action_10 (108) = happyShift action_30
action_10 (109) = happyShift action_31
action_10 (113) = happyShift action_32
action_10 (119) = happyShift action_33
action_10 (5) = happyGoto action_26
action_10 (21) = happyGoto action_27
action_10 (23) = happyGoto action_28
action_10 _ = happyReduce_29

action_11 _ = happyReduce_7

action_12 (55) = happyGoto action_25
action_12 _ = happyReduce_121

action_13 (55) = happyGoto action_24
action_13 _ = happyReduce_121

action_14 (55) = happyGoto action_23
action_14 _ = happyReduce_121

action_15 (118) = happyShift action_2
action_15 (4) = happyGoto action_19
action_15 (25) = happyGoto action_20
action_15 (50) = happyGoto action_21
action_15 (57) = happyGoto action_22
action_15 _ = happyFail

action_16 _ = happyReduce_13

action_17 (118) = happyShift action_2
action_17 (4) = happyGoto action_18
action_17 _ = happyFail

action_18 (84) = happyShift action_87
action_18 _ = happyFail

action_19 _ = happyReduce_113

action_20 (65) = happyShift action_84
action_20 (66) = happyShift action_85
action_20 (89) = happyShift action_86
action_20 (119) = happyShift action_33
action_20 (5) = happyGoto action_81
action_20 (22) = happyGoto action_82
action_20 (23) = happyGoto action_83
action_20 _ = happyReduce_35

action_21 (91) = happyShift action_80
action_21 _ = happyReduce_125

action_22 _ = happyReduce_44

action_23 (58) = happyShift action_62
action_23 (60) = happyShift action_63
action_23 (63) = happyShift action_64
action_23 (69) = happyShift action_66
action_23 (92) = happyShift action_79
action_23 (95) = happyShift action_67
action_23 (99) = happyShift action_68
action_23 (101) = happyShift action_69
action_23 (102) = happyShift action_70
action_23 (103) = happyShift action_71
action_23 (105) = happyShift action_72
action_23 (107) = happyShift action_73
action_23 (110) = happyShift action_74
action_23 (111) = happyShift action_75
action_23 (118) = happyShift action_2
action_23 (119) = happyShift action_33
action_23 (120) = happyShift action_76
action_23 (121) = happyShift action_77
action_23 (4) = happyGoto action_19
action_23 (5) = happyGoto action_36
action_23 (6) = happyGoto action_37
action_23 (7) = happyGoto action_38
action_23 (25) = happyGoto action_39
action_23 (26) = happyGoto action_40
action_23 (27) = happyGoto action_41
action_23 (28) = happyGoto action_42
action_23 (29) = happyGoto action_43
action_23 (30) = happyGoto action_44
action_23 (31) = happyGoto action_45
action_23 (32) = happyGoto action_46
action_23 (33) = happyGoto action_47
action_23 (34) = happyGoto action_48
action_23 (35) = happyGoto action_49
action_23 (36) = happyGoto action_50
action_23 (37) = happyGoto action_51
action_23 (38) = happyGoto action_52
action_23 (39) = happyGoto action_53
action_23 (40) = happyGoto action_54
action_23 (41) = happyGoto action_55
action_23 (42) = happyGoto action_56
action_23 (43) = happyGoto action_57
action_23 (44) = happyGoto action_58
action_23 (45) = happyGoto action_59
action_23 (46) = happyGoto action_60
action_23 (48) = happyGoto action_61
action_23 (50) = happyGoto action_21
action_23 (57) = happyGoto action_22
action_23 _ = happyFail

action_24 (58) = happyShift action_62
action_24 (60) = happyShift action_63
action_24 (63) = happyShift action_64
action_24 (69) = happyShift action_66
action_24 (88) = happyShift action_78
action_24 (95) = happyShift action_67
action_24 (99) = happyShift action_68
action_24 (101) = happyShift action_69
action_24 (102) = happyShift action_70
action_24 (103) = happyShift action_71
action_24 (105) = happyShift action_72
action_24 (107) = happyShift action_73
action_24 (110) = happyShift action_74
action_24 (111) = happyShift action_75
action_24 (118) = happyShift action_2
action_24 (119) = happyShift action_33
action_24 (120) = happyShift action_76
action_24 (121) = happyShift action_77
action_24 (4) = happyGoto action_19
action_24 (5) = happyGoto action_36
action_24 (6) = happyGoto action_37
action_24 (7) = happyGoto action_38
action_24 (25) = happyGoto action_39
action_24 (26) = happyGoto action_40
action_24 (27) = happyGoto action_41
action_24 (28) = happyGoto action_42
action_24 (29) = happyGoto action_43
action_24 (30) = happyGoto action_44
action_24 (31) = happyGoto action_45
action_24 (32) = happyGoto action_46
action_24 (33) = happyGoto action_47
action_24 (34) = happyGoto action_48
action_24 (35) = happyGoto action_49
action_24 (36) = happyGoto action_50
action_24 (37) = happyGoto action_51
action_24 (38) = happyGoto action_52
action_24 (39) = happyGoto action_53
action_24 (40) = happyGoto action_54
action_24 (41) = happyGoto action_55
action_24 (42) = happyGoto action_56
action_24 (43) = happyGoto action_57
action_24 (44) = happyGoto action_58
action_24 (45) = happyGoto action_59
action_24 (46) = happyGoto action_60
action_24 (48) = happyGoto action_61
action_24 (50) = happyGoto action_21
action_24 (57) = happyGoto action_22
action_24 _ = happyFail

action_25 (58) = happyShift action_62
action_25 (60) = happyShift action_63
action_25 (63) = happyShift action_64
action_25 (64) = happyShift action_65
action_25 (69) = happyShift action_66
action_25 (95) = happyShift action_67
action_25 (99) = happyShift action_68
action_25 (101) = happyShift action_69
action_25 (102) = happyShift action_70
action_25 (103) = happyShift action_71
action_25 (105) = happyShift action_72
action_25 (107) = happyShift action_73
action_25 (110) = happyShift action_74
action_25 (111) = happyShift action_75
action_25 (118) = happyShift action_2
action_25 (119) = happyShift action_33
action_25 (120) = happyShift action_76
action_25 (121) = happyShift action_77
action_25 (4) = happyGoto action_19
action_25 (5) = happyGoto action_36
action_25 (6) = happyGoto action_37
action_25 (7) = happyGoto action_38
action_25 (25) = happyGoto action_39
action_25 (26) = happyGoto action_40
action_25 (27) = happyGoto action_41
action_25 (28) = happyGoto action_42
action_25 (29) = happyGoto action_43
action_25 (30) = happyGoto action_44
action_25 (31) = happyGoto action_45
action_25 (32) = happyGoto action_46
action_25 (33) = happyGoto action_47
action_25 (34) = happyGoto action_48
action_25 (35) = happyGoto action_49
action_25 (36) = happyGoto action_50
action_25 (37) = happyGoto action_51
action_25 (38) = happyGoto action_52
action_25 (39) = happyGoto action_53
action_25 (40) = happyGoto action_54
action_25 (41) = happyGoto action_55
action_25 (42) = happyGoto action_56
action_25 (43) = happyGoto action_57
action_25 (44) = happyGoto action_58
action_25 (45) = happyGoto action_59
action_25 (46) = happyGoto action_60
action_25 (48) = happyGoto action_61
action_25 (50) = happyGoto action_21
action_25 (57) = happyGoto action_22
action_25 _ = happyFail

action_26 (73) = happyShift action_35
action_26 _ = happyFail

action_27 (118) = happyShift action_2
action_27 (4) = happyGoto action_34
action_27 _ = happyFail

action_28 _ = happyReduce_34

action_29 _ = happyReduce_32

action_30 _ = happyReduce_33

action_31 _ = happyReduce_31

action_32 _ = happyReduce_30

action_33 _ = happyReduce_2

action_34 (71) = happyShift action_142
action_34 (75) = happyShift action_143
action_34 (17) = happyGoto action_140
action_34 (18) = happyGoto action_141
action_34 _ = happyReduce_21

action_35 (65) = happyShift action_139
action_35 (119) = happyShift action_33
action_35 (5) = happyGoto action_137
action_35 (24) = happyGoto action_138
action_35 _ = happyFail

action_36 _ = happyReduce_87

action_37 _ = happyReduce_88

action_38 _ = happyReduce_89

action_39 _ = happyReduce_105

action_40 _ = happyReduce_122

action_41 (83) = happyShift action_136
action_41 _ = happyReduce_49

action_42 (85) = happyShift action_135
action_42 _ = happyReduce_53

action_43 (116) = happyShift action_134
action_43 _ = happyReduce_55

action_44 (113) = happyShift action_133
action_44 _ = happyReduce_57

action_45 (62) = happyShift action_132
action_45 _ = happyReduce_59

action_46 _ = happyReduce_61

action_47 (59) = happyShift action_124
action_47 (79) = happyShift action_125
action_47 (82) = happyShift action_126
action_47 (84) = happyShift action_127
action_47 (86) = happyShift action_128
action_47 (87) = happyShift action_129
action_47 (100) = happyShift action_130
action_47 (106) = happyShift action_131
action_47 _ = happyReduce_63

action_48 _ = happyReduce_72

action_49 (66) = happyShift action_122
action_49 (69) = happyShift action_123
action_49 _ = happyReduce_74

action_50 (65) = happyShift action_120
action_50 (74) = happyShift action_121
action_50 _ = happyReduce_77

action_51 _ = happyReduce_80

action_52 _ = happyReduce_84

action_53 _ = happyReduce_86

action_54 (67) = happyShift action_118
action_54 (68) = happyShift action_119
action_54 _ = happyReduce_90

action_55 (70) = happyShift action_117
action_55 _ = happyReduce_94

action_56 (61) = happyShift action_116
action_56 _ = happyReduce_96

action_57 (80) = happyShift action_115
action_57 _ = happyReduce_98

action_58 (77) = happyShift action_114
action_58 _ = happyReduce_100

action_59 (72) = happyShift action_113
action_59 _ = happyReduce_102

action_60 _ = happyReduce_104

action_61 (63) = happyShift action_64
action_61 (96) = happyShift action_112
action_61 (99) = happyShift action_68
action_61 (118) = happyShift action_2
action_61 (119) = happyShift action_33
action_61 (120) = happyShift action_76
action_61 (121) = happyShift action_77
action_61 (4) = happyGoto action_109
action_61 (5) = happyGoto action_36
action_61 (6) = happyGoto action_37
action_61 (7) = happyGoto action_38
action_61 (25) = happyGoto action_39
action_61 (38) = happyGoto action_110
action_61 (39) = happyGoto action_53
action_61 (40) = happyGoto action_54
action_61 (41) = happyGoto action_55
action_61 (42) = happyGoto action_56
action_61 (43) = happyGoto action_57
action_61 (44) = happyGoto action_58
action_61 (45) = happyGoto action_59
action_61 (46) = happyGoto action_60
action_61 (47) = happyGoto action_111
action_61 (50) = happyGoto action_21
action_61 (51) = happyGoto action_101
action_61 (56) = happyGoto action_102
action_61 (57) = happyGoto action_22
action_61 _ = happyFail

action_62 (60) = happyShift action_63
action_62 (63) = happyShift action_64
action_62 (69) = happyShift action_66
action_62 (99) = happyShift action_68
action_62 (101) = happyShift action_69
action_62 (105) = happyShift action_72
action_62 (107) = happyShift action_73
action_62 (110) = happyShift action_74
action_62 (111) = happyShift action_75
action_62 (118) = happyShift action_2
action_62 (119) = happyShift action_33
action_62 (120) = happyShift action_76
action_62 (121) = happyShift action_77
action_62 (4) = happyGoto action_19
action_62 (5) = happyGoto action_36
action_62 (6) = happyGoto action_37
action_62 (7) = happyGoto action_38
action_62 (25) = happyGoto action_39
action_62 (33) = happyGoto action_108
action_62 (34) = happyGoto action_48
action_62 (35) = happyGoto action_49
action_62 (36) = happyGoto action_50
action_62 (37) = happyGoto action_51
action_62 (38) = happyGoto action_52
action_62 (39) = happyGoto action_53
action_62 (40) = happyGoto action_54
action_62 (41) = happyGoto action_55
action_62 (42) = happyGoto action_56
action_62 (43) = happyGoto action_57
action_62 (44) = happyGoto action_58
action_62 (45) = happyGoto action_59
action_62 (46) = happyGoto action_60
action_62 (48) = happyGoto action_96
action_62 (50) = happyGoto action_21
action_62 (57) = happyGoto action_22
action_62 _ = happyFail

action_63 (63) = happyShift action_64
action_63 (99) = happyShift action_68
action_63 (118) = happyShift action_2
action_63 (119) = happyShift action_33
action_63 (120) = happyShift action_76
action_63 (121) = happyShift action_77
action_63 (4) = happyGoto action_19
action_63 (5) = happyGoto action_36
action_63 (6) = happyGoto action_37
action_63 (7) = happyGoto action_38
action_63 (25) = happyGoto action_39
action_63 (38) = happyGoto action_107
action_63 (39) = happyGoto action_53
action_63 (40) = happyGoto action_54
action_63 (41) = happyGoto action_55
action_63 (42) = happyGoto action_56
action_63 (43) = happyGoto action_57
action_63 (44) = happyGoto action_58
action_63 (45) = happyGoto action_59
action_63 (46) = happyGoto action_60
action_63 (50) = happyGoto action_21
action_63 (57) = happyGoto action_22
action_63 _ = happyFail

action_64 (58) = happyShift action_62
action_64 (60) = happyShift action_63
action_64 (63) = happyShift action_64
action_64 (69) = happyShift action_66
action_64 (95) = happyShift action_67
action_64 (99) = happyShift action_68
action_64 (101) = happyShift action_69
action_64 (102) = happyShift action_70
action_64 (103) = happyShift action_71
action_64 (105) = happyShift action_72
action_64 (107) = happyShift action_73
action_64 (110) = happyShift action_74
action_64 (111) = happyShift action_75
action_64 (118) = happyShift action_2
action_64 (119) = happyShift action_33
action_64 (120) = happyShift action_76
action_64 (121) = happyShift action_77
action_64 (4) = happyGoto action_19
action_64 (5) = happyGoto action_36
action_64 (6) = happyGoto action_37
action_64 (7) = happyGoto action_38
action_64 (25) = happyGoto action_39
action_64 (26) = happyGoto action_105
action_64 (27) = happyGoto action_41
action_64 (28) = happyGoto action_42
action_64 (29) = happyGoto action_43
action_64 (30) = happyGoto action_44
action_64 (31) = happyGoto action_45
action_64 (32) = happyGoto action_46
action_64 (33) = happyGoto action_47
action_64 (34) = happyGoto action_48
action_64 (35) = happyGoto action_49
action_64 (36) = happyGoto action_50
action_64 (37) = happyGoto action_51
action_64 (38) = happyGoto action_52
action_64 (39) = happyGoto action_53
action_64 (40) = happyGoto action_106
action_64 (41) = happyGoto action_55
action_64 (42) = happyGoto action_56
action_64 (43) = happyGoto action_57
action_64 (44) = happyGoto action_58
action_64 (45) = happyGoto action_59
action_64 (46) = happyGoto action_60
action_64 (48) = happyGoto action_61
action_64 (50) = happyGoto action_21
action_64 (57) = happyGoto action_22
action_64 _ = happyFail

action_65 _ = happyReduce_10

action_66 (63) = happyShift action_64
action_66 (99) = happyShift action_68
action_66 (118) = happyShift action_2
action_66 (119) = happyShift action_33
action_66 (120) = happyShift action_76
action_66 (121) = happyShift action_77
action_66 (4) = happyGoto action_19
action_66 (5) = happyGoto action_36
action_66 (6) = happyGoto action_37
action_66 (7) = happyGoto action_38
action_66 (25) = happyGoto action_39
action_66 (38) = happyGoto action_104
action_66 (39) = happyGoto action_53
action_66 (40) = happyGoto action_54
action_66 (41) = happyGoto action_55
action_66 (42) = happyGoto action_56
action_66 (43) = happyGoto action_57
action_66 (44) = happyGoto action_58
action_66 (45) = happyGoto action_59
action_66 (46) = happyGoto action_60
action_66 (50) = happyGoto action_21
action_66 (57) = happyGoto action_22
action_66 _ = happyFail

action_67 (96) = happyShift action_103
action_67 (118) = happyShift action_2
action_67 (4) = happyGoto action_99
action_67 (47) = happyGoto action_100
action_67 (51) = happyGoto action_101
action_67 (56) = happyGoto action_102
action_67 _ = happyFail

action_68 (63) = happyShift action_64
action_68 (99) = happyShift action_68
action_68 (118) = happyShift action_2
action_68 (119) = happyShift action_33
action_68 (120) = happyShift action_76
action_68 (121) = happyShift action_77
action_68 (4) = happyGoto action_19
action_68 (5) = happyGoto action_36
action_68 (6) = happyGoto action_37
action_68 (7) = happyGoto action_38
action_68 (25) = happyGoto action_39
action_68 (38) = happyGoto action_98
action_68 (39) = happyGoto action_53
action_68 (40) = happyGoto action_54
action_68 (41) = happyGoto action_55
action_68 (42) = happyGoto action_56
action_68 (43) = happyGoto action_57
action_68 (44) = happyGoto action_58
action_68 (45) = happyGoto action_59
action_68 (46) = happyGoto action_60
action_68 (50) = happyGoto action_21
action_68 (57) = happyGoto action_22
action_68 _ = happyFail

action_69 _ = happyReduce_109

action_70 (58) = happyShift action_62
action_70 (60) = happyShift action_63
action_70 (63) = happyShift action_64
action_70 (69) = happyShift action_66
action_70 (99) = happyShift action_68
action_70 (101) = happyShift action_69
action_70 (105) = happyShift action_72
action_70 (107) = happyShift action_73
action_70 (110) = happyShift action_74
action_70 (111) = happyShift action_75
action_70 (118) = happyShift action_2
action_70 (119) = happyShift action_33
action_70 (120) = happyShift action_76
action_70 (121) = happyShift action_77
action_70 (4) = happyGoto action_19
action_70 (5) = happyGoto action_36
action_70 (6) = happyGoto action_37
action_70 (7) = happyGoto action_38
action_70 (25) = happyGoto action_39
action_70 (28) = happyGoto action_97
action_70 (29) = happyGoto action_43
action_70 (30) = happyGoto action_44
action_70 (31) = happyGoto action_45
action_70 (32) = happyGoto action_46
action_70 (33) = happyGoto action_47
action_70 (34) = happyGoto action_48
action_70 (35) = happyGoto action_49
action_70 (36) = happyGoto action_50
action_70 (37) = happyGoto action_51
action_70 (38) = happyGoto action_52
action_70 (39) = happyGoto action_53
action_70 (40) = happyGoto action_54
action_70 (41) = happyGoto action_55
action_70 (42) = happyGoto action_56
action_70 (43) = happyGoto action_57
action_70 (44) = happyGoto action_58
action_70 (45) = happyGoto action_59
action_70 (46) = happyGoto action_60
action_70 (48) = happyGoto action_96
action_70 (50) = happyGoto action_21
action_70 (57) = happyGoto action_22
action_70 _ = happyFail

action_71 (58) = happyShift action_62
action_71 (60) = happyShift action_63
action_71 (63) = happyShift action_64
action_71 (69) = happyShift action_66
action_71 (99) = happyShift action_68
action_71 (101) = happyShift action_69
action_71 (105) = happyShift action_72
action_71 (107) = happyShift action_73
action_71 (110) = happyShift action_74
action_71 (111) = happyShift action_75
action_71 (118) = happyShift action_2
action_71 (119) = happyShift action_33
action_71 (120) = happyShift action_76
action_71 (121) = happyShift action_77
action_71 (4) = happyGoto action_19
action_71 (5) = happyGoto action_36
action_71 (6) = happyGoto action_37
action_71 (7) = happyGoto action_38
action_71 (25) = happyGoto action_39
action_71 (28) = happyGoto action_95
action_71 (29) = happyGoto action_43
action_71 (30) = happyGoto action_44
action_71 (31) = happyGoto action_45
action_71 (32) = happyGoto action_46
action_71 (33) = happyGoto action_47
action_71 (34) = happyGoto action_48
action_71 (35) = happyGoto action_49
action_71 (36) = happyGoto action_50
action_71 (37) = happyGoto action_51
action_71 (38) = happyGoto action_52
action_71 (39) = happyGoto action_53
action_71 (40) = happyGoto action_54
action_71 (41) = happyGoto action_55
action_71 (42) = happyGoto action_56
action_71 (43) = happyGoto action_57
action_71 (44) = happyGoto action_58
action_71 (45) = happyGoto action_59
action_71 (46) = happyGoto action_60
action_71 (48) = happyGoto action_96
action_71 (50) = happyGoto action_21
action_71 (57) = happyGoto action_22
action_71 _ = happyFail

action_72 _ = happyReduce_108

action_73 _ = happyReduce_110

action_74 _ = happyReduce_111

action_75 (63) = happyShift action_64
action_75 (99) = happyShift action_68
action_75 (118) = happyShift action_2
action_75 (119) = happyShift action_33
action_75 (120) = happyShift action_76
action_75 (121) = happyShift action_77
action_75 (4) = happyGoto action_19
action_75 (5) = happyGoto action_36
action_75 (6) = happyGoto action_37
action_75 (7) = happyGoto action_38
action_75 (25) = happyGoto action_39
action_75 (38) = happyGoto action_94
action_75 (39) = happyGoto action_53
action_75 (40) = happyGoto action_54
action_75 (41) = happyGoto action_55
action_75 (42) = happyGoto action_56
action_75 (43) = happyGoto action_57
action_75 (44) = happyGoto action_58
action_75 (45) = happyGoto action_59
action_75 (46) = happyGoto action_60
action_75 (50) = happyGoto action_21
action_75 (57) = happyGoto action_22
action_75 _ = happyFail

action_76 _ = happyReduce_3

action_77 _ = happyReduce_4

action_78 _ = happyReduce_11

action_79 _ = happyReduce_9

action_80 (118) = happyShift action_2
action_80 (4) = happyGoto action_19
action_80 (50) = happyGoto action_21
action_80 (57) = happyGoto action_93
action_80 _ = happyFail

action_81 (73) = happyShift action_35
action_81 _ = happyReduce_39

action_82 (114) = happyShift action_92
action_82 (15) = happyGoto action_91
action_82 _ = happyReduce_14

action_83 _ = happyReduce_40

action_84 _ = happyReduce_38

action_85 _ = happyReduce_37

action_86 _ = happyReduce_36

action_87 (118) = happyShift action_2
action_87 (4) = happyGoto action_88
action_87 (49) = happyGoto action_89
action_87 (53) = happyGoto action_90
action_87 _ = happyFail

action_88 _ = happyReduce_112

action_89 (115) = happyShift action_181
action_89 _ = happyReduce_117

action_90 _ = happyReduce_6

action_91 _ = happyReduce_17

action_92 (54) = happyGoto action_180
action_92 _ = happyReduce_119

action_93 _ = happyReduce_126

action_94 _ = happyReduce_81

action_95 (85) = happyShift action_135
action_95 _ = happyReduce_51

action_96 (63) = happyShift action_64
action_96 (99) = happyShift action_68
action_96 (118) = happyShift action_2
action_96 (119) = happyShift action_33
action_96 (120) = happyShift action_76
action_96 (121) = happyShift action_77
action_96 (4) = happyGoto action_19
action_96 (5) = happyGoto action_36
action_96 (6) = happyGoto action_37
action_96 (7) = happyGoto action_38
action_96 (25) = happyGoto action_39
action_96 (38) = happyGoto action_110
action_96 (39) = happyGoto action_53
action_96 (40) = happyGoto action_54
action_96 (41) = happyGoto action_55
action_96 (42) = happyGoto action_56
action_96 (43) = happyGoto action_57
action_96 (44) = happyGoto action_58
action_96 (45) = happyGoto action_59
action_96 (46) = happyGoto action_60
action_96 (50) = happyGoto action_21
action_96 (57) = happyGoto action_22
action_96 _ = happyFail

action_97 (85) = happyShift action_135
action_97 _ = happyReduce_50

action_98 (112) = happyShift action_179
action_98 _ = happyFail

action_99 _ = happyReduce_114

action_100 (115) = happyShift action_178
action_100 _ = happyFail

action_101 (78) = happyShift action_177
action_101 _ = happyReduce_123

action_102 (75) = happyShift action_176
action_102 _ = happyFail

action_103 (118) = happyShift action_2
action_103 (4) = happyGoto action_99
action_103 (47) = happyGoto action_175
action_103 (51) = happyGoto action_101
action_103 (56) = happyGoto action_102
action_103 _ = happyFail

action_104 _ = happyReduce_83

action_105 (64) = happyShift action_174
action_105 _ = happyFail

action_106 (64) = happyShift action_173
action_106 (67) = happyShift action_118
action_106 (68) = happyShift action_119
action_106 _ = happyReduce_90

action_107 _ = happyReduce_82

action_108 (59) = happyShift action_124
action_108 (79) = happyShift action_125
action_108 (82) = happyShift action_126
action_108 (84) = happyShift action_127
action_108 (86) = happyShift action_128
action_108 (87) = happyShift action_129
action_108 (100) = happyShift action_130
action_108 (106) = happyShift action_131
action_108 _ = happyReduce_62

action_109 (75) = happyReduce_114
action_109 (78) = happyReduce_114
action_109 _ = happyReduce_113

action_110 _ = happyReduce_73

action_111 (115) = happyShift action_172
action_111 _ = happyFail

action_112 (118) = happyShift action_2
action_112 (4) = happyGoto action_99
action_112 (47) = happyGoto action_171
action_112 (51) = happyGoto action_101
action_112 (56) = happyGoto action_102
action_112 _ = happyFail

action_113 (63) = happyShift action_145
action_113 (118) = happyShift action_2
action_113 (4) = happyGoto action_19
action_113 (25) = happyGoto action_39
action_113 (46) = happyGoto action_170
action_113 (50) = happyGoto action_21
action_113 (57) = happyGoto action_22
action_113 _ = happyFail

action_114 (63) = happyShift action_145
action_114 (118) = happyShift action_2
action_114 (4) = happyGoto action_19
action_114 (25) = happyGoto action_39
action_114 (45) = happyGoto action_169
action_114 (46) = happyGoto action_60
action_114 (50) = happyGoto action_21
action_114 (57) = happyGoto action_22
action_114 _ = happyFail

action_115 (63) = happyShift action_145
action_115 (118) = happyShift action_2
action_115 (4) = happyGoto action_19
action_115 (25) = happyGoto action_39
action_115 (44) = happyGoto action_168
action_115 (45) = happyGoto action_59
action_115 (46) = happyGoto action_60
action_115 (50) = happyGoto action_21
action_115 (57) = happyGoto action_22
action_115 _ = happyFail

action_116 (63) = happyShift action_145
action_116 (118) = happyShift action_2
action_116 (4) = happyGoto action_19
action_116 (25) = happyGoto action_39
action_116 (43) = happyGoto action_167
action_116 (44) = happyGoto action_58
action_116 (45) = happyGoto action_59
action_116 (46) = happyGoto action_60
action_116 (50) = happyGoto action_21
action_116 (57) = happyGoto action_22
action_116 _ = happyFail

action_117 (63) = happyShift action_145
action_117 (118) = happyShift action_2
action_117 (4) = happyGoto action_19
action_117 (25) = happyGoto action_39
action_117 (42) = happyGoto action_166
action_117 (43) = happyGoto action_57
action_117 (44) = happyGoto action_58
action_117 (45) = happyGoto action_59
action_117 (46) = happyGoto action_60
action_117 (50) = happyGoto action_21
action_117 (57) = happyGoto action_22
action_117 _ = happyFail

action_118 (63) = happyShift action_145
action_118 (118) = happyShift action_2
action_118 (4) = happyGoto action_19
action_118 (25) = happyGoto action_39
action_118 (41) = happyGoto action_165
action_118 (42) = happyGoto action_56
action_118 (43) = happyGoto action_57
action_118 (44) = happyGoto action_58
action_118 (45) = happyGoto action_59
action_118 (46) = happyGoto action_60
action_118 (50) = happyGoto action_21
action_118 (57) = happyGoto action_22
action_118 _ = happyFail

action_119 (63) = happyShift action_145
action_119 (118) = happyShift action_2
action_119 (4) = happyGoto action_19
action_119 (25) = happyGoto action_39
action_119 (41) = happyGoto action_164
action_119 (42) = happyGoto action_56
action_119 (43) = happyGoto action_57
action_119 (44) = happyGoto action_58
action_119 (45) = happyGoto action_59
action_119 (46) = happyGoto action_60
action_119 (50) = happyGoto action_21
action_119 (57) = happyGoto action_22
action_119 _ = happyFail

action_120 (60) = happyShift action_63
action_120 (63) = happyShift action_64
action_120 (69) = happyShift action_66
action_120 (99) = happyShift action_68
action_120 (111) = happyShift action_75
action_120 (118) = happyShift action_2
action_120 (119) = happyShift action_33
action_120 (120) = happyShift action_76
action_120 (121) = happyShift action_77
action_120 (4) = happyGoto action_19
action_120 (5) = happyGoto action_36
action_120 (6) = happyGoto action_37
action_120 (7) = happyGoto action_38
action_120 (25) = happyGoto action_39
action_120 (37) = happyGoto action_163
action_120 (38) = happyGoto action_52
action_120 (39) = happyGoto action_53
action_120 (40) = happyGoto action_54
action_120 (41) = happyGoto action_55
action_120 (42) = happyGoto action_56
action_120 (43) = happyGoto action_57
action_120 (44) = happyGoto action_58
action_120 (45) = happyGoto action_59
action_120 (46) = happyGoto action_60
action_120 (50) = happyGoto action_21
action_120 (57) = happyGoto action_22
action_120 _ = happyFail

action_121 (60) = happyShift action_63
action_121 (63) = happyShift action_64
action_121 (69) = happyShift action_66
action_121 (99) = happyShift action_68
action_121 (111) = happyShift action_75
action_121 (118) = happyShift action_2
action_121 (119) = happyShift action_33
action_121 (120) = happyShift action_76
action_121 (121) = happyShift action_77
action_121 (4) = happyGoto action_19
action_121 (5) = happyGoto action_36
action_121 (6) = happyGoto action_37
action_121 (7) = happyGoto action_38
action_121 (25) = happyGoto action_39
action_121 (37) = happyGoto action_162
action_121 (38) = happyGoto action_52
action_121 (39) = happyGoto action_53
action_121 (40) = happyGoto action_54
action_121 (41) = happyGoto action_55
action_121 (42) = happyGoto action_56
action_121 (43) = happyGoto action_57
action_121 (44) = happyGoto action_58
action_121 (45) = happyGoto action_59
action_121 (46) = happyGoto action_60
action_121 (50) = happyGoto action_21
action_121 (57) = happyGoto action_22
action_121 _ = happyFail

action_122 (60) = happyShift action_63
action_122 (63) = happyShift action_64
action_122 (69) = happyShift action_66
action_122 (99) = happyShift action_68
action_122 (111) = happyShift action_75
action_122 (118) = happyShift action_2
action_122 (119) = happyShift action_33
action_122 (120) = happyShift action_76
action_122 (121) = happyShift action_77
action_122 (4) = happyGoto action_19
action_122 (5) = happyGoto action_36
action_122 (6) = happyGoto action_37
action_122 (7) = happyGoto action_38
action_122 (25) = happyGoto action_39
action_122 (36) = happyGoto action_161
action_122 (37) = happyGoto action_51
action_122 (38) = happyGoto action_52
action_122 (39) = happyGoto action_53
action_122 (40) = happyGoto action_54
action_122 (41) = happyGoto action_55
action_122 (42) = happyGoto action_56
action_122 (43) = happyGoto action_57
action_122 (44) = happyGoto action_58
action_122 (45) = happyGoto action_59
action_122 (46) = happyGoto action_60
action_122 (50) = happyGoto action_21
action_122 (57) = happyGoto action_22
action_122 _ = happyFail

action_123 (60) = happyShift action_63
action_123 (63) = happyShift action_64
action_123 (69) = happyShift action_66
action_123 (99) = happyShift action_68
action_123 (111) = happyShift action_75
action_123 (118) = happyShift action_2
action_123 (119) = happyShift action_33
action_123 (120) = happyShift action_76
action_123 (121) = happyShift action_77
action_123 (4) = happyGoto action_19
action_123 (5) = happyGoto action_36
action_123 (6) = happyGoto action_37
action_123 (7) = happyGoto action_38
action_123 (25) = happyGoto action_39
action_123 (36) = happyGoto action_160
action_123 (37) = happyGoto action_51
action_123 (38) = happyGoto action_52
action_123 (39) = happyGoto action_53
action_123 (40) = happyGoto action_54
action_123 (41) = happyGoto action_55
action_123 (42) = happyGoto action_56
action_123 (43) = happyGoto action_57
action_123 (44) = happyGoto action_58
action_123 (45) = happyGoto action_59
action_123 (46) = happyGoto action_60
action_123 (50) = happyGoto action_21
action_123 (57) = happyGoto action_22
action_123 _ = happyFail

action_124 (60) = happyShift action_63
action_124 (63) = happyShift action_64
action_124 (69) = happyShift action_66
action_124 (99) = happyShift action_68
action_124 (101) = happyShift action_69
action_124 (105) = happyShift action_72
action_124 (107) = happyShift action_73
action_124 (110) = happyShift action_74
action_124 (111) = happyShift action_75
action_124 (118) = happyShift action_2
action_124 (119) = happyShift action_33
action_124 (120) = happyShift action_76
action_124 (121) = happyShift action_77
action_124 (4) = happyGoto action_19
action_124 (5) = happyGoto action_36
action_124 (6) = happyGoto action_37
action_124 (7) = happyGoto action_38
action_124 (25) = happyGoto action_39
action_124 (34) = happyGoto action_159
action_124 (35) = happyGoto action_49
action_124 (36) = happyGoto action_50
action_124 (37) = happyGoto action_51
action_124 (38) = happyGoto action_52
action_124 (39) = happyGoto action_53
action_124 (40) = happyGoto action_54
action_124 (41) = happyGoto action_55
action_124 (42) = happyGoto action_56
action_124 (43) = happyGoto action_57
action_124 (44) = happyGoto action_58
action_124 (45) = happyGoto action_59
action_124 (46) = happyGoto action_60
action_124 (48) = happyGoto action_96
action_124 (50) = happyGoto action_21
action_124 (57) = happyGoto action_22
action_124 _ = happyFail

action_125 (60) = happyShift action_63
action_125 (63) = happyShift action_64
action_125 (69) = happyShift action_66
action_125 (99) = happyShift action_68
action_125 (101) = happyShift action_69
action_125 (105) = happyShift action_72
action_125 (107) = happyShift action_73
action_125 (110) = happyShift action_74
action_125 (111) = happyShift action_75
action_125 (118) = happyShift action_2
action_125 (119) = happyShift action_33
action_125 (120) = happyShift action_76
action_125 (121) = happyShift action_77
action_125 (4) = happyGoto action_19
action_125 (5) = happyGoto action_36
action_125 (6) = happyGoto action_37
action_125 (7) = happyGoto action_38
action_125 (25) = happyGoto action_39
action_125 (34) = happyGoto action_158
action_125 (35) = happyGoto action_49
action_125 (36) = happyGoto action_50
action_125 (37) = happyGoto action_51
action_125 (38) = happyGoto action_52
action_125 (39) = happyGoto action_53
action_125 (40) = happyGoto action_54
action_125 (41) = happyGoto action_55
action_125 (42) = happyGoto action_56
action_125 (43) = happyGoto action_57
action_125 (44) = happyGoto action_58
action_125 (45) = happyGoto action_59
action_125 (46) = happyGoto action_60
action_125 (48) = happyGoto action_96
action_125 (50) = happyGoto action_21
action_125 (57) = happyGoto action_22
action_125 _ = happyFail

action_126 (60) = happyShift action_63
action_126 (63) = happyShift action_64
action_126 (69) = happyShift action_66
action_126 (99) = happyShift action_68
action_126 (101) = happyShift action_69
action_126 (105) = happyShift action_72
action_126 (107) = happyShift action_73
action_126 (110) = happyShift action_74
action_126 (111) = happyShift action_75
action_126 (118) = happyShift action_2
action_126 (119) = happyShift action_33
action_126 (120) = happyShift action_76
action_126 (121) = happyShift action_77
action_126 (4) = happyGoto action_19
action_126 (5) = happyGoto action_36
action_126 (6) = happyGoto action_37
action_126 (7) = happyGoto action_38
action_126 (25) = happyGoto action_39
action_126 (34) = happyGoto action_157
action_126 (35) = happyGoto action_49
action_126 (36) = happyGoto action_50
action_126 (37) = happyGoto action_51
action_126 (38) = happyGoto action_52
action_126 (39) = happyGoto action_53
action_126 (40) = happyGoto action_54
action_126 (41) = happyGoto action_55
action_126 (42) = happyGoto action_56
action_126 (43) = happyGoto action_57
action_126 (44) = happyGoto action_58
action_126 (45) = happyGoto action_59
action_126 (46) = happyGoto action_60
action_126 (48) = happyGoto action_96
action_126 (50) = happyGoto action_21
action_126 (57) = happyGoto action_22
action_126 _ = happyFail

action_127 (60) = happyShift action_63
action_127 (63) = happyShift action_64
action_127 (69) = happyShift action_66
action_127 (99) = happyShift action_68
action_127 (101) = happyShift action_69
action_127 (105) = happyShift action_72
action_127 (107) = happyShift action_73
action_127 (110) = happyShift action_74
action_127 (111) = happyShift action_75
action_127 (118) = happyShift action_2
action_127 (119) = happyShift action_33
action_127 (120) = happyShift action_76
action_127 (121) = happyShift action_77
action_127 (4) = happyGoto action_19
action_127 (5) = happyGoto action_36
action_127 (6) = happyGoto action_37
action_127 (7) = happyGoto action_38
action_127 (25) = happyGoto action_39
action_127 (34) = happyGoto action_156
action_127 (35) = happyGoto action_49
action_127 (36) = happyGoto action_50
action_127 (37) = happyGoto action_51
action_127 (38) = happyGoto action_52
action_127 (39) = happyGoto action_53
action_127 (40) = happyGoto action_54
action_127 (41) = happyGoto action_55
action_127 (42) = happyGoto action_56
action_127 (43) = happyGoto action_57
action_127 (44) = happyGoto action_58
action_127 (45) = happyGoto action_59
action_127 (46) = happyGoto action_60
action_127 (48) = happyGoto action_96
action_127 (50) = happyGoto action_21
action_127 (57) = happyGoto action_22
action_127 _ = happyFail

action_128 (60) = happyShift action_63
action_128 (63) = happyShift action_64
action_128 (69) = happyShift action_66
action_128 (99) = happyShift action_68
action_128 (101) = happyShift action_69
action_128 (105) = happyShift action_72
action_128 (107) = happyShift action_73
action_128 (110) = happyShift action_74
action_128 (111) = happyShift action_75
action_128 (118) = happyShift action_2
action_128 (119) = happyShift action_33
action_128 (120) = happyShift action_76
action_128 (121) = happyShift action_77
action_128 (4) = happyGoto action_19
action_128 (5) = happyGoto action_36
action_128 (6) = happyGoto action_37
action_128 (7) = happyGoto action_38
action_128 (25) = happyGoto action_39
action_128 (34) = happyGoto action_155
action_128 (35) = happyGoto action_49
action_128 (36) = happyGoto action_50
action_128 (37) = happyGoto action_51
action_128 (38) = happyGoto action_52
action_128 (39) = happyGoto action_53
action_128 (40) = happyGoto action_54
action_128 (41) = happyGoto action_55
action_128 (42) = happyGoto action_56
action_128 (43) = happyGoto action_57
action_128 (44) = happyGoto action_58
action_128 (45) = happyGoto action_59
action_128 (46) = happyGoto action_60
action_128 (48) = happyGoto action_96
action_128 (50) = happyGoto action_21
action_128 (57) = happyGoto action_22
action_128 _ = happyFail

action_129 (60) = happyShift action_63
action_129 (63) = happyShift action_64
action_129 (69) = happyShift action_66
action_129 (99) = happyShift action_68
action_129 (101) = happyShift action_69
action_129 (105) = happyShift action_72
action_129 (107) = happyShift action_73
action_129 (110) = happyShift action_74
action_129 (111) = happyShift action_75
action_129 (118) = happyShift action_2
action_129 (119) = happyShift action_33
action_129 (120) = happyShift action_76
action_129 (121) = happyShift action_77
action_129 (4) = happyGoto action_19
action_129 (5) = happyGoto action_36
action_129 (6) = happyGoto action_37
action_129 (7) = happyGoto action_38
action_129 (25) = happyGoto action_39
action_129 (34) = happyGoto action_154
action_129 (35) = happyGoto action_49
action_129 (36) = happyGoto action_50
action_129 (37) = happyGoto action_51
action_129 (38) = happyGoto action_52
action_129 (39) = happyGoto action_53
action_129 (40) = happyGoto action_54
action_129 (41) = happyGoto action_55
action_129 (42) = happyGoto action_56
action_129 (43) = happyGoto action_57
action_129 (44) = happyGoto action_58
action_129 (45) = happyGoto action_59
action_129 (46) = happyGoto action_60
action_129 (48) = happyGoto action_96
action_129 (50) = happyGoto action_21
action_129 (57) = happyGoto action_22
action_129 _ = happyFail

action_130 (60) = happyShift action_63
action_130 (63) = happyShift action_64
action_130 (69) = happyShift action_66
action_130 (99) = happyShift action_68
action_130 (101) = happyShift action_69
action_130 (105) = happyShift action_72
action_130 (107) = happyShift action_73
action_130 (110) = happyShift action_74
action_130 (111) = happyShift action_75
action_130 (118) = happyShift action_2
action_130 (119) = happyShift action_33
action_130 (120) = happyShift action_76
action_130 (121) = happyShift action_77
action_130 (4) = happyGoto action_19
action_130 (5) = happyGoto action_36
action_130 (6) = happyGoto action_37
action_130 (7) = happyGoto action_38
action_130 (25) = happyGoto action_39
action_130 (34) = happyGoto action_153
action_130 (35) = happyGoto action_49
action_130 (36) = happyGoto action_50
action_130 (37) = happyGoto action_51
action_130 (38) = happyGoto action_52
action_130 (39) = happyGoto action_53
action_130 (40) = happyGoto action_54
action_130 (41) = happyGoto action_55
action_130 (42) = happyGoto action_56
action_130 (43) = happyGoto action_57
action_130 (44) = happyGoto action_58
action_130 (45) = happyGoto action_59
action_130 (46) = happyGoto action_60
action_130 (48) = happyGoto action_96
action_130 (50) = happyGoto action_21
action_130 (57) = happyGoto action_22
action_130 _ = happyFail

action_131 (100) = happyShift action_152
action_131 _ = happyFail

action_132 (58) = happyShift action_62
action_132 (60) = happyShift action_63
action_132 (63) = happyShift action_64
action_132 (69) = happyShift action_66
action_132 (99) = happyShift action_68
action_132 (101) = happyShift action_69
action_132 (105) = happyShift action_72
action_132 (107) = happyShift action_73
action_132 (110) = happyShift action_74
action_132 (111) = happyShift action_75
action_132 (118) = happyShift action_2
action_132 (119) = happyShift action_33
action_132 (120) = happyShift action_76
action_132 (121) = happyShift action_77
action_132 (4) = happyGoto action_19
action_132 (5) = happyGoto action_36
action_132 (6) = happyGoto action_37
action_132 (7) = happyGoto action_38
action_132 (25) = happyGoto action_39
action_132 (32) = happyGoto action_151
action_132 (33) = happyGoto action_47
action_132 (34) = happyGoto action_48
action_132 (35) = happyGoto action_49
action_132 (36) = happyGoto action_50
action_132 (37) = happyGoto action_51
action_132 (38) = happyGoto action_52
action_132 (39) = happyGoto action_53
action_132 (40) = happyGoto action_54
action_132 (41) = happyGoto action_55
action_132 (42) = happyGoto action_56
action_132 (43) = happyGoto action_57
action_132 (44) = happyGoto action_58
action_132 (45) = happyGoto action_59
action_132 (46) = happyGoto action_60
action_132 (48) = happyGoto action_96
action_132 (50) = happyGoto action_21
action_132 (57) = happyGoto action_22
action_132 _ = happyFail

action_133 (58) = happyShift action_62
action_133 (60) = happyShift action_63
action_133 (63) = happyShift action_64
action_133 (69) = happyShift action_66
action_133 (99) = happyShift action_68
action_133 (101) = happyShift action_69
action_133 (105) = happyShift action_72
action_133 (107) = happyShift action_73
action_133 (110) = happyShift action_74
action_133 (111) = happyShift action_75
action_133 (118) = happyShift action_2
action_133 (119) = happyShift action_33
action_133 (120) = happyShift action_76
action_133 (121) = happyShift action_77
action_133 (4) = happyGoto action_19
action_133 (5) = happyGoto action_36
action_133 (6) = happyGoto action_37
action_133 (7) = happyGoto action_38
action_133 (25) = happyGoto action_39
action_133 (31) = happyGoto action_150
action_133 (32) = happyGoto action_46
action_133 (33) = happyGoto action_47
action_133 (34) = happyGoto action_48
action_133 (35) = happyGoto action_49
action_133 (36) = happyGoto action_50
action_133 (37) = happyGoto action_51
action_133 (38) = happyGoto action_52
action_133 (39) = happyGoto action_53
action_133 (40) = happyGoto action_54
action_133 (41) = happyGoto action_55
action_133 (42) = happyGoto action_56
action_133 (43) = happyGoto action_57
action_133 (44) = happyGoto action_58
action_133 (45) = happyGoto action_59
action_133 (46) = happyGoto action_60
action_133 (48) = happyGoto action_96
action_133 (50) = happyGoto action_21
action_133 (57) = happyGoto action_22
action_133 _ = happyFail

action_134 (58) = happyShift action_62
action_134 (60) = happyShift action_63
action_134 (63) = happyShift action_64
action_134 (69) = happyShift action_66
action_134 (99) = happyShift action_68
action_134 (101) = happyShift action_69
action_134 (105) = happyShift action_72
action_134 (107) = happyShift action_73
action_134 (110) = happyShift action_74
action_134 (111) = happyShift action_75
action_134 (118) = happyShift action_2
action_134 (119) = happyShift action_33
action_134 (120) = happyShift action_76
action_134 (121) = happyShift action_77
action_134 (4) = happyGoto action_19
action_134 (5) = happyGoto action_36
action_134 (6) = happyGoto action_37
action_134 (7) = happyGoto action_38
action_134 (25) = happyGoto action_39
action_134 (30) = happyGoto action_149
action_134 (31) = happyGoto action_45
action_134 (32) = happyGoto action_46
action_134 (33) = happyGoto action_47
action_134 (34) = happyGoto action_48
action_134 (35) = happyGoto action_49
action_134 (36) = happyGoto action_50
action_134 (37) = happyGoto action_51
action_134 (38) = happyGoto action_52
action_134 (39) = happyGoto action_53
action_134 (40) = happyGoto action_54
action_134 (41) = happyGoto action_55
action_134 (42) = happyGoto action_56
action_134 (43) = happyGoto action_57
action_134 (44) = happyGoto action_58
action_134 (45) = happyGoto action_59
action_134 (46) = happyGoto action_60
action_134 (48) = happyGoto action_96
action_134 (50) = happyGoto action_21
action_134 (57) = happyGoto action_22
action_134 _ = happyFail

action_135 (58) = happyShift action_62
action_135 (60) = happyShift action_63
action_135 (63) = happyShift action_64
action_135 (69) = happyShift action_66
action_135 (99) = happyShift action_68
action_135 (101) = happyShift action_69
action_135 (105) = happyShift action_72
action_135 (107) = happyShift action_73
action_135 (110) = happyShift action_74
action_135 (111) = happyShift action_75
action_135 (118) = happyShift action_2
action_135 (119) = happyShift action_33
action_135 (120) = happyShift action_76
action_135 (121) = happyShift action_77
action_135 (4) = happyGoto action_19
action_135 (5) = happyGoto action_36
action_135 (6) = happyGoto action_37
action_135 (7) = happyGoto action_38
action_135 (25) = happyGoto action_39
action_135 (29) = happyGoto action_148
action_135 (30) = happyGoto action_44
action_135 (31) = happyGoto action_45
action_135 (32) = happyGoto action_46
action_135 (33) = happyGoto action_47
action_135 (34) = happyGoto action_48
action_135 (35) = happyGoto action_49
action_135 (36) = happyGoto action_50
action_135 (37) = happyGoto action_51
action_135 (38) = happyGoto action_52
action_135 (39) = happyGoto action_53
action_135 (40) = happyGoto action_54
action_135 (41) = happyGoto action_55
action_135 (42) = happyGoto action_56
action_135 (43) = happyGoto action_57
action_135 (44) = happyGoto action_58
action_135 (45) = happyGoto action_59
action_135 (46) = happyGoto action_60
action_135 (48) = happyGoto action_96
action_135 (50) = happyGoto action_21
action_135 (57) = happyGoto action_22
action_135 _ = happyFail

action_136 (58) = happyShift action_62
action_136 (60) = happyShift action_63
action_136 (63) = happyShift action_64
action_136 (69) = happyShift action_66
action_136 (99) = happyShift action_68
action_136 (101) = happyShift action_69
action_136 (105) = happyShift action_72
action_136 (107) = happyShift action_73
action_136 (110) = happyShift action_74
action_136 (111) = happyShift action_75
action_136 (118) = happyShift action_2
action_136 (119) = happyShift action_33
action_136 (120) = happyShift action_76
action_136 (121) = happyShift action_77
action_136 (4) = happyGoto action_19
action_136 (5) = happyGoto action_36
action_136 (6) = happyGoto action_37
action_136 (7) = happyGoto action_38
action_136 (25) = happyGoto action_39
action_136 (28) = happyGoto action_147
action_136 (29) = happyGoto action_43
action_136 (30) = happyGoto action_44
action_136 (31) = happyGoto action_45
action_136 (32) = happyGoto action_46
action_136 (33) = happyGoto action_47
action_136 (34) = happyGoto action_48
action_136 (35) = happyGoto action_49
action_136 (36) = happyGoto action_50
action_136 (37) = happyGoto action_51
action_136 (38) = happyGoto action_52
action_136 (39) = happyGoto action_53
action_136 (40) = happyGoto action_54
action_136 (41) = happyGoto action_55
action_136 (42) = happyGoto action_56
action_136 (43) = happyGoto action_57
action_136 (44) = happyGoto action_58
action_136 (45) = happyGoto action_59
action_136 (46) = happyGoto action_60
action_136 (48) = happyGoto action_96
action_136 (50) = happyGoto action_21
action_136 (57) = happyGoto action_22
action_136 _ = happyFail

action_137 _ = happyReduce_43

action_138 _ = happyReduce_41

action_139 _ = happyReduce_42

action_140 (65) = happyShift action_84
action_140 (66) = happyShift action_85
action_140 (89) = happyShift action_86
action_140 (119) = happyShift action_33
action_140 (5) = happyGoto action_81
action_140 (22) = happyGoto action_146
action_140 (23) = happyGoto action_83
action_140 _ = happyReduce_35

action_141 (63) = happyShift action_145
action_141 (118) = happyShift action_2
action_141 (4) = happyGoto action_19
action_141 (25) = happyGoto action_39
action_141 (40) = happyGoto action_144
action_141 (41) = happyGoto action_55
action_141 (42) = happyGoto action_56
action_141 (43) = happyGoto action_57
action_141 (44) = happyGoto action_58
action_141 (45) = happyGoto action_59
action_141 (46) = happyGoto action_60
action_141 (50) = happyGoto action_21
action_141 (57) = happyGoto action_22
action_141 _ = happyFail

action_142 _ = happyReduce_24

action_143 _ = happyReduce_23

action_144 (67) = happyShift action_118
action_144 (68) = happyShift action_119
action_144 _ = happyReduce_22

action_145 (63) = happyShift action_145
action_145 (118) = happyShift action_2
action_145 (4) = happyGoto action_19
action_145 (25) = happyGoto action_39
action_145 (40) = happyGoto action_197
action_145 (41) = happyGoto action_55
action_145 (42) = happyGoto action_56
action_145 (43) = happyGoto action_57
action_145 (44) = happyGoto action_58
action_145 (45) = happyGoto action_59
action_145 (46) = happyGoto action_60
action_145 (50) = happyGoto action_21
action_145 (57) = happyGoto action_22
action_145 _ = happyFail

action_146 (76) = happyShift action_195
action_146 (84) = happyShift action_196
action_146 (19) = happyGoto action_193
action_146 (20) = happyGoto action_194
action_146 _ = happyReduce_25

action_147 (85) = happyShift action_135
action_147 _ = happyReduce_52

action_148 (116) = happyShift action_134
action_148 _ = happyReduce_54

action_149 (113) = happyShift action_133
action_149 _ = happyReduce_56

action_150 (62) = happyShift action_132
action_150 _ = happyReduce_58

action_151 _ = happyReduce_60

action_152 (60) = happyShift action_63
action_152 (63) = happyShift action_64
action_152 (69) = happyShift action_66
action_152 (99) = happyShift action_68
action_152 (101) = happyShift action_69
action_152 (105) = happyShift action_72
action_152 (107) = happyShift action_73
action_152 (110) = happyShift action_74
action_152 (111) = happyShift action_75
action_152 (118) = happyShift action_2
action_152 (119) = happyShift action_33
action_152 (120) = happyShift action_76
action_152 (121) = happyShift action_77
action_152 (4) = happyGoto action_19
action_152 (5) = happyGoto action_36
action_152 (6) = happyGoto action_37
action_152 (7) = happyGoto action_38
action_152 (25) = happyGoto action_39
action_152 (34) = happyGoto action_192
action_152 (35) = happyGoto action_49
action_152 (36) = happyGoto action_50
action_152 (37) = happyGoto action_51
action_152 (38) = happyGoto action_52
action_152 (39) = happyGoto action_53
action_152 (40) = happyGoto action_54
action_152 (41) = happyGoto action_55
action_152 (42) = happyGoto action_56
action_152 (43) = happyGoto action_57
action_152 (44) = happyGoto action_58
action_152 (45) = happyGoto action_59
action_152 (46) = happyGoto action_60
action_152 (48) = happyGoto action_96
action_152 (50) = happyGoto action_21
action_152 (57) = happyGoto action_22
action_152 _ = happyFail

action_153 _ = happyReduce_70

action_154 _ = happyReduce_68

action_155 _ = happyReduce_65

action_156 _ = happyReduce_66

action_157 _ = happyReduce_67

action_158 _ = happyReduce_64

action_159 _ = happyReduce_69

action_160 (65) = happyShift action_120
action_160 (74) = happyShift action_121
action_160 _ = happyReduce_76

action_161 (65) = happyShift action_120
action_161 (74) = happyShift action_121
action_161 _ = happyReduce_75

action_162 _ = happyReduce_79

action_163 _ = happyReduce_78

action_164 (70) = happyShift action_117
action_164 _ = happyReduce_93

action_165 (70) = happyShift action_117
action_165 _ = happyReduce_92

action_166 (61) = happyShift action_116
action_166 _ = happyReduce_95

action_167 (80) = happyShift action_115
action_167 _ = happyReduce_97

action_168 (77) = happyShift action_114
action_168 _ = happyReduce_99

action_169 (72) = happyShift action_113
action_169 _ = happyReduce_101

action_170 _ = happyReduce_103

action_171 (115) = happyShift action_191
action_171 _ = happyFail

action_172 (58) = happyShift action_62
action_172 (60) = happyShift action_63
action_172 (63) = happyShift action_64
action_172 (69) = happyShift action_66
action_172 (95) = happyShift action_67
action_172 (99) = happyShift action_68
action_172 (101) = happyShift action_69
action_172 (102) = happyShift action_70
action_172 (103) = happyShift action_71
action_172 (105) = happyShift action_72
action_172 (107) = happyShift action_73
action_172 (110) = happyShift action_74
action_172 (111) = happyShift action_75
action_172 (118) = happyShift action_2
action_172 (119) = happyShift action_33
action_172 (120) = happyShift action_76
action_172 (121) = happyShift action_77
action_172 (4) = happyGoto action_19
action_172 (5) = happyGoto action_36
action_172 (6) = happyGoto action_37
action_172 (7) = happyGoto action_38
action_172 (25) = happyGoto action_39
action_172 (26) = happyGoto action_190
action_172 (27) = happyGoto action_41
action_172 (28) = happyGoto action_42
action_172 (29) = happyGoto action_43
action_172 (30) = happyGoto action_44
action_172 (31) = happyGoto action_45
action_172 (32) = happyGoto action_46
action_172 (33) = happyGoto action_47
action_172 (34) = happyGoto action_48
action_172 (35) = happyGoto action_49
action_172 (36) = happyGoto action_50
action_172 (37) = happyGoto action_51
action_172 (38) = happyGoto action_52
action_172 (39) = happyGoto action_53
action_172 (40) = happyGoto action_54
action_172 (41) = happyGoto action_55
action_172 (42) = happyGoto action_56
action_172 (43) = happyGoto action_57
action_172 (44) = happyGoto action_58
action_172 (45) = happyGoto action_59
action_172 (46) = happyGoto action_60
action_172 (48) = happyGoto action_61
action_172 (50) = happyGoto action_21
action_172 (57) = happyGoto action_22
action_172 _ = happyFail

action_173 _ = happyReduce_106

action_174 _ = happyReduce_91

action_175 (115) = happyShift action_189
action_175 _ = happyFail

action_176 (63) = happyShift action_145
action_176 (118) = happyShift action_2
action_176 (4) = happyGoto action_19
action_176 (25) = happyGoto action_39
action_176 (40) = happyGoto action_188
action_176 (41) = happyGoto action_55
action_176 (42) = happyGoto action_56
action_176 (43) = happyGoto action_57
action_176 (44) = happyGoto action_58
action_176 (45) = happyGoto action_59
action_176 (46) = happyGoto action_60
action_176 (50) = happyGoto action_21
action_176 (57) = happyGoto action_22
action_176 _ = happyFail

action_177 (118) = happyShift action_2
action_177 (4) = happyGoto action_99
action_177 (51) = happyGoto action_101
action_177 (56) = happyGoto action_187
action_177 _ = happyFail

action_178 (58) = happyShift action_62
action_178 (60) = happyShift action_63
action_178 (63) = happyShift action_64
action_178 (69) = happyShift action_66
action_178 (95) = happyShift action_67
action_178 (99) = happyShift action_68
action_178 (101) = happyShift action_69
action_178 (102) = happyShift action_70
action_178 (103) = happyShift action_71
action_178 (105) = happyShift action_72
action_178 (107) = happyShift action_73
action_178 (110) = happyShift action_74
action_178 (111) = happyShift action_75
action_178 (118) = happyShift action_2
action_178 (119) = happyShift action_33
action_178 (120) = happyShift action_76
action_178 (121) = happyShift action_77
action_178 (4) = happyGoto action_19
action_178 (5) = happyGoto action_36
action_178 (6) = happyGoto action_37
action_178 (7) = happyGoto action_38
action_178 (25) = happyGoto action_39
action_178 (26) = happyGoto action_186
action_178 (27) = happyGoto action_41
action_178 (28) = happyGoto action_42
action_178 (29) = happyGoto action_43
action_178 (30) = happyGoto action_44
action_178 (31) = happyGoto action_45
action_178 (32) = happyGoto action_46
action_178 (33) = happyGoto action_47
action_178 (34) = happyGoto action_48
action_178 (35) = happyGoto action_49
action_178 (36) = happyGoto action_50
action_178 (37) = happyGoto action_51
action_178 (38) = happyGoto action_52
action_178 (39) = happyGoto action_53
action_178 (40) = happyGoto action_54
action_178 (41) = happyGoto action_55
action_178 (42) = happyGoto action_56
action_178 (43) = happyGoto action_57
action_178 (44) = happyGoto action_58
action_178 (45) = happyGoto action_59
action_178 (46) = happyGoto action_60
action_178 (48) = happyGoto action_61
action_178 (50) = happyGoto action_21
action_178 (57) = happyGoto action_22
action_178 _ = happyFail

action_179 (63) = happyShift action_64
action_179 (99) = happyShift action_68
action_179 (118) = happyShift action_2
action_179 (119) = happyShift action_33
action_179 (120) = happyShift action_76
action_179 (121) = happyShift action_77
action_179 (4) = happyGoto action_19
action_179 (5) = happyGoto action_36
action_179 (6) = happyGoto action_37
action_179 (7) = happyGoto action_38
action_179 (25) = happyGoto action_39
action_179 (38) = happyGoto action_185
action_179 (39) = happyGoto action_53
action_179 (40) = happyGoto action_54
action_179 (41) = happyGoto action_55
action_179 (42) = happyGoto action_56
action_179 (43) = happyGoto action_57
action_179 (44) = happyGoto action_58
action_179 (45) = happyGoto action_59
action_179 (46) = happyGoto action_60
action_179 (50) = happyGoto action_21
action_179 (57) = happyGoto action_22
action_179 _ = happyFail

action_180 (63) = happyShift action_12
action_180 (81) = happyShift action_13
action_180 (90) = happyShift action_14
action_180 (93) = happyShift action_15
action_180 (94) = happyShift action_16
action_180 (117) = happyShift action_184
action_180 (10) = happyGoto action_6
action_180 (11) = happyGoto action_7
action_180 (12) = happyGoto action_8
action_180 (13) = happyGoto action_9
action_180 (14) = happyGoto action_10
action_180 (16) = happyGoto action_183
action_180 _ = happyReduce_12

action_181 (118) = happyShift action_2
action_181 (4) = happyGoto action_88
action_181 (49) = happyGoto action_89
action_181 (53) = happyGoto action_182
action_181 _ = happyFail

action_182 _ = happyReduce_118

action_183 _ = happyReduce_120

action_184 _ = happyReduce_15

action_185 (97) = happyShift action_202
action_185 _ = happyFail

action_186 _ = happyReduce_46

action_187 _ = happyReduce_124

action_188 (67) = happyShift action_118
action_188 (68) = happyShift action_119
action_188 _ = happyReduce_107

action_189 (58) = happyShift action_62
action_189 (60) = happyShift action_63
action_189 (63) = happyShift action_64
action_189 (69) = happyShift action_66
action_189 (95) = happyShift action_67
action_189 (99) = happyShift action_68
action_189 (101) = happyShift action_69
action_189 (102) = happyShift action_70
action_189 (103) = happyShift action_71
action_189 (105) = happyShift action_72
action_189 (107) = happyShift action_73
action_189 (110) = happyShift action_74
action_189 (111) = happyShift action_75
action_189 (118) = happyShift action_2
action_189 (119) = happyShift action_33
action_189 (120) = happyShift action_76
action_189 (121) = happyShift action_77
action_189 (4) = happyGoto action_19
action_189 (5) = happyGoto action_36
action_189 (6) = happyGoto action_37
action_189 (7) = happyGoto action_38
action_189 (25) = happyGoto action_39
action_189 (26) = happyGoto action_201
action_189 (27) = happyGoto action_41
action_189 (28) = happyGoto action_42
action_189 (29) = happyGoto action_43
action_189 (30) = happyGoto action_44
action_189 (31) = happyGoto action_45
action_189 (32) = happyGoto action_46
action_189 (33) = happyGoto action_47
action_189 (34) = happyGoto action_48
action_189 (35) = happyGoto action_49
action_189 (36) = happyGoto action_50
action_189 (37) = happyGoto action_51
action_189 (38) = happyGoto action_52
action_189 (39) = happyGoto action_53
action_189 (40) = happyGoto action_54
action_189 (41) = happyGoto action_55
action_189 (42) = happyGoto action_56
action_189 (43) = happyGoto action_57
action_189 (44) = happyGoto action_58
action_189 (45) = happyGoto action_59
action_189 (46) = happyGoto action_60
action_189 (48) = happyGoto action_61
action_189 (50) = happyGoto action_21
action_189 (57) = happyGoto action_22
action_189 _ = happyFail

action_190 _ = happyReduce_48

action_191 (58) = happyShift action_62
action_191 (60) = happyShift action_63
action_191 (63) = happyShift action_64
action_191 (69) = happyShift action_66
action_191 (95) = happyShift action_67
action_191 (99) = happyShift action_68
action_191 (101) = happyShift action_69
action_191 (102) = happyShift action_70
action_191 (103) = happyShift action_71
action_191 (105) = happyShift action_72
action_191 (107) = happyShift action_73
action_191 (110) = happyShift action_74
action_191 (111) = happyShift action_75
action_191 (118) = happyShift action_2
action_191 (119) = happyShift action_33
action_191 (120) = happyShift action_76
action_191 (121) = happyShift action_77
action_191 (4) = happyGoto action_19
action_191 (5) = happyGoto action_36
action_191 (6) = happyGoto action_37
action_191 (7) = happyGoto action_38
action_191 (25) = happyGoto action_39
action_191 (26) = happyGoto action_200
action_191 (27) = happyGoto action_41
action_191 (28) = happyGoto action_42
action_191 (29) = happyGoto action_43
action_191 (30) = happyGoto action_44
action_191 (31) = happyGoto action_45
action_191 (32) = happyGoto action_46
action_191 (33) = happyGoto action_47
action_191 (34) = happyGoto action_48
action_191 (35) = happyGoto action_49
action_191 (36) = happyGoto action_50
action_191 (37) = happyGoto action_51
action_191 (38) = happyGoto action_52
action_191 (39) = happyGoto action_53
action_191 (40) = happyGoto action_54
action_191 (41) = happyGoto action_55
action_191 (42) = happyGoto action_56
action_191 (43) = happyGoto action_57
action_191 (44) = happyGoto action_58
action_191 (45) = happyGoto action_59
action_191 (46) = happyGoto action_60
action_191 (48) = happyGoto action_61
action_191 (50) = happyGoto action_21
action_191 (57) = happyGoto action_22
action_191 _ = happyFail

action_192 _ = happyReduce_71

action_193 (114) = happyShift action_92
action_193 (15) = happyGoto action_199
action_193 _ = happyReduce_14

action_194 (58) = happyShift action_62
action_194 (60) = happyShift action_63
action_194 (63) = happyShift action_64
action_194 (69) = happyShift action_66
action_194 (95) = happyShift action_67
action_194 (99) = happyShift action_68
action_194 (101) = happyShift action_69
action_194 (102) = happyShift action_70
action_194 (103) = happyShift action_71
action_194 (105) = happyShift action_72
action_194 (107) = happyShift action_73
action_194 (110) = happyShift action_74
action_194 (111) = happyShift action_75
action_194 (118) = happyShift action_2
action_194 (119) = happyShift action_33
action_194 (120) = happyShift action_76
action_194 (121) = happyShift action_77
action_194 (4) = happyGoto action_19
action_194 (5) = happyGoto action_36
action_194 (6) = happyGoto action_37
action_194 (7) = happyGoto action_38
action_194 (25) = happyGoto action_39
action_194 (26) = happyGoto action_198
action_194 (27) = happyGoto action_41
action_194 (28) = happyGoto action_42
action_194 (29) = happyGoto action_43
action_194 (30) = happyGoto action_44
action_194 (31) = happyGoto action_45
action_194 (32) = happyGoto action_46
action_194 (33) = happyGoto action_47
action_194 (34) = happyGoto action_48
action_194 (35) = happyGoto action_49
action_194 (36) = happyGoto action_50
action_194 (37) = happyGoto action_51
action_194 (38) = happyGoto action_52
action_194 (39) = happyGoto action_53
action_194 (40) = happyGoto action_54
action_194 (41) = happyGoto action_55
action_194 (42) = happyGoto action_56
action_194 (43) = happyGoto action_57
action_194 (44) = happyGoto action_58
action_194 (45) = happyGoto action_59
action_194 (46) = happyGoto action_60
action_194 (48) = happyGoto action_61
action_194 (50) = happyGoto action_21
action_194 (57) = happyGoto action_22
action_194 _ = happyFail

action_195 _ = happyReduce_28

action_196 _ = happyReduce_27

action_197 (64) = happyShift action_173
action_197 (67) = happyShift action_118
action_197 (68) = happyShift action_119
action_197 _ = happyFail

action_198 _ = happyReduce_26

action_199 _ = happyReduce_8

action_200 _ = happyReduce_47

action_201 _ = happyReduce_45

action_202 (63) = happyShift action_64
action_202 (118) = happyShift action_2
action_202 (119) = happyShift action_33
action_202 (120) = happyShift action_76
action_202 (121) = happyShift action_77
action_202 (4) = happyGoto action_19
action_202 (5) = happyGoto action_36
action_202 (6) = happyGoto action_37
action_202 (7) = happyGoto action_38
action_202 (25) = happyGoto action_39
action_202 (39) = happyGoto action_203
action_202 (40) = happyGoto action_54
action_202 (41) = happyGoto action_55
action_202 (42) = happyGoto action_56
action_202 (43) = happyGoto action_57
action_202 (44) = happyGoto action_58
action_202 (45) = happyGoto action_59
action_202 (46) = happyGoto action_60
action_202 (50) = happyGoto action_21
action_202 (57) = happyGoto action_22
action_202 _ = happyFail

action_203 _ = happyReduce_85

happyReduce_1 = happySpecReduce_1  4 happyReduction_1
happyReduction_1 (HappyTerminal (PT _ (TV happy_var_1)))
	 =  HappyAbsSyn4
		 (Ident happy_var_1
	)
happyReduction_1 _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_1  5 happyReduction_2
happyReduction_2 (HappyTerminal (PT _ (TI happy_var_1)))
	 =  HappyAbsSyn5
		 ((read ( happy_var_1)) :: Integer
	)
happyReduction_2 _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_1  6 happyReduction_3
happyReduction_3 (HappyTerminal (PT _ (TD happy_var_1)))
	 =  HappyAbsSyn6
		 ((read ( happy_var_1)) :: Double
	)
happyReduction_3 _  = notHappyAtAll 

happyReduce_4 = happySpecReduce_1  7 happyReduction_4
happyReduction_4 (HappyTerminal (PT _ (TL happy_var_1)))
	 =  HappyAbsSyn7
		 (happy_var_1
	)
happyReduction_4 _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_1  8 happyReduction_5
happyReduction_5 (HappyAbsSyn52  happy_var_1)
	 =  HappyAbsSyn8
		 (Module (reverse happy_var_1)
	)
happyReduction_5 _  = notHappyAtAll 

happyReduce_6 = happyReduce 4 9 happyReduction_6
happyReduction_6 ((HappyAbsSyn53  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (EnumDecl happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_7 = happySpecReduce_1  9 happyReduction_7
happyReduction_7 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn9
		 (ElementDecl happy_var_1
	)
happyReduction_7 _  = notHappyAtAll 

happyReduce_8 = happyReduce 7 10 happyReduction_8
happyReduction_8 ((HappyAbsSyn15  happy_var_7) `HappyStk`
	(HappyAbsSyn19  happy_var_6) `HappyStk`
	(HappyAbsSyn22  happy_var_5) `HappyStk`
	(HappyAbsSyn17  happy_var_4) `HappyStk`
	(HappyAbsSyn4  happy_var_3) `HappyStk`
	(HappyAbsSyn21  happy_var_2) `HappyStk`
	(HappyAbsSyn14  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Clafer happy_var_1 happy_var_2 happy_var_3 happy_var_4 happy_var_5 happy_var_6 happy_var_7
	) `HappyStk` happyRest

happyReduce_9 = happySpecReduce_3  11 happyReduction_9
happyReduction_9 _
	(HappyAbsSyn55  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (Constraint (reverse happy_var_2)
	)
happyReduction_9 _ _ _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_3  12 happyReduction_10
happyReduction_10 _
	(HappyAbsSyn55  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (SoftConstraint (reverse happy_var_2)
	)
happyReduction_10 _ _ _  = notHappyAtAll 

happyReduce_11 = happySpecReduce_3  13 happyReduction_11
happyReduction_11 _
	(HappyAbsSyn55  happy_var_2)
	_
	 =  HappyAbsSyn13
		 (Goal (reverse happy_var_2)
	)
happyReduction_11 _ _ _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_0  14 happyReduction_12
happyReduction_12  =  HappyAbsSyn14
		 (AbstractEmpty
	)

happyReduce_13 = happySpecReduce_1  14 happyReduction_13
happyReduction_13 _
	 =  HappyAbsSyn14
		 (Abstract
	)

happyReduce_14 = happySpecReduce_0  15 happyReduction_14
happyReduction_14  =  HappyAbsSyn15
		 (ElementsEmpty
	)

happyReduce_15 = happySpecReduce_3  15 happyReduction_15
happyReduction_15 _
	(HappyAbsSyn54  happy_var_2)
	_
	 =  HappyAbsSyn15
		 (ElementsList (reverse happy_var_2)
	)
happyReduction_15 _ _ _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_1  16 happyReduction_16
happyReduction_16 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn16
		 (Subclafer happy_var_1
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happyReduce 4 16 happyReduction_17
happyReduction_17 ((HappyAbsSyn15  happy_var_4) `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	(HappyAbsSyn25  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn16
		 (ClaferUse happy_var_2 happy_var_3 happy_var_4
	) `HappyStk` happyRest

happyReduce_18 = happySpecReduce_1  16 happyReduction_18
happyReduction_18 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn16
		 (Subconstraint happy_var_1
	)
happyReduction_18 _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_1  16 happyReduction_19
happyReduction_19 (HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn16
		 (Subgoal happy_var_1
	)
happyReduction_19 _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  16 happyReduction_20
happyReduction_20 (HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn16
		 (Subsoftconstraint happy_var_1
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_0  17 happyReduction_21
happyReduction_21  =  HappyAbsSyn17
		 (SuperEmpty
	)

happyReduce_22 = happySpecReduce_2  17 happyReduction_22
happyReduction_22 (HappyAbsSyn40  happy_var_2)
	(HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn17
		 (SuperSome happy_var_1 happy_var_2
	)
happyReduction_22 _ _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_1  18 happyReduction_23
happyReduction_23 _
	 =  HappyAbsSyn18
		 (SuperHow_1
	)

happyReduce_24 = happySpecReduce_1  18 happyReduction_24
happyReduction_24 _
	 =  HappyAbsSyn18
		 (SuperHow_2
	)

happyReduce_25 = happySpecReduce_0  19 happyReduction_25
happyReduction_25  =  HappyAbsSyn19
		 (InitEmpty
	)

happyReduce_26 = happySpecReduce_2  19 happyReduction_26
happyReduction_26 (HappyAbsSyn26  happy_var_2)
	(HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn19
		 (InitSome happy_var_1 happy_var_2
	)
happyReduction_26 _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_1  20 happyReduction_27
happyReduction_27 _
	 =  HappyAbsSyn20
		 (InitHow_1
	)

happyReduce_28 = happySpecReduce_1  20 happyReduction_28
happyReduction_28 _
	 =  HappyAbsSyn20
		 (InitHow_2
	)

happyReduce_29 = happySpecReduce_0  21 happyReduction_29
happyReduction_29  =  HappyAbsSyn21
		 (GCardEmpty
	)

happyReduce_30 = happySpecReduce_1  21 happyReduction_30
happyReduction_30 _
	 =  HappyAbsSyn21
		 (GCardXor
	)

happyReduce_31 = happySpecReduce_1  21 happyReduction_31
happyReduction_31 _
	 =  HappyAbsSyn21
		 (GCardOr
	)

happyReduce_32 = happySpecReduce_1  21 happyReduction_32
happyReduction_32 _
	 =  HappyAbsSyn21
		 (GCardMux
	)

happyReduce_33 = happySpecReduce_1  21 happyReduction_33
happyReduction_33 _
	 =  HappyAbsSyn21
		 (GCardOpt
	)

happyReduce_34 = happySpecReduce_1  21 happyReduction_34
happyReduction_34 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn21
		 (GCardInterval happy_var_1
	)
happyReduction_34 _  = notHappyAtAll 

happyReduce_35 = happySpecReduce_0  22 happyReduction_35
happyReduction_35  =  HappyAbsSyn22
		 (CardEmpty
	)

happyReduce_36 = happySpecReduce_1  22 happyReduction_36
happyReduction_36 _
	 =  HappyAbsSyn22
		 (CardLone
	)

happyReduce_37 = happySpecReduce_1  22 happyReduction_37
happyReduction_37 _
	 =  HappyAbsSyn22
		 (CardSome
	)

happyReduce_38 = happySpecReduce_1  22 happyReduction_38
happyReduction_38 _
	 =  HappyAbsSyn22
		 (CardAny
	)

happyReduce_39 = happySpecReduce_1  22 happyReduction_39
happyReduction_39 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn22
		 (CardNum happy_var_1
	)
happyReduction_39 _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_1  22 happyReduction_40
happyReduction_40 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn22
		 (CardInterval happy_var_1
	)
happyReduction_40 _  = notHappyAtAll 

happyReduce_41 = happySpecReduce_3  23 happyReduction_41
happyReduction_41 (HappyAbsSyn24  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn23
		 (NCard happy_var_1 happy_var_3
	)
happyReduction_41 _ _ _  = notHappyAtAll 

happyReduce_42 = happySpecReduce_1  24 happyReduction_42
happyReduction_42 _
	 =  HappyAbsSyn24
		 (ExIntegerAst
	)

happyReduce_43 = happySpecReduce_1  24 happyReduction_43
happyReduction_43 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn24
		 (ExIntegerNum happy_var_1
	)
happyReduction_43 _  = notHappyAtAll 

happyReduce_44 = happySpecReduce_1  25 happyReduction_44
happyReduction_44 (HappyAbsSyn57  happy_var_1)
	 =  HappyAbsSyn25
		 (Path happy_var_1
	)
happyReduction_44 _  = notHappyAtAll 

happyReduce_45 = happyReduce 5 26 happyReduction_45
happyReduction_45 ((HappyAbsSyn26  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn47  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn26
		 (DeclAllDisj happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_46 = happyReduce 4 26 happyReduction_46
happyReduction_46 ((HappyAbsSyn26  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn47  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn26
		 (DeclAll happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_47 = happyReduce 5 26 happyReduction_47
happyReduction_47 ((HappyAbsSyn26  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn47  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn48  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn26
		 (DeclQuantDisj happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_48 = happyReduce 4 26 happyReduction_48
happyReduction_48 ((HappyAbsSyn26  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn47  happy_var_2) `HappyStk`
	(HappyAbsSyn48  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn26
		 (DeclQuant happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_49 = happySpecReduce_1  26 happyReduction_49
happyReduction_49 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_49 _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_2  27 happyReduction_50
happyReduction_50 (HappyAbsSyn26  happy_var_2)
	_
	 =  HappyAbsSyn26
		 (EGMax happy_var_2
	)
happyReduction_50 _ _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_2  27 happyReduction_51
happyReduction_51 (HappyAbsSyn26  happy_var_2)
	_
	 =  HappyAbsSyn26
		 (EGMin happy_var_2
	)
happyReduction_51 _ _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_3  27 happyReduction_52
happyReduction_52 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EIff happy_var_1 happy_var_3
	)
happyReduction_52 _ _ _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_1  27 happyReduction_53
happyReduction_53 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_53 _  = notHappyAtAll 

happyReduce_54 = happySpecReduce_3  28 happyReduction_54
happyReduction_54 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EImplies happy_var_1 happy_var_3
	)
happyReduction_54 _ _ _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_1  28 happyReduction_55
happyReduction_55 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_55 _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_3  29 happyReduction_56
happyReduction_56 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EOr happy_var_1 happy_var_3
	)
happyReduction_56 _ _ _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_1  29 happyReduction_57
happyReduction_57 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_57 _  = notHappyAtAll 

happyReduce_58 = happySpecReduce_3  30 happyReduction_58
happyReduction_58 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EXor happy_var_1 happy_var_3
	)
happyReduction_58 _ _ _  = notHappyAtAll 

happyReduce_59 = happySpecReduce_1  30 happyReduction_59
happyReduction_59 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_59 _  = notHappyAtAll 

happyReduce_60 = happySpecReduce_3  31 happyReduction_60
happyReduction_60 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EAnd happy_var_1 happy_var_3
	)
happyReduction_60 _ _ _  = notHappyAtAll 

happyReduce_61 = happySpecReduce_1  31 happyReduction_61
happyReduction_61 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_61 _  = notHappyAtAll 

happyReduce_62 = happySpecReduce_2  32 happyReduction_62
happyReduction_62 (HappyAbsSyn26  happy_var_2)
	_
	 =  HappyAbsSyn26
		 (ENeg happy_var_2
	)
happyReduction_62 _ _  = notHappyAtAll 

happyReduce_63 = happySpecReduce_1  32 happyReduction_63
happyReduction_63 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_63 _  = notHappyAtAll 

happyReduce_64 = happySpecReduce_3  33 happyReduction_64
happyReduction_64 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (ELt happy_var_1 happy_var_3
	)
happyReduction_64 _ _ _  = notHappyAtAll 

happyReduce_65 = happySpecReduce_3  33 happyReduction_65
happyReduction_65 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EGt happy_var_1 happy_var_3
	)
happyReduction_65 _ _ _  = notHappyAtAll 

happyReduce_66 = happySpecReduce_3  33 happyReduction_66
happyReduction_66 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EEq happy_var_1 happy_var_3
	)
happyReduction_66 _ _ _  = notHappyAtAll 

happyReduce_67 = happySpecReduce_3  33 happyReduction_67
happyReduction_67 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (ELte happy_var_1 happy_var_3
	)
happyReduction_67 _ _ _  = notHappyAtAll 

happyReduce_68 = happySpecReduce_3  33 happyReduction_68
happyReduction_68 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EGte happy_var_1 happy_var_3
	)
happyReduction_68 _ _ _  = notHappyAtAll 

happyReduce_69 = happySpecReduce_3  33 happyReduction_69
happyReduction_69 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (ENeq happy_var_1 happy_var_3
	)
happyReduction_69 _ _ _  = notHappyAtAll 

happyReduce_70 = happySpecReduce_3  33 happyReduction_70
happyReduction_70 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EIn happy_var_1 happy_var_3
	)
happyReduction_70 _ _ _  = notHappyAtAll 

happyReduce_71 = happyReduce 4 33 happyReduction_71
happyReduction_71 ((HappyAbsSyn26  happy_var_4) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn26  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn26
		 (ENin happy_var_1 happy_var_4
	) `HappyStk` happyRest

happyReduce_72 = happySpecReduce_1  33 happyReduction_72
happyReduction_72 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_72 _  = notHappyAtAll 

happyReduce_73 = happySpecReduce_2  34 happyReduction_73
happyReduction_73 (HappyAbsSyn26  happy_var_2)
	(HappyAbsSyn48  happy_var_1)
	 =  HappyAbsSyn26
		 (QuantExp happy_var_1 happy_var_2
	)
happyReduction_73 _ _  = notHappyAtAll 

happyReduce_74 = happySpecReduce_1  34 happyReduction_74
happyReduction_74 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_74 _  = notHappyAtAll 

happyReduce_75 = happySpecReduce_3  35 happyReduction_75
happyReduction_75 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EAdd happy_var_1 happy_var_3
	)
happyReduction_75 _ _ _  = notHappyAtAll 

happyReduce_76 = happySpecReduce_3  35 happyReduction_76
happyReduction_76 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (ESub happy_var_1 happy_var_3
	)
happyReduction_76 _ _ _  = notHappyAtAll 

happyReduce_77 = happySpecReduce_1  35 happyReduction_77
happyReduction_77 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_77 _  = notHappyAtAll 

happyReduce_78 = happySpecReduce_3  36 happyReduction_78
happyReduction_78 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EMul happy_var_1 happy_var_3
	)
happyReduction_78 _ _ _  = notHappyAtAll 

happyReduce_79 = happySpecReduce_3  36 happyReduction_79
happyReduction_79 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (EDiv happy_var_1 happy_var_3
	)
happyReduction_79 _ _ _  = notHappyAtAll 

happyReduce_80 = happySpecReduce_1  36 happyReduction_80
happyReduction_80 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_80 _  = notHappyAtAll 

happyReduce_81 = happySpecReduce_2  37 happyReduction_81
happyReduction_81 (HappyAbsSyn26  happy_var_2)
	_
	 =  HappyAbsSyn26
		 (ESumSetExp happy_var_2
	)
happyReduction_81 _ _  = notHappyAtAll 

happyReduce_82 = happySpecReduce_2  37 happyReduction_82
happyReduction_82 (HappyAbsSyn26  happy_var_2)
	_
	 =  HappyAbsSyn26
		 (ECSetExp happy_var_2
	)
happyReduction_82 _ _  = notHappyAtAll 

happyReduce_83 = happySpecReduce_2  37 happyReduction_83
happyReduction_83 (HappyAbsSyn26  happy_var_2)
	_
	 =  HappyAbsSyn26
		 (EMinExp happy_var_2
	)
happyReduction_83 _ _  = notHappyAtAll 

happyReduce_84 = happySpecReduce_1  37 happyReduction_84
happyReduction_84 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_84 _  = notHappyAtAll 

happyReduce_85 = happyReduce 6 38 happyReduction_85
happyReduction_85 ((HappyAbsSyn26  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn26  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn26  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn26
		 (EImpliesElse happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_86 = happySpecReduce_1  38 happyReduction_86
happyReduction_86 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1
	)
happyReduction_86 _  = notHappyAtAll 

happyReduce_87 = happySpecReduce_1  39 happyReduction_87
happyReduction_87 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn26
		 (EInt happy_var_1
	)
happyReduction_87 _  = notHappyAtAll 

happyReduce_88 = happySpecReduce_1  39 happyReduction_88
happyReduction_88 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn26
		 (EDouble happy_var_1
	)
happyReduction_88 _  = notHappyAtAll 

happyReduce_89 = happySpecReduce_1  39 happyReduction_89
happyReduction_89 (HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn26
		 (EStr happy_var_1
	)
happyReduction_89 _  = notHappyAtAll 

happyReduce_90 = happySpecReduce_1  39 happyReduction_90
happyReduction_90 (HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn26
		 (ESetExp happy_var_1
	)
happyReduction_90 _  = notHappyAtAll 

happyReduce_91 = happySpecReduce_3  39 happyReduction_91
happyReduction_91 _
	(HappyAbsSyn26  happy_var_2)
	_
	 =  HappyAbsSyn26
		 (happy_var_2
	)
happyReduction_91 _ _ _  = notHappyAtAll 

happyReduce_92 = happySpecReduce_3  40 happyReduction_92
happyReduction_92 (HappyAbsSyn40  happy_var_3)
	_
	(HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (Union happy_var_1 happy_var_3
	)
happyReduction_92 _ _ _  = notHappyAtAll 

happyReduce_93 = happySpecReduce_3  40 happyReduction_93
happyReduction_93 (HappyAbsSyn40  happy_var_3)
	_
	(HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (UnionCom happy_var_1 happy_var_3
	)
happyReduction_93 _ _ _  = notHappyAtAll 

happyReduce_94 = happySpecReduce_1  40 happyReduction_94
happyReduction_94 (HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (happy_var_1
	)
happyReduction_94 _  = notHappyAtAll 

happyReduce_95 = happySpecReduce_3  41 happyReduction_95
happyReduction_95 (HappyAbsSyn40  happy_var_3)
	_
	(HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (Difference happy_var_1 happy_var_3
	)
happyReduction_95 _ _ _  = notHappyAtAll 

happyReduce_96 = happySpecReduce_1  41 happyReduction_96
happyReduction_96 (HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (happy_var_1
	)
happyReduction_96 _  = notHappyAtAll 

happyReduce_97 = happySpecReduce_3  42 happyReduction_97
happyReduction_97 (HappyAbsSyn40  happy_var_3)
	_
	(HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (Intersection happy_var_1 happy_var_3
	)
happyReduction_97 _ _ _  = notHappyAtAll 

happyReduce_98 = happySpecReduce_1  42 happyReduction_98
happyReduction_98 (HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (happy_var_1
	)
happyReduction_98 _  = notHappyAtAll 

happyReduce_99 = happySpecReduce_3  43 happyReduction_99
happyReduction_99 (HappyAbsSyn40  happy_var_3)
	_
	(HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (Domain happy_var_1 happy_var_3
	)
happyReduction_99 _ _ _  = notHappyAtAll 

happyReduce_100 = happySpecReduce_1  43 happyReduction_100
happyReduction_100 (HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (happy_var_1
	)
happyReduction_100 _  = notHappyAtAll 

happyReduce_101 = happySpecReduce_3  44 happyReduction_101
happyReduction_101 (HappyAbsSyn40  happy_var_3)
	_
	(HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (Range happy_var_1 happy_var_3
	)
happyReduction_101 _ _ _  = notHappyAtAll 

happyReduce_102 = happySpecReduce_1  44 happyReduction_102
happyReduction_102 (HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (happy_var_1
	)
happyReduction_102 _  = notHappyAtAll 

happyReduce_103 = happySpecReduce_3  45 happyReduction_103
happyReduction_103 (HappyAbsSyn40  happy_var_3)
	_
	(HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (Join happy_var_1 happy_var_3
	)
happyReduction_103 _ _ _  = notHappyAtAll 

happyReduce_104 = happySpecReduce_1  45 happyReduction_104
happyReduction_104 (HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (happy_var_1
	)
happyReduction_104 _  = notHappyAtAll 

happyReduce_105 = happySpecReduce_1  46 happyReduction_105
happyReduction_105 (HappyAbsSyn25  happy_var_1)
	 =  HappyAbsSyn40
		 (ClaferId happy_var_1
	)
happyReduction_105 _  = notHappyAtAll 

happyReduce_106 = happySpecReduce_3  46 happyReduction_106
happyReduction_106 _
	(HappyAbsSyn40  happy_var_2)
	_
	 =  HappyAbsSyn40
		 (happy_var_2
	)
happyReduction_106 _ _ _  = notHappyAtAll 

happyReduce_107 = happySpecReduce_3  47 happyReduction_107
happyReduction_107 (HappyAbsSyn40  happy_var_3)
	_
	(HappyAbsSyn56  happy_var_1)
	 =  HappyAbsSyn47
		 (Decl happy_var_1 happy_var_3
	)
happyReduction_107 _ _ _  = notHappyAtAll 

happyReduce_108 = happySpecReduce_1  48 happyReduction_108
happyReduction_108 _
	 =  HappyAbsSyn48
		 (QuantNo
	)

happyReduce_109 = happySpecReduce_1  48 happyReduction_109
happyReduction_109 _
	 =  HappyAbsSyn48
		 (QuantLone
	)

happyReduce_110 = happySpecReduce_1  48 happyReduction_110
happyReduction_110 _
	 =  HappyAbsSyn48
		 (QuantOne
	)

happyReduce_111 = happySpecReduce_1  48 happyReduction_111
happyReduction_111 _
	 =  HappyAbsSyn48
		 (QuantSome
	)

happyReduce_112 = happySpecReduce_1  49 happyReduction_112
happyReduction_112 (HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn49
		 (EnumIdIdent happy_var_1
	)
happyReduction_112 _  = notHappyAtAll 

happyReduce_113 = happySpecReduce_1  50 happyReduction_113
happyReduction_113 (HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn50
		 (ModIdIdent happy_var_1
	)
happyReduction_113 _  = notHappyAtAll 

happyReduce_114 = happySpecReduce_1  51 happyReduction_114
happyReduction_114 (HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn51
		 (LocIdIdent happy_var_1
	)
happyReduction_114 _  = notHappyAtAll 

happyReduce_115 = happySpecReduce_0  52 happyReduction_115
happyReduction_115  =  HappyAbsSyn52
		 ([]
	)

happyReduce_116 = happySpecReduce_2  52 happyReduction_116
happyReduction_116 (HappyAbsSyn9  happy_var_2)
	(HappyAbsSyn52  happy_var_1)
	 =  HappyAbsSyn52
		 (flip (:) happy_var_1 happy_var_2
	)
happyReduction_116 _ _  = notHappyAtAll 

happyReduce_117 = happySpecReduce_1  53 happyReduction_117
happyReduction_117 (HappyAbsSyn49  happy_var_1)
	 =  HappyAbsSyn53
		 ((:[]) happy_var_1
	)
happyReduction_117 _  = notHappyAtAll 

happyReduce_118 = happySpecReduce_3  53 happyReduction_118
happyReduction_118 (HappyAbsSyn53  happy_var_3)
	_
	(HappyAbsSyn49  happy_var_1)
	 =  HappyAbsSyn53
		 ((:) happy_var_1 happy_var_3
	)
happyReduction_118 _ _ _  = notHappyAtAll 

happyReduce_119 = happySpecReduce_0  54 happyReduction_119
happyReduction_119  =  HappyAbsSyn54
		 ([]
	)

happyReduce_120 = happySpecReduce_2  54 happyReduction_120
happyReduction_120 (HappyAbsSyn16  happy_var_2)
	(HappyAbsSyn54  happy_var_1)
	 =  HappyAbsSyn54
		 (flip (:) happy_var_1 happy_var_2
	)
happyReduction_120 _ _  = notHappyAtAll 

happyReduce_121 = happySpecReduce_0  55 happyReduction_121
happyReduction_121  =  HappyAbsSyn55
		 ([]
	)

happyReduce_122 = happySpecReduce_2  55 happyReduction_122
happyReduction_122 (HappyAbsSyn26  happy_var_2)
	(HappyAbsSyn55  happy_var_1)
	 =  HappyAbsSyn55
		 (flip (:) happy_var_1 happy_var_2
	)
happyReduction_122 _ _  = notHappyAtAll 

happyReduce_123 = happySpecReduce_1  56 happyReduction_123
happyReduction_123 (HappyAbsSyn51  happy_var_1)
	 =  HappyAbsSyn56
		 ((:[]) happy_var_1
	)
happyReduction_123 _  = notHappyAtAll 

happyReduce_124 = happySpecReduce_3  56 happyReduction_124
happyReduction_124 (HappyAbsSyn56  happy_var_3)
	_
	(HappyAbsSyn51  happy_var_1)
	 =  HappyAbsSyn56
		 ((:) happy_var_1 happy_var_3
	)
happyReduction_124 _ _ _  = notHappyAtAll 

happyReduce_125 = happySpecReduce_1  57 happyReduction_125
happyReduction_125 (HappyAbsSyn50  happy_var_1)
	 =  HappyAbsSyn57
		 ((:[]) happy_var_1
	)
happyReduction_125 _  = notHappyAtAll 

happyReduce_126 = happySpecReduce_3  57 happyReduction_126
happyReduction_126 (HappyAbsSyn57  happy_var_3)
	_
	(HappyAbsSyn50  happy_var_1)
	 =  HappyAbsSyn57
		 ((:) happy_var_1 happy_var_3
	)
happyReduction_126 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 123 123 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 58;
	PT _ (TS _ 2) -> cont 59;
	PT _ (TS _ 3) -> cont 60;
	PT _ (TS _ 4) -> cont 61;
	PT _ (TS _ 5) -> cont 62;
	PT _ (TS _ 6) -> cont 63;
	PT _ (TS _ 7) -> cont 64;
	PT _ (TS _ 8) -> cont 65;
	PT _ (TS _ 9) -> cont 66;
	PT _ (TS _ 10) -> cont 67;
	PT _ (TS _ 11) -> cont 68;
	PT _ (TS _ 12) -> cont 69;
	PT _ (TS _ 13) -> cont 70;
	PT _ (TS _ 14) -> cont 71;
	PT _ (TS _ 15) -> cont 72;
	PT _ (TS _ 16) -> cont 73;
	PT _ (TS _ 17) -> cont 74;
	PT _ (TS _ 18) -> cont 75;
	PT _ (TS _ 19) -> cont 76;
	PT _ (TS _ 20) -> cont 77;
	PT _ (TS _ 21) -> cont 78;
	PT _ (TS _ 22) -> cont 79;
	PT _ (TS _ 23) -> cont 80;
	PT _ (TS _ 24) -> cont 81;
	PT _ (TS _ 25) -> cont 82;
	PT _ (TS _ 26) -> cont 83;
	PT _ (TS _ 27) -> cont 84;
	PT _ (TS _ 28) -> cont 85;
	PT _ (TS _ 29) -> cont 86;
	PT _ (TS _ 30) -> cont 87;
	PT _ (TS _ 31) -> cont 88;
	PT _ (TS _ 32) -> cont 89;
	PT _ (TS _ 33) -> cont 90;
	PT _ (TS _ 34) -> cont 91;
	PT _ (TS _ 35) -> cont 92;
	PT _ (TS _ 36) -> cont 93;
	PT _ (TS _ 37) -> cont 94;
	PT _ (TS _ 38) -> cont 95;
	PT _ (TS _ 39) -> cont 96;
	PT _ (TS _ 40) -> cont 97;
	PT _ (TS _ 41) -> cont 98;
	PT _ (TS _ 42) -> cont 99;
	PT _ (TS _ 43) -> cont 100;
	PT _ (TS _ 44) -> cont 101;
	PT _ (TS _ 45) -> cont 102;
	PT _ (TS _ 46) -> cont 103;
	PT _ (TS _ 47) -> cont 104;
	PT _ (TS _ 48) -> cont 105;
	PT _ (TS _ 49) -> cont 106;
	PT _ (TS _ 50) -> cont 107;
	PT _ (TS _ 51) -> cont 108;
	PT _ (TS _ 52) -> cont 109;
	PT _ (TS _ 53) -> cont 110;
	PT _ (TS _ 54) -> cont 111;
	PT _ (TS _ 55) -> cont 112;
	PT _ (TS _ 56) -> cont 113;
	PT _ (TS _ 57) -> cont 114;
	PT _ (TS _ 58) -> cont 115;
	PT _ (TS _ 59) -> cont 116;
	PT _ (TS _ 60) -> cont 117;
	PT _ (TV happy_dollar_dollar) -> cont 118;
	PT _ (TI happy_dollar_dollar) -> cont 119;
	PT _ (TD happy_dollar_dollar) -> cont 120;
	PT _ (TL happy_dollar_dollar) -> cont 121;
	_ -> cont 122;
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
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn8 z -> happyReturn z; _other -> notHappyAtAll })

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
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 30 "templates/GenericTemplate.hs" #-}








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

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
	happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
	 (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

{-# LINE 148 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let (i) = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
	 sts1@(((st1@(HappyState (action))):(_))) ->
        	let r = fn stk in  -- it doesn't hurt to always seq here...
       		happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
        happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
       happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk





             new_state = action


happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

{-# LINE 246 "templates/GenericTemplate.hs" #-}
happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail  (1) tk old_st _ stk =
--	trace "failing" $ 
    	happyError_ tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
						(saved_tok `HappyStk` _ `HappyStk` stk) =
--	trace ("discarding state, depth " ++ show (length stk))  $
	action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
	action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







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

{-# LINE 311 "templates/GenericTemplate.hs" #-}
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
