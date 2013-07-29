open util/integer
pred show {}


abstract sig c1_A
{}

some sig c2_a extends c1_A
{}

fact { 3 <= #c3_setRefToA and #c3_setRefToA <= 3 }
sig c3_setRefToA
{ ref : one c1_A }

fact { all disj x, y : c3_setRefToA | (x.@ref) != (y.@ref) }
fact { 3 <= #c13_multisetRefToA and #c13_multisetRefToA <= 3 }
sig c13_multisetRefToA
{ ref : one c1_A }

