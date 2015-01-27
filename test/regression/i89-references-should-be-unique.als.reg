open util/integer
pred show {}


abstract sig c0_A
{}

some sig c0_a extends c0_A
{}

fact { 3 <= #c0_setRefToA and #c0_setRefToA <= 3 }
sig c0_setRefToA
{ ref : one c0_A }

fact {  all disj x, y : c0_setRefToA | (x.@ref) != (y.@ref)  }
fact { 3 <= #c0_multisetRefToA and #c0_multisetRefToA <= 3 }
sig c0_multisetRefToA
{ ref : one c0_A }

