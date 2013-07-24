open util/integer
pred show {}


abstract sig c1_B
{}

fact { 4 <= #c2_A and #c2_A <= 4 }
abstract sig c2_A extends c1_B
{ r_c3_X : set c3_X }
{ let children = (r_c3_X) | 2 <= #children and #children <= 3 }

sig c3_X
{}
{ one @r_c3_X.this }

fact { 4 <= #c4_C and #c4_C <= 4 }
sig c4_C extends c2_A
{}

