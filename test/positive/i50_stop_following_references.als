open util/integer
pred show {}


abstract sig c1_A
{ r_c2_b : lone c2_b }

sig c2_b
{}
{ one @r_c2_b.this }

one sig c3_A1 extends c1_A
{}
{ no this.@r_c2_b }

one sig c4_C
{ r_c5_b : lone c5_b
, r_c6_a : one c6_a }
{ some c4_C.@r_c5_b
  all disj x, y : this.@r_c6_a | (x.@ref) != (y.@ref) }

lone sig c5_b
{}
{ one r_c5_b }

one sig c6_a
{ ref : one c1_A
, r_c7_d : one c7_d }
{ some (this.@r_c7_d).@r_c8_b }

one sig c7_d
{ r_c8_b : lone c8_b }

lone sig c8_b
{}
{ one r_c8_b }

