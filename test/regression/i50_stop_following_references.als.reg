open util/integer
pred show {}


abstract sig c1_A
{ r_c2_b : lone c2_b }

sig c2_b
{}
{ one @r_c2_b.this }

lone sig c3_A1 extends c1_A
{}
{ no this.@r_c2_b }

lone sig c6_C
{ r_c7_b : lone c7_b
, r_c12_a : one c12_a }
{ some c6_C.@r_c7_b
  all disj x, y : this.@r_c12_a | (x.@ref) != (y.@ref) }

lone sig c7_b
{}
{ one r_c7_b }

lone sig c12_a
{ ref : one c1_A
, r_c15_d : one c15_d }
{ one r_c12_a
  some (this.@r_c15_d).@r_c16_b }

lone sig c15_d
{ r_c16_b : lone c16_b }
{ one r_c15_d }

lone sig c16_b
{}
{ one r_c16_b }

