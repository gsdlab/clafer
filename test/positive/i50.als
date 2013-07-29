open util/integer
pred show {}


fact { #c1_A = 0 }
abstract sig c1_A
{ r_c2_b : lone c2_b }

sig c2_b
{}
{ one @r_c2_b.this }

one sig c3_C
{ r_c4_b : lone c4_b
, r_c5_a : one c5_a }
{ all disj x, y : this.@r_c5_a | (x.@ref) != (y.@ref) }

lone sig c4_b
{}
{ one r_c4_b }

one sig c5_a
{ ref : one c1_A
, r_c6_d : one c6_d }
{ some (this.@r_c6_d).@r_c7_b }

one sig c6_d
{ r_c7_b : lone c7_b }

lone sig c7_b
{}
{ one r_c7_b }

