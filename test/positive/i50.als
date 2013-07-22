open util/integer
pred show {}


fact { #c1_A <= 0 }
abstract sig c1_A
{ r_c2_b : lone c2_b }

sig c2_b
{}
{ one @r_c2_b.this }

lone sig c3_C
{ r_c4_b : lone c4_b
, r_c5_a : one c5_a }
{ all disj x, y : this.@r_c5_a | (x.@ref) != (y.@ref) }

lone sig c4_b
{}
{ one r_c4_b }

lone sig c5_a
{ ref : one c1_A
, r_c8_d : one c8_d }
{ one r_c5_a
  some (this.@r_c8_d).@r_c9_b }

lone sig c8_d
{ r_c9_b : lone c9_b }
{ one r_c8_d }

lone sig c9_b
{}
{ one r_c9_b }

