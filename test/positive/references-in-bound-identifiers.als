open util/integer
pred show {}


lone sig c1_A
{ r_c2_B : set c2_B }
{ all  b : this.@r_c2_B | some b.@r_c3_C
  all  b : this.@r_c2_B | ((b.@ref).add[1]) = 2 }

sig c2_B
{ ref : one Int
, r_c3_C : lone c3_C }
{ one @r_c2_B.this }

sig c3_C
{}
{ one @r_c3_C.this }

