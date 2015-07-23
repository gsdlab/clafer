open util/integer
pred show {}


one sig c0_A
{ r_c0_B : set c0_B }
{ all disj x, y : this.@r_c0_B | (x.@ref) != (y.@ref) 
  all  b : this.@r_c0_B | some b.@r_c0_C
  all  b : this.@r_c0_B | ((b.@ref).plus[1]) = 2 }

sig c0_B
{ ref : one Int
, r_c0_C : lone c0_C }
{ one @r_c0_B.this }

sig c0_C
{}
{ one @r_c0_C.this }

