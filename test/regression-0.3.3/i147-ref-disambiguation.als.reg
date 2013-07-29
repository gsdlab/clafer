open util/integer
pred show {}


lone sig c1_a
{ ref : one Int
, r_c2_b : lone c2_b }

lone sig c2_b
{}
{ one r_c2_b
  (this.(~@r_c2_b.@ref)) = 4 }

fact { all disj x, y : c1_a | (x.@ref) != (y.@ref) }
