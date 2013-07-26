open util/integer
pred show {}


sig c1_a
{ ref : one Int }

one sig c2_b
{ ref : one Int }

fact { (c2_b.@ref) = (sum temp : c1_a | temp.@ref) }
fact { all disj x, y : c2_b | (x.@ref) != (y.@ref) }
fact { (c2_b.@ref) = 2 }
