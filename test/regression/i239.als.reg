open util/integer
pred show {}


sig c1_x
{ ref : one Int }

sig c2_y
{ ref : one Int }

one sig c3_z
{ ref : one Int }

fact { (c3_z.@ref) = (sum temp : ((c1_x.@ref) + c2_y) | temp.@ref) }
fact { all disj x, y : c3_z | (x.@ref) != (y.@ref) }
