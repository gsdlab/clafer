open util/integer
pred show {}


fact { #c1_A <= 0 }
abstract sig c1_A
{}

lone sig c2_aRef
{ ref : one c1_A }

fact { all disj x, y : c2_aRef | (x.@ref) != (y.@ref) }
