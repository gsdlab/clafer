open util/integer
pred show {}


lone sig c1_A
{ r_c2_B : one c2_B
, r_c3_C : lone c3_C }

lone sig c2_B
{}
{ one r_c2_B }

lone sig c3_C
{}
{ one r_c3_C }

lone sig c4_D
{ ref : one c1_A }

fact { all disj x, y : c4_D | (x.@ref) != (y.@ref) }
