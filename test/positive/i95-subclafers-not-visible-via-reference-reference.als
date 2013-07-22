open util/integer
pred show {}


abstract sig c1_A
{ r_c2_x : lone c2_x }

sig c2_x
{}
{ one @r_c2_x.this }

fact { 2 <= #c3_a and #c3_a <= 2 }
sig c3_a extends c1_A
{}

lone sig c4_ref1
{ ref : one c1_A }

fact { all disj x, y : c4_ref1 | (x.@ref) != (y.@ref) }
lone sig c14_ref2
{ ref : one c4_ref1 }
{ some (this.@ref).(@ref.@r_c2_x) }

fact { all disj x, y : c14_ref2 | (x.@ref) != (y.@ref) }
