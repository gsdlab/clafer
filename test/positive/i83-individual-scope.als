open util/integer
pred show {}


lone sig c1_a
{}

one sig c2_b
{}

some sig c3_c
{}

fact { 2 <= #c4_d }
sig c4_d
{ r_c5_e : lone c5_e
, r_c6_f : one c6_f
, r_c7_g : set c7_g }
{ 2 <= #r_c7_g }

sig c5_e
{}
{ one @r_c5_e.this }

sig c6_f
{}
{ one @r_c6_f.this }

sig c7_g
{}
{ one @r_c7_g.this }

