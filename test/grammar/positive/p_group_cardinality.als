open util/integer
pred show {}


lone sig c1_A
{ r_c2_X : set c2_X }
{ let children = (r_c2_X) | 2 <= #children and #children <= 3
  1 <= #r_c2_X and #r_c2_X <= 5 }

sig c2_X
{}
{ one @r_c2_X.this }

