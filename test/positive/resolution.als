open util/integer
pred show {}


one sig c1_X
{ r_c2_x : one c2_x }
{ some this.@r_c2_x }

one sig c2_x
{ r_c3_y : one c3_y }

one sig c3_y
{}

one sig c4_Z
{ r_c5_z : one c5_z }
{ (this.(@r_c5_z.@ref)) > 0 }

one sig c5_z
{ ref : one Int
, r_c6_y : one c6_y }

one sig c6_y
{}

