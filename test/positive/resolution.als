open util/integer
pred show {}


lone sig c1_X
{ r_c2_x : one c2_x }
{ some this.@r_c2_x }

lone sig c2_x
{ r_c3_y : one c3_y }
{ one r_c2_x }

lone sig c3_y
{}
{ one r_c3_y }

lone sig c6_Z
{ r_c7_z : one c7_z }
{ (this.(@r_c7_z.@ref)) > 0 }

lone sig c7_z
{ ref : one Int
, r_c8_y : one c8_y }
{ one r_c7_z }

lone sig c8_y
{}
{ one r_c8_y }

