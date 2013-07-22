open util/integer
pred show {}


lone sig c1_z
{ r_c2_y : one c2_y }
{ (this.(@r_c2_y.@ref)) = (-1.mul[1]) }

lone sig c2_y
{ ref : one Int }
{ one r_c2_y }

