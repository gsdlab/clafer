open util/integer
pred show {}


lone sig c1_A
{ r_c2_i : one c2_i }
{ (this.(@r_c2_i.@ref)) = 1
  (this.(@r_c2_i.@ref)) = 1 }

lone sig c2_i
{ ref : one Int }
{ one r_c2_i
  (this.@ref) = 1 }

