open util/integer
pred show {}


lone sig c1_A
{ r_c2_x : one c2_x
, r_c3_y : one c3_y }
{ (this.(@r_c2_x.@ref)) = ((-1.mul[((6.add[(5-4)]).mul[3])]).div[(2.add[1])])
  (this.(@r_c3_y.@ref)) = (this.(@r_c2_x.@ref)) }

lone sig c2_x
{ ref : one Int }
{ one r_c2_x }

lone sig c3_y
{ ref : one Int }
{ one r_c3_y }

