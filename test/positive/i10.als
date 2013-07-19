open util/integer
pred show {}


lone sig c1_A
{ r_c2_x : one c2_x }

lone sig c2_x
{ ref : one Int }
{ one r_c2_x
  (this.@ref) >= 0 }

