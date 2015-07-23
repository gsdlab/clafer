open util/integer
pred show {}


one sig c0_D
{ r_c0_b : lone c0_b
, r_c0_c : lone c0_c }
{ (this.(@r_c0_c.@ref)) = 5
  (this.(@r_c0_c.@ref)) = 5
  some this.@r_c0_b }

lone sig c0_b
{}
{ one r_c0_b }

lone sig c0_c
{ ref : one Int }
{ one r_c0_c }

