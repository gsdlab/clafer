open util/integer
pred show {}


abstract sig c1_A
{ r_c2_s : lone c2_s }

sig c2_s
{ ref : one Int }
{ one @r_c2_s.this }

one sig c3_A1 extends c1_A
{}
{ (this.(@r_c2_s.@ref)) = 0 }

