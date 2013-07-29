open util/integer
pred show {}


abstract sig c1_Component
{ r_c2_energy : one c2_energy }

sig c2_energy
{ ref : one Int }
{ one @r_c2_energy.this }

one sig c3_c1 extends c1_Component
{}
{ (this.(@r_c2_energy.@ref)) = 1 }

one sig c4_c2 extends c1_Component
{}
{ (this.(@r_c2_energy.@ref)) = 1 }

one sig c5_c3 extends c1_Component
{}
{ (this.(@r_c2_energy.@ref)) = 1 }

one sig c6_total
{ ref : one Int }

fact { (c6_total.@ref) = (sum temp : (c1_Component.@r_c2_energy) | temp.@ref) }
