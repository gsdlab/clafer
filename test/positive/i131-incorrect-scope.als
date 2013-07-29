open util/integer
pred show {}


abstract sig c1_Animal
{ r_c2_leg : set c2_leg }

sig c2_leg
{}
{ one @r_c2_leg.this }

sig c3_Dog extends c1_Animal
{}
{ (#(this.@r_c2_leg)) = 4 }

sig c4_Spider extends c1_Animal
{}
{ (#(this.@r_c2_leg)) = 8 }

