open util/integer
pred show {}


abstract sig c1_Animal
{ r_c2_leg : set c2_leg }

sig c2_leg
{}
{ one @r_c2_leg.this }

abstract sig c3_Owner
{ r_c4_Pet : one c4_Pet }

sig c4_Pet extends c1_Animal
{}
{ one @r_c4_Pet.this }

some sig c5_SnakeOwner extends c3_Owner
{}
{ no (this.@r_c4_Pet).@r_c2_leg }

some sig c10_DogOwner extends c3_Owner
{}
{ (#((this.@r_c4_Pet).@r_c2_leg)) = 4 }

