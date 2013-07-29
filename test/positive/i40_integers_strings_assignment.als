open util/integer
pred show {}


abstract sig c1_Entity
{ r_c2_type : one c2_type }

sig c2_type
{ ref : one Int }
{ one @r_c2_type.this }

one sig c3_E1 extends c1_Entity
{}
{ (this.(@r_c2_type.@ref)) = 0 }

one sig c4_E2 extends c1_Entity
{}
{ (this.(@r_c2_type.@ref)) = 0 }

one sig c5_E3 extends c1_Entity
{}
{ (this.(@r_c2_type.@ref)) = 0 }

sig c6_E1TEntities
{ ref : one c1_Entity }
{ (c1_Entity.(@r_c2_type.@ref)) = 0 }

fact { all disj x, y : c6_E1TEntities | (x.@ref) != (y.@ref) }
fact { (#c6_E1TEntities) = 3 }
