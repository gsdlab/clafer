open util/integer
pred show {}


fact { #c1_Person = 0 }
abstract sig c1_Person
{ r_c2_age : one c2_age
, r_c3_married : lone c3_married }
{ all disj x, y : this.@r_c2_age | (x.@ref) != (y.@ref) }

sig c2_age
{ ref : one Int }
{ one @r_c2_age.this }

sig c3_married
{}
{ one @r_c3_married.this }

fact { #c4_NewBorn = 0 }
abstract sig c4_NewBorn
{ ref : one c1_Person }
{ ((c1_Person.(@r_c2_age.@ref)) = 0) && (no c1_Person.@r_c3_married) }

fact { all disj x, y : c4_NewBorn | (x.@ref) != (y.@ref) }
