open util/integer
pred show {}


abstract sig c1_Person
{ r_c2_age : one c2_age
, r_c3_maritalStatus : one c3_maritalStatus
, r_c8_childs : set c8_childs
, r_c9_parents : set c9_parents }
{ all disj x, y : this.@r_c8_childs | (x.@ref) != (y.@ref)
  #r_c9_parents <= 2
  all disj x, y : this.@r_c9_parents | (x.@ref) != (y.@ref) }

sig c2_age
{ ref : one Int }
{ one @r_c2_age.this }

sig c3_maritalStatus
{ r_c4_neverMarried : lone c4_neverMarried
, r_c5_married : lone c5_married
, r_c7_divorced : lone c7_divorced }
{ one @r_c3_maritalStatus.this
  let children = (r_c4_neverMarried + r_c5_married + r_c7_divorced) | one children
  ((some this.@r_c5_married) || (some this.@r_c7_divorced)) => (((this.~@r_c3_maritalStatus).(@r_c2_age.@ref)) >= 3) }

sig c4_neverMarried
{}
{ one @r_c4_neverMarried.this }

sig c5_married
{ r_c6_spouse : one c6_spouse }
{ one @r_c5_married.this
  all disj x, y : this.@r_c6_spouse | (x.@ref) != (y.@ref) }

sig c6_spouse
{ ref : one c1_Person }
{ one @r_c6_spouse.this
  (this.@ref) != (((this.~@r_c6_spouse).~@r_c5_married).~@r_c3_maritalStatus)
  (((this.(@ref.@r_c3_maritalStatus)).@r_c5_married).(@r_c6_spouse.@ref)) = (((this.~@r_c6_spouse).~@r_c5_married).~@r_c3_maritalStatus) }

sig c7_divorced
{}
{ one @r_c7_divorced.this }

sig c8_childs
{ ref : one c1_Person }
{ one @r_c8_childs.this
  (this.~@r_c8_childs) in (this.(@ref.(@r_c9_parents.@ref)))
  ((((this.~@r_c8_childs).@r_c3_maritalStatus).@r_c5_married).(@r_c6_spouse.@ref)) in (this.(@ref.(@r_c9_parents.@ref)))
  (this.(@ref.(@r_c2_age.@ref))) < ((this.~@r_c8_childs).(@r_c2_age.@ref)) }

sig c9_parents
{ ref : one c1_Person }
{ one @r_c9_parents.this
  (this.~@r_c9_parents) in (this.(@ref.(@r_c8_childs.@ref))) }

one sig c10_Alice extends c1_Person
{}
{ (this.(@r_c2_age.@ref)) = 4
  some (this.@r_c3_maritalStatus).@r_c5_married }

one sig c11_Bob extends c1_Person
{}
{ (this.(@r_c2_age.@ref)) = 5 }

one sig c12_Carol extends c1_Person
{}
{ (this.(@r_c2_age.@ref)) = 1 }

