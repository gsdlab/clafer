open util/integer
pred show {}


abstract sig c1_Person
{ r_c2_age : one c2_age
, r_c3_maritalStatus : one c3_maritalStatus
, r_c38_childs : set c38_childs
, r_c63_parents : set c63_parents }
{ all disj x, y : this.@r_c38_childs | (x.@ref) != (y.@ref)
  #r_c63_parents <= 2
  all disj x, y : this.@r_c63_parents | (x.@ref) != (y.@ref) }

sig c2_age
{ ref : one Int }
{ one @r_c2_age.this }

sig c3_maritalStatus
{ r_c4_neverMarried : lone c4_neverMarried
, r_c5_married : lone c5_married
, r_c28_divorced : lone c28_divorced }
{ one @r_c3_maritalStatus.this
  let children = (r_c4_neverMarried + r_c5_married + r_c28_divorced) | one children
  ((some this.@r_c5_married) || (some this.@r_c28_divorced)) => (((this.~@r_c3_maritalStatus).(@r_c2_age.@ref)) >= 3) }

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

sig c28_divorced
{}
{ one @r_c28_divorced.this }

sig c38_childs
{ ref : one c1_Person }
{ one @r_c38_childs.this
  (this.~@r_c38_childs) in (this.(@ref.(@r_c63_parents.@ref)))
  ((((this.~@r_c38_childs).@r_c3_maritalStatus).@r_c5_married).(@r_c6_spouse.@ref)) in (this.(@ref.(@r_c63_parents.@ref)))
  (this.(@ref.(@r_c2_age.@ref))) < ((this.~@r_c38_childs).(@r_c2_age.@ref)) }

sig c63_parents
{ ref : one c1_Person }
{ one @r_c63_parents.this
  (this.~@r_c63_parents) in (this.(@ref.(@r_c38_childs.@ref))) }

lone sig c78_Alice extends c1_Person
{}
{ (this.(@r_c2_age.@ref)) = 4
  some (this.@r_c3_maritalStatus).@r_c5_married }

lone sig c84_Bob extends c1_Person
{}
{ (this.(@r_c2_age.@ref)) = 5 }

lone sig c88_Carol extends c1_Person
{}
{ (this.(@r_c2_age.@ref)) = 1 }

