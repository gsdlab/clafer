open util/integer
pred show {}


abstract sig c1_date
{ ref : one Int }

abstract sig c2_Person
{ r_c3_Name : one c3_Name
, r_c4_DateOfBirth : one c4_DateOfBirth }

sig c3_Name
{ ref : one Int }
{ one @r_c3_Name.this }

sig c4_DateOfBirth extends c1_date
{}
{ one @r_c4_DateOfBirth.this }

lone sig c5_JohnDoe extends c2_Person
{}
{ ((this.(@r_c3_Name.@ref)) = 0) && ((this.(@r_c4_DateOfBirth.@ref)) = 1) }

