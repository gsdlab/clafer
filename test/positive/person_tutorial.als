open util/integer
pred show {}


abstract sig c1_date
{ ref : one Int }

abstract sig c2_NorthAmericanCountry
{}

one sig c3_Canada extends c2_NorthAmericanCountry
{}

one sig c4_USA extends c2_NorthAmericanCountry
{}

abstract sig c5_Person
{ r_c6_Name : one c6_Name
, r_c7_Surname : one c7_Surname
, r_c8_DateOfBirth : one c8_DateOfBirth
, r_c9_Gender : one c9_Gender
, r_c12_MaritalStatus : one c12_MaritalStatus
, r_c16_Address : one c16_Address }

sig c6_Name
{ ref : one Int }
{ one @r_c6_Name.this }

sig c7_Surname
{ ref : one Int }
{ one @r_c7_Surname.this }

sig c8_DateOfBirth extends c1_date
{}
{ one @r_c8_DateOfBirth.this }

sig c9_Gender
{ r_c10_Male : lone c10_Male
, r_c11_Female : lone c11_Female }
{ one @r_c9_Gender.this
  let children = (r_c10_Male + r_c11_Female) | some children }

sig c10_Male
{}
{ one @r_c10_Male.this }

sig c11_Female
{}
{ one @r_c11_Female.this }

sig c12_MaritalStatus
{ r_c13_NeverMarried : lone c13_NeverMarried
, r_c14_Married : lone c14_Married
, r_c15_Divorced : lone c15_Divorced }
{ one @r_c12_MaritalStatus.this
  let children = (r_c13_NeverMarried + r_c14_Married + r_c15_Divorced) | one children }

sig c13_NeverMarried
{}
{ one @r_c13_NeverMarried.this }

sig c14_Married
{}
{ one @r_c14_Married.this }

sig c15_Divorced
{}
{ one @r_c15_Divorced.this }

sig c16_Address
{ r_c17_Street : one c17_Street
, r_c19_City : one c19_City
, r_c20_Country : one c20_Country
, r_c21_PostalCode : one c21_PostalCode }
{ one @r_c16_Address.this
  all disj x, y : this.@r_c20_Country | (x.@ref) != (y.@ref) }

sig c17_Street
{ ref : one Int
, r_c18_UnitNo : lone c18_UnitNo }
{ one @r_c17_Street.this }

sig c18_UnitNo
{ ref : one Int }
{ one @r_c18_UnitNo.this }

sig c19_City
{ ref : one Int }
{ one @r_c19_City.this }

sig c20_Country
{ ref : one c2_NorthAmericanCountry }
{ one @r_c20_Country.this }

sig c21_PostalCode
{ ref : one Int }
{ one @r_c21_PostalCode.this }

one sig c22_JohnDoe extends c5_Person
{}
{ (((((((((this.(@r_c6_Name.@ref)) = 0) && ((this.(@r_c7_Surname.@ref)) = 1)) && ((this.(@r_c8_DateOfBirth.@ref)) = 2)) && (some (this.@r_c9_Gender).@r_c10_Male)) && (some (this.@r_c12_MaritalStatus).@r_c14_Married)) && (((this.@r_c16_Address).(@r_c17_Street.@ref)) = 3)) && (((this.@r_c16_Address).(@r_c19_City.@ref)) = 4)) && (((this.@r_c16_Address).(@r_c20_Country.@ref)) = c3_Canada)) && (((this.@r_c16_Address).(@r_c21_PostalCode.@ref)) = 5) }

abstract sig c23_Student extends c5_Person
{ r_c24_StudentId : one c24_StudentId }

sig c24_StudentId
{ ref : one Int }
{ one @r_c24_StudentId.this }

abstract sig c25_WaitingLine
{ r_c26_participants : set c26_participants }
{ all disj x, y : this.@r_c26_participants | (x.@ref) != (y.@ref) }

sig c26_participants
{ ref : one c5_Person }
{ one @r_c26_participants.this }

one sig c27_MaryJane extends c23_Student
{}
{ (this.(@r_c24_StudentId.@ref)) = 6 }

one sig c28_BusLine extends c25_WaitingLine
{}
{ (c22_JohnDoe in (this.(@r_c26_participants.@ref))) && (c27_MaryJane in (this.(@r_c26_participants.@ref))) }

one sig c29_JohnAndMaryLine extends c25_WaitingLine
{}
{ (this.(@r_c26_participants.@ref)) = (c22_JohnDoe + c27_MaryJane) }

fact { #c30_TwoPersonLine = 0 }
abstract sig c30_TwoPersonLine extends c25_WaitingLine
{}
{ (#(this.@r_c26_participants)) = 2 }

fact { #c31_OneToTenPersonLine = 0 }
abstract sig c31_OneToTenPersonLine extends c25_WaitingLine
{}
{ ((#(this.@r_c26_participants)) >= 1) && ((#(this.@r_c26_participants)) <= 10) }

