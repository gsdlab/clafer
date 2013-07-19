open util/integer
pred show {}


lone sig c1_Person
{ r_c2_maritalStatus : one c2_maritalStatus }

lone sig c2_maritalStatus
{ r_c3_married : one c3_married }
{ one r_c2_maritalStatus }

lone sig c3_married
{}
{ one r_c3_married
  some (this.~@r_c3_married).~@r_c2_maritalStatus }

