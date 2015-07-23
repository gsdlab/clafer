open util/integer
pred show {}


one sig c0_Person
{ r_c0_maritalStatus : one c0_maritalStatus }

one sig c0_maritalStatus
{ r_c0_married : one c0_married }

one sig c0_married
{}
{ some (this.~@r_c0_married).~@r_c0_maritalStatus }

