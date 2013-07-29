open util/integer
pred show {}


one sig c1_claferA
{ r_c2_claferB : one c2_claferB }

one sig c2_claferB
{ r_c3_claferC : one c3_claferC }
{ some this.~@r_c2_claferB }

one sig c3_claferC
{}
{ some this.~@r_c3_claferC
  some (this.~@r_c3_claferC).@r_c3_claferC }

