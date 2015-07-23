open util/integer
pred show {}


one sig c0_claferA
{ r_c0_claferB : one c0_claferB }

one sig c0_claferB
{ r_c0_claferC : one c0_claferC }
{ some this.~@r_c0_claferB }

one sig c0_claferC
{}
{ some this.~@r_c0_claferC
  some (this.~@r_c0_claferC).@r_c0_claferC }

