open util/integer
pred show {}


lone sig c1_claferA
{ r_c2_claferB : one c2_claferB }

lone sig c2_claferB
{ r_c5_claferC : one c5_claferC }
{ one r_c2_claferB
  some this.~@r_c2_claferB }

lone sig c5_claferC
{}
{ one r_c5_claferC
  some this.~@r_c5_claferC
  some (this.~@r_c5_claferC).@r_c5_claferC }

