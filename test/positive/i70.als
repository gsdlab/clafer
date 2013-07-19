open util/integer
pred show {}


lone sig c1_Clafer1
{ r_c2_type : one c2_type }

lone sig c2_type
{ r_c3_Type1 : lone c3_Type1
, r_c4_Type2 : lone c4_Type2 }
{ one r_c2_type
  let children = (r_c3_Type1 + r_c4_Type2) | one children }

lone sig c3_Type1
{}
{ one r_c3_Type1 }

lone sig c4_Type2
{}
{ one r_c4_Type2 }

lone sig c5_Clafer2
{ r_c6_clafer1 : one c6_clafer1
, r_c16_type : one c16_type }
{ all disj x, y : this.@r_c6_clafer1 | (x.@ref) != (y.@ref)
  (some (this.@r_c16_type).@r_c17_Type1) => (some ((this.@r_c6_clafer1).(@ref.@r_c2_type)).@r_c4_Type2)
  (some (this.@r_c16_type).@r_c17_Type1) => (some ((this.@r_c6_clafer1).(@ref.@r_c2_type)).@r_c4_Type2) }

lone sig c6_clafer1
{ ref : one c1_Clafer1 }
{ one r_c6_clafer1 }

lone sig c16_type
{ r_c17_Type1 : lone c17_Type1
, r_c18_Type2 : lone c18_Type2 }
{ one r_c16_type
  let children = (r_c17_Type1 + r_c18_Type2) | one children }

lone sig c17_Type1
{}
{ one r_c17_Type1 }

lone sig c18_Type2
{}
{ one r_c18_Type2 }

