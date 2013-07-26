open util/integer
pred show {}


one sig c1_A
{ r_c2_x : lone c2_x
, r_c3_y : lone c3_y }
{ ((some this.@r_c2_x) => (no this.@r_c3_y)) && ((some this.@r_c3_y) => (no this.@r_c2_x)) }

lone sig c2_x
{}
{ one r_c2_x }

lone sig c3_y
{}
{ one r_c3_y }

