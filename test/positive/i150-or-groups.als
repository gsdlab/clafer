/*
All clafers: 3 | Abstract: 0 | Concrete: 3 | References: 0
Constraints: 0
Goals: 0
Global scope: 1..1
All names unique: True
*/
open util/integer
pred show {}
run  show for 1 but 1 c1_A, 1 c2_B, 1 c3_C

one sig c1_A
{ r_c2_B : one c2_B
, r_c3_C : one c3_C }
{ let children = (r_c2_B + r_c3_C) | some children }

one sig c2_B
{}

one sig c3_C
{}

