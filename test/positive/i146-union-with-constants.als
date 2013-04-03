/*
All clafers: 3 | Abstract: 0 | Concrete: 3 | References: 0
Constraints: 1
Goals: 0
Global scope: 1..*
All names unique: True
*/
open util/integer
pred show {}
run  show for 1

sig c1_AlicePicks
{ ref : one Int }

sig c2_BobPicks
{ ref : one Int }

sig c3_CarolPicks
{ ref : one Int }
{ (this.@ref) = (c1_AlicePicks + (c2_BobPicks.@ref)) }

