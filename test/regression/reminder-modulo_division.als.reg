open util/integer
pred show {}


one sig c0_a
{ ref : one Int }

fact { (some c0_a) => ((c0_a.@ref) = (6.rem[4])) }
assert assertOnLine_2 { (c0_a.@ref) = 2 }
check assertOnLine_2 for 1

one sig c0_b
{ ref : one Int }

fact { (some c0_b) => ((c0_b.@ref) = (0.rem[4])) }
assert assertOnLine_5 { (c0_b.@ref) = 0 }
check assertOnLine_5 for 1

one sig c0_c
{ ref : one Int }

fact { (some c0_c) => ((c0_c.@ref) = (4.rem[2])) }
assert assertOnLine_8 { (c0_c.@ref) = 0 }
check assertOnLine_8 for 1

