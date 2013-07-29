open util/integer
pred show {}


one sig c1_text
{ ref : one Int }

fact { (c1_text.@ref) = 0 }
one sig c2_text1
{ ref : one Int }

fact { (c2_text1.@ref) = 0 }
one sig c3_text2
{ ref : one Int }

fact { (c3_text2.@ref) = 0 }
lone sig c4_equal1
{}
{ (c1_text.@ref) = (c2_text1.@ref) }

lone sig c5_equal2
{}
{ (c2_text1.@ref) = (c3_text2.@ref) }

fact { some c4_equal1 }
fact { some c5_equal2 }
