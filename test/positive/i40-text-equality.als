open util/integer
pred show {}


lone sig c1_text
{ ref : one Int }

fact { (c1_text.@ref) = 0 }
lone sig c5_text1
{ ref : one Int }

fact { (c5_text1.@ref) = 0 }
lone sig c9_text2
{ ref : one Int }

fact { (c9_text2.@ref) = 0 }
lone sig c13_equal1
{}
{ (c1_text.@ref) = (c5_text1.@ref) }

lone sig c17_equal2
{}
{ (c5_text1.@ref) = (c9_text2.@ref) }

fact { some c13_equal1 }
fact { some c17_equal2 }
