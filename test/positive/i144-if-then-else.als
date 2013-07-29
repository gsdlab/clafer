open util/integer
pred show {}


one sig c1_AliceAge
{ ref : one Int }

fact { all disj x, y : c1_AliceAge | (x.@ref) != (y.@ref) }
one sig c2_BobAge
{ ref : one Int }

fact { all disj x, y : c2_BobAge | (x.@ref) != (y.@ref) }
lone sig c3_BobsBirthday
{}

fact { ((some c3_BobsBirthday) => (c2_BobAge.@ref) else (c1_AliceAge.@ref)) = 5 }
