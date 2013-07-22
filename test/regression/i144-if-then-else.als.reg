open util/integer
pred show {}


lone sig c1_AliceAge
{ ref : one Int }

fact { all disj x, y : c1_AliceAge | (x.@ref) != (y.@ref) }
lone sig c11_BobAge
{ ref : one Int }

fact { all disj x, y : c11_BobAge | (x.@ref) != (y.@ref) }
lone sig c21_BobsBirthday
{}

fact { ((some c21_BobsBirthday) => (c11_BobAge.@ref) else (c1_AliceAge.@ref)) = 5 }
