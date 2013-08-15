open util/integer
pred show {}


fact { all disj c1, c2 : c14_Car | ((c1.@r_c15_owner).@ref) != ((c2.@r_c15_owner).@ref) }
fact { 4 <= #c14_Car and #c14_Car <= 4 }
sig c14_Car
{ r_c15_owner : one c15_owner }
{ all disj x, y : this.@r_c15_owner | (x.@ref) != (y.@ref) }

sig c15_owner
{ ref : one c25_Person }
{ one @r_c15_owner.this }

fact { 4 <= #c25_Person and #c25_Person <= 4 }
sig c25_Person
{}

