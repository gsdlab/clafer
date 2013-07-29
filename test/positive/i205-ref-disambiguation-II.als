open util/integer
pred show {}


fact { all disj c1, c2 : c1_Car | ((c1.@r_c2_owner).@ref) != ((c2.@r_c2_owner).@ref) }
fact { 4 <= #c1_Car and #c1_Car <= 4 }
sig c1_Car
{ r_c2_owner : one c2_owner }
{ all disj x, y : this.@r_c2_owner | (x.@ref) != (y.@ref) }

sig c2_owner
{ ref : one c3_Person }
{ one @r_c2_owner.this }

fact { 4 <= #c3_Person and #c3_Person <= 4 }
sig c3_Person
{}

