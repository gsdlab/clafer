open util/integer
pred show {}


abstract sig c1_Person
{}

one sig c2_JohnDoe extends c1_Person
{}

one sig c3_MaryJane extends c1_Person
{}

abstract sig c4_WaitingLine
{ r_c5_participants : set c5_participants }
{ all disj x, y : this.@r_c5_participants | (x.@ref) != (y.@ref) }

sig c5_participants
{ ref : one c1_Person }
{ one @r_c5_participants.this }

one sig c6_BusLine extends c4_WaitingLine
{}
{ (c2_JohnDoe in (this.(@r_c5_participants.@ref))) && (c3_MaryJane in (this.(@r_c5_participants.@ref))) }

one sig c7_JohnAndMaryLine extends c4_WaitingLine
{}
{ (this.(@r_c5_participants.@ref)) = (c2_JohnDoe + c3_MaryJane) }

