open util/integer
pred show {}


abstract sig c1_Person
{ r_c2_Age : one c2_Age }

sig c2_Age
{ ref : one Int }
{ one @r_c2_Age.this }

lone sig c3_Team
{ r_c4_Contractor : one c4_Contractor
, r_c15_Member : set c15_Member }
{ 2 <= #r_c15_Member
  all disj x, y : this.@r_c15_Member | (x.@ref) != (y.@ref) }

lone sig c4_Contractor extends c1_Person
{ r_c5_since : one c5_since }
{ one r_c4_Contractor
  all disj x, y : this.@r_c5_since | (x.@ref) != (y.@ref) }

lone sig c5_since
{ ref : one Int }
{ one r_c5_since }

sig c15_Member
{ ref : one c1_Person }
{ one @r_c15_Member.this }

lone sig c25_Alice extends c1_Person
{}

lone sig c26_Bob extends c1_Person
{}

