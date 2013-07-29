open util/integer
pred show {}


abstract sig c1_Person
{ r_c2_Age : one c2_Age }

sig c2_Age
{ ref : one Int }
{ one @r_c2_Age.this }

one sig c3_Team
{ r_c4_Contractor : one c4_Contractor
, r_c6_Member : set c6_Member }
{ 2 <= #r_c6_Member
  all disj x, y : this.@r_c6_Member | (x.@ref) != (y.@ref) }

one sig c4_Contractor extends c1_Person
{ r_c5_since : one c5_since }
{ all disj x, y : this.@r_c5_since | (x.@ref) != (y.@ref) }

one sig c5_since
{ ref : one Int }

sig c6_Member
{ ref : one c1_Person }
{ one @r_c6_Member.this }

one sig c7_Alice extends c1_Person
{}

one sig c8_Bob extends c1_Person
{}

