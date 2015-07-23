/*
All clafers: 15 | Abstract: 2 | Concrete: 13 | Reference: 9
Constraints: 6
Goals: 0
Global scope: 2..*
Can skip name resolver: no
*/
open util/integer
pred show {}


one sig c0_numberOne
{ c0_numberOne_ref : one 1 }

one sig c0_alice
{ c0_alice_ref : one 0 }

one sig c0_likertScaleVal
{ c0_likertScaleVal_ref : one (((1 + 2) + 3) + 4) + 5 }

one sig c0_nonZero
{ c0_nonZero_ref : one Int - 0 }

abstract sig c0_Person
{ r_c0_Head : set c0_Head
, r_c0_likes : lone c0_likes }

abstract sig c0_Head
{}
{ one @r_c0_Head.this }

sig c0_likes
{ c0_likes_ref : one c0_Person }
{ one @r_c0_likes.this }

one sig c0_Alice extends c0_Person
{ r_c1_Head : one c1_Head }
{ r_c1_Head in r_c0_Head
  (this.(@r_c0_likes.@c0_likes_ref)) = c0_Ella }

one sig c1_Head extends c0_Head
{}

one sig c0_Ella extends c0_Person
{ r_c0_h : one c0_h }
{ no this.@r_c0_likes }

one sig c0_h
{}

sig c0_heads
{ c0_heads_ref : one c0_Head }

fact {  all disj x, y : c0_heads | (x.@c0_heads_ref) != (y.@c0_heads_ref)  }
fact { 2 <= #c0_friend and #c0_friend <= 2 }
sig c0_friend
{ c0_friend_ref : one c0_Alice + c0_Ella }

fact {  all disj x, y : c0_friend | (x.@c0_friend_ref) != (y.@c0_friend_ref)  }
one sig c0_onlyAlice
{ c0_onlyAlice_ref : one c0_Alice & c0_Person }

assert assertOnLine_37 { c0_Alice in (c0_onlyAlice.@c0_onlyAlice_ref) }
check assertOnLine_37 for 1 but 2 c0_Person, 2 c0_friend, 2 c0_likes

assert assertOnLine_38 { c0_Ella not in (c0_onlyAlice.@c0_onlyAlice_ref) }
check assertOnLine_38 for 1 but 2 c0_Person, 2 c0_friend, 2 c0_likes

one sig c0_exceptElla
{ c0_exceptElla_ref : one c0_Person - c0_Ella }

assert assertOnLine_43 { c0_Alice in (c0_exceptElla.@c0_exceptElla_ref) }
check assertOnLine_43 for 1 but 2 c0_Person, 2 c0_friend, 2 c0_likes

assert assertOnLine_44 { c0_Ella not in (c0_exceptElla.@c0_exceptElla_ref) }
check assertOnLine_44 for 1 but 2 c0_Person, 2 c0_friend, 2 c0_likes

