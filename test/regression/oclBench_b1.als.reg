open util/integer
pred show {}


abstract sig c0_Person
{ r_c0_name : one c0_name
, r_c0_civstat : one c0_civstat
, r_c0_gender : one c0_gender
, r_c0_alive : lone c0_alive
, r_c0_husband : lone c0_husband
, r_c0_wife : lone c0_wife }
{ ((((this.(@r_c0_civstat.@ref)) = 0) || ((this.(@r_c0_civstat.@ref)) = 1)) || ((this.(@r_c0_civstat.@ref)) = 2)) || ((this.(@r_c0_civstat.@ref)) = 3)
  ((this.(@r_c0_gender.@ref)) = 4) || ((this.(@r_c0_gender.@ref)) = 5)
  all  p : c0_Person | (this != p) => (((this.@r_c0_name).@ref) != ((p.@r_c0_name).@ref))
  one  p : c0_Person | ((p.@r_c0_name).@ref) = ((this.@r_c0_name).@ref) }

sig c0_name
{ ref : one Int }
{ one @r_c0_name.this }

sig c0_civstat
{ ref : one Int }
{ one @r_c0_civstat.this }

sig c0_gender
{ ref : one Int }
{ one @r_c0_gender.this }

sig c0_alive
{}
{ one @r_c0_alive.this }

sig c0_husband
{ ref : one c0_Person }
{ one @r_c0_husband.this
  (this.~@r_c0_husband) in (this.(@ref.(@r_c0_wife.@ref))) }

sig c0_wife
{ ref : one c0_Person }
{ one @r_c0_wife.this
  (this.~@r_c0_wife) in (this.(@ref.(@r_c0_husband.@ref))) }

one sig c0_ada extends c0_Person
{}
{ ((((((this.(@r_c0_name.@ref)) = 6) && ((this.(@r_c0_civstat.@ref)) = 3)) && ((this.(@r_c0_gender.@ref)) = 4)) && (some this.@r_c0_alive)) && (no this.@r_c0_husband)) && (no this.@r_c0_wife) }

one sig c0_cyd extends c0_Person
{}
{ ((((((this.(@r_c0_name.@ref)) = 7) && ((this.(@r_c0_civstat.@ref)) = 1)) && ((this.(@r_c0_gender.@ref)) = 5)) && (no this.@r_c0_alive)) && (no this.@r_c0_husband)) && (no this.@r_c0_wife) }

one sig c0_eve extends c0_Person
{}
{ ((((((this.(@r_c0_name.@ref)) = 8) && ((this.(@r_c0_civstat.@ref)) = 1)) && ((this.(@r_c0_gender.@ref)) = 4)) && (some this.@r_c0_alive)) && ((this.(@r_c0_husband.@ref)) = c0_dan)) && (no this.@r_c0_wife) }

one sig c0_bob extends c0_Person
{}
{ ((((((this.(@r_c0_name.@ref)) = 9) && ((this.(@r_c0_civstat.@ref)) = 2)) && ((this.(@r_c0_gender.@ref)) = 5)) && (some this.@r_c0_alive)) && (no this.@r_c0_husband)) && (no this.@r_c0_wife) }

one sig c0_dan extends c0_Person
{}
{ ((((((this.(@r_c0_name.@ref)) = 10) && ((this.(@r_c0_civstat.@ref)) = 1)) && ((this.(@r_c0_gender.@ref)) = 5)) && (some this.@r_c0_alive)) && (no this.@r_c0_husband)) && ((this.(@r_c0_wife.@ref)) = c0_eve) }

fact { (c0_adaBobCyd.(@ref.(@r_c0_name.@ref))) = (c0_stringSet1.@ref) }
fact { (c0_personWithUndefinedHusband1.(@ref.(@r_c0_name.@ref))) = (c0_stringSet2.@ref) }
fact { (c0_personWithUndefinedHusband2.(@ref.(@r_c0_name.@ref))) = (c0_stringSet2.@ref) }
fact { (((c0_possiblePairs.(@ref.@r_c0_first)).(@ref.(@r_c0_name.@ref))) = 6) && (((c0_possiblePairs.(@ref.@r_c0_second)).(@ref.(@r_c0_name.@ref))) = 9) }
sig c0_adaBobCyd
{ ref : one c0_Person }
{ (this.(@ref.(@r_c0_name.@ref))) in (c0_stringSet1.@ref) }

fact {  all disj x, y : c0_adaBobCyd | (x.@ref) != (y.@ref)  }
fact { all  p : c0_Person | ((p.(@r_c0_name.@ref)) in (c0_stringSet1.@ref)) => (p in (c0_adaBobCyd.@ref)) }
sig c0_personWithUndefinedHusband1
{ ref : one c0_Person }
{ (this.(@ref.(@r_c0_husband.@ref))) = (c0_emptyPersonSet1.@ref) }

fact {  all disj x, y : c0_personWithUndefinedHusband1 | (x.@ref) != (y.@ref)  }
fact { all  p : c0_Person | ((p.(@r_c0_husband.@ref)) = (c0_emptyPersonSet1.@ref)) => (p in (c0_personWithUndefinedHusband1.@ref)) }
sig c0_personWithUndefinedHusband2
{ ref : one c0_Person }
{ (this.(@ref.(@r_c0_husband.@ref))) = (c0_emptyPersonSet2.@ref) }

fact {  all disj x, y : c0_personWithUndefinedHusband2 | (x.@ref) != (y.@ref)  }
fact { all  p : c0_Person | ((p.(@r_c0_husband.@ref)) = (c0_emptyPersonSet2.@ref)) => (p in (c0_personWithUndefinedHusband2.@ref)) }
sig c0_personWithNoWife
{ ref : one c0_Person }
{ no this.(@ref.@r_c0_wife) }

fact {  all disj x, y : c0_personWithNoWife | (x.@ref) != (y.@ref)  }
fact { all  p : c0_Person | (no p.@r_c0_wife) => (p in (c0_personWithNoWife.@ref)) }
sig c0_emptyPersonSet1
{ ref : one c0_Person }

fact {  all disj x, y : c0_emptyPersonSet1 | (x.@ref) != (y.@ref)  }
fact { (c0_emptyPersonSet1.@ref) = (c0_personWithNoWife.(@ref.(@r_c0_wife.@ref))) }
sig c0_emptyPersonSet2
{ ref : one c0_Person }
{ 1 > 2 }

fact {  all disj x, y : c0_emptyPersonSet2 | (x.@ref) != (y.@ref)  }
sig c0_personPair
{ r_c0_first : one c0_first
, r_c0_second : one c0_second }

sig c0_first
{ ref : one c0_Person }
{ one @r_c0_first.this }

sig c0_second
{ ref : one c0_Person }
{ one @r_c0_second.this }

sig c0_possiblePairs
{ ref : one c0_personPair }
{ (((((this.(@ref.@r_c0_first)).(@ref.(@r_c0_gender.@ref))) = 4) && (some (this.(@ref.@r_c0_first)).(@ref.@r_c0_alive))) && (((this.(@ref.@r_c0_first)).(@ref.(@r_c0_civstat.@ref))) != 1)) && (((((this.(@ref.@r_c0_second)).(@ref.(@r_c0_gender.@ref))) = 5) && (some (this.(@ref.@r_c0_second)).(@ref.@r_c0_alive))) && (((this.(@ref.@r_c0_second)).(@ref.(@r_c0_civstat.@ref))) != 1)) }

fact {  all disj x, y : c0_possiblePairs | (x.@ref) != (y.@ref)  }
fact { all  p, q : c0_Person | (((((((p.(@r_c0_gender.@ref)) = 4) && (some p.@r_c0_alive)) && ((p.(@r_c0_civstat.@ref)) != 1)) && ((q.(@r_c0_gender.@ref)) = 5)) && (some q.@r_c0_alive)) && ((q.(@r_c0_civstat.@ref)) != 1)) => (one  pair : c0_personPair | (((pair.(@r_c0_first.@ref)) = p) && ((pair.(@r_c0_second.@ref)) = q)) && (pair in (c0_possiblePairs.@ref))) }
fact { 3 <= #c0_stringSet1 and #c0_stringSet1 <= 3 }
sig c0_stringSet1
{ ref : one Int }
{ (((this.@ref) = 6) || ((this.@ref) = 9)) || ((this.@ref) = 7) }

fact {  all disj x, y : c0_stringSet1 | (x.@ref) != (y.@ref)  }
fact { 4 <= #c0_stringSet2 and #c0_stringSet2 <= 4 }
sig c0_stringSet2
{ ref : one Int }
{ ((((this.@ref) = 6) || ((this.@ref) = 9)) || ((this.@ref) = 7)) || ((this.@ref) = 10) }

fact {  all disj x, y : c0_stringSet2 | (x.@ref) != (y.@ref)  }
