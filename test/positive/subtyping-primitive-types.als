open util/integer
pred show {}


abstract sig c1_percent
{ ref : one Int }
{ ((this.@ref) >= 0) && ((this.@ref) <= 5) }

one sig c2_twoPercent extends c1_percent
{}

fact { (c2_twoPercent.@ref) = 2 }
one sig c3_threePercent extends c1_percent
{}

fact { (c3_threePercent.@ref) = ((c2_twoPercent.@ref).add[1]) }
abstract sig c4_date
{ ref : one Int }

one sig c5_today extends c4_date
{}

fact { (c5_today.@ref) = 0 }
abstract sig c6_time
{ ref : one Int
, r_c7_minute : one c7_minute
, r_c8_hour : one c8_hour }

sig c7_minute
{ ref : one Int }
{ one @r_c7_minute.this
  ((this.@ref) >= 0) && ((this.@ref) <= 5) }

sig c8_hour
{ ref : one Int }
{ one @r_c8_hour.this
  ((this.@ref) >= 0) && ((this.@ref) <= 5) }

fact { (c6_time.@ref) = ((c6_time.(@r_c7_minute.@ref)).add[(c6_time.(@r_c8_hour.@ref))]) }
one sig c9_now extends c6_time
{}
{ (this.(@r_c7_minute.@ref)) = 3
  (this.(@r_c8_hour.@ref)) = 1 }

