open util/integer
pred show {}


abstract sig c1_percent
{ ref : one Int }
{ ((this.@ref) >= 0) && ((this.@ref) <= 5) }

lone sig c9_twoPercent extends c1_percent
{}

fact { (c9_twoPercent.@ref) = 2 }
lone sig c13_threePercent extends c1_percent
{}

fact { (c13_threePercent.@ref) = ((c9_twoPercent.@ref).add[1]) }
abstract sig c19_date
{ ref : one Int }

lone sig c20_today extends c19_date
{}

fact { (c20_today.@ref) = 0 }
abstract sig c24_time
{ ref : one Int
, r_c25_minute : one c25_minute
, r_c33_hour : one c33_hour }

sig c25_minute
{ ref : one Int }
{ one @r_c25_minute.this
  ((this.@ref) >= 0) && ((this.@ref) <= 5) }

sig c33_hour
{ ref : one Int }
{ one @r_c33_hour.this
  ((this.@ref) >= 0) && ((this.@ref) <= 5) }

fact { (c24_time.@ref) = ((c24_time.(@r_c25_minute.@ref)).add[(c24_time.(@r_c33_hour.@ref))]) }
lone sig c46_now extends c24_time
{}
{ (this.(@r_c25_minute.@ref)) = 3
  (this.(@r_c33_hour.@ref)) = 1 }

