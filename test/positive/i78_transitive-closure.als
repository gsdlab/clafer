open util/integer
pred show {}


abstract sig c1_TimeLevel
{ r_c2_aggregatesTo : lone c2_aggregatesTo }
{ all disj x, y : this.@r_c2_aggregatesTo | (x.@ref) != (y.@ref) }

sig c2_aggregatesTo
{ ref : one c1_TimeLevel }
{ one @r_c2_aggregatesTo.this }

abstract sig c3_YearLevel extends c1_TimeLevel
{}
{ no this.@r_c2_aggregatesTo }

abstract sig c4_MonthLevel extends c1_TimeLevel
{}
{ (this.(@r_c2_aggregatesTo.@ref)) in c3_YearLevel }

abstract sig c5_WeekLevel extends c1_TimeLevel
{}
{ (this.(@r_c2_aggregatesTo.@ref)) in c4_MonthLevel }

one sig c6_Year2012 extends c3_YearLevel
{}

one sig c7_Jan2012 extends c4_MonthLevel
{}
{ (this.(@r_c2_aggregatesTo.@ref)) = c6_Year2012 }

one sig c8_Week1 extends c5_WeekLevel
{}
{ (this.(@r_c2_aggregatesTo.@ref)) = c7_Jan2012 }

sig c9_Week1AggregatesTo
{ ref : one c1_TimeLevel }

fact { all disj x, y : c9_Week1AggregatesTo | (x.@ref) != (y.@ref) }
fact { (c8_Week1.(@r_c2_aggregatesTo.@ref)) in (c9_Week1AggregatesTo.@ref) }
fact { ((c8_Week1.@r_c2_aggregatesTo).(@ref.(@r_c2_aggregatesTo.@ref))) in (c9_Week1AggregatesTo.@ref) }
fact { (c9_Week1AggregatesTo.@ref) = (c7_Jan2012 + c6_Year2012) }
