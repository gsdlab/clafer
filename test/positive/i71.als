open util/integer
pred show {}


abstract sig c1_Course
{ r_c2_taughtBy : set c2_taughtBy }
{ all disj x, y : this.@r_c2_taughtBy | (x.@ref) != (y.@ref) }

sig c2_taughtBy
{ ref : one c4_Teacher
, r_c3_x : lone c3_x }
{ one @r_c2_taughtBy.this }

sig c3_x
{}
{ one @r_c3_x.this }

abstract sig c4_Teacher
{ r_c5_teaches : set c5_teaches }
{ all disj x, y : this.@r_c5_teaches | (x.@ref) != (y.@ref) }

sig c5_teaches
{ ref : one c1_Course }
{ one @r_c5_teaches.this }

fact { all  c : c1_Course | all  t : c.@r_c2_taughtBy | (some t.@r_c3_x) && (c in (t.(@ref.(@r_c5_teaches.@ref)))) }
fact { 5 <= #c6_course and #c6_course <= 5 }
sig c6_course extends c1_Course
{}

fact { 3 <= #c7_teacher and #c7_teacher <= 3 }
sig c7_teacher extends c4_Teacher
{}

