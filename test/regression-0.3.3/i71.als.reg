open util/integer
pred show {}


abstract sig c1_Course
{ r_c2_taughtBy : set c2_taughtBy }
{ all disj x, y : this.@r_c2_taughtBy | (x.@ref) != (y.@ref) }

sig c2_taughtBy
{ ref : one c13_Teacher
, r_c3_x : lone c3_x }
{ one @r_c2_taughtBy.this }

sig c3_x
{}
{ one @r_c3_x.this }

abstract sig c13_Teacher
{ r_c14_teaches : set c14_teaches }
{ all disj x, y : this.@r_c14_teaches | (x.@ref) != (y.@ref) }

sig c14_teaches
{ ref : one c1_Course }
{ one @r_c14_teaches.this }

fact { all  c : c1_Course | all  t : c.@r_c2_taughtBy | (some t.@r_c3_x) && (c in (t.(@ref.(@r_c14_teaches.@ref)))) }
fact { 5 <= #c40_course and #c40_course <= 5 }
sig c40_course extends c1_Course
{}

fact { 3 <= #c41_teacher and #c41_teacher <= 3 }
sig c41_teacher extends c13_Teacher
{}

