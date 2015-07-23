open util/integer
pred show {}


abstract sig c0_Course
{ r_c0_taughtBy : set c0_taughtBy }
{ all disj x, y : this.@r_c0_taughtBy | (x.@ref) != (y.@ref)  }

sig c0_taughtBy
{ ref : one c0_Teacher
, r_c0_x : lone c0_x }
{ one @r_c0_taughtBy.this }

sig c0_x
{}
{ one @r_c0_x.this }

abstract sig c0_Teacher
{ r_c0_teaches : set c0_teaches }
{ all disj x, y : this.@r_c0_teaches | (x.@ref) != (y.@ref)  }

sig c0_teaches
{ ref : one c0_Course }
{ one @r_c0_teaches.this }

fact { all  c : c0_Course | all  t : c.@r_c0_taughtBy | (some t.@r_c0_x) && (c in (t.(@ref.(@r_c0_teaches.@ref)))) }
fact { 5 <= #c0_course and #c0_course <= 5 }
sig c0_course extends c0_Course
{}

fact { 3 <= #c0_teacher and #c0_teacher <= 3 }
sig c0_teacher extends c0_Teacher
{}

