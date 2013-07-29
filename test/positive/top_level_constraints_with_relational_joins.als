open util/integer
pred show {}


abstract sig c1_Course
{ r_c2_assistants : set c2_assistants }
{ all disj x, y : this.@r_c2_assistants | (x.@ref) != (y.@ref) }

sig c2_assistants
{ ref : one c3_TA }
{ one @r_c2_assistants.this }

abstract sig c3_TA
{ r_c4_first : lone c4_first }
{ all disj x, y : this.@r_c4_first | (x.@ref) != (y.@ref) }

sig c4_first
{ ref : one c1_Course }
{ one @r_c4_first.this
  (this.~@r_c4_first) in (this.(@ref.(@r_c2_assistants.@ref))) }

one sig c5_CompilerGradStudent extends c3_TA
{}

one sig c6_AIGradStudent extends c3_TA
{}

one sig c7_CompilerCourse extends c1_Course
{}

one sig c8_MachineLearningCourse extends c1_Course
{}

fact { (c5_CompilerGradStudent.(@r_c4_first.@ref)) = c7_CompilerCourse }
fact { (c6_AIGradStudent.(@r_c4_first.@ref)) = c8_MachineLearningCourse }
one sig c9_numerOfAssistants
{ ref : one Int }

fact { (c9_numerOfAssistants.@ref) = (#(c1_Course.@r_c2_assistants)) }
