open util/integer
pred show {}


abstract sig c1_Course
{ r_c2_assistants : set c2_assistants }
{ all disj x, y : this.@r_c2_assistants | (x.@ref) != (y.@ref) }

sig c2_assistants
{ ref : one c12_TA }
{ one @r_c2_assistants.this }

abstract sig c12_TA
{ r_c13_first : lone c13_first }
{ all disj x, y : this.@r_c13_first | (x.@ref) != (y.@ref) }

sig c13_first
{ ref : one c1_Course }
{ one @r_c13_first.this
  (this.~@r_c13_first) in (this.(@ref.(@r_c2_assistants.@ref))) }

lone sig c28_CompilerGradStudent extends c12_TA
{}

lone sig c29_AIGradStudent extends c12_TA
{}

lone sig c30_CompilerCourse extends c1_Course
{}

lone sig c31_MachineLearningCourse extends c1_Course
{}

fact { (c28_CompilerGradStudent.(@r_c13_first.@ref)) = c30_CompilerCourse }
fact { (c29_AIGradStudent.(@r_c13_first.@ref)) = c31_MachineLearningCourse }
lone sig c42_numerOfAssistants
{ ref : one Int }

fact { (c42_numerOfAssistants.@ref) = (#(c1_Course.@r_c2_assistants)) }
