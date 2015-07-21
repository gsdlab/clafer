open util/integer
pred show {}


one sig c0_x
{ ref : one Int }
{ (this.@ref) = 1
  (this.@ref) = 1 }

fact { (c0_x.@ref) = 1 }
fact { (c0_x.@ref) = 1 }
one sig c0_y
{ ref : one c0_x }
{ ((this.@ref).@ref) = 1
  ((this.@ref).@ref) = 1
  ((this.@ref).@ref) = 1 }

fact { ((c0_y.@ref).@ref) = 1 }
fact { ((c0_y.@ref).@ref) = 1 }
fact { ((c0_y.@ref).@ref) = 1 }
one sig c0_z
{ ref : one c0_y }
{ (((this.@ref).@ref).@ref) = 1
  (((this.@ref).@ref).@ref) = 1
  (((this.@ref).@ref).@ref) = 1
  (((this.@ref).@ref).@ref) = 1 }

fact { (((c0_z.@ref).@ref).@ref) = 1 }
fact { (((c0_z.@ref).@ref).@ref) = 1 }
fact { (((c0_z.@ref).@ref).@ref) = 1 }
fact { (((c0_z.@ref).@ref).@ref) = 1 }
