open util/integer
pred show {}


fact { #c0_Kernel = 0 }
abstract sig c0_Kernel
{ r_c0_memory : lone c0_memory }

sig c0_memory
{}
{ one @r_c0_memory.this }

one sig c0_Phone
{ r_c0_name : one c0_name }
{ some c0_Kernel.@r_c0_memory }

one sig c0_name
{ ref : one Int }

