open util/integer
pred show {}


sig c0_a
{ r_c0_b : set c0_b }
{ all  x : (this.@r_c0_b).@r_c0_c | one x.@r_c0_d }

sig c0_b
{ r_c0_c : set c0_c }
{ one @r_c0_b.this
  one (this.@r_c0_c).@r_c0_d }

sig c0_c
{ r_c0_d : lone c0_d }
{ one @r_c0_c.this }

sig c0_d
{}
{ one @r_c0_d.this }

fact { all  x : (c0_a.@r_c0_b).@r_c0_c | one x.@r_c0_d }
assert assertOnLine_9 { all  x : (c0_a.@r_c0_b).@r_c0_c | some x.@r_c0_d }
check assertOnLine_9 for 1

