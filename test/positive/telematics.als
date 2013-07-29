open util/integer
pred show {}


abstract sig c1_options
{ r_c2_size : one c2_size
, r_c5_cache : lone c5_cache }
{ ((some (this.@r_c2_size).@r_c3_small) && (some this.@r_c5_cache)) => (some ((this.@r_c5_cache).@r_c6_size).@r_c7_fixed) }

sig c2_size
{ r_c3_small : lone c3_small
, r_c4_large : lone c4_large }
{ one @r_c2_size.this
  let children = (r_c3_small + r_c4_large) | one children }

sig c3_small
{}
{ one @r_c3_small.this }

sig c4_large
{}
{ one @r_c4_large.this }

sig c5_cache
{ r_c6_size : one c6_size }
{ one @r_c5_cache.this }

sig c6_size
{ ref : one Int
, r_c7_fixed : lone c7_fixed }
{ one @r_c6_size.this }

sig c7_fixed
{}
{ one @r_c7_fixed.this }

abstract sig c8_comp
{ r_c9_version : one c9_version }
{ (this.(@r_c9_version.@ref)) = (1.add[2]) }

sig c9_version
{ ref : one Int }
{ one @r_c9_version.this }

abstract sig c10_ECU extends c8_comp
{}

abstract sig c11_display extends c8_comp
{ r_c12_server : one c12_server
, r_c13_options : one c13_options }
{ all disj x, y : this.@r_c12_server | (x.@ref) != (y.@ref)
  (this.(@r_c9_version.@ref)) >= ((this.@r_c12_server).(@ref.(@r_c9_version.@ref))) }

sig c12_server
{ ref : one c10_ECU }
{ one @r_c12_server.this }

sig c13_options extends c1_options
{}
{ one @r_c13_options.this }

abstract sig c14_plaECU extends c10_ECU
{ r_c15_display : set c15_display }
{ 1 <= #r_c15_display and #r_c15_display <= 2 }

sig c15_display extends c11_display
{}
{ one @r_c15_display.this
  ((this.(@r_c12_server.@ref)) = (this.~@r_c15_display)) && (no (this.@r_c13_options).@r_c5_cache) }

one sig c16_ECU1 extends c14_plaECU
{}

lone sig c17_ECU2 extends c14_plaECU
{ r_c18_master : one c18_master }
{ all disj x, y : this.@r_c18_master | (x.@ref) != (y.@ref) }

lone sig c18_master
{ ref : one c16_ECU1 }
{ one r_c18_master }

one sig c19_telematicsSystem
{ r_c20_channel : one c20_channel
, r_c23_extraDisplay : lone c23_extraDisplay
, r_c24_size : one c24_size }
{ (((((some (this.@r_c20_channel).@r_c22_dual) <=> (some c17_ECU2)) && ((some this.@r_c23_extraDisplay) <=> ((#(c16_ECU1.@r_c15_display)) = 2))) && ((some this.@r_c23_extraDisplay) <=> ((some c17_ECU2) => ((#(c17_ECU2.@r_c15_display)) = 2)))) && ((some (this.@r_c24_size).@r_c26_large) <=> (no (((c14_plaECU.@r_c15_display).@r_c13_options).@r_c2_size).@r_c3_small))) && ((some (this.@r_c24_size).@r_c25_small) <=> (no (((c14_plaECU.@r_c15_display).@r_c13_options).@r_c2_size).@r_c4_large)) }

one sig c20_channel
{ r_c21_single : lone c21_single
, r_c22_dual : lone c22_dual }
{ let children = (r_c21_single + r_c22_dual) | one children }

lone sig c21_single
{}
{ one r_c21_single }

lone sig c22_dual
{}
{ one r_c22_dual }

lone sig c23_extraDisplay
{}
{ one r_c23_extraDisplay }

one sig c24_size
{ r_c25_small : lone c25_small
, r_c26_large : lone c26_large }
{ let children = (r_c25_small + r_c26_large) | one children }

lone sig c25_small
{}
{ one r_c25_small }

lone sig c26_large
{}
{ one r_c26_large }

fact { ((some (c19_telematicsSystem.@r_c20_channel).@r_c22_dual) && (some c19_telematicsSystem.@r_c23_extraDisplay)) && (some (c19_telematicsSystem.@r_c24_size).@r_c26_large) }
