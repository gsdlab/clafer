open util/integer
pred show {}


abstract sig c1_Dimension
{ r_c2_levels : set c2_levels }
{ all disj x, y : this.@r_c2_levels | (x.@ref) != (y.@ref)
  all  dl : this.@r_c2_levels | ((dl.(@ref.@r_c4_belongsTo)).@ref) = this }

sig c2_levels
{ ref : one c3_DimensionLevel }
{ one @r_c2_levels.this }

abstract sig c3_DimensionLevel
{ r_c4_belongsTo : one c4_belongsTo }
{ all disj x, y : this.@r_c4_belongsTo | (x.@ref) != (y.@ref) }

sig c4_belongsTo
{ ref : one c1_Dimension }
{ one @r_c4_belongsTo.this }

one sig c5_dim1 extends c1_Dimension
{}

one sig c6_dim2 extends c1_Dimension
{}

one sig c7_dimLevel1 extends c3_DimensionLevel
{}

one sig c8_dimLevel2 extends c3_DimensionLevel
{}

fact { some disj dl1, dl2 : c3_DimensionLevel | ((dl1.@r_c4_belongsTo).@ref) = ((dl2.@r_c4_belongsTo).@ref) }
