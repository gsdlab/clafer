open util/integer
pred show {}


abstract sig c0_Dimension
{ r_c0_levels : set c0_levels }
{ all disj x, y : this.@r_c0_levels | (x.@ref) != (y.@ref) 
  all  dl : this.@r_c0_levels | ((dl.(@ref.@r_c0_belongsTo)).@ref) = this }

sig c0_levels
{ ref : one c0_DimensionLevel }
{ one @r_c0_levels.this }

abstract sig c0_DimensionLevel
{ r_c0_belongsTo : one c0_belongsTo }

sig c0_belongsTo
{ ref : one c0_Dimension }
{ one @r_c0_belongsTo.this }

one sig c0_dim1 extends c0_Dimension
{}

one sig c0_dim2 extends c0_Dimension
{}

one sig c0_dimLevel1 extends c0_DimensionLevel
{}

one sig c0_dimLevel2 extends c0_DimensionLevel
{}

fact { some disj dl1, dl2 : c0_DimensionLevel | ((dl1.@r_c0_belongsTo).@ref) = ((dl2.@r_c0_belongsTo).@ref) }
