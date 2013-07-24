open util/integer
pred show {}


abstract sig c1_Dimension
{ r_c2_levels : set c2_levels }
{ all disj x, y : this.@r_c2_levels | (x.@ref) != (y.@ref)
  all  dl : this.@r_c2_levels | ((dl.(@ref.@r_c24_belongsTo)).@ref) = this }

sig c2_levels
{ ref : one c23_DimensionLevel }
{ one @r_c2_levels.this }

abstract sig c23_DimensionLevel
{ r_c24_belongsTo : one c24_belongsTo }
{ all disj x, y : this.@r_c24_belongsTo | (x.@ref) != (y.@ref) }

sig c24_belongsTo
{ ref : one c1_Dimension }
{ one @r_c24_belongsTo.this }

lone sig c34_dim1 extends c1_Dimension
{}

lone sig c35_dim2 extends c1_Dimension
{}

lone sig c36_dimLevel1 extends c23_DimensionLevel
{}

lone sig c37_dimLevel2 extends c23_DimensionLevel
{}

fact { some disj dl1, dl2 : c23_DimensionLevel | ((dl1.@r_c24_belongsTo).@ref) = ((dl2.@r_c24_belongsTo).@ref) }
