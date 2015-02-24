open util/integer
pred show {}


one sig c0_aCar extends c0_Car
{}

abstract sig c0_Car
{ r_c0_ABS : lone c0_ABS
, r_c0_Transmission : one c0_Transmission
, r_c0_FCA : lone c0_FCA
, r_c0_CC : lone c0_CC
, r_c0_total_cost : one c0_total_cost
, r_c0_total_comfort : one c0_total_comfort
, r_c0_total_fuel : one c0_total_fuel
, r_c0_total_mass : one c0_total_mass }
{ (some (this.@r_c0_CC).@r_c0_ACC) => (some this.@r_c0_FCA)
  (some this.@r_c0_total_cost) => ((this.(@r_c0_total_cost.@ref)) = (sum temp : (c0_Feature.@r_c0_cost) | temp.@ref))
  (some this.@r_c0_total_comfort) => ((this.(@r_c0_total_comfort.@ref)) = (sum temp : (c0_ComfortFeature.@r_c0_cost) | temp.@ref))
  (some this.@r_c0_total_fuel) => ((this.(@r_c0_total_fuel.@ref)) = (sum temp : (c0_FuelFeature.@r_c0_cost) | temp.@ref))
  (some this.@r_c0_total_mass) => ((this.(@r_c0_total_mass.@ref)) = (sum temp : (c0_FuelFeature.@r_c0_mass) | temp.@ref)) }

sig c0_ABS extends c0_ComfortFeature
{}
{ one @r_c0_ABS.this
  (this.(@r_c0_cost.@ref)) = 2
  (this.(@r_c0_mass.@ref)) = 1
  (this.(@r_c0_comfort.@ref)) = 1 }

sig c0_Transmission
{ r_c0_Automatic : lone c0_Automatic
, r_c0_Manual : lone c0_Manual }
{ one @r_c0_Transmission.this
  let children = (r_c0_Automatic + r_c0_Manual) | one children }

sig c0_Automatic extends c0_FuelFeature
{}
{ one @r_c0_Automatic.this
  (this.(@r_c0_fuel.@ref)) = 2
  (this.(@r_c0_mass.@ref)) = 1
  (this.(@r_c0_comfort.@ref)) = 2
  (this.(@r_c0_cost.@ref)) = 4 }

sig c0_Manual extends c0_FuelFeature
{}
{ one @r_c0_Manual.this
  (this.(@r_c0_fuel.@ref)) = 0
  (this.(@r_c0_mass.@ref)) = 1
  (this.(@r_c0_comfort.@ref)) = 1
  (this.(@r_c0_cost.@ref)) = 3 }

sig c0_FCA extends c0_FuelFeature
{ r_c0_Sensor : one c0_Sensor
, r_c0_Alert : lone c0_Alert }
{ one @r_c0_FCA.this
  (this.(@r_c0_fuel.@ref)) = 2
  (this.(@r_c0_mass.@ref)) = 2
  (this.(@r_c0_comfort.@ref)) = 4
  (this.(@r_c0_cost.@ref)) = 5 }

sig c0_Sensor
{ r_c0_Radar : lone c0_Radar
, r_c0_Lidar : lone c0_Lidar }
{ one @r_c0_Sensor.this
  let children = (r_c0_Radar + r_c0_Lidar) | one children }

sig c0_Radar extends c0_Feature
{}
{ one @r_c0_Radar.this
  (this.(@r_c0_cost.@ref)) = 3
  (this.(@r_c0_mass.@ref)) = 1 }

sig c0_Lidar extends c0_Feature
{}
{ one @r_c0_Lidar.this
  (this.(@r_c0_cost.@ref)) = 5
  (this.(@r_c0_mass.@ref)) = 1 }

sig c0_Alert
{ r_c0_Haptic : lone c0_Haptic
, r_c0_Audible : lone c0_Audible }
{ one @r_c0_Alert.this
  let children = (r_c0_Haptic + r_c0_Audible) | one children }

sig c0_Haptic extends c0_ComfortFeature
{}
{ one @r_c0_Haptic.this
  (this.(@r_c0_comfort.@ref)) = 4
  (this.(@r_c0_cost.@ref)) = 2
  (this.(@r_c0_mass.@ref)) = 1 }

sig c0_Audible extends c0_ComfortFeature
{}
{ one @r_c0_Audible.this
  (this.(@r_c0_comfort.@ref)) = 2
  (this.(@r_c0_cost.@ref)) = 1
  (this.(@r_c0_mass.@ref)) = 1 }

sig c0_CC extends c0_FuelFeature
{ r_c0_ACC : lone c0_ACC }
{ one @r_c0_CC.this
  (this.(@r_c0_fuel.@ref)) = 1
  (this.(@r_c0_mass.@ref)) = 1
  (this.(@r_c0_comfort.@ref)) = 3
  (this.(@r_c0_cost.@ref)) = 4 }

sig c0_ACC extends c0_FuelFeature
{}
{ one @r_c0_ACC.this
  (this.(@r_c0_fuel.@ref)) = 2
  (this.(@r_c0_mass.@ref)) = 2
  (this.(@r_c0_comfort.@ref)) = 6
  (this.(@r_c0_cost.@ref)) = 3 }

sig c0_total_cost
{ ref : one Int }
{ one @r_c0_total_cost.this }

sig c0_total_comfort
{ ref : one Int }
{ one @r_c0_total_comfort.this }

sig c0_total_fuel
{ ref : one Int }
{ one @r_c0_total_fuel.this }

sig c0_total_mass
{ ref : one Int }
{ one @r_c0_total_mass.this }

abstract sig c0_Feature
{ r_c0_cost : one c0_cost
, r_c0_mass : one c0_mass }

sig c0_cost
{ ref : one Int }
{ one @r_c0_cost.this }

sig c0_mass
{ ref : one Int }
{ one @r_c0_mass.this }

abstract sig c0_ComfortFeature extends c0_Feature
{ r_c0_comfort : one c0_comfort }

sig c0_comfort
{ ref : one Int }
{ one @r_c0_comfort.this }

abstract sig c0_FuelFeature extends c0_ComfortFeature
{ r_c0_fuel : one c0_fuel }

sig c0_fuel
{ ref : one Int }
{ one @r_c0_fuel.this }

