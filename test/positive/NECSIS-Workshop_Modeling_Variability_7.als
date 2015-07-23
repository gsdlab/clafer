open util/integer
pred show {}


one sig c0_BumbleBee extends c0_Camaro
{}
{ some this.@r_c0_transformer }

abstract sig c0_Camaro extends c0_Car
{ r_c0_transformer : lone c0_transformer }
{ some (this.@r_c0_CC).@r_c0_ACC
  some ((this.@r_c0_CC).@r_c0_switch).@r_c0_backlight }

sig c0_transformer
{}
{ one @r_c0_transformer.this }

abstract sig c0_Car
{ r_c0_ABS : lone c0_ABS
, r_c0_Transmission : one c0_Transmission
, r_c0_FCA : lone c0_FCA
, r_c0_CC : lone c0_CC }
{ (some (this.@r_c0_CC).@r_c0_ACC) => (some this.@r_c0_FCA) }

sig c0_ABS
{}
{ one @r_c0_ABS.this }

sig c0_Transmission
{ r_c0_Automatic : lone c0_Automatic
, r_c0_Manual : lone c0_Manual }
{ one @r_c0_Transmission.this
  let children = (r_c0_Automatic + r_c0_Manual) | one children }

sig c0_Automatic
{}
{ one @r_c0_Automatic.this }

sig c0_Manual
{}
{ one @r_c0_Manual.this }

sig c0_FCA extends c1_FCA
{}
{ one @r_c0_FCA.this }

sig c0_CC extends c1_CC
{}
{ one @r_c0_CC.this }

abstract sig c1_FCA
{ r_c0_Sensor : one c0_Sensor
, r_c0_Alert : one c0_Alert }

sig c0_Sensor
{ r_c0_Radar : lone c0_Radar
, r_c0_Lidar : lone c0_Lidar }
{ one @r_c0_Sensor.this
  let children = (r_c0_Radar + r_c0_Lidar) | one children }

sig c0_Radar
{}
{ one @r_c0_Radar.this }

sig c0_Lidar
{}
{ one @r_c0_Lidar.this }

sig c0_Alert
{ r_c0_Haptic : lone c0_Haptic
, r_c0_Audible : lone c0_Audible }
{ one @r_c0_Alert.this
  let children = (r_c0_Haptic + r_c0_Audible) | one children }

sig c0_Haptic
{}
{ one @r_c0_Haptic.this }

sig c0_Audible
{}
{ one @r_c0_Audible.this }

abstract sig c1_CC
{ r_c0_switch : one c0_switch
, r_c0_ACC : lone c0_ACC }

sig c0_switch
{ r_c0_backlight : lone c0_backlight }
{ one @r_c0_switch.this }

sig c0_backlight
{}
{ one @r_c0_backlight.this }

sig c0_ACC
{}
{ one @r_c0_ACC.this }

