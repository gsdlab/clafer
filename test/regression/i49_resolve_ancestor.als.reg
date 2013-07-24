open util/integer
pred show {}


lone sig c1_person
{ r_c2_haha : one c2_haha
, r_c5_ble : one c5_ble }

lone sig c2_haha
{ r_c3_lala : one c3_lala }
{ one r_c2_haha }

lone sig c3_lala
{ r_c4_age : one c4_age }
{ one r_c3_lala }

lone sig c4_age
{ ref : one Int }
{ one r_c4_age }

lone sig c5_ble
{ r_c6_married : lone c6_married }
{ one r_c5_ble }

lone sig c6_married
{}
{ one r_c6_married
  (((((this.~@r_c6_married).~@r_c5_ble).@r_c2_haha).@r_c3_lala).(@r_c4_age.@ref)) >= 18 }

