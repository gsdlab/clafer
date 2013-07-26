open util/integer
pred show {}


one sig c1_Office
{ r_c2_Printer : lone c2_Printer
, r_c13_Scanner : lone c13_Scanner }

lone sig c2_Printer
{ r_c3_resolution : one c3_resolution
, r_c4_Cartridge : set c4_Cartridge
, r_c10_Type : one c10_Type }
{ one r_c2_Printer
  1 <= #r_c4_Cartridge and #r_c4_Cartridge <= 4 }

lone sig c3_resolution
{ ref : one Int }
{ one r_c3_resolution }

sig c4_Cartridge
{ r_c5_inkVolume : one c5_inkVolume
, r_c6_Speed : one c6_Speed
, r_c9_Turbo : lone c9_Turbo }
{ one @r_c4_Cartridge.this }

sig c5_inkVolume
{ ref : one Int }
{ one @r_c5_inkVolume.this }

sig c6_Speed
{ r_c7_High : lone c7_High
, r_c8_Low : lone c8_Low }
{ one @r_c6_Speed.this
  let children = (r_c7_High + r_c8_Low) | some children }

sig c7_High
{}
{ one @r_c7_High.this }

sig c8_Low
{}
{ one @r_c8_Low.this }

sig c9_Turbo
{}
{ one @r_c9_Turbo.this }

lone sig c10_Type
{ r_c11_Color : lone c11_Color
, r_c12_BW : lone c12_BW }
{ one r_c10_Type
  let children = (r_c11_Color + r_c12_BW) | one children }

lone sig c11_Color
{}
{ one r_c11_Color }

lone sig c12_BW
{}
{ one r_c12_BW }

lone sig c13_Scanner
{ r_c14_GreenMode : lone c14_GreenMode
, r_c15_Head : set c15_Head }
{ one r_c13_Scanner
  1 <= #r_c15_Head and #r_c15_Head <= 2 }

lone sig c14_GreenMode
{}
{ one r_c14_GreenMode }

sig c15_Head
{}
{ one @r_c15_Head.this }

one sig c16_PrinterPool
{ r_c17_fax : lone c17_fax
, r_c18_printer : lone c18_printer
, r_c19_copier : lone c19_copier
, r_c20_scan : lone c20_scan }
{ (some this.@r_c17_fax) => (some this.@r_c18_printer) }

lone sig c17_fax
{}
{ one r_c17_fax }

lone sig c18_printer
{}
{ one r_c18_printer }

lone sig c19_copier
{}
{ one r_c19_copier }

lone sig c20_scan
{}
{ one r_c20_scan }

fact { ((some c16_PrinterPool.@r_c17_fax) => (some c16_PrinterPool.@r_c18_printer)) && ((some c16_PrinterPool.@r_c19_copier) => ((some c16_PrinterPool.@r_c17_fax) && (some c16_PrinterPool.@r_c18_printer))) }
