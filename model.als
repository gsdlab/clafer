/*
All clafers: 13 | Abstract: 4 | Concrete: 8 | References: 1
Constraints: 3
Goals: 0
Global scope: 1..*
Can skip resolver: no
*/
open util/integer
pred show {}
run show for 1 but 3 c0_Command, 0 c0_WinController, 0 c0_cmd, 0 c0_goingDown, 0 c0_goingUp, 0 c0_states, 0 c0_stopped

abstract sig c0_Command
{}
{ ref =  }

one sig c0_Up extends c0_Command
{}
{ ref = (c0_Command) }

one sig c0_Down extends c0_Command
{}
{ ref = (c0_Command) }

one sig c0_Stop extends c0_Command
{}
{ ref = (c0_Command) }

fact { #c0_Component = 0 }
abstract sig c0_Component
{ r_c0_Port : set c0_Port }
{ ref =  }

abstract sig c0_Port
{}
{ one @r_c0_Port.this
  ref =  }

fact { #c0_WinController = 0 }
abstract sig c0_WinController extends c0_Component
{ r_c0_cmd : one c0_cmd
, r_c0_states : one c0_states }
{ ref = (c0_Component) }

sig c0_cmd extends c0_Port
{ ref : one c0_Command }
{ one @r_c0_cmd.this }

sig c0_states
{ r_c0_goingUp : lone c0_goingUp
, r_c0_goingDown : lone c0_goingDown
, r_c0_stopped : lone c0_stopped }
{ one @r_c0_states.this
  let children = (r_c0_goingUp + r_c0_goingDown + r_c0_stopped) | one children
  ref =  }

sig c0_goingUp
{}
{ one @r_c0_goingUp.this
  ref = 
  (((this.~@r_c0_goingUp).~@r_c0_states).(@r_c0_cmd.@ref)) = c0_Up }

sig c0_goingDown
{}
{ one @r_c0_goingDown.this
  ref = 
  (((this.~@r_c0_goingDown).~@r_c0_states).(@r_c0_cmd.@ref)) = c0_Down }

sig c0_stopped
{}
{ one @r_c0_stopped.this
  ref = 
  (((this.~@r_c0_stopped).~@r_c0_states).(@r_c0_cmd.@ref)) = c0_Stop }

