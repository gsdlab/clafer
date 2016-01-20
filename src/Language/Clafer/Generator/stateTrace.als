/* Definition of timed traces (input independent) */ 
sig State {}

private one sig Ord {
   First: set State,
   Next: State -> State
} {
   pred/totalOrder[State,First,Next]
}

lone sig back in State {}

fun loop : State -> State {
  last -> back
}

fun first: one State { Ord.First }

fun last: one State { State - ((Ord.Next).State) }

fun next : State->State { Ord.Next + loop }

fun prev : State->State { ~this/next }

fun past : State->State { ^(~this/next) }

fun future : State -> State { State <: *this/next }

fun upto[s,s' : State] : set State {
  (s' in s.*(Ord.Next) or finite) implies s.future & ^(Ord.Next).s' else s.*(Ord.Next) + (^(Ord.Next).s' & back.*(Ord.Next))
}


pred finite {
  no loop
}

pred infinite {
  some loop
}

fun localFirst [rel: univ->univ->State, parentSet: univ, child: univ] : State {
       let lifetime = child.(parentSet.rel) | lifetime - (lifetime.next)
}
