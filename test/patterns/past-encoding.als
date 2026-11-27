// The encoding of Clafer's past-time operators in Alloy 6 (gsdlab/clafer#127), checked against
// an independent definition of each operator by recursion on the states (a monitor, written
// with `after` only, without past-time operators).
//
// In the context of a clafer with a parent, the past is looked at while the parent exists, in
// its current lifetime: P is "the parent of the context instance exists", which the temporal
// Alloy output writes as `some this.<parent relation>`. A parent that disappears and is born
// again starts a new lifetime, in which the previous one is not visible.
//
// Run with the Alloy 6.2.0 jar, e.g., from the root of the clafer repository:
//
//     java -jar alloy6.2.0.jar exec -c '*' -o - test/patterns/past-encoding.als
//
// A bounded check, on traces of up to 10 states; test/patterns/check-patterns.py proves the
// same with nuXmv, on all traces. The `encodings` assertion has no counterexample; `unbounded`
// has one, a parent born again that sees its previous lifetime with Alloy's own operators.

one sig U {}

// the parent exists (P), and the arguments a and b of the operators
var sig P, A, B in U {}

pred p { some P }
pred a { some A }
pred b { some B }

// --- the encodings, as the temporal Alloy output writes them in the context of a clafer with a parent

pred previousEnc     { before (p and a) }
pred weakPreviousEnc { not before (p and not a) }
pred onceEnc         { p since (p and a) }
pred historicallyEnc { not (p since (p and not a)) }
pred sinceEnc        { (p and a) since (p and b) }
pred triggeredEnc    { not ((p and not a) since (p and not b)) }

// --- the monitors, by recursion on the states of the current lifetime of the parent; each
// holds at a state where the parent exists, and only those states are compared

var sig Previous, WeakPrevious, Once, Historically, Since, Triggered in U {}

// at the first state of the trace, which is the first state of a lifetime if the parent exists
fact firstState {
  no Previous
  some WeakPrevious
  some Once iff (p and a)
  some Historically iff (p and a)
  some Since iff (p and b)
  some Triggered iff b
}

// from each state to the next one; a lifetime starts at a state with p after one without
fact nextState {
  always {
    after some Previous iff (p and a)
    after some WeakPrevious iff (not p or a)
    after some Once iff (after p and (after a or (p and some Once)))
    after some Historically iff (after p and after a and (not p or some Historically))
    after some Since iff (after p and (after b or (after a and p and some Since)))
    after some Triggered iff (after b and (after a or not p or some Triggered))
  }
}

assert encodings {
  always (p implies {
    previousEnc     iff some Previous
    weakPreviousEnc iff some WeakPrevious
    onceEnc         iff some Once
    historicallyEnc iff some Historically
    sinceEnc        iff some Since
    triggeredEnc    iff some Triggered
  })
}
check encodings for 1 but 1..10 steps

// Alloy's own operators, without the bound, see a previous lifetime of the parent
assert unbounded {
  always (p implies {
    (before a)       iff some Previous
    (once a)         iff some Once
    (historically a) iff some Historically
    (a since b)      iff some Since
  })
}
check unbounded for 1 but 1..10 steps
