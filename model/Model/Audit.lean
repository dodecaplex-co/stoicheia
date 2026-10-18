module

public import Model.Euclidean.Circles

/-!
# What the model's proofs rest on

A model is evidence only if its proofs do not use the laws they are meant to satisfy. So
each theorem that proves a law in the plane is listed here with exactly the axioms Lean
reports beneath it: Lean's own `propext`, `Classical.choice` and `Quot.sound`, and nothing
else. No axiom of the library can appear (the model never imports it), and neither can
`sorryAx`, which an unfinished proof would bring in. If a proof changes what it rests on,
the message changes, `#guard_msgs` fails, and so does the build.
-/

/--
info: 'Model.Euclidean.circles_meet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.circles_meet

/--
info: 'Model.Euclidean.circles_meet_of_on_inside_outside' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.circles_meet_of_on_inside_outside
