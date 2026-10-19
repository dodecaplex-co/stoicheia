module

public import Model.Signature
public import Model.Hand
public import Model.Laws.incidence
public import Model.Euclidean
public import Model.Euclidean.Circles
public import Model.Euclidean.CircleSides
public import Model.Euclidean.Magnitudes
public import Model.Euclidean.Centre
public import Model.Euclidean.Incidence
public import Model.Euclidean.Avoidance

/-!
# What the model's proofs rest on

A model is evidence only if its proofs do not use the laws they are meant to satisfy. This
file imports every module of the `Model` library, and checks two things at every build.

* **The library is not imported,** directly or through another file: its words are unknown
  here, so none of its laws is in scope.
* **Each theorem that proves a law in the plane rests on Lean's own axioms alone,**
  `propext`, `Classical.choice` and `Quot.sound`, which Mathlib's real numbers use. No
  axiom of the library can appear, and neither can `sorryAx`, which an unfinished proof
  would bring in.

If either changes, the message changes, `#guard_msgs` fails, and so does the build. A new
module of `Model` is imported here, and a new law's theorem is listed here.
-/

/-! ## The library is not imported -/

/-- error: Unknown identifier `Elements.Point` -/
#guard_msgs in
#check Elements.Point

/-! ## What each proof rests on -/

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

/--
info: 'Model.Euclidean.circles_meet_same_side' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.circles_meet_same_side

/--
info: 'Model.Euclidean.circles_meet_opposite_side' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.circles_meet_opposite_side

/--
info: 'Model.Euclidean.add_assoc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.add_assoc

/--
info: 'Model.Euclidean.add_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.add_comm

/--
info: 'Model.Euclidean.add_lt_add_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.add_lt_add_right

/--
info: 'Model.Euclidean.add_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.add_zero

/--
info: 'Model.Euclidean.lt_irrefl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.lt_irrefl

/--
info: 'Model.Euclidean.lt_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.lt_trans

/--
info: 'Model.Euclidean.lt_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.lt_trichotomy

/--
info: 'Model.Euclidean.not_lt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.not_lt_zero

/--
info: 'Model.Euclidean.exists_centre' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_centre

/--
info: 'Model.Euclidean.Postulate1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.Postulate1

/--
info: 'Model.Euclidean.line_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.line_unique

/--
info: 'Model.Euclidean.centre_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.centre_unique

/--
info: 'Model.Euclidean.centre_inside' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.centre_inside

/--
info: 'Model.Euclidean.inside_not_on' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.inside_not_on

/--
info: 'Model.Euclidean.lines_meet_of_opposite_sides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.lines_meet_of_opposite_sides

/--
info: 'Model.Euclidean.exists_point' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point

/--
info: 'Model.Euclidean.exists_point_on_line' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point_on_line

/--
info: 'Model.Euclidean.exists_point_on_line_off_line' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point_on_line_off_line

/--
info: 'Model.Euclidean.exists_point_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point_between

/--
info: 'Model.Euclidean.Postulate2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.Postulate2
