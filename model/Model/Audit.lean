module

public import Model.Signature
public import Model.Hand
public import Model.Euclidean
public import Model.Euclidean.Circles
public import Model.Euclidean.CircleSides
public import Model.Euclidean.Magnitudes
public import Model.Euclidean.Centre
public import Model.Laws.circles
public import Model.Euclidean.CircleBasics
public import Model.Euclidean.CircleRules
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

/-! ## The circle rules

Postulate 3, Definition 15, the generalities of a centre and the inside of a circle, System
E's Circle 1 to 4, the finite avoidance rules for the open regions and the circumference,
and `circlesMeet_self`, the case `CirclesMeet α α` that the laws about two circles must
allow. -/

/--
info: 'Model.Euclidean.Postulate3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.Postulate3

/--
info: 'Model.Euclidean.Definition15' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.Definition15

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
info: 'Model.Euclidean.circle_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.circle_eq

/--
info: 'Model.Euclidean.inside_of_len_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.inside_of_len_lt

/--
info: 'Model.Euclidean.len_lt_of_inside' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.len_lt_of_inside

/--
info: 'Model.Euclidean.on_circle_of_len_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.on_circle_of_len_eq

/--
info: 'Model.Euclidean.between_of_inside_chord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.between_of_inside_chord

/--
info: 'Model.Euclidean.inside_of_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.inside_of_between

/--
info: 'Model.Euclidean.outside_of_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.outside_of_between

/--
info: 'Model.Euclidean.not_same_side_of_circles_meet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.not_same_side_of_circles_meet

/--
info: 'Model.Euclidean.circlesMeet_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.circlesMeet_self

/--
info: 'Model.Euclidean.exists_point' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point

/--
info: 'Model.Euclidean.exists_point_same_side' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point_same_side

/--
info: 'Model.Euclidean.exists_point_opposite_side' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point_opposite_side

/--
info: 'Model.Euclidean.exists_point_inside_circle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point_inside_circle

/--
info: 'Model.Euclidean.exists_point_outside_circle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point_outside_circle

/--
info: 'Model.Euclidean.exists_point_on_circle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point_on_circle
