module

public import Model.Signature
public import Model.Hand
public import Model.Euclidean
public import Model.Euclidean.Circles
public import Model.Euclidean.CircleSides
public import Model.Euclidean.Magnitudes
public import Model.Euclidean.Centre
public import Model.Laws.angles
public import Model.Euclidean.AngleBasics
public import Model.Euclidean.Angles
public import Model.Euclidean.AngleAdd

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
info: 'Model.Euclidean.Definition15' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.Definition15

/--
info: 'Model.Euclidean.Postulate4' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.Postulate4

/--
info: 'Model.Euclidean.angle_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.angle_symm

/--
info: 'Model.Euclidean.angle_le_two_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.angle_le_two_right

/--
info: 'Model.Euclidean.angle_eq_zero_of_same_ray' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.angle_eq_zero_of_same_ray

/--
info: 'Model.Euclidean.same_ray_of_angle_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.same_ray_of_angle_eq_zero

/--
info: 'Model.Euclidean.angle_add_of_inside' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.angle_add_of_inside

/--
info: 'Model.Euclidean.inside_of_angle_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.inside_of_angle_add

/--
info: 'Model.Euclidean.adjacent_eq_of_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.adjacent_eq_of_right

/--
info: 'Model.Euclidean.angle_eq_of_same_rays' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.angle_eq_of_same_rays
