module

public import Model.Laws.angles
public import Model.Euclidean.AngleBasics
public import Model.Euclidean.Angles
public import Model.Euclidean.AngleAdd

public import Model.Laws.intersections
public import Model.Euclidean.LineCircle
public import Model.Euclidean.LineSides

public import Model.Laws.circles
public import Model.Euclidean.CircleBasics
public import Model.Euclidean.CircleRules

public import Model.Signature
public import Model.Laws
public import Model.Hand
public import Model.Laws.incidence
public import Model.Euclidean
public import Model.Euclidean.Circles
public import Model.Euclidean.CircleSides
public import Model.Euclidean.Magnitudes
public import Model.Euclidean.Centre
public import Model.Assembly
public import Model.Euclidean.Incidence
public import Model.Euclidean.Avoidance
public import Model.Laws.order
public import Model.Euclidean.Order
public import Model.Euclidean.OrderLines
public import Model.Euclidean.Segments
public import Model.Laws.sides
public import Model.Euclidean.Sides
public import Model.Euclidean.Pasch

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
module of `Model` is imported here. `Model.euclidean_laws`, which `Model/Assembly.lean`
generates from every theorem that proves a law in the plane, is audited last, so a law's
theorem is audited through it as soon as the generator gathers it; the theorems listed one by
one before it include every integrated family and the proposed `exists_centre`, which is
no law yet.
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

/--
info: 'Model.Euclidean.between_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.between_symm

/--
info: 'Model.Euclidean.ne_of_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.ne_of_between

/--
info: 'Model.Euclidean.ne_of_between_ends' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.ne_of_between_ends

/--
info: 'Model.Euclidean.not_between_of_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.not_between_of_between

/--
info: 'Model.Euclidean.on_line_of_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.on_line_of_between

/--
info: 'Model.Euclidean.on_line_of_between_ends' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.on_line_of_between_ends

/--
info: 'Model.Euclidean.between_of_between_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.between_of_between_left

/--
info: 'Model.Euclidean.between_of_between_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.between_of_between_right

/--
info: 'Model.Euclidean.between_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.between_cases

/--
info: 'Model.Euclidean.not_between_of_between_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.not_between_of_between_between

/--
info: 'Model.Euclidean.len_add_of_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.len_add_of_between

/--
info: 'Model.Euclidean.circle_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.circle_eq

/--
info: 'Model.Euclidean.on_circle_of_len_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.on_circle_of_len_eq

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
info: 'Model.Euclidean.same_side_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.same_side_refl

/--
info: 'Model.Euclidean.same_side_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.same_side_symm

/--
info: 'Model.Euclidean.not_on_line_of_same_side' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.not_on_line_of_same_side

/--
info: 'Model.Euclidean.same_side_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.same_side_trans

/--
info: 'Model.Euclidean.same_side_or' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.same_side_or

/--
info: 'Model.Euclidean.pasch1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.pasch1

/--
info: 'Model.Euclidean.pasch2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.pasch2

/--
info: 'Model.Euclidean.pasch3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.pasch3

/--
info: 'Model.Euclidean.pasch4' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.pasch4

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
info: 'Model.Euclidean.centre_unique_circles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.centre_unique_circles

/--
info: 'Model.Euclidean.centre_inside_circles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.centre_inside_circles

/--
info: 'Model.Euclidean.inside_not_on_circles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.inside_not_on_circles

/--
info: 'Model.Euclidean.circle_eq_circles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.circle_eq_circles

/--
info: 'Model.Euclidean.inside_of_len_lt_circles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.inside_of_len_lt_circles

/--
info: 'Model.Euclidean.len_lt_of_inside_circles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.len_lt_of_inside_circles

/--
info: 'Model.Euclidean.on_circle_of_len_eq_circles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.on_circle_of_len_eq_circles

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
info: 'Model.Euclidean.exists_point_circles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.exists_point_circles

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

/--
info: 'Model.Euclidean.lines_meet_of_opposite_sides_intersections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.lines_meet_of_opposite_sides_intersections

/--
info: 'Model.Euclidean.line_meets_circle_of_opposite_sides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.line_meets_circle_of_opposite_sides

/--
info: 'Model.Euclidean.line_meets_circle_of_inside' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.line_meets_circle_of_inside

/--
info: 'Model.Euclidean.line_circle_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.line_circle_between

/--
info: 'Model.Euclidean.line_circle_beyond' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.line_circle_beyond

/--
info: 'Model.Euclidean.between_of_inside_chord_intersections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.between_of_inside_chord_intersections

/--
info: 'Model.Euclidean.inside_of_between_intersections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.inside_of_between_intersections

/--
info: 'Model.Euclidean.outside_of_between_intersections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.outside_of_between_intersections

/--
info: 'Model.Euclidean.not_same_side_of_circles_meet_intersections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.not_same_side_of_circles_meet_intersections

/--
info: 'Model.Euclidean.Definition15_angles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Euclidean.Definition15_angles

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

/-! ## What the assembled model rests on

`euclidean_laws` gathers every theorem that proves a law in the plane, with the laws not yet
proved there as hypotheses, so what it rests on is what all those proofs rest on. -/

/--
info: 'Model.euclidean_laws' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Model.euclidean_laws
