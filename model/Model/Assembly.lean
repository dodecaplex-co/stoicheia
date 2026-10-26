module

public import Model.Laws
public import Model.Euclidean
public import Model.Euclidean.AngleAdd
public import Model.Euclidean.Angles
public import Model.Euclidean.Areas
public import Model.Euclidean.Avoidance
public import Model.Euclidean.Centre
public import Model.Euclidean.CircleBasics
public import Model.Euclidean.CircleRules
public import Model.Euclidean.CircleSides
public import Model.Euclidean.Circles
public import Model.Euclidean.Incidence
public import Model.Euclidean.Lengths
public import Model.Euclidean.LineCircle
public import Model.Euclidean.Magnitudes
public import Model.Euclidean.Order
public import Model.Euclidean.OrderLines
public import Model.Euclidean.Pasch
public import Model.Euclidean.Postulate5
public import Model.Euclidean.Segments
public import Model.Euclidean.Sides
public import Model.Euclidean.Superposition

/-!
# The plane satisfies the laws

**This file is generated: do not edit it.** `Check/Generator.lean` writes it, and `lake build`
fails while it differs from what the generator writes. To write it again, run
`lake lean Check/Write.lean` in `model/`.

A theorem of `Model/Euclidean/` named as a field of `Laws` (`Euclidean.circles_meet` for the
field `circles_meet`) proves that law in the plane, and `euclidean_laws` gathers them; Lean
checks here that each proves the law the generator wrote.

All 49 laws are proved in the plane, so `euclidean_laws` has no hypothesis, and
`model_exists` follows from it.
-/

@[expose] public section

namespace Model

/-- **The plane satisfies every law.** -/
theorem euclidean_laws : Laws Euclidean.plane where
  Definition15 := Euclidean.Definition15
  Postulate1 := Euclidean.Postulate1
  Postulate2 := Euclidean.Postulate2
  Postulate3 := Euclidean.Postulate3
  Postulate4 := Euclidean.Postulate4
  Postulate5 := Euclidean.Postulate5
  add_assoc := Euclidean.add_assoc
  add_comm := Euclidean.add_comm
  add_lt_add_right := Euclidean.add_lt_add_right
  add_zero := Euclidean.add_zero
  angle_add_of_inside := Euclidean.angle_add_of_inside
  angle_eq_of_same_rays := Euclidean.angle_eq_of_same_rays
  angle_eq_zero_of_same_ray := Euclidean.angle_eq_zero_of_same_ray
  angle_le_two_right := Euclidean.angle_le_two_right
  angle_symm := Euclidean.angle_symm
  area_add_of_between := Euclidean.area_add_of_between
  area_congruent := Euclidean.area_congruent
  area_degenerate := Euclidean.area_degenerate
  area_eq_zero_of_on_line := Euclidean.area_eq_zero_of_on_line
  area_rotate := Euclidean.area_rotate
  between_cases := Euclidean.between_cases
  between_of_inside_chord := Euclidean.between_of_inside_chord
  between_symm := Euclidean.between_symm
  circle_eq := Euclidean.circle_eq
  circles_meet := Euclidean.circles_meet
  circles_meet_same_side := Euclidean.circles_meet_same_side
  exists_centre := Euclidean.exists_centre
  exists_point := Euclidean.exists_point
  exists_point_inside_circle := Euclidean.exists_point_inside_circle
  exists_point_on_line := Euclidean.exists_point_on_line
  len_add_of_between := Euclidean.len_add_of_between
  len_self := Euclidean.len_self
  len_symm := Euclidean.len_symm
  line_circle_between := Euclidean.line_circle_between
  line_circle_beyond := Euclidean.line_circle_beyond
  line_unique := Euclidean.line_unique
  lines_meet_of_opposite_sides := Euclidean.lines_meet_of_opposite_sides
  lt_irrefl := Euclidean.lt_irrefl
  lt_trans := Euclidean.lt_trans
  lt_trichotomy := Euclidean.lt_trichotomy
  not_between_of_between := Euclidean.not_between_of_between
  not_lt_zero := Euclidean.not_lt_zero
  not_on_line_of_same_side := Euclidean.not_on_line_of_same_side
  on_line_of_area_eq_zero := Euclidean.on_line_of_area_eq_zero
  pasch2 := Euclidean.pasch2
  radius_ne_zero := Euclidean.radius_ne_zero
  same_ray_of_angle_eq_zero := Euclidean.same_ray_of_angle_eq_zero
  same_side_trans := Euclidean.same_side_trans
  superposition := Euclidean.superposition

/-- **The laws have a model:** the ordinary plane. -/
theorem model_exists : ∃ S : Signature, Laws S :=
  ⟨Euclidean.plane, euclidean_laws⟩

end Model
