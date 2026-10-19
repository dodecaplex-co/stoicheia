module

public import Model.Laws
public import Model.Euclidean
public import Model.Euclidean.AngleAdd
public import Model.Euclidean.Angles
public import Model.Euclidean.Areas
public import Model.Euclidean.Avoidance
public import Model.Euclidean.CircleBasics
public import Model.Euclidean.CircleRules
public import Model.Euclidean.CircleSides
public import Model.Euclidean.Circles
public import Model.Euclidean.Incidence
public import Model.Euclidean.LineCircle
public import Model.Euclidean.LineSides
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

So far 81 of the 87 laws are proved in the plane. Until the rest are,
`euclidean_laws` takes them as hypotheses, so that it states exactly what is proved: the plane
satisfies every law, given the 6 that are not yet proved in it. When none is left,
the generator writes it with no hypothesis, and `model_exists` after it.
-/

@[expose] public section

namespace Model

/-- **The plane satisfies the laws,** given the 6 not yet proved in it. -/
theorem euclidean_laws
    (eq_of_len_eq_zero : Law.Tacit.eq_of_len_eq_zero Euclidean.plane)
    (len_self : Law.Tacit.len_self Euclidean.plane)
    (len_symm : Law.Tacit.len_symm Euclidean.plane)
    (triple_incidence1 : Law.Tacit.triple_incidence1 Euclidean.plane)
    (triple_incidence2 : Law.Tacit.triple_incidence2 Euclidean.plane)
    (triple_incidence3 : Law.Tacit.triple_incidence3 Euclidean.plane) :
    Laws Euclidean.plane where
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
  adjacent_eq_of_right := Euclidean.adjacent_eq_of_right
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
  area_swap := Euclidean.area_swap
  between_cases := Euclidean.between_cases
  between_of_area_add := Euclidean.between_of_area_add
  between_of_between_left := Euclidean.between_of_between_left
  between_of_between_right := Euclidean.between_of_between_right
  between_of_inside_chord := Euclidean.between_of_inside_chord
  between_symm := Euclidean.between_symm
  centre_inside := Euclidean.centre_inside
  centre_unique := Euclidean.centre_unique
  circle_eq := Euclidean.circle_eq
  circles_meet := Euclidean.circles_meet
  circles_meet_of_on_inside_outside := Euclidean.circles_meet_of_on_inside_outside
  circles_meet_opposite_side := Euclidean.circles_meet_opposite_side
  circles_meet_same_side := Euclidean.circles_meet_same_side
  eq_of_len_eq_zero := eq_of_len_eq_zero
  exists_point := Euclidean.exists_point
  exists_point_between := Euclidean.exists_point_between
  exists_point_inside_circle := Euclidean.exists_point_inside_circle
  exists_point_on_circle := Euclidean.exists_point_on_circle
  exists_point_on_line := Euclidean.exists_point_on_line
  exists_point_on_line_off_line := Euclidean.exists_point_on_line_off_line
  exists_point_opposite_side := Euclidean.exists_point_opposite_side
  exists_point_outside_circle := Euclidean.exists_point_outside_circle
  exists_point_same_side := Euclidean.exists_point_same_side
  inside_not_on := Euclidean.inside_not_on
  inside_of_angle_add := Euclidean.inside_of_angle_add
  inside_of_between := Euclidean.inside_of_between
  inside_of_len_lt := Euclidean.inside_of_len_lt
  len_add_of_between := Euclidean.len_add_of_between
  len_lt_of_inside := Euclidean.len_lt_of_inside
  len_self := len_self
  len_symm := len_symm
  line_circle_between := Euclidean.line_circle_between
  line_circle_beyond := Euclidean.line_circle_beyond
  line_meets_circle_of_inside := Euclidean.line_meets_circle_of_inside
  line_meets_circle_of_opposite_sides := Euclidean.line_meets_circle_of_opposite_sides
  line_unique := Euclidean.line_unique
  lines_meet_of_opposite_sides := Euclidean.lines_meet_of_opposite_sides
  lt_irrefl := Euclidean.lt_irrefl
  lt_trans := Euclidean.lt_trans
  lt_trichotomy := Euclidean.lt_trichotomy
  ne_of_between := Euclidean.ne_of_between
  ne_of_between_ends := Euclidean.ne_of_between_ends
  not_between_of_between := Euclidean.not_between_of_between
  not_between_of_between_between := Euclidean.not_between_of_between_between
  not_lt_zero := Euclidean.not_lt_zero
  not_on_line_of_same_side := Euclidean.not_on_line_of_same_side
  not_same_side_of_circles_meet := Euclidean.not_same_side_of_circles_meet
  on_circle_of_len_eq := Euclidean.on_circle_of_len_eq
  on_line_of_area_eq_zero := Euclidean.on_line_of_area_eq_zero
  on_line_of_between := Euclidean.on_line_of_between
  on_line_of_between_ends := Euclidean.on_line_of_between_ends
  outside_of_between := Euclidean.outside_of_between
  pasch1 := Euclidean.pasch1
  pasch2 := Euclidean.pasch2
  pasch3 := Euclidean.pasch3
  pasch4 := Euclidean.pasch4
  same_ray_of_angle_eq_zero := Euclidean.same_ray_of_angle_eq_zero
  same_side_or := Euclidean.same_side_or
  same_side_refl := Euclidean.same_side_refl
  same_side_symm := Euclidean.same_side_symm
  same_side_trans := Euclidean.same_side_trans
  superposition := Euclidean.superposition
  triple_incidence1 := triple_incidence1
  triple_incidence2 := triple_incidence2
  triple_incidence3 := triple_incidence3

end Model
