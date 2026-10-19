module

public import Model.Laws
public import Model.Euclidean
public import Model.Euclidean.Avoidance
public import Model.Euclidean.CircleSides
public import Model.Euclidean.Circles
public import Model.Euclidean.Incidence
public import Model.Euclidean.Magnitudes

/-!
# The plane satisfies the laws

**This file is generated: do not edit it.** `Check/Generator.lean` writes it, and `lake build`
fails while it differs from what the generator writes. To write it again, run
`lake lean Check/Write.lean` in `model/`.

A theorem of `Model/Euclidean/` named as a field of `Laws` (`Euclidean.circles_meet` for the
field `circles_meet`) proves that law in the plane, and `euclidean_laws` gathers them; Lean
checks here that each proves the law the generator wrote.

So far 23 of the 87 laws are proved in the plane. Until the rest are,
`euclidean_laws` takes them as hypotheses, so that it states exactly what is proved: the plane
satisfies every law, given the 64 that are not yet proved in it. When none is left,
the generator writes it with no hypothesis, and `model_exists` after it.
-/

@[expose] public section

namespace Model

/-- **The plane satisfies the laws,** given the 64 not yet proved in it. -/
theorem euclidean_laws
    (Definition15 : Law.Definition15 Euclidean.plane)
    (Postulate3 : Law.Postulate3 Euclidean.plane)
    (Postulate4 : Law.Postulate4 Euclidean.plane)
    (Postulate5 : Law.Postulate5 Euclidean.plane)
    (adjacent_eq_of_right : Law.Tacit.adjacent_eq_of_right Euclidean.plane)
    (angle_add_of_inside : Law.Tacit.angle_add_of_inside Euclidean.plane)
    (angle_eq_of_same_rays : Law.Tacit.angle_eq_of_same_rays Euclidean.plane)
    (angle_eq_zero_of_same_ray : Law.Tacit.angle_eq_zero_of_same_ray Euclidean.plane)
    (angle_le_two_right : Law.Tacit.angle_le_two_right Euclidean.plane)
    (angle_symm : Law.Tacit.angle_symm Euclidean.plane)
    (area_add_of_between : Law.Tacit.area_add_of_between Euclidean.plane)
    (area_congruent : Law.Tacit.area_congruent Euclidean.plane)
    (area_degenerate : Law.Tacit.area_degenerate Euclidean.plane)
    (area_eq_zero_of_on_line : Law.Tacit.area_eq_zero_of_on_line Euclidean.plane)
    (area_rotate : Law.Tacit.area_rotate Euclidean.plane)
    (area_swap : Law.Tacit.area_swap Euclidean.plane)
    (between_cases : Law.Tacit.between_cases Euclidean.plane)
    (between_of_area_add : Law.Tacit.between_of_area_add Euclidean.plane)
    (between_of_between_left : Law.Tacit.between_of_between_left Euclidean.plane)
    (between_of_between_right : Law.Tacit.between_of_between_right Euclidean.plane)
    (between_of_inside_chord : Law.Tacit.between_of_inside_chord Euclidean.plane)
    (between_symm : Law.Tacit.between_symm Euclidean.plane)
    (circle_eq : Law.Tacit.circle_eq Euclidean.plane)
    (eq_of_len_eq_zero : Law.Tacit.eq_of_len_eq_zero Euclidean.plane)
    (exists_point_inside_circle : Law.Tacit.exists_point_inside_circle Euclidean.plane)
    (exists_point_on_circle : Law.Tacit.exists_point_on_circle Euclidean.plane)
    (exists_point_opposite_side : Law.Tacit.exists_point_opposite_side Euclidean.plane)
    (exists_point_outside_circle : Law.Tacit.exists_point_outside_circle Euclidean.plane)
    (exists_point_same_side : Law.Tacit.exists_point_same_side Euclidean.plane)
    (inside_of_angle_add : Law.Tacit.inside_of_angle_add Euclidean.plane)
    (inside_of_between : Law.Tacit.inside_of_between Euclidean.plane)
    (inside_of_len_lt : Law.Tacit.inside_of_len_lt Euclidean.plane)
    (len_add_of_between : Law.Tacit.len_add_of_between Euclidean.plane)
    (len_lt_of_inside : Law.Tacit.len_lt_of_inside Euclidean.plane)
    (len_self : Law.Tacit.len_self Euclidean.plane)
    (len_symm : Law.Tacit.len_symm Euclidean.plane)
    (line_circle_between : Law.Tacit.line_circle_between Euclidean.plane)
    (line_circle_beyond : Law.Tacit.line_circle_beyond Euclidean.plane)
    (line_meets_circle_of_inside : Law.Tacit.line_meets_circle_of_inside Euclidean.plane)
    (line_meets_circle_of_opposite_sides :
      Law.Tacit.line_meets_circle_of_opposite_sides Euclidean.plane)
    (ne_of_between : Law.Tacit.ne_of_between Euclidean.plane)
    (ne_of_between_ends : Law.Tacit.ne_of_between_ends Euclidean.plane)
    (not_between_of_between : Law.Tacit.not_between_of_between Euclidean.plane)
    (not_between_of_between_between : Law.Tacit.not_between_of_between_between Euclidean.plane)
    (not_on_line_of_same_side : Law.Tacit.not_on_line_of_same_side Euclidean.plane)
    (not_same_side_of_circles_meet : Law.Tacit.not_same_side_of_circles_meet Euclidean.plane)
    (on_circle_of_len_eq : Law.Tacit.on_circle_of_len_eq Euclidean.plane)
    (on_line_of_area_eq_zero : Law.Tacit.on_line_of_area_eq_zero Euclidean.plane)
    (on_line_of_between : Law.Tacit.on_line_of_between Euclidean.plane)
    (on_line_of_between_ends : Law.Tacit.on_line_of_between_ends Euclidean.plane)
    (outside_of_between : Law.Tacit.outside_of_between Euclidean.plane)
    (pasch1 : Law.Tacit.pasch1 Euclidean.plane)
    (pasch2 : Law.Tacit.pasch2 Euclidean.plane)
    (pasch3 : Law.Tacit.pasch3 Euclidean.plane)
    (pasch4 : Law.Tacit.pasch4 Euclidean.plane)
    (same_ray_of_angle_eq_zero : Law.Tacit.same_ray_of_angle_eq_zero Euclidean.plane)
    (same_side_or : Law.Tacit.same_side_or Euclidean.plane)
    (same_side_refl : Law.Tacit.same_side_refl Euclidean.plane)
    (same_side_symm : Law.Tacit.same_side_symm Euclidean.plane)
    (same_side_trans : Law.Tacit.same_side_trans Euclidean.plane)
    (superposition : Law.Tacit.superposition Euclidean.plane)
    (triple_incidence1 : Law.Tacit.triple_incidence1 Euclidean.plane)
    (triple_incidence2 : Law.Tacit.triple_incidence2 Euclidean.plane)
    (triple_incidence3 : Law.Tacit.triple_incidence3 Euclidean.plane) :
    Laws Euclidean.plane where
  Definition15 := Definition15
  Postulate1 := Euclidean.Postulate1
  Postulate2 := Euclidean.Postulate2
  Postulate3 := Postulate3
  Postulate4 := Postulate4
  Postulate5 := Postulate5
  add_assoc := Euclidean.add_assoc
  add_comm := Euclidean.add_comm
  add_lt_add_right := Euclidean.add_lt_add_right
  add_zero := Euclidean.add_zero
  adjacent_eq_of_right := adjacent_eq_of_right
  angle_add_of_inside := angle_add_of_inside
  angle_eq_of_same_rays := angle_eq_of_same_rays
  angle_eq_zero_of_same_ray := angle_eq_zero_of_same_ray
  angle_le_two_right := angle_le_two_right
  angle_symm := angle_symm
  area_add_of_between := area_add_of_between
  area_congruent := area_congruent
  area_degenerate := area_degenerate
  area_eq_zero_of_on_line := area_eq_zero_of_on_line
  area_rotate := area_rotate
  area_swap := area_swap
  between_cases := between_cases
  between_of_area_add := between_of_area_add
  between_of_between_left := between_of_between_left
  between_of_between_right := between_of_between_right
  between_of_inside_chord := between_of_inside_chord
  between_symm := between_symm
  centre_inside := Euclidean.centre_inside
  centre_unique := Euclidean.centre_unique
  circle_eq := circle_eq
  circles_meet := Euclidean.circles_meet
  circles_meet_of_on_inside_outside := Euclidean.circles_meet_of_on_inside_outside
  circles_meet_opposite_side := Euclidean.circles_meet_opposite_side
  circles_meet_same_side := Euclidean.circles_meet_same_side
  eq_of_len_eq_zero := eq_of_len_eq_zero
  exists_point := Euclidean.exists_point
  exists_point_between := Euclidean.exists_point_between
  exists_point_inside_circle := exists_point_inside_circle
  exists_point_on_circle := exists_point_on_circle
  exists_point_on_line := Euclidean.exists_point_on_line
  exists_point_on_line_off_line := Euclidean.exists_point_on_line_off_line
  exists_point_opposite_side := exists_point_opposite_side
  exists_point_outside_circle := exists_point_outside_circle
  exists_point_same_side := exists_point_same_side
  inside_not_on := Euclidean.inside_not_on
  inside_of_angle_add := inside_of_angle_add
  inside_of_between := inside_of_between
  inside_of_len_lt := inside_of_len_lt
  len_add_of_between := len_add_of_between
  len_lt_of_inside := len_lt_of_inside
  len_self := len_self
  len_symm := len_symm
  line_circle_between := line_circle_between
  line_circle_beyond := line_circle_beyond
  line_meets_circle_of_inside := line_meets_circle_of_inside
  line_meets_circle_of_opposite_sides := line_meets_circle_of_opposite_sides
  line_unique := Euclidean.line_unique
  lines_meet_of_opposite_sides := Euclidean.lines_meet_of_opposite_sides
  lt_irrefl := Euclidean.lt_irrefl
  lt_trans := Euclidean.lt_trans
  lt_trichotomy := Euclidean.lt_trichotomy
  ne_of_between := ne_of_between
  ne_of_between_ends := ne_of_between_ends
  not_between_of_between := not_between_of_between
  not_between_of_between_between := not_between_of_between_between
  not_lt_zero := Euclidean.not_lt_zero
  not_on_line_of_same_side := not_on_line_of_same_side
  not_same_side_of_circles_meet := not_same_side_of_circles_meet
  on_circle_of_len_eq := on_circle_of_len_eq
  on_line_of_area_eq_zero := on_line_of_area_eq_zero
  on_line_of_between := on_line_of_between
  on_line_of_between_ends := on_line_of_between_ends
  outside_of_between := outside_of_between
  pasch1 := pasch1
  pasch2 := pasch2
  pasch3 := pasch3
  pasch4 := pasch4
  same_ray_of_angle_eq_zero := same_ray_of_angle_eq_zero
  same_side_or := same_side_or
  same_side_refl := same_side_refl
  same_side_symm := same_side_symm
  same_side_trans := same_side_trans
  superposition := superposition
  triple_incidence1 := triple_incidence1
  triple_incidence2 := triple_incidence2
  triple_incidence3 := triple_incidence3

end Model
