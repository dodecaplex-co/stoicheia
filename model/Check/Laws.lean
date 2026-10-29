import Elements.Foundations.CommonNotions
import Elements.Foundations.Definitions
import Elements.Foundations.DefinitionsII
import Elements.Foundations.DefinitionsIII
import Elements.Foundations.Figures
import Elements.Foundations.Magnitudes
import Elements.Foundations.Phrases
import Elements.Foundations.Postulates
import Elements.Foundations.Superposition.Restriction
import Elements.Foundations.Superposition.Semantics
import Elements.Foundations.Superposition.Soundness
import Elements.Foundations.Superposition.Syntax
import Elements.Foundations.Tacit.Constructions
import Elements.Foundations.Tacit.Diagram
import Elements.Foundations.Tacit.Magnitudes
import Elements.Foundations.Tacit.Metric
import Elements.Foundations.Tacit.Superposition
import Elements.Foundations.Tacit.Transfer
import Elements.Foundations.Words
import Model.Laws
import Check.Original

/-!
# The generated laws and words, checked by the kernel

**This file is generated: do not edit it.** `Check/Generator.lean` writes it with
`Model/Laws.lean`; to write it again, run `lake lean Check/Write.lean` in `model/`.

For each word and each law of `Model/Laws.lean`, the library's own words are put back for the
signature (`original`), and the kernel is asked whether the result is the library's
declaration. Each check is `rfl`: the kernel accepts it only if the two are the same
proposition, up to unfolding definitions. A law over every kind of magnitude makes the same
check up to relabelling the kinds, since the model's `Kind` is a copy of the library's: each
direction is the other statement at the matching kind. The words written by hand in
`Model/Signature.lean` are checked in `Check/Hand.lean`.

`Check/RoundTrip.lean` makes the stricter check by syntax, which also sees binder kinds and the
order of the binders. This file reads the library's axioms only through `type_of%`, which takes
a declaration's statement and does not use it.
-/

namespace Check

open Model

/-! ## The words -/

example : original.CirclesMeet = Elements.CirclesMeet := rfl
example : original.Collinear = Elements.Collinear := rfl
example : original.IsRightAngle = Elements.IsRightAngle := rfl
example : original.LinesMeet = Elements.LinesMeet := rfl
example : original.OppositeSides = Elements.OppositeSides := rfl
example : original.OutsideCircle = Elements.OutsideCircle := rfl
example : original.primitives = Elements.primitives := rfl

/-! ## The laws -/

example : Law.Definition15 original = type_of% @Elements.Definition15 := rfl

example : Law.Postulate1 original = type_of% @Elements.Postulate1 := rfl

example : Law.Postulate2 original = type_of% @Elements.Postulate2 := rfl

example : Law.Postulate3 original = type_of% @Elements.Postulate3 := rfl

example : Law.Postulate4 original = type_of% @Elements.Postulate4 := rfl

example : Law.Postulate5 original = type_of% @Elements.Postulate5 := rfl

example : Law.Tacit.add_assoc original ↔ type_of% @Elements.Tacit.add_assoc :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Law.Tacit.add_comm original ↔ type_of% @Elements.Tacit.add_comm :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Law.Tacit.add_lt_add_right original ↔ type_of% @Elements.Tacit.add_lt_add_right :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Law.Tacit.add_zero original ↔ type_of% @Elements.Tacit.add_zero :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Law.Tacit.angle_add_of_inside original =
    type_of% @Elements.Tacit.angle_add_of_inside := rfl

example : Law.Tacit.angle_eq_of_same_rays original =
    type_of% @Elements.Tacit.angle_eq_of_same_rays := rfl

example : Law.Tacit.angle_eq_zero_of_same_ray original =
    type_of% @Elements.Tacit.angle_eq_zero_of_same_ray := rfl

example : Law.Tacit.angle_le_two_right original = type_of% @Elements.Tacit.angle_le_two_right := rfl

example : Law.Tacit.angle_symm original = type_of% @Elements.Tacit.angle_symm := rfl

example : Law.Tacit.area_add_of_between original =
    type_of% @Elements.Tacit.area_add_of_between := rfl

example : Law.Tacit.area_congruent original = type_of% @Elements.Tacit.area_congruent := rfl

example : Law.Tacit.area_degenerate original = type_of% @Elements.Tacit.area_degenerate := rfl

example : Law.Tacit.area_eq_zero_of_on_line original =
    type_of% @Elements.Tacit.area_eq_zero_of_on_line := rfl

example : Law.Tacit.area_rotate original = type_of% @Elements.Tacit.area_rotate := rfl

example : Law.Tacit.between_cases original = type_of% @Elements.Tacit.between_cases := rfl

example : Law.Tacit.between_symm original = type_of% @Elements.Tacit.between_symm := rfl

example : Law.Tacit.circle_eq original = type_of% @Elements.Tacit.circle_eq := rfl

example : Law.Tacit.circles_meet original = type_of% @Elements.Tacit.circles_meet := rfl

example : Law.Tacit.circles_meet_same_side original =
    type_of% @Elements.Tacit.circles_meet_same_side := rfl

example : Law.Tacit.exists_centre original = type_of% @Elements.Tacit.exists_centre := rfl

example : Law.Tacit.exists_point original = type_of% @Elements.Tacit.exists_point := rfl

example : Law.Tacit.exists_point_inside_circle original =
    type_of% @Elements.Tacit.exists_point_inside_circle := rfl

example : Law.Tacit.exists_point_on_line original =
    type_of% @Elements.Tacit.exists_point_on_line := rfl

example : Law.Tacit.len_add_of_between original = type_of% @Elements.Tacit.len_add_of_between := rfl

example : Law.Tacit.len_self original = type_of% @Elements.Tacit.len_self := rfl

example : Law.Tacit.len_symm original = type_of% @Elements.Tacit.len_symm := rfl

example : Law.Tacit.line_circle_between original =
    type_of% @Elements.Tacit.line_circle_between := rfl

example : Law.Tacit.line_circle_beyond original = type_of% @Elements.Tacit.line_circle_beyond := rfl

example : Law.Tacit.line_unique original = type_of% @Elements.Tacit.line_unique := rfl

example : Law.Tacit.lines_meet_of_opposite_sides original =
    type_of% @Elements.Tacit.lines_meet_of_opposite_sides := rfl

example : Law.Tacit.lt_irrefl original ↔ type_of% @Elements.Tacit.lt_irrefl :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Law.Tacit.lt_trans original ↔ type_of% @Elements.Tacit.lt_trans :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Law.Tacit.lt_trichotomy original ↔ type_of% @Elements.Tacit.lt_trichotomy :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Law.Tacit.not_between_of_between original =
    type_of% @Elements.Tacit.not_between_of_between := rfl

example : Law.Tacit.not_lt_zero original ↔ type_of% @Elements.Tacit.not_lt_zero :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Law.Tacit.not_on_line_of_same_side original =
    type_of% @Elements.Tacit.not_on_line_of_same_side := rfl

example : Law.Tacit.on_line_of_area_eq_zero original =
    type_of% @Elements.Tacit.on_line_of_area_eq_zero := rfl

example : Law.Tacit.pasch2 original = type_of% @Elements.Tacit.pasch2 := rfl

example : Law.Tacit.radius_ne_zero original = type_of% @Elements.Tacit.radius_ne_zero := rfl

example : Law.Tacit.same_ray_of_angle_eq_zero original =
    type_of% @Elements.Tacit.same_ray_of_angle_eq_zero := rfl

example : Law.Tacit.same_side_trans original = type_of% @Elements.Tacit.same_side_trans := rfl

example : Law.Tacit.superposition original = type_of% @Elements.Tacit.superposition := rfl

end Check
