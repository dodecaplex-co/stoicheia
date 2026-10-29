import Elements.Figure.Basics
import Elements.BookI.Prop07
import Elements.Figure.Circles
import Elements.BookIII.Prop02
import Check.Hand
import Check.Generator
import Model.Laws.intersections

/-!
# Checking the hand-translated intersection rules against the library

`Model/Laws/intersections.lean` translates the intersection rules and the circle rules by
hand. As in `Check/Hand.lean`, the library's own words are put in for the signature's
fields (`original`), and Lean is asked whether each translated law, and each defined word
it reaches, is then the library's declaration. Each kernel check is `rfl`: the kernel accepts it
only if the two are the same proposition, up to unfolding definitions, so a dropped guard,
two swapped arguments or a change in the order of the binders fails here, and the build
with it. The generator's syntactic round trip checks binder kinds for the locked laws
imported under their original names in `Model.Hand`; the comparisons with generated laws
below also cover the copies kept under suffixed names, up to unfolding.

The kernel comparisons read the library's declarations through `type_of%`. For the
properties retained through axiom retirement, `comparePlanted` also translates the
hand definition back and compares it directly with the declaration's type, including
binder kinds. This includes Intersections 2 and 3: before translating their hand
`LineMeetsCircle`, it compares that word's type and body with the library's definition,
including binder kinds and without unfolding. The rule comparisons read only the
statement, whether it is an axiom or a theorem. A planted explicit binder in Intersection 3,
kept in `Check/RoundTrip.lean` with the other planted faults, passes `rfl` but must be
refused by the syntactic comparison. Nothing in `Model/` imports this file.
-/

namespace Check

/-! ## The defined words -/

example : original.LinesMeet = Elements.LinesMeet := rfl

/-! ## The intersection rules -/

example : Model.Hand.lines_meet_of_opposite_sides_intersections original =
    type_of% @Elements.Tacit.lines_meet_of_opposite_sides := rfl

example : Model.Hand.line_meets_circle_of_opposite_sides original =
    type_of% @Elements.Tacit.line_meets_circle_of_opposite_sides := rfl

example : Model.Hand.line_meets_circle_of_inside original =
    type_of% @Elements.Tacit.line_meets_circle_of_inside := rfl

example : Model.Hand.line_circle_between original =
    type_of% @Elements.Tacit.line_circle_between := rfl

example : Model.Hand.line_circle_beyond original =
    type_of% @Elements.Tacit.line_circle_beyond := rfl

/-! ## The circle rules -/

example : Model.Hand.between_of_inside_chord_intersections original =
    type_of% @Elements.Tacit.between_of_inside_chord := rfl

example : Model.Hand.inside_of_between_intersections original =
    type_of% @Elements.Tacit.inside_of_between := rfl

example : Model.Hand.outside_of_between_intersections original =
    type_of% @Elements.Tacit.outside_of_between := rfl

example : Model.Hand.not_same_side_of_circles_meet_intersections original =
    type_of% @Elements.Tacit.not_same_side_of_circles_meet := rfl

example (S : Model.Signature) : Model.Hand.Intersections.LinesMeet S = S.LinesMeet := rfl
example : Model.Hand.Intersections.LinesMeet original = Elements.LinesMeet := rfl
example : Model.Hand.Intersections.LineMeetsCircle original = Elements.LineMeetsCircle := rfl

/-! ## The hand translations against generated laws or declaration types -/

example (S : Model.Signature) : Model.Hand.lines_meet_of_opposite_sides_intersections S =
    Model.Law.Tacit.lines_meet_of_opposite_sides S := rfl
/- Intersections 2 and 3 reach the hand `LineMeetsCircle`, whose type and body are checked
before it is translated back. Both rules are compared with their declaration types,
including binder kinds, even though no locked law reaches this word. -/
run_cmd (Check.Generator.comparePlanted ``Model.Hand.line_meets_circle_of_opposite_sides
  ``Elements.Tacit.line_meets_circle_of_opposite_sides)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.line_meets_circle_of_inside
  ``Elements.Tacit.line_meets_circle_of_inside)
example (S : Model.Signature) : Model.Hand.line_circle_between S =
    Model.Law.Tacit.line_circle_between S := rfl
example (S : Model.Signature) : Model.Hand.line_circle_beyond S =
    Model.Law.Tacit.line_circle_beyond S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.between_of_inside_chord_intersections
  ``Elements.Tacit.between_of_inside_chord)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.inside_of_between_intersections
  ``Elements.Tacit.inside_of_between)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.outside_of_between_intersections
  ``Elements.Tacit.outside_of_between)
run_cmd (Check.Generator.comparePlanted ``Model.Hand.not_same_side_of_circles_meet_intersections
  ``Elements.Tacit.not_same_side_of_circles_meet)

end Check
