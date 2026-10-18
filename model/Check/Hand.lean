import Elements.Foundations.Tacit.Constructions
import Elements.Foundations.Tacit.Diagram
import Model.Hand

/-!
# Checking the hand translation against the library

`Model/Hand.lean` translates a few of the library's laws by hand. Here the library's own
words are put in for the signature's fields (`original`), and Lean is asked whether each
translated law, and each defined word it reaches, then is the library's declaration. Each
check is `rfl`: the kernel accepts it only if the two are the same proposition, up to
unfolding definitions. A translation that drops a guard, swaps two arguments or changes
the order of the binders fails here, and the build fails with it.

This file reads the library's axioms only through `type_of%`, which takes a declaration's
statement and does not use it. Nothing in `Model/` imports this file.
-/

namespace Check

/-- The library's kinds of magnitude, constructor by constructor. -/
def kind : Model.Kind → Elements.Kind
  | .length => .length
  | .angle => .angle
  | .area => .area

/-- The library's seventeen words, as a signature. Specializing a translated law here must
give back the original declaration. -/
noncomputable def original : Model.Signature where
  Point := Elements.Point
  Line := Elements.Line
  Circle := Elements.Circle
  OnLine := Elements.OnLine
  SameSide := Elements.SameSide
  Between := Elements.Between
  OnCircle := Elements.OnCircle
  InsideCircle := Elements.InsideCircle
  Centre := Elements.Centre
  MagnitudeImpl k := Elements.MagnitudeImpl (kind k)
  zero {k} := @Elements.Magnitude.zero (kind k)
  add {k} := @Elements.Magnitude.add (kind k)
  lt {k} := @Elements.Magnitude.lt (kind k)
  len := Elements.len
  ang := Elements.ang
  area := Elements.area
  rightAngle := Elements.rightAngle

/-! ## The defined words -/

example : original.OppositeSides = Elements.OppositeSides := rfl
example : original.OutsideCircle = Elements.OutsideCircle := rfl
example : original.CirclesMeet = Elements.CirclesMeet := rfl

/-! ## The laws -/

example : Model.Hand.circles_meet original = type_of% @Elements.Tacit.circles_meet := rfl

example : Model.Hand.circles_meet_of_on_inside_outside original =
    type_of% @Elements.Tacit.circles_meet_of_on_inside_outside := rfl

example : Model.Hand.circles_meet_same_side original =
    type_of% @Elements.Tacit.circles_meet_same_side := rfl

example : Model.Hand.circles_meet_opposite_side original =
    type_of% @Elements.Tacit.circles_meet_opposite_side := rfl

end Check
