import Elements.Foundations.Magnitudes
import Model.Signature

/-!
# The library's words, as a signature

`original` is the signature whose fields are the library's own words: `Point` is
`Elements.Point`, and so on. Putting it for `S` in a translated law must give back the
library's declaration. `Check/Hand.lean` asks the kernel so of each law translated by hand,
and the generated `Check/Laws.lean` of each law the generator writes; `Check/RoundTrip.lean`
checks that each field here is the library's word.

This file reads only the library's words, and none of its axioms. Nothing in `Model/` imports
it.
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

end Check
