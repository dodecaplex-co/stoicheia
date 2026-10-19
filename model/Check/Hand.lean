import Elements.Figure.Basics
import Elements.Foundations.Tacit.Constructions
import Elements.Foundations.Tacit.Diagram
import Elements.Foundations.Tacit.Magnitudes
import Model.Hand
import Check.Original
import Check.Generator

/-!
# Checking the hand translation against the library

`Model/Hand.lean` translates a few of the library's laws by hand, and `Model/Signature.lean`
writes by hand the words behind the magnitudes. Here the library's own words are put in for
the signature's fields (`original`, in `Check/Original.lean`), and Lean is asked whether each
law translated by hand, and each word written by hand, then is the library's declaration.
Each check is `rfl`: the kernel accepts it only if the two are the same proposition, up to
unfolding definitions. (The laws that quantify over the kind of magnitude make the same
check up to relabelling the kinds, as their section says.) A translation that drops a
guard, swaps two arguments or changes the order of the binders fails here, and the build
fails with it. Last, each law translated by hand is checked against the law the generator
writes for it in `Model/Laws.lean`, the field of `Laws` it stands for.

This file reads the library's axioms only through `type_of%`, which takes a declaration's
statement and does not use it. Nothing in `Model/` imports this file.
-/

namespace Check

/-! ## The defined words

The words of `Model/Signature.lean` behind the magnitudes, each at the matching kind, and
the three words the laws below reach, which were written here by hand before the generator
wrote them in `Model/Laws.lean` (`Check/Laws.lean` checks every word it writes). -/

example (k : Model.Kind) : original.Magnitude k = Elements.Magnitude (kind k) := rfl
example : original.Length = Elements.Length := rfl
example : original.Angle = Elements.Angle := rfl
example : original.Area = Elements.Area := rfl
example (k : Model.Kind) :
    original.instAddMagnitude (k := k) = Elements.instAddMagnitude (k := kind k) := rfl
example (k : Model.Kind) :
    original.instOfNatMagnitude (k := k) = Elements.instOfNatMagnitudeOfNatNat (k := kind k) :=
  rfl
example (k : Model.Kind) :
    original.instLTMagnitude (k := k) = Elements.instLTMagnitude (k := kind k) := rfl
example (k : Model.Kind) :
    original.instLEMagnitude (k := k) = Elements.instLEMagnitude (k := kind k) := rfl

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

/-! ## The magnitude laws

These quantify over the kind of magnitude, and the model's `Kind` is a copy of the
library's, so their round trip is an equivalence, not `rfl`. Each direction is the other
statement itself, put at the matching kind, with no other step: so this is the same check
as `rfl`, up to relabelling the kinds, and the kernel checks that every instance, behind
`+`, `0` and `<`, comes back as the library's. -/

example : Model.Hand.add_assoc original ↔ type_of% @Elements.Tacit.add_assoc :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Model.Hand.add_comm original ↔ type_of% @Elements.Tacit.add_comm :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Model.Hand.add_lt_add_right original ↔ type_of% @Elements.Tacit.add_lt_add_right :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Model.Hand.add_zero original ↔ type_of% @Elements.Tacit.add_zero :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Model.Hand.lt_irrefl original ↔ type_of% @Elements.Tacit.lt_irrefl :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Model.Hand.lt_trans original ↔ type_of% @Elements.Tacit.lt_trans :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Model.Hand.lt_trichotomy original ↔ type_of% @Elements.Tacit.lt_trichotomy :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

example : Model.Hand.not_lt_zero original ↔ type_of% @Elements.Tacit.not_lt_zero :=
  ⟨fun h {k} => by
    cases k with
    | length => exact @h .length
    | angle => exact @h .angle
    | area => exact @h .area,
    fun h => h⟩

/-! ## The hand translations against the generated laws

Each law translated by hand in `Model/Hand.lean` is the law the generator writes for it, over
any signature: the field of `Laws` it stands for. (`Check/RoundTrip.lean` compares the two by
syntax as well, binder kinds and names included.) -/

example (S : Model.Signature) : Model.Hand.circles_meet S = Model.Law.Tacit.circles_meet S :=
  rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.circles_meet_of_on_inside_outside
  ``Elements.Tacit.circles_meet_of_on_inside_outside)
example (S : Model.Signature) : Model.Hand.circles_meet_same_side S =
    Model.Law.Tacit.circles_meet_same_side S := rfl
run_cmd (Check.Generator.comparePlanted ``Model.Hand.circles_meet_opposite_side
  ``Elements.Tacit.circles_meet_opposite_side)
example (S : Model.Signature) : Model.Hand.add_assoc S = Model.Law.Tacit.add_assoc S := rfl
example (S : Model.Signature) : Model.Hand.add_comm S = Model.Law.Tacit.add_comm S := rfl
example (S : Model.Signature) : Model.Hand.add_lt_add_right S =
    Model.Law.Tacit.add_lt_add_right S := rfl
example (S : Model.Signature) : Model.Hand.add_zero S = Model.Law.Tacit.add_zero S := rfl
example (S : Model.Signature) : Model.Hand.lt_irrefl S = Model.Law.Tacit.lt_irrefl S := rfl
example (S : Model.Signature) : Model.Hand.lt_trans S = Model.Law.Tacit.lt_trans S := rfl
example (S : Model.Signature) : Model.Hand.lt_trichotomy S = Model.Law.Tacit.lt_trichotomy S :=
  rfl
example (S : Model.Signature) : Model.Hand.not_lt_zero S = Model.Law.Tacit.not_lt_zero S := rfl

end Check
