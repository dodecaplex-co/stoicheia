module

/-!
# The signature: the seventeen words as fields

The main library takes seventeen words as `opaque` constants
(`Elements/Foundations/Words.lean` and `Magnitudes.lean`): Lean knows nothing of them but
what the axioms say. Nothing can be put in their place, so the library alone cannot show
that the axioms have a model. Here the same seventeen words are the fields of a structure,
`Signature`, and anything that fills the fields is a candidate reading of the words. A
reading is a model when it satisfies the laws, the translated axioms
([README](../README.md)).

Each field has the type of the opaque constant it stands for, with the words before it in
place of the library's: `Point`, `Line` and `Circle`; the six relations; the carrier of
each kind of magnitude with its zero, addition and order; and length, angle, area and the
right angle. Where the library's type uses its defined words `Magnitude k`, `Length`,
`Angle` and `Area`, the field's type writes out what they unfold to,
`(MagnitudeImpl k).type` at the matching kind, since a structure's fields cannot use a word
defined from those fields. So the types agree up to unfolding, which Lean checks when
`Check.original` fills the fields with the library's words. Besides that unfolding, the one
difference is the kinds of magnitude: the library's `Elements.Kind` lives in a file that
also declares the opaque words and their notation, so the model has its own copy,
`Model.Kind`, with the same three constructors, and the translation maps one to the other
by name.

This file is plain Lean, with no Mathlib and no import of the library, so that the
translation checks in `Check/` can read it beside the original declarations.
-/

@[expose] public section

namespace Model

/-- The kinds of magnitude, as in the library's `Elements.Kind`. -/
inductive Kind where
  | length
  | angle
  | area
  deriving DecidableEq

/-- A reading of the seventeen primitive words. Each field is named as the opaque
constant it stands for in `Elements` (`Magnitude.zero` becomes `zero`, and so on), and has
that constant's type with the earlier fields in place of the earlier words, and with
`Magnitude k`, `Length`, `Angle` and `Area` written out as `(MagnitudeImpl k).type` at the
matching kind: the same type up to unfolding. -/
structure Signature where
  /-- `Elements.Point`. -/
  Point : Type
  /-- `Elements.Line`. -/
  Line : Type
  /-- `Elements.Circle`. -/
  Circle : Type
  /-- `Elements.OnLine`. -/
  OnLine : Point → Line → Prop
  /-- `Elements.SameSide`. -/
  SameSide : Point → Point → Line → Prop
  /-- `Elements.Between`. -/
  Between : Point → Point → Point → Prop
  /-- `Elements.OnCircle`. -/
  OnCircle : Point → Circle → Prop
  /-- `Elements.InsideCircle`. -/
  InsideCircle : Point → Circle → Prop
  /-- `Elements.Centre`. -/
  Centre : Point → Circle → Prop
  /-- `Elements.MagnitudeImpl`: a nonempty carrier for each kind of magnitude. -/
  MagnitudeImpl : Kind → NonemptyType
  /-- `Elements.Magnitude.zero`. -/
  zero : {k : Kind} → (MagnitudeImpl k).type
  /-- `Elements.Magnitude.add`. -/
  add : {k : Kind} → (MagnitudeImpl k).type → (MagnitudeImpl k).type → (MagnitudeImpl k).type
  /-- `Elements.Magnitude.lt`. -/
  lt : {k : Kind} → (MagnitudeImpl k).type → (MagnitudeImpl k).type → Prop
  /-- `Elements.len`, written `‖A B‖` in the library. -/
  len : Point → Point → (MagnitudeImpl .length).type
  /-- `Elements.ang`, written `∠ A B C` in the library. -/
  ang : Point → Point → Point → (MagnitudeImpl .angle).type
  /-- `Elements.area`, written `△ A B C` in the library. -/
  area : Point → Point → Point → (MagnitudeImpl .area).type
  /-- `Elements.rightAngle`, written `∟` in the library. -/
  rightAngle : (MagnitudeImpl .angle).type

namespace Signature

variable (S : Signature)

/-- `Elements.Magnitude`: the carrier of a kind of magnitude.

It is reducible, as the library's is not, and for one reason. The fields write the carrier
out, so `S.len A B` has the type `(S.MagnitudeImpl .length).type`, not `S.Length`; Lean finds
the instances below for such a term, and so reads `S.len A B + S.len B C` or `S.ang A B C = 0`
at all, only when it can unfold `S.Magnitude k` to the carrier as it looks for them. The
definition is the library's all the same, which is what the round trips check. -/
abbrev Magnitude (k : Kind) : Type := (S.MagnitudeImpl k).type

/-- `Elements.Length`. -/
abbrev Length := S.Magnitude .length
/-- `Elements.Angle`. -/
abbrev Angle := S.Magnitude .angle
/-- `Elements.Area`. -/
abbrev Area := S.Magnitude .area

/-- `Elements.instAddMagnitude`. -/
instance instAddMagnitude {k : Kind} : Add (S.Magnitude k) := ⟨S.add⟩
/-- `Elements.instOfNatMagnitudeOfNatNat`. -/
instance instOfNatMagnitude {k : Kind} : OfNat (S.Magnitude k) 0 := ⟨S.zero⟩
/-- `Elements.instLTMagnitude`. -/
instance instLTMagnitude {k : Kind} : LT (S.Magnitude k) := ⟨S.lt⟩
/-- `Elements.instLEMagnitude`: `a ≤ b` means that `a` is not greater than `b`. -/
instance instLEMagnitude {k : Kind} : LE (S.Magnitude k) := ⟨fun a b => ¬ b < a⟩

end Signature

end Model
