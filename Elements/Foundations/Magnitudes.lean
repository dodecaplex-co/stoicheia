import Elements.Foundations.Words

/-!
# Magnitudes

Euclid compares lengths, angles and areas ("the straight line AB is equal to
the straight line CD", "the angle ABC is greater than the angle DEF", "the
triangle ABC is equal to the triangle DEF") without ever saying what they are.
He adds them, subtracts them, and compares them. We do the same: a `Magnitude`
of each kind can be added and compared, and nothing more.

There are no numbers here. A length is not a real number; it is just something
that can be added to another length and compared with it. That is Euclid's
point of view, and it keeps us honest: no coordinates can sneak in.

Following System E, each kind of magnitude has a `0`. Euclid's magnitudes are
always positive, and the zero is only a convenience: it lets us say that the
"line" from a point to itself has no length, or that a "triangle" whose corners
lie on one line has no area.

A sum of any number of magnitudes of one kind, `Magnitude.sum`, adds them one at a
time. II.1 cuts a straight line "into any number of segments whatever", and I.45 and
II.14 take a figure of any number of triangles; Lean says "any number" with a list.

The laws these magnitudes obey are in `Foundations/Tacit/Magnitudes.lean`.
-/

namespace Elements

/-- The kinds of magnitude in Book I. -/
inductive Kind where
  | length
  | angle
  | area
  deriving DecidableEq

/-- A hidden carrier for each kind of magnitude. -/
opaque MagnitudeImpl : Kind → NonemptyType

/-- A magnitude of a given kind: a length, an angle, or an area. -/
def Magnitude (k : Kind) : Type := (MagnitudeImpl k).type

instance {k : Kind} : Nonempty (Magnitude k) := (MagnitudeImpl k).property

namespace Magnitude

/-- The zero magnitude of each kind. -/
noncomputable opaque zero {k : Kind} : Magnitude k

/-- Putting two magnitudes of the same kind together. -/
noncomputable opaque add {k : Kind} : Magnitude k → Magnitude k → Magnitude k

/-- `a < b`: the magnitude `a` is less than the magnitude `b`. -/
opaque lt {k : Kind} : Magnitude k → Magnitude k → Prop

end Magnitude

noncomputable instance {k : Kind} : Add (Magnitude k) := ⟨Magnitude.add⟩
noncomputable instance {k : Kind} : OfNat (Magnitude k) 0 := ⟨Magnitude.zero⟩
instance {k : Kind} : LT (Magnitude k) := ⟨Magnitude.lt⟩

/-- `a ≤ b` means "`a` is not greater than `b`". -/
instance {k : Kind} : LE (Magnitude k) := ⟨fun a b => ¬ b < a⟩

/-- **The sum of a list of magnitudes** of one kind: nothing for the empty list, and
otherwise the first added to the sum of the rest. So `Magnitude.sum [a, b, c]` is
`a + (b + (c + 0))`, which is `a + b + c`. -/
noncomputable def Magnitude.sum {k : Kind} : List (Magnitude k) → Magnitude k
  | [] => 0
  | a :: as => a + Magnitude.sum as

/-- A length (of a finite straight line). -/
abbrev Length := Magnitude .length
/-- An angle. -/
abbrev Angle := Magnitude .angle
/-- An area. -/
abbrev Area := Magnitude .area

/-- The length of the finite straight line from `A` to `B`. Written `‖A B‖`. -/
noncomputable opaque len : Point → Point → Length

/-- The angle `ABC`, with vertex `B`. Written `∠ A B C`. -/
noncomputable opaque ang : Point → Point → Point → Angle

/-- The area of the triangle `ABC`. Written `△ A B C`. -/
noncomputable opaque area : Point → Point → Point → Area

/-- The size of a right angle. Postulate 4 says all right angles are equal, so
it makes sense to have one name for their common size. Written `∟`. -/
noncomputable opaque rightAngle : Angle

@[inherit_doc] notation:max "‖" A:max B:max "‖" => len A B
@[inherit_doc] notation:max "∠" A:max B:max C:max => ang A B C
@[inherit_doc] notation:max "△" A:max B:max C:max => area A B C
@[inherit_doc] notation "∟" => rightAngle

end Elements
