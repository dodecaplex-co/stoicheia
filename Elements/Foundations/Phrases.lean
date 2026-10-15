import Elements.Foundations.Postulates

/-!
# Phrases

Euclid's statements use a handful of phrases he never defines, such as "on the
same side of AB", "AB is parallel to CD", "within the triangle", "the
parallelogram ABCD". Here they are spelled out once, in terms of the
undefined words, so that each proposition can be stated in Euclid's own
manner: with points named by letters, as in Heath's figures.

None of these is an assumption; they are only abbreviations.
-/

namespace Elements

/-- `P` and `Q` lie on the same side of the straight line `AB`. -/
def SameSideOf (P Q A B : Point) : Prop :=
  A ≠ B ∧ ∀ L : Line, OnLine A L → OnLine B L → SameSide P Q L

/-- `P` and `Q` lie on opposite sides of the straight line `AB`. -/
def OppositeSidesOf (P Q A B : Point) : Prop :=
  A ≠ B ∧ ∀ L : Line, OnLine A L → OnLine B L → OppositeSides P Q L

/-- `P` lies on the straight line from `A` through `B`, on `B`'s side of `A`
(it may be `B` itself, or nearer, or beyond). -/
def OnRay (P A B : Point) : Prop :=
  A ≠ B ∧ P ≠ A ∧ Collinear A B P ∧ ¬ Between P A B

/-- `D` lies within the triangle `ABC`. -/
def InsideTriangle (D A B C : Point) : Prop :=
  SameSideOf D A B C ∧ SameSideOf D B C A ∧ SameSideOf D C A B

/-- The straight lines `AB` and `CD` are parallel (Definition 23). -/
def AreParallel (A B C D : Point) : Prop :=
  A ≠ B ∧ C ≠ D ∧
    ∀ L M : Line, OnLine A L → OnLine B L → OnLine C M → OnLine D M → Parallel L M

/-- The parallelogram `ABCD`, its corners taken in order: `AB` is parallel to
`CD`, and `BC` to `DA`. Euclid does not define it; he first speaks of
"parallelogrammic areas" in I.34. -/
def Parallelogram (A B C D : Point) : Prop :=
  AreParallel A B C D ∧ AreParallel B C D A

/-- The area of the four-sided figure `ABCD` (corners in order), measured as the
two triangles into which its diameter `AC` cuts it. -/
noncomputable def quadArea (A B C D : Point) : Area := △ A B C + △ A C D

end Elements
