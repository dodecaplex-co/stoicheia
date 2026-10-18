import Staging.Stage2.Sums

/-!
# Staging: a rectilineal figure, given with its triangles

Brief 0006, stage 2. I.45 makes a parallelogram "equal to a given rectilineal figure", and
II.14 a square. Euclid's proof of I.45 joins DB and works with the triangles ABD, DBC; his
words take any figure. Here a figure is given as the triangles it is cut into, glued edge to
edge, as the owner decided (brief 0006): each new triangle is laid across a side of an
earlier one, and meets the triangles already there only along that side. Such a figure may
be convex or not.

**The convention, stated on the page:** the figure comes with its dissection. That every
rectilineal figure can be cut into triangles in this way is a separate theorem, not stated
here; and that two dissections of one figure give one area is a fact about area that no
statement here assumes.

"Meeting only along that side" is said with the predicates already in the foundations: a
point is within or on a triangle when it is inside it (`InsideTriangle`), on a side between
two corners (`Between`), or at a corner (`OnOrInsideTriangle`); a point is on a finite
straight line when it is an end or between the ends (`OnFiniteLine`). The new triangle `PQX`
meets the earlier triangles only along `PQ` when every point within or on it that is within
or on one of them is on the finite straight line `PQ`.

The definitions here are new words, and go to the foundations when adopted, with the lock
and a decisions entry (WORKFLOW, section 2). `Fitted.ne_nil` and `Fitted.triangle` only
unfold the definition, and are proved here; `Fitted.two`, which connects the definition with
Euclid's own figure, is a statement awaiting proof.
-/

namespace Elements

/-- `Y` lies on the finite straight line `PQ`: it is one of the ends, or between them. -/
def OnFiniteLine (Y P Q : Point) : Prop := Y = P ∨ Y = Q ∨ Between P Y Q

/-- `Y` lies within the triangle `ABC` or on its boundary: inside it, on one of its sides
between two corners, or at a corner. -/
def OnOrInsideTriangle (Y A B C : Point) : Prop :=
  InsideTriangle Y A B C ∨ Between A Y B ∨ Between B Y C ∨ Between C Y A ∨
    Y = A ∨ Y = B ∨ Y = C

/-- The triangle `t` has the corners `P`, `Q`, `R`: read from some corner, one way round or
the other, it is `(P, Q, R)`. So `PQ` is one of its sides, and `R` the corner opposite. -/
def Corners (t : Point × Point × Point) (P Q R : Point) : Prop :=
  t = (P, Q, R) ∨ t = (Q, R, P) ∨ t = (R, P, Q) ∨ t = (Q, P, R) ∨ t = (P, R, Q) ∨
    t = (R, Q, P)

/-- **Triangles fitted together into one rectilineal figure**, in the order listed.

* `single`: one triangle is a figure.
* `glue`: a figure, with a new triangle `PQX` laid against the side `PQ` of one of its
  triangles `t`, whose third corner is `R`. The new triangle lies across that side, `X` being
  on the other side of `PQ` from `R`; and it meets the triangles already there only along
  `PQ`: a point within or on the new triangle, and within or on one of the earlier ones,
  lies on the finite straight line `PQ`.

The new triangle goes at the end of the list. A figure made this way may be convex or not;
a ring of triangles closing up round a point is not made this way, for its last triangle
would meet the others along two sides. -/
inductive Fitted : List (Point × Point × Point) → Prop
  | single {A B C : Point} (h : Triangle A B C) : Fitted [(A, B, C)]
  | glue {ps : List (Point × Point × Point)} {t : Point × Point × Point} {P Q R X : Point}
      (hps : Fitted ps) (ht : t ∈ ps) (hside : Corners t P Q R)
      (hX : OppositeSidesOf X R P Q)
      (hmeet : ∀ Y : Point, OnOrInsideTriangle Y P Q X →
        ∀ s ∈ ps, OnOrInsideTriangle Y s.1 s.2.1 s.2.2 → OnFiniteLine Y P Q) :
      Fitted (ps ++ [(P, Q, X)])

/-- **A rectilineal figure, given with its triangles**: the triangles it is cut into, each
named by its three corners, with the proof that they fit together. -/
structure Rectilineal where
  /-- The triangles the figure is cut into, in the order they were fitted. -/
  pieces : List (Point × Point × Point)
  /-- They fit together into one figure. -/
  fitted : Fitted pieces

/-- **The area of a rectilineal figure**: the sum of its triangles. -/
noncomputable def Rectilineal.area (R : Rectilineal) : Area :=
  Magnitude.sum (R.pieces.map fun t => △ t.1 t.2.1 t.2.2)

/-- A figure has at least one triangle. -/
theorem Fitted.ne_nil {ps : List (Point × Point × Point)} (h : Fitted ps) : ps ≠ [] := by
  cases h with
  | single => exact List.cons_ne_nil _ _
  | glue => exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

/-- Each piece of a figure is a triangle: its corners are not on one straight line. -/
theorem Fitted.triangle {ps : List (Point × Point × Point)} (h : Fitted ps) :
    ∀ t ∈ ps, Triangle t.1 t.2.1 t.2.2 := by
  induction h with
  | single h =>
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact h
  | glue _ _ _ hX _ ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ih t ht
    · rw [List.mem_singleton] at ht
      subst ht
      exact hX.triangle

/-- **Euclid's figure is one.** The four-sided figure ABCD of I.45, with DB joined, is the
triangles ABD, DBC fitted together, when A and C are on opposite sides of BD: DBC is laid
against the side DB of ABD, and the two meet only along DB. -/
theorem Fitted.two {A B C D : Point} (hABD : Triangle A B D) (hAC : OppositeSidesOf C A D B) :
    Fitted [(A, B, D), (D, B, C)] := by
  sorry

end Elements
