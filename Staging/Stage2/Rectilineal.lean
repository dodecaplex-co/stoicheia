import Staging.Stage2.Sums

/-!
# Staging: a rectilineal figure, given with its triangles

Brief 0006, stage 2. I.45 makes a parallelogram "equal to a given rectilineal figure", and
II.14 a square. Euclid's proof of I.45 joins DB and works with the triangles ABD and DBC;
his words take any figure. Here a figure is given with a division of it into triangles, in
one of two forms. Any division at all is taken as triangles that lie apart (`Apart`), below.
A figure with one boundary may also be given as triangles fitted together in a suitable
order (`Fitted`): each new triangle is laid across a side of an earlier one, and meets the
triangles already there only along that side. The figure is the triangles together. Such a
figure may be convex or not, and need have no corner from which the straight lines to the
others divide it.

**The convention, stated on the page:** the figure comes with its division, and the division
is checked. FORMALIZATION, section 4, accepts a finite dissection supplied as input when it
is stated and checked geometrically. For any division the check is `Apart`: no point is
inside two of the triangles. For a figure with one boundary it may also be `Fitted`: the
triangles do not overlap (`Fitted.inside_pairwise`), and each meets the figure already made
only along one side, so they make up one figure. Either way their sum is what Euclid calls
the whole of it. Two things are not stated here. That every rectilineal figure can be cut
into triangles in these ways is a separate theorem. That two divisions of one figure give
one sum is the step Euclid takes for granted, which David Hilbert proved, for his measure of
area; it goes in the gap catalogue (brief 0006), and no statement here assumes it. So "equal
to the given rectilineal figure", in I.45 and II.14, means equal to the sum of the triangles
the figure is given with, and the records of I.45 and II.14 carry that as the tag
`figure-with-dissection`.

**A figure with a hole, or in pieces.** Euclid defines a figure as "that which is contained
by any boundary or boundaries" (Definition I.14), so a square with a smaller square cut from
its middle is a rectilineal figure, contained by two boundaries. Gluing cannot make it: a
ring of triangles round the hole cannot close. So the figure is also taken given with
triangles that lie apart (`Apart`): no point is inside two of them, and nothing else is
asked. The figure is the triangles together, which may have a hole, touch itself at a
corner, or be in more than one piece, which only claims more. Lying apart is exactly what
makes the sum of the triangles the area of the figure they make up, and a fitted figure's
triangles lie apart (`Fitted.inside_pairwise`), so `Apart` takes every figure `Fitted` takes.
`Fitted` stays, as the figure with one boundary, the triangles fitted together.

**Euclid's and Byrne's division** is one such figure. Euclid's DB, drawn from the corner D
of ABCD, and Byrne's two straight lines from one corner of his figure (1847, p. 46), cut it
into triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ from one corner A₀. `Fitted.fan` says when those
triangles are a figure in this sense: each two neighbouring triangles lie on opposite sides
of the straight line A₀Aᵢ they share, and the angles A₁A₀A₂, …, Aₙ₋₁A₀Aₙ together are less
than four right angles. Without the two conditions the triangles from A₀ may overlap or
reach outside the figure, and their sum need not equal the area of their union: a pentagon
whose second and fourth corners lie on one side of the straight line from the first corner
to the third has three triangles from the first corner together greater than it, and the
first condition fails there (brief 0006 gives its corners). That the figure the fan's
triangles make is the one bounded by the closed line A₀A₁…AₙA₀, its corners in that order,
is a reading of the conditions, true in the plane, and is not stated in Lean: `Fitted.fan`
says only that the triangles fit together into one figure.

"Meeting only along that side" is said with the predicates already in the foundations: a
point is within or on a triangle when it is inside it (`InsideTriangle`), on a side between
two corners (`Between`), or at a corner (`OnOrInsideTriangle`); a point is on a finite
straight line when it is an end or between the ends (`OnFiniteLine`). The new triangle `PQX`
meets the earlier triangles only along `PQ` when every point within or on it that is within
or on one of them is on the finite straight line `PQ`.

The definitions here (`Apart` and `Apart.area` among them) are new words, and go to the
foundations when adopted, with the lock and a decisions entry (WORKFLOW, section 2).
`Fitted.ne_nil`, `Fitted.triangle` and `Fitted.inside_pairwise` follow from the definition,
and are proved here; they go to Book Zero (`Elements/Figure/Rectilineal.lean`).
`Fitted.fan`, which connects the definition with Euclid's and Byrne's division, is a
statement awaiting proof.
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

The new triangle goes at the end of the list. A figure made this way may be convex or not.
Every figure made this way is bounded by one closed line that neither crosses nor touches
itself, with no hole; and every such figure can be cut this way, since it can be cut into
triangles by straight lines joining its corners, and those triangles, listed so that each
after the first shares a side with one before it, with each later triangle named so that
its attached side is its first two corners, satisfy the rule: a later triangle meets an
earlier one that is not its neighbour only at an end of the side it is glued along.
Neither fact is stated in Lean. That no point is inside two of the triangles is stated, and
proved (`Fitted.inside_pairwise`). So every such figure has a division that is fitted, but
not every division of it is: a ring of triangles round a point inside it is not (below),
nor is a list whose later triangle is named from the wrong corner, as the square ABCD cut
along AC and listed ABC, ADC (the second must be named ACD).

A ring of triangles closing up round a point, or round a hole, is not made this way, for its
last triangle would meet the others along two sides. A triangle laid against part of a
side, or against two sides in line, is not glued this way either; its figure is cut
differently. A figure with a hole cannot be cut so as to be glued. Any division of any
figure, with a hole or without, is taken given with triangles that lie apart (`Apart`), and
a fitted figure's triangles lie apart too. -/
inductive Fitted : List (Point × Point × Point) → Prop
  | single {A B C : Point} (h : Triangle A B C) : Fitted [(A, B, C)]
  | glue {ps : List (Point × Point × Point)} {t : Point × Point × Point} {P Q R X : Point}
      (hps : Fitted ps) (ht : t ∈ ps) (hside : Corners t P Q R)
      (hX : OppositeSidesOf X R P Q)
      (hmeet : ∀ Y : Point, OnOrInsideTriangle Y P Q X →
        ∀ s ∈ ps, OnOrInsideTriangle Y s.1 s.2.1 s.2.2 → OnFiniteLine Y P Q) :
      Fitted (ps ++ [(P, Q, X)])

/-- **A rectilineal figure with one boundary, given with its triangles fitted together**
(Definition I.19: "Rectilineal figures are those which are contained by straight lines"):
the triangles it is cut into, each named by its three corners, in an order in which they
fit together, with the proof that they do. The figure is the triangles together. -/
structure Rectilineal where
  /-- The triangles the figure is cut into, in the order they were fitted. -/
  pieces : List (Point × Point × Point)
  /-- They fit together into one figure. -/
  fitted : Fitted pieces

/-- **The area of a rectilineal figure, as given**: the sum of the triangles it is given
with, which do not overlap (`Fitted.inside_pairwise`) and make up the figure. That another
division of the same figure gives the same sum is not proved here (brief 0006, the gap
catalogue), so this is the area of the figure with its division, not yet a measure of the
figure alone. -/
noncomputable def Rectilineal.area (R : Rectilineal) : Area :=
  Magnitude.sum (R.pieces.map fun t => △ t.1 t.2.1 t.2.2)

/-- **A rectilineal figure, given with triangles that lie apart** (Definition I.14: a figure
is "that which is contained by any boundary or boundaries"; Definition I.19: rectilineal
figures are "those which are contained by straight lines"): any division of it into
triangles, each named by its three corners, at least one; each a triangle; and no point
inside two of them. The figure is the triangles together. It may have a hole, as a square
with a smaller square cut from its middle has, may touch itself at a corner, and may be in
more than one piece. No order of the triangles is asked, and a triangle may lie against part
of a side of another. A figure given by gluing is one of these, its triangles lying apart by
`Fitted.inside_pairwise`. That every rectilineal figure, with any boundaries, can be cut
into triangles that lie apart is not stated in Lean. -/
structure Apart where
  /-- The triangles the figure is cut into. -/
  pieces : List (Point × Point × Point)
  /-- There is at least one. -/
  ne : pieces ≠ []
  /-- Each is a triangle: its corners are not on one straight line. -/
  triangle : ∀ t ∈ pieces, Triangle t.1 t.2.1 t.2.2
  /-- No point is inside two of them. -/
  apart : pieces.Pairwise fun s s' => ∀ Y : Point,
    InsideTriangle Y s.1 s.2.1 s.2.2 → ¬ InsideTriangle Y s'.1 s'.2.1 s'.2.2

/-- **The area of a figure given with triangles that lie apart, as given**: the sum of its
triangles. As with `Rectilineal.area`, that another division of the same figure gives the
same sum is not proved here (brief 0006, the gap catalogue), so this is the area of the
figure with its division, not yet a measure of the figure alone. -/
noncomputable def Apart.area (R : Apart) : Area :=
  Magnitude.sum (R.pieces.map fun t => △ t.1 t.2.1 t.2.2)

/-- **The corners three at a time**: each corner of the list with the next two. The triples
of `[A₁, A₂, A₃, A₄]` are A₁A₂A₃ and A₂A₃A₄. In a division from one corner A₀, the middle
corner of each triple is the far end of the straight line A₀Aᵢ that two neighbouring
triangles share, and the other two are their third corners. -/
def triples : List Point → List (Point × Point × Point)
  | p :: q :: r :: rest => (p, q, r) :: triples (q :: r :: rest)
  | _ => []

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

/-- **The triangles of a figure do not overlap**: no point is inside two of them. Each new
triangle meets the earlier ones only along the side it is glued to, and a point inside a
triangle is off its sides. This is what makes the sum of the triangles the area of the figure
they make up (`Rectilineal.area`), and it pins that meaning of `Fitted` against a later
change of the definition. -/
theorem Fitted.inside_pairwise {ps : List (Point × Point × Point)} (h : Fitted ps) :
    ps.Pairwise (fun s s' => ∀ Y : Point,
      InsideTriangle Y s.1 s.2.1 s.2.2 → ¬ InsideTriangle Y s'.1 s'.2.1 s'.2.2) := by
  induction h with
  | single _ => exact List.pairwise_singleton _ _
  | @glue ps t P Q R X hps ht hside hX hmeet ih =>
    rw [List.pairwise_append]
    refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
    intro s hs s' hs' Y hYs hYn
    rw [List.mem_singleton] at hs'
    subst hs'
    have hY := hmeet Y (Or.inl hYn) s hs (Or.inl hYs)
    obtain ⟨L, hP, hQ⟩ := Postulate1 P Q hX.1
    have hoff : ¬ OnLine Y L := Tacit.not_on_line_of_same_side (hYn.2.2.sameSide hP hQ)
    rcases hY with rfl | rfl | hb
    · exact hoff hP
    · exact hoff hQ
    · exact hoff (Tacit.on_line_of_between_ends hb hP hQ)

/-- **Euclid's and Byrne's division is a figure, when it is checked.** A figure given by its
corners A₀, A₁, A₂, …, Aₙ, the list `ps` being A₃, …, Aₙ, and divided by the straight lines
from A₀ into the triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ, one on each side
`segments (A₁ :: A₂ :: ps)`. Suppose each is a triangle; each two neighbouring triangles,
A₀Aᵢ₋₁Aᵢ and A₀AᵢAᵢ₊₁, lie on opposite sides of the straight line A₀Aᵢ they share, that is,
Aᵢ₋₁ and Aᵢ₊₁ are on opposite sides of it (one condition for each of `triples (A₁ :: A₂ ::
ps)`); and the angles A₁A₀A₂, A₂A₀A₃, …, Aₙ₋₁A₀Aₙ at A₀ together are less than four right
angles. Then those triangles, in that order, are fitted together into one figure: each is
laid across the straight line A₀Aᵢ against the one before it, and meets the earlier ones only
along that straight line. The figure they make is read as the figure with corners A₀, A₁, …,
Aₙ in order round it; that its boundary is the closed line A₀A₁…AₙA₀ is not stated in Lean.

The two conditions are what make the triangles turn one way round A₀ and not come round on
themselves, so that they do not overlap. Euclid's ABCD, divided from D by DB, is the figure
with corners D, A, B, C: A and C are on opposite sides of DB, and the two angles at D,
each less than two right angles, are together less than four. -/
theorem Fitted.fan {A₀ A₁ A₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2)
    (hopp : ∀ t ∈ triples (A₁ :: A₂ :: ps), OppositeSidesOf t.1 t.2.2 A₀ t.2.1)
    (hA₀ : Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => ∠ s.1 A₀ s.2) <
      ∟ + ∟ + (∟ + ∟)) :
    Fitted ((segments (A₁ :: A₂ :: ps)).map fun s => (A₀, s.1, s.2)) := by
  sorry

end Elements
