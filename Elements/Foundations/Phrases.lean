import Elements.Foundations.Postulates

/-!
# Phrases

Euclid's statements use a handful of phrases he never defines, such as "on the
same side of AB", "AB is parallel to CD", "within the triangle", "the
parallelogram ABCD". Here they are spelled out once, in terms of the
undefined words, so that each proposition can be stated in Euclid's own
manner: with points named by letters, as in Heath's figures.

The last of them say "any number". II.1 cuts a straight line "into any number of
segments whatever": its points of section are a list, in order along it (`InOrder`),
and its segments run from each point to the next (`segments`, `endOf`). I.45 and II.14
take "a given rectilineal figure", of any number of sides: it is given with the
triangles it is cut into, as the section below says.

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

/-! ## Points in order on a straight line -/

/-- **Points in order.** `InOrder ps`: each point of the list `ps` differs from the next,
and of any three in a row the middle one lies between the other two. So the points lie on
one straight line, in the order listed: `InOrder [B, D, E, C]` is II.1's straight line BC
cut at the points D and E. A list of one point, or of none, is in order. -/
def InOrder : List Point → Prop
  | [] => True
  | [_] => True
  | [p, q] => p ≠ q
  | p :: q :: r :: rest => p ≠ q ∧ Between p q r ∧ InOrder (q :: r :: rest)

/-- **The segments** of a straight line cut at points in order: each point of the list with
the next, as the ends of one segment. The segments of `[B, D, E, C]` are BD, DE and EC. The
points need not be in order, or on one straight line: in the companions of I.45 and II.14
for a checked fan (`Prop45.fan`, `Prop14.fan`), the segments of a figure's corners A₁, A₂,
…, Aₙ are its sides A₁A₂, …, Aₙ₋₁Aₙ, those away from the corner A₀, and each side with A₀
makes one of the triangles into which the straight lines from A₀ divide the figure, when the
fan's conditions hold. -/
def segments : List Point → List (Point × Point)
  | p :: q :: rest => (p, q) :: segments (q :: rest)
  | _ => []

/-- **The end** of the straight line that starts at `B` and runs through the points `ps`:
the last of them, or `B` itself if there are none. `endOf B [D, E, C]` is C. -/
def endOf (B : Point) : List Point → Point
  | [] => B
  | p :: ps => endOf p ps

/-! ## A rectilineal figure, given with its triangles

I.45 makes a parallelogram "equal to a given rectilineal figure", and II.14 a square.
Euclid's proof of I.45 joins DB and works with the triangles ABD and DBC; his words take
any figure. Here a figure is given with a division of it into triangles, in one of two
forms. Any division at all is taken as triangles that lie apart (`Apart`). A figure with one
boundary may also be given as triangles fitted together in a suitable order (`Fitted`):
each new triangle is laid across a side of an earlier one, and meets the triangles already
there only along that side. The figure is the triangles together. Such a figure may be
convex or not, and need have no corner from which the straight lines to the others divide
it.

**The convention, stated on the page:** the figure comes with its division, and the division
is checked, as a division supplied with a figure must be. For any division the check is
`Apart`: no point is inside two of the triangles. For a figure with one boundary it may also
be `Fitted`: the triangles do not overlap (`Fitted.inside_pairwise`, in Book Zero), and each
meets the figure already made only along one side, so they make up one figure. Either way
their sum is what Euclid calls the whole of it. Two things are not stated here. That every
rectilineal figure can be cut into triangles in these ways is a separate theorem. That two
divisions of one figure give one sum is the step Euclid takes for granted, which David
Hilbert proved, for his measure of area; Book I's gap catalogue tells it, under I.45, and no
statement here assumes it. So "equal to the given rectilineal figure", in I.45 and II.14,
means equal to the sum of the triangles the figure is given with. The records of I.45 and
II.14 carry that as the tag `figure-with-dissection`, and their pages show it.

**A figure with a hole, or in pieces.** Euclid defines a figure as "that which is contained
by any boundary or boundaries" (Definition I.14), so a square with a smaller square cut from
its middle is a rectilineal figure, contained by two boundaries. Gluing cannot make it: a
ring of triangles round the hole cannot close. So the figure is also taken given with
triangles that lie apart (`Apart`): no point is inside two of them, and nothing else is
asked. The figure is the triangles together, which may have a hole, touch itself at a
corner, or be in more than one piece, which only claims more. Lying apart is exactly what
makes the sum of the triangles the area of the figure they make up, and a fitted figure's
triangles lie apart (`Fitted.inside_pairwise`), so `Apart` takes every figure `Fitted`
takes. `Fitted` is the figure with one boundary, its triangles fitted together.

"Meeting only along that side" is said with the predicates already in the foundations: a
point is within or on a triangle when it is inside it (`InsideTriangle`), on a side between
two corners (`Between`), or at a corner (`OnOrInsideTriangle`); a point is on a finite
straight line when it is an end or between the ends (`OnFiniteLine`). The new triangle `PQX` meets the
earlier triangles only along `PQ` when every point within or on it that is within or on one
of them is on the finite straight line `PQ`.

Euclid's and Oliver Byrne's division of a figure by the straight lines from one corner is
one such figure when two conditions hold; `Fitted.fan`, beside I.45, proves it.
-/

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

/-- **The corners three at a time**: each corner of the list with the next two. The triples
of `[A₁, A₂, A₃, A₄]` are A₁A₂A₃ and A₂A₃A₄. In a division from one corner A₀, the middle
corner of each triple is the far end of the straight line A₀Aᵢ that two neighbouring
triangles share, and the other two are their third corners. -/
def triples : List Point → List (Point × Point × Point)
  | p :: q :: r :: rest => (p, q, r) :: triples (q :: r :: rest)
  | _ => []

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
along AC and listed ABC, ADC (the second must be named with AC as its first two corners,
ACD or CAD).

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
division of the same figure gives the same sum is not proved here (Book I's gap catalogue,
under I.45), so this is the area of the figure with its division, not yet a measure of the
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
same sum is not proved here (Book I's gap catalogue, under I.45), so this is the area of the
figure with its division, not yet a measure of the figure alone. -/
noncomputable def Apart.area (R : Apart) : Area :=
  Magnitude.sum (R.pieces.map fun t => △ t.1 t.2.1 t.2.2)

end Elements
