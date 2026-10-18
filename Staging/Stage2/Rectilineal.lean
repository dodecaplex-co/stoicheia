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
the figure is given with. The records of I.45 and II.14 will carry that as the tag
`figure-with-dissection`, which joins `review/terms.toml` when they change.

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

**Euclid's and Oliver Byrne's division** is one such figure. Euclid's DB, drawn from the
corner D of ABCD, and Byrne's two straight lines from one corner of his figure (1847,
p. 46), cut it into triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ from one corner A₀. `Fitted.fan`
says when those triangles are a figure in this sense: each two neighbouring triangles lie on
opposite sides of the straight line A₀Aᵢ they share, and the angles A₁A₀A₂, …, Aₙ₋₁A₀Aₙ
together are less than four right angles. Without the two conditions the triangles from A₀
may overlap or reach outside the figure, and their sum need not equal the area of their
union: a pentagon whose second and fourth corners lie on one side of the straight line from
the first corner to the third has three triangles from the first corner together greater
than it, and the first condition fails there (brief 0006 gives its corners). That the figure
the fan's triangles make is the one bounded by the closed line A₀A₁…AₙA₀, its corners in
that order, is a reading of the conditions, true in the plane, and is not stated in Lean:
`Fitted.fan` says only that the triangles fit together into one figure.

"Meeting only along that side" is said with the predicates already in the foundations: a
point is within or on a triangle when it is inside it (`InsideTriangle`), on a side between
two corners (`Between`), or at a corner (`OnOrInsideTriangle`); a point is on a finite
straight line when it is an end or between the ends (`OnFiniteLine`). The new triangle `PQX`
meets the earlier triangles only along `PQ` when every point within or on it that is within
or on one of them is on the finite straight line `PQ`.

The definitions here (`Apart` and `Apart.area` among them), all but `Rectilineal.toApart`,
are new words, and go to the foundations when adopted, with the lock and a decisions entry
(WORKFLOW, section 2).
`Fitted.ne_nil`, `Fitted.triangle` and `Fitted.inside_pairwise` follow from the definition,
and are proved here; they go to Book Zero (`Elements/Figure/Rectilineal.lean`). So do
`Rectilineal.toApart`, which takes a figure glued together as one whose triangles lie apart,
and `Rectilineal.area_toApart`, that its area is the same sum; no statement uses them, and
they let a companion that takes `Apart` take a glued figure in one step.
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

/-- **A figure glued together, taken with triangles that lie apart**: the same triangles,
which lie apart by `Fitted.inside_pairwise`. A companion that takes `Apart` takes a glued
figure `R` as `R.toApart`: `Prop45.figure` and `Prop14.figure` are `Prop45.apart` and
`Prop14.apart` for it, and `Prop14.square R.toApart` draws its square. -/
def Rectilineal.toApart (R : Rectilineal) : Apart :=
  ⟨R.pieces, R.fitted.ne_nil, R.fitted.triangle, R.fitted.inside_pairwise⟩

/-- **The area is the same sum**: the area of a glued figure taken with triangles that lie
apart is its area as a glued figure. Lean checks it by unfolding, so the two definitions of
the sum, `Apart.area` and `Rectilineal.area`, cannot drift apart. -/
theorem Rectilineal.area_toApart (R : Rectilineal) : R.toApart.area = R.area := rfl

/-- If x and y together are less than z, then x alone is less than z, being not greater than
the whole (C.N. 5). -/
theorem Fitted.fan.part {k : Kind} {x y z : Magnitude k} (h : x + y < z) : x < z := by
  by_cases hy : y = 0
  · simpa only [hy, Tacit.add_zero] using h
  · exact Tacit.lt_trans (CommonNotion5 (Magnitude.pos_of_ne_zero hy)) h

/-- "Not greater than" carries on: if x is not greater than y, nor y than z, then x is not
greater than z. -/
theorem Fitted.fan.weaken {k : Kind} {x y z : Magnitude k}
    (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  intro hzx
  rcases Tacit.lt_trichotomy x y with h | h | h
  · exact hyz (Tacit.lt_trans hzx h)
  · exact hyz (h ▸ hzx)
  · exact hxy h

/-- If x is not greater than y, and y is less than z, then x is less than z. -/
theorem Fitted.fan.bounded {k : Kind} {x y z : Magnitude k}
    (hxy : x ≤ y) (hyz : y < z) : x < z := by
  rcases Tacit.lt_trichotomy x y with h | h | h
  · exact Tacit.lt_trans h hyz
  · exact h ▸ hyz
  · exact False.elim (hxy h)

/-- Adding the same thing keeps "not greater than": if y is not greater than z, then x and y
together are not greater than x and z together. -/
theorem Fitted.fan.addition {k : Kind} (x : Magnitude k) {y z : Magnitude k}
    (hyz : y ≤ z) : x + y ≤ x + z := by
  intro h
  exact hyz (Magnitude.lt_of_add_lt_add_left h)

/-- Something added makes nothing less: x and y together are not less than x. -/
theorem Fitted.fan.growth {k : Kind} (x y : Magnitude k) : x ≤ x + y := by
  intro h
  have h' : x + y < x + 0 := by simpa only [Tacit.add_zero] using h
  exact Tacit.not_lt_zero y (Magnitude.lt_of_add_lt_add_left h')

/-- If B lies on the ray from O through A, every point of the ray from O through B
lies on it too. This carries positions along a boundary ray. -/
theorem Fitted.fan.ray {O A B Y : Point} (hY : OnRay Y O B) (hB : OnRay B O A) :
    OnRay Y O A := by
  obtain ⟨L, hO, hA, hBL⟩ := hB.2.2.1
  exact ⟨hB.1, hY.2.1, ⟨L, hO, hA, hY.onLine hO hBL⟩,
    hY.not_between hB.symm⟩

/-- If B is on the other side of OA from D, so is every point of the ray from O through B.
This carries positions along rays in the second half-plane. -/
theorem Fitted.fan.rayOpposite {O A B D Y : Point}
    (hY : OnRay Y O B) (hBD : OppositeSidesOf B D O A) :
    OppositeSidesOf Y D O A := by
  obtain ⟨L, hO, hA⟩ := Postulate1 O A hBD.1
  have hBB : SameSideOf B B O A :=
    SameSideOf.of_line hBD.1 hO hA (Tacit.same_side_refl (hBD.oppositeSides hO hA).1)
  exact (SameSideOf.of_onRay hY hBB).trans_opposite hBD

/-- A point between B and C is on C's side of OB (System E, Pasch 2): the side BC of the
triangle OBC, in `Fitted.fan.within`. -/
theorem Fitted.fan.base {O B C Y : Point} (hOBC : Triangle O B C)
    (hBYC : Between B Y C) : SameSideOf Y C O B := by
  obtain ⟨L, hO, hB⟩ := Postulate1 O B hOBC.ne₁₂
  have hY : ¬ OnLine Y L := fun hY =>
    hOBC.off_line hO hB (Tacit.on_line_of_between hBYC hB hY)
  exact SameSideOf.of_line hOBC.ne₁₂ hO hB (Tacit.pasch2 hBYC hB hY)

/-- **A point within or on the triangle OBC** lies on the finite straight line OB, or on C's
side of OB, making with OB an angle not greater than BOC. O itself, the corners and the
sides are among the cases. -/
theorem Fitted.fan.within {O B C Y : Point} (hOBC : Triangle O B C)
    (hY : OnOrInsideTriangle Y O B C) :
    OnFiniteLine Y O B ∨ (SameSideOf Y C O B ∧ ∠ B O Y ≤ ∠ B O C) := by
  have hCC : SameSideOf C C O B := by
    obtain ⟨L, hO, hB⟩ := Postulate1 O B hOBC.ne₁₂
    exact SameSideOf.of_line hOBC.ne₁₂ hO hB
      (Tacit.same_side_refl (hOBC.off_line hO hB))
  rcases hY with hY | hY | hY | hY | rfl | rfl | rfl
  · /- Within the triangle: on C's side of OB and on B's side of OC, so within the angle
       BOC, which is made up of BOY and YOC. -/
    refine Or.inr ⟨hY.2.2, ?_⟩
    rw [angle_add_of_within hY.2.2 hY.2.1.swap]
    exact fan.growth _ _
  · exact Or.inl (Or.inr (Or.inr hY))
  · /- On the side BC: on C's side of OB, and BOC is made up of BOY and YOC. -/
    refine Or.inr ⟨fan.base hOBC hY, ?_⟩
    rw [angle_add_of_between hOBC.bca hY]
    exact fan.growth _ _
  · /- On the side CO: on the ray from O through C, where the angle is BOC itself. -/
    have hYC : OnRay Y O C := OnRay.of_between (Tacit.between_symm hY)
    refine Or.inr ⟨SameSideOf.of_onRay hYC hCC, ?_⟩
    rw [angle_onRay_right hYC hOBC.ne₁₂.symm]
    exact Tacit.lt_irrefl _
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inr ⟨hCC, Tacit.lt_irrefl _⟩

/-- **The half turn.** Let AO be produced beyond O to A', let B be off the straight line AA',
and let C be on the other side of OB from A, so that the ray OC turns on from OB, away from
OA. Then OC stays on B's side of AA', B is within the angle AOC, on A's side of OC, and the
angles AOB and BOC make up AOC; or C lies on OA', and AOB and BOC make two right angles
(I.13); or C passes beyond, to the other side of AA', B is on the same side of OC as A',
and AOB and BOC make two right angles and the angle A'OC (I.13). Triple incidence places
the rays; no straight angle is measured. -/
theorem Fitted.fan.advance {O A A' B C : Point} (hAOA' : Between A O A')
    (hOAB : Triangle O A B) (hAC : OppositeSidesOf A C O B) :
    (SameSideOf B C O A ∧ SameSideOf B A O C ∧
      ∠ A O B + ∠ B O C = ∠ A O C) ∨
    (Between A O C ∧ ∠ A O B + ∠ B O C = ∟ + ∟) ∨
    (OppositeSidesOf B C O A ∧ SameSideOf B A' O C ∧
      ∠ A O B + ∠ B O C = ∟ + ∟ + ∠ A' O C) := by
  obtain ⟨L, hOL, hAL⟩ := Postulate1 O A hOAB.ne₁₂
  have hA'L : OnLine A' L := Tacit.on_line_of_between hAOA' hAL hOL
  have hBL : ¬ OnLine B L := hOAB.off_line hOL hAL
  obtain ⟨M, hOM, hBM⟩ := Postulate1 O B hOAB.ne₁₃
  have hACM := hAC.oppositeSides hOM hBM
  have hOC : O ≠ C := hAC.symm.triangle.ne₁₃
  obtain ⟨N, hON, hCN⟩ := Postulate1 O C hOC
  by_cases hCL : OnLine C L
  · /- On OA, the side condition puts C beyond O from A, on the ray through A'. -/
    have hAOA'C : SameSideOf A' C O B :=
      hAC.sameSideOf_of_between hAOA'
    have hCA' : OnRay C O A' := OnRay.of_sameSideOf hAOA'C.symm
      ⟨L, hOL, hA'L, hCL⟩ hOC.symm
    have hAOC : Between A O C := hCA'.between hAOA'
    have hACB : Triangle A C B := Triangle.of_line hAL hCL
      (Tacit.ne_of_between_ends hAOC) hBL
    exact Or.inr (Or.inl ⟨hAOC, BookI.Prop13 hAOC hACB⟩)
  by_cases hBC : SameSide B C L
  · /- In one half-plane, OB lies within AOC by Triple incidence 2. -/
    have hABN : SameSide A B N := Tacit.triple_incidence2
      hOL hOM hON hAL hBM hCN hBC hACM.2.2 hACM.2.1 hOAB.ne₁₂.symm
    have hBC' := SameSideOf.of_line hOAB.ne₁₂ hOL hAL hBC
    have hBA_OC := SameSideOf.of_line hOC hON hCN (Tacit.same_side_symm hABN)
    exact Or.inl ⟨hBC', hBA_OC, (angle_add_of_within hBC' hBA_OC).symm⟩
  · /- Across OA, the produced ray OA' lies within BOC. I.13 accounts for the
       angles from OA through OB to OA', leaving the angle A'OC. -/
    have hBC' : OppositeSidesOf B C O A :=
      OppositeSidesOf.of_line hOAB.ne₁₂ hOL hAL ⟨hBL, hCL, hBC⟩
    have hA'C : SameSideOf A' C O B := hAC.sameSideOf_of_between hAOA'
    have hBA'N : SameSide B A' N := Tacit.triple_incidence2
      hOM hOL hON hBM hA'L hCN (hA'C.sameSide hOM hBM) hBC hCL hOAB.ne₁₃.symm
    have hBA' : SameSideOf B A' O C := SameSideOf.of_line hOC hON hCN hBA'N
    have hAA'B : Triangle A A' B := Triangle.of_line hAL hA'L
      (Tacit.ne_of_between_ends hAOA') hBL
    refine Or.inr (Or.inr ⟨hBC', hBA', ?_⟩)
    rw [angle_add_of_within hA'C hBA'.symm, ← Tacit.add_assoc,
      BookI.Prop13 hAOA' hAA'B]

/-- **The position of a point round O.** There is a measure p of where each point lies
round O, starting from the ray OA and turning towards D's side of OA: nothing on the ray
OA; the angle AOY at a point Y on D's side; two right angles on the ray OA', which is AO
produced beyond O; and two right angles together with A'OY at a point Y on the other side.
The two rays are given their positions outright, so that no straight angle, and no angle
at a repeated point, is ever measured: the axioms fix the size of neither. The measure is
chosen by cases, and the proof uses only these four properties of it. -/
theorem Fitted.fan.positions {O A A' D : Point} (hAOA' : Between A O A')
    (hOAD : Triangle O A D) :
    ∃ p : Point → Angle, ∀ Y : Point,
      (OnRay Y O A → p Y = 0) ∧
      (SameSideOf Y D O A → p Y = ∠ A O Y) ∧
      (OnRay Y O A' → p Y = ∟ + ∟) ∧
      (OppositeSidesOf Y D O A → p Y = ∟ + ∟ + ∠ A' O Y) := by
  classical
  let p : Point → Angle := fun Y =>
    if SameSideOf Y D O A then ∠ A O Y
    else if OppositeSidesOf Y D O A then ∟ + ∟ + ∠ A' O Y
    else if OnRay Y O A then 0 else ∟ + ∟
  obtain ⟨L, hO, hA⟩ := Postulate1 O A hOAD.ne₁₂
  have hA' : OnLine A' L := Tacit.on_line_of_between hAOA' hA hO
  refine ⟨p, ?_⟩
  intro Y
  have hline : OnLine Y L → ¬ SameSideOf Y D O A ∧ ¬ OppositeSidesOf Y D O A := by
    intro hY
    exact ⟨fun h => Tacit.not_on_line_of_same_side (h.sameSide hO hA) hY,
      fun h => (h.oppositeSides hO hA).1 hY⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hY
    obtain ⟨hs, ho⟩ := hline (hY.onLine hO hA)
    simp only [p, ite_eq_right hs, ite_eq_right ho, ite_eq_left hY]
  · intro hY
    simp only [p, ite_eq_left hY]
  · intro hY
    obtain ⟨hs, ho⟩ := hline (hY.onLine hO hA')
    have hr : ¬ OnRay Y O A := fun h => h.2.2.2 (Tacit.between_symm (hY.between hAOA'))
    simp only [p, ite_eq_right hs, ite_eq_right ho, ite_eq_right hr]
  · intro hY
    have hs : ¬ SameSideOf Y D O A := fun h =>
      (hY.oppositeSides hO hA).2.2 (h.sameSide hO hA)
    simp only [p, ite_eq_right hs, ite_eq_left hY]

/-- Every point of the ray from O through B is at B's position, wherever B is: on D's side
of OA, on the ray OA', or on the other side. -/
theorem Fitted.fan.along {O A A' D B Y : Point} {p : Point → Angle}
    (hAOA' : Between A O A')
    (hposition : ∀ Y : Point,
      (OnRay Y O A → p Y = 0) ∧
      (SameSideOf Y D O A → p Y = ∠ A O Y) ∧
      (OnRay Y O A' → p Y = ∟ + ∟) ∧
      (OppositeSidesOf Y D O A → p Y = ∟ + ∟ + ∠ A' O Y))
    (hB : SameSideOf B D O A ∨ OnRay B O A' ∨ OppositeSidesOf B D O A)
    (hY : OnRay Y O B) : p Y = p B := by
  rcases hB with hBD | hBA' | hBD
  · rw [(hposition Y).2.1 (SameSideOf.of_onRay hY hBD), (hposition B).2.1 hBD]
    exact angle_onRay_right hY (Tacit.ne_of_between hAOA')
  · rw [(hposition Y).2.2.1 (fan.ray hY hBA'), (hposition B).2.2.1 hBA']
  · rw [(hposition Y).2.2.2 (fan.rayOpposite hY hBD), (hposition B).2.2.2 hBD,
      angle_onRay_right hY (Tacit.ne_of_between (Tacit.between_symm hAOA'))]

/-- **A step round O.** Let B be at position S, with the corner P before it behind B: on A's
side of OB when B is on D's side of OA, on D's side of OA when B is on the ray OA', and on
the same side of OB as A' when B is on the other side of OA. These are the three cases of
the running sum S: less than two right angles, exactly two, and more than two. If C is on the
other side of OB from P, and S together with the angle BOC is less than four right angles,
then C is at the position S together with BOC, and B is behind C in the same sense. In the
first case the step is the half turn from OA; in the second, OC leaves the ray OA' for the
other side; in the third, the half turn from OA', in which OC can neither come back to the
ray OA nor pass it, for the angles would make four right angles or more. That is the one
place the bound of four right angles is used. -/
theorem Fitted.fan.turn {O A A' D P B C : Point} {p : Point → Angle} {S : Angle}
    (hAOA' : Between A O A')
    (hposition : ∀ Y : Point,
      (OnRay Y O A → p Y = 0) ∧
      (SameSideOf Y D O A → p Y = ∠ A O Y) ∧
      (OnRay Y O A' → p Y = ∟ + ∟) ∧
      (OppositeSidesOf Y D O A → p Y = ∟ + ∟ + ∠ A' O Y))
    (hB : (SameSideOf B D O A ∧ SameSideOf P A O B) ∨
      (OnRay B O A' ∧ SameSideOf P D O A) ∨
      (OppositeSidesOf B D O A ∧ SameSideOf P A' O B))
    (hpB : p B = S) (hPC : OppositeSidesOf P C O B)
    (hS : S + ∠ B O C < ∟ + ∟ + (∟ + ∟)) :
    p C = S + ∠ B O C ∧
      ((SameSideOf C D O A ∧ SameSideOf B A O C) ∨
      (OnRay C O A' ∧ SameSideOf B D O A) ∨
      (OppositeSidesOf C D O A ∧ SameSideOf B A' O C)) := by
  obtain ⟨L, hOL, hAL⟩ := Postulate1 O A (Tacit.ne_of_between hAOA').symm
  have hA'L : OnLine A' L := Tacit.on_line_of_between hAOA' hAL hOL
  have hOA' : O ≠ A' := (Tacit.ne_of_between (Tacit.between_symm hAOA')).symm
  have hOBC : Triangle O B C := hPC.symm.triangle
  rcases hB with ⟨hBD, hPA⟩ | ⟨hBA', hPD⟩ | ⟨hBD, hPA'⟩
  · /- Less than two right angles: the position is the angle AOB. -/
    have hSB : S = ∠ A O B := hpB.symm.trans ((hposition B).2.1 hBD)
    have hAC : OppositeSidesOf A C O B := hPA.symm.trans_opposite hPC
    rcases fan.advance hAOA' hBD.triangle hAC with
      ⟨hBC, hBA, hsum⟩ | ⟨hAOC, hsum⟩ | ⟨hBC, hBA', hsum⟩
    · have hCD : SameSideOf C D O A := hBC.symm.trans hBD
      refine ⟨?_, Or.inl ⟨hCD, hBA⟩⟩
      rw [hSB, hsum]
      exact (hposition C).2.1 hCD
    · have hCA' : OnRay C O A' := OnRay.of_between_between hAOA' hAOC
      refine ⟨?_, Or.inr (Or.inl ⟨hCA', hBD⟩)⟩
      rw [hSB, hsum]
      exact (hposition C).2.2.1 hCA'
    · have hCD : OppositeSidesOf C D O A := (hBD.symm.trans_opposite hBC).symm
      refine ⟨?_, Or.inr (Or.inr ⟨hCD, hBA'⟩)⟩
      rw [hSB, hsum]
      exact (hposition C).2.2.2 hCD
  · /- Exactly two right angles: OB is the opposite ray from OA. -/
    have hSB : S = ∟ + ∟ := hpB.symm.trans ((hposition B).2.2.1 hBA')
    have hBL : OnLine B L := hBA'.onLine hOL hA'L
    have hPC' : OppositeSidesOf P C O A := OppositeSidesOf.of_line
      (Tacit.ne_of_between hAOA').symm hOL hAL (hPC.oppositeSides hOL hBL)
    have hCD : OppositeSidesOf C D O A := (hPD.symm.trans_opposite hPC').symm
    obtain ⟨N, hON, hCN⟩ := Postulate1 O C hOBC.ne₁₃
    have hA'N : ¬ OnLine A' N := fun h => hOBC.acb.off_line hON hCN (hBA'.onLine hON h)
    have hA'A' : SameSideOf A' A' O C := SameSideOf.of_line hOBC.ne₁₃ hON hCN
      (Tacit.same_side_refl hA'N)
    refine ⟨?_, Or.inr (Or.inr ⟨hCD, SameSideOf.of_onRay hBA' hA'A'⟩)⟩
    rw [hSB, angle_onRay_left hBA' hOBC.ne₁₃.symm]
    exact (hposition C).2.2.2 hCD
  · /- More than two right angles: measure the rest from OA produced through O. -/
    have hSB : S = ∟ + ∟ + ∠ A' O B := hpB.symm.trans ((hposition B).2.2.2 hBD)
    have hOA'B : Triangle O A' B := Triangle.of_line hOL hA'L hOA'
      (hBD.oppositeSides hOL hAL).1
    have hA'C : OppositeSidesOf A' C O B := hPA'.symm.trans_opposite hPC
    rcases fan.advance (Tacit.between_symm hAOA') hOA'B hA'C with
      ⟨hBC, hBA', hsum⟩ | ⟨_, hsum⟩ | ⟨_, _, hsum⟩
    · have hBC' : SameSideOf B C O A := SameSideOf.of_line
        (Tacit.ne_of_between hAOA').symm hOL hAL (hBC.sameSide hOL hA'L)
      have hCD : OppositeSidesOf C D O A := hBC'.symm.trans_opposite hBD
      refine ⟨?_, Or.inr (Or.inr ⟨hCD, hBA'⟩)⟩
      rw [hSB, Tacit.add_assoc, hsum]
      exact (hposition C).2.2.2 hCD
    · rw [hSB, Tacit.add_assoc, hsum] at hS
      exact False.elim (Tacit.lt_irrefl _ hS)
    · rw [hSB, Tacit.add_assoc, hsum, ← Tacit.add_assoc] at hS
      exact False.elim (Tacit.lt_irrefl _ (fan.part hS))

/-- **The new triangle lies beyond the region already swept**, save along its side OB. With
B at position S and P behind it, as in `Fitted.fan.turn`, every point within or on the
triangle OBC lies on the finite straight line OB, or is a point other than O at a position
greater than S and not greater than S together with the angle BOC. -/
theorem Fitted.fan.sweep {O A A' D P B C Y : Point} {p : Point → Angle} {S : Angle}
    (hAOA' : Between A O A')
    (hposition : ∀ Y : Point,
      (OnRay Y O A → p Y = 0) ∧
      (SameSideOf Y D O A → p Y = ∠ A O Y) ∧
      (OnRay Y O A' → p Y = ∟ + ∟) ∧
      (OppositeSidesOf Y D O A → p Y = ∟ + ∟ + ∠ A' O Y))
    (hB : (SameSideOf B D O A ∧ SameSideOf P A O B) ∨
      (OnRay B O A' ∧ SameSideOf P D O A) ∨
      (OppositeSidesOf B D O A ∧ SameSideOf P A' O B))
    (hpB : p B = S) (hPC : OppositeSidesOf P C O B)
    (hOBC : Triangle O B C) (hS : S + ∠ B O C < ∟ + ∟ + (∟ + ∟))
    (hY : OnOrInsideTriangle Y O B C) :
    OnFiniteLine Y O B ∨ (Y ≠ O ∧ S < p Y ∧ p Y ≤ S + ∠ B O C) := by
  rcases fan.within hOBC hY with hY | ⟨hYC, hBY⟩
  · exact Or.inl hY
  · /- Off OB, Y is on C's side of OB, and so on the other side from P: the step round O
       from B reaches Y at the position S together with BOY, which is greater than S,
       BOY being something, and not greater than S together with BOC. -/
    have hPY : OppositeSidesOf P Y O B := (hYC.trans_opposite hPC.symm).symm
    have hSY : S + ∠ B O Y ≤ S + ∠ B O C := fan.addition S hBY
    obtain ⟨hpY, _⟩ := fan.turn hAOA' hposition hB hpB hPY (fan.bounded hSY hS)
    refine Or.inr ⟨hYC.triangle.ne₁₃.symm, ?_, ?_⟩
    · rw [hpY]
      exact CommonNotion5 hYC.triangle.bac.angle_pos
    · rw [hpY]
      exact hSY

/-- **Euclid's and Oliver Byrne's division is a figure, when it is checked.** A figure given
by its corners A₀, A₁, A₂, …, Aₙ, the list `ps` being A₃, …, Aₙ, and divided by the straight
lines from A₀ into the triangles A₀A₁A₂, A₀A₂A₃, …, A₀Aₙ₋₁Aₙ, one on each side
`segments (A₁ :: A₂ :: ps)`. Suppose each is a triangle; each two neighbouring triangles,
A₀Aᵢ₋₁Aᵢ and A₀AᵢAᵢ₊₁, lie on opposite sides of the straight line A₀Aᵢ they share, that is,
Aᵢ₋₁ and Aᵢ₊₁ are on opposite sides of it (one condition for each of
`triples (A₁ :: A₂ :: ps)`); and the angles A₁A₀A₂, A₂A₀A₃, …, Aₙ₋₁A₀Aₙ at A₀ together are
less than four right angles. Then those triangles, in that order, are fitted together into
one figure: each is laid across the straight line A₀Aᵢ against the one before it, and meets
the earlier ones only along that straight line. The figure they make is read as the figure
with corners A₀, A₁, …, Aₙ in order round it; that its boundary is the closed line A₀A₁…AₙA₀
is not stated in Lean.

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
  have hA₀A₁A₂ : Triangle A₀ A₁ A₂ := htri (A₁, A₂) (List.mem_cons_self ..)
  cases ps with
  | nil =>
    /- One triangle, A₀A₁A₂, is a figure. -/
    exact Fitted.single hA₀A₁A₂
  | cons C rest =>
    /- Produce A₁A₀ beyond A₀ to A₁', and measure the position of each point round A₀
       from the ray A₀A₁, turning towards A₂'s side (`Fitted.fan.positions`). -/
    obtain ⟨A₁', hA₁A₀A₁'⟩ := produce hA₀A₁A₂.ne₁₂.symm
    obtain ⟨p, hposition⟩ := fan.positions hA₁A₀A₁' hA₀A₁A₂
    /- The induction along the corners. Carry the triangles already fitted, `acc`; the
       last corner reached, B, at position S, the sum of their angles at A₀; and the
       corner P before it. Each point of the earlier triangles is A₀, or at a position
       not greater than S: it lies in the sector swept from the ray A₀A₁ to the ray A₀B,
       which is the closed angle A₁A₀B while S is less than two right angles, the closed
       half-plane on A₂'s side of A₁A₁' when S is two, and that half-plane together
       with the closed angle A₁'A₀B when S is more. P is behind B, and so fixes the side
       of A₀B on which the next corner lies. -/
    have step : ∀ (rest : List Point) (P B : Point)
        (acc : List (Point × Point × Point)) (S : Angle),
        Fitted acc → (A₀, P, B) ∈ acc →
        ((SameSideOf B A₂ A₀ A₁ ∧ SameSideOf P A₁ A₀ B) ∨
          (OnRay B A₀ A₁' ∧ SameSideOf P A₂ A₀ A₁) ∨
          (OppositeSidesOf B A₂ A₀ A₁ ∧ SameSideOf P A₁' A₀ B)) →
        p B = S →
        (∀ t ∈ acc, ∀ Y : Point, OnOrInsideTriangle Y t.1 t.2.1 t.2.2 →
          Y = A₀ ∨ p Y ≤ S) →
        (∀ s ∈ segments (B :: rest), Triangle A₀ s.1 s.2) →
        (∀ t ∈ triples (P :: B :: rest), OppositeSidesOf t.1 t.2.2 A₀ t.2.1) →
        S + Magnitude.sum ((segments (B :: rest)).map fun s => ∠ s.1 A₀ s.2) <
          ∟ + ∟ + (∟ + ∟) →
        Fitted (acc ++ (segments (B :: rest)).map fun s => (A₀, s.1, s.2)) := by
      intro rest
      induction rest with
      | nil =>
        /- No corner is left: the triangles fitted so far are the figure. -/
        intro P B acc S hacc _ _ _ _ _ _ _
        simpa only [segments, List.map, List.append_nil] using hacc
      | cons C rest ih =>
        intro P B acc S hacc hPB hB hpB hregion htri hopp hbound
        have hA₀BC : Triangle A₀ B C := htri (B, C) (List.mem_cons_self ..)
        have hPC : OppositeSidesOf P C A₀ B := hopp (P, B, C) (List.mem_cons_self ..)
        have hremaining : S + ∠ B A₀ C +
            Magnitude.sum ((segments (C :: rest)).map fun s => ∠ s.1 A₀ s.2) <
            ∟ + ∟ + (∟ + ∟) := by
          rw [Tacit.add_assoc]
          exact hbound
        have hSC : S + ∠ B A₀ C < ∟ + ∟ + (∟ + ∟) := fan.part hremaining
        obtain ⟨hpC, hC⟩ := fan.turn hA₁A₀A₁' hposition hB hpB hPC hSC
        /- The new triangle A₀BC meets the earlier ones only along A₀B: a point of
           it off the finite straight line A₀B is at a position greater than S
           (`Fitted.fan.sweep`, where the bound of four right angles does its work),
           while a point of an earlier triangle is A₀ or at a position not greater
           than S. -/
        have hmeet : ∀ Y : Point, OnOrInsideTriangle Y A₀ B C →
            ∀ t ∈ acc, OnOrInsideTriangle Y t.1 t.2.1 t.2.2 → OnFiniteLine Y A₀ B := by
          intro Y hY t ht hYt
          rcases fan.sweep hA₁A₀A₁' hposition hB hpB hPC hA₀BC hSC hY with
            hYB | ⟨hYA₀, hSY, _⟩
          · exact hYB
          · rcases hregion t ht Y hYt with hYA₀' | hYS
            · exact False.elim (hYA₀ hYA₀')
            · exact False.elim (hYS hSY)
        /- So A₀BC is glued to A₀PB along A₀B, C being on the other side of A₀B from
           P by the condition on neighbours. -/
        have hglue : Fitted (acc ++ [(A₀, B, C)]) :=
          Fitted.glue hacc hPB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            hPC.symm hmeet
        /- The region grows to the position of C. Old points keep their bound as S
           increases; on A₀B the position is S; the rest of the new triangle is at a
           position not greater than S together with the angle BA₀C. -/
        have hregion' : ∀ t ∈ acc ++ [(A₀, B, C)], ∀ Y : Point,
            OnOrInsideTriangle Y t.1 t.2.1 t.2.2 → Y = A₀ ∨ p Y ≤ S + ∠ B A₀ C := by
          intro t ht Y hY
          rcases List.mem_append.mp ht with ht | ht
          · rcases hregion t ht Y hY with hYA₀ | hYS
            · exact Or.inl hYA₀
            · exact Or.inr (fan.weaken hYS (fan.growth _ _))
          · rw [List.mem_singleton] at ht
            subst t
            rcases fan.sweep hA₁A₀A₁' hposition hB hpB hPC hA₀BC hSC hY with
              hYB | ⟨_, _, hYS⟩
            · rcases hYB with rfl | rfl | hA₀YB
              · exact Or.inl rfl
              · exact Or.inr (hpB ▸ fan.growth S (∠ Y A₀ C))
              · have hpY : p Y = S :=
                  (fan.along hA₁A₀A₁' hposition (Or.imp And.left (Or.imp And.left And.left) hB)
                    (OnRay.of_between hA₀YB)).trans hpB
                exact Or.inr (hpY ▸ fan.growth S (∠ B A₀ C))
            · exact Or.inr hYS
        have hnext := ih B C (acc ++ [(A₀, B, C)]) (S + ∠ B A₀ C) hglue
          (List.mem_append.mpr (Or.inr (List.mem_singleton_self _))) hC hpC hregion'
          (fun s hs => htri s (List.mem_cons_of_mem _ hs))
          (fun t ht => hopp t (List.mem_cons_of_mem _ ht)) hremaining
        simpa only [segments, List.map, List.append_assoc, List.cons_append,
          List.nil_append] using hnext
    /- The first triangle A₀A₁A₂ lies within the closed angle A₁A₀A₂, the region of
       positions not greater than the angle A₁A₀A₂, at which A₂ lies; A₁, on its own
       side of A₀A₂, is behind A₂. -/
    obtain ⟨L, hA₀L, hA₁L⟩ := Postulate1 A₀ A₁ hA₀A₁A₂.ne₁₂
    obtain ⟨M, hA₀M, hA₂M⟩ := Postulate1 A₀ A₂ hA₀A₁A₂.ne₁₃
    have hA₂A₂ : SameSideOf A₂ A₂ A₀ A₁ := SameSideOf.of_line
      hA₀A₁A₂.ne₁₂ hA₀L hA₁L (Tacit.same_side_refl (hA₀A₁A₂.off_line hA₀L hA₁L))
    have hA₁A₁ : SameSideOf A₁ A₁ A₀ A₂ := SameSideOf.of_line
      hA₀A₁A₂.ne₁₃ hA₀M hA₂M (Tacit.same_side_refl (hA₀A₁A₂.acb.off_line hA₀M hA₂M))
    have hfirst : ∀ t ∈ [(A₀, A₁, A₂)], ∀ Y : Point,
        OnOrInsideTriangle Y t.1 t.2.1 t.2.2 → Y = A₀ ∨ p Y ≤ ∠ A₁ A₀ A₂ := by
      intro t ht Y hY
      rw [List.mem_singleton] at ht
      subst t
      rcases fan.within hA₀A₁A₂ hY with hYA₁ | ⟨hYA₂, hYangle⟩
      · rcases hYA₁ with rfl | rfl | hA₀YA₁
        · exact Or.inl rfl
        · rw [(hposition Y).1 (OnRay.self hA₀A₁A₂.ne₁₂)]
          exact Or.inr (Tacit.not_lt_zero _)
        · rw [(hposition Y).1 (OnRay.of_between hA₀YA₁)]
          exact Or.inr (Tacit.not_lt_zero _)
      · rw [(hposition Y).2.1 hYA₂]
        exact Or.inr hYangle
    exact step (C :: rest) A₁ A₂ [(A₀, A₁, A₂)] (∠ A₁ A₀ A₂)
      (Fitted.single hA₀A₁A₂) (List.mem_singleton_self _) (Or.inl ⟨hA₂A₂, hA₁A₁⟩)
      ((hposition A₂).2.1 hA₂A₂) hfirst
      (fun s hs => htri s (List.mem_cons_of_mem _ hs)) hopp hA₀

end Elements
