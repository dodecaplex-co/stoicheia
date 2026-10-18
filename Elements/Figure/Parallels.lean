import Elements.Figure.Angles

/-!
# Book Zero: parallel straight lines

"Parallel straight lines are straight lines which, being in the same plane and
being produced indefinitely in both directions, do not meet one another in either
direction" (Definition 23). Euclid says "AB is parallel to CD" of two finite
straight lines, and means the whole straight lines on which they lie. In Lean that
is `AreParallel A B C D` (from `Foundations/Phrases.lean`); `Parallel L M` says it
of two straight lines drawn and named.

Euclid never doubts that "AB is parallel to CD" says the same as "CD is parallel
to AB", or the same of any other two points of those straight lines; that
parallels do not meet, and that straight lines which do not meet are parallel;
that a straight line falling on two parallels meets each of them in one point
only; that all the points of one parallel lie on one side of the other; or that a
straight line joining two parallels "in the same directions" leaves their other
ends on either side of it. These are those facts, together with the figure of I.29
drawn about any straight line falling on two parallels.

None of their proofs uses Postulate 5. They say only what "do not meet" means,
read with System E's rules for sides (Avigad, Dean and Mumma, §3.4).
-/

namespace Elements

open Tacit

variable {A B C D G H P Q R S : Point} {L M T : Line}

/-! ## Parallel straight lines, drawn and named -/

/-- If `L` is parallel to `M`, then `M` is parallel to `L`. -/
theorem Parallel.symm (h : Parallel L M) : Parallel M L :=
  ⟨h.1.symm, fun ⟨P, hM, hL⟩ => h.2 ⟨P, hL, hM⟩⟩

/-- Parallels do not meet: a point of `L` is not on `M`. -/
theorem Parallel.not_onLine (h : Parallel L M) (hP : OnLine P L) : ¬ OnLine P M :=
  fun hPM => h.2 ⟨P, hP, hPM⟩

/-- Straight lines which do not meet are parallel (Definition 23): if no point of
`L` is on `M`, then `L` and `M` are parallel. They are not one straight line, for
`A` is on `L` and not on `M`. -/
theorem Parallel.of_not_meet (hA : OnLine A L) (h : ∀ P : Point, OnLine P L → ¬ OnLine P M) :
    Parallel L M :=
  ⟨fun e => h A hA (e ▸ hA), fun ⟨P, hL, hM⟩ => h P hL hM⟩

/-- All the points of one parallel lie on one side of the other: two points of `L`
are on the same side of `M`. Were they on opposite sides, the straight line `L`
joining them would cross `M` (System E, Intersection 1). -/
theorem Parallel.sameSide (h : Parallel L M) (hP : OnLine P L) (hQ : OnLine Q L) :
    SameSide P Q M := by
  refine Classical.byContradiction fun hs => ?_
  obtain ⟨-, X, hXM, hXL⟩ :=
    lines_meet_of_opposite_sides ⟨h.not_onLine hP, h.not_onLine hQ, hs⟩ hP hQ
  exact h.not_onLine hXL hXM

/-- A straight line `T` falling on two parallels, at `G` on `L` and at `H` on `M`,
meets `L` at `G` alone: every other point of `L` is off `T`. Otherwise `T`, through
two points of `L`, would be `L` itself (System E, Generalities 1), and `H` would lie
on both parallels. -/
theorem Parallel.off_transversal (h : Parallel L M) (hG : OnLine G L) (hH : OnLine H M)
    (hGT : OnLine G T) (hHT : OnLine H T) (hP : OnLine P L) (hPG : P ≠ G) : ¬ OnLine P T := by
  intro hPT
  have hLT : L = T := line_unique hPG hP hG hPT hGT
  exact h.not_onLine (hLT ▸ hHT) hH

/-! ## "AB is parallel to CD" -/

/-- If `AB` is parallel to `CD`, then a straight line through `A` and `B` is parallel
to one through `C` and `D`. -/
theorem AreParallel.parallel (h : AreParallel A B C D) (hA : OnLine A L) (hB : OnLine B L)
    (hC : OnLine C M) (hD : OnLine D M) : Parallel L M :=
  h.2.2 L M hA hB hC hD

/-- Two different points of `L`, and two different points of `M`, are the ends of
parallel straight lines when `L` and `M` are parallel: two points fix one straight
line (System E, Generalities 1). With `AreParallel.parallel`, this says "AB is
parallel to CD" of any other two points `P`, `Q` of the straight line `AB` and `R`,
`S` of `CD`. -/
theorem AreParallel.of_parallel (hPQ : P ≠ Q) (hRS : R ≠ S) (hP : OnLine P L) (hQ : OnLine Q L)
    (hR : OnLine R M) (hS : OnLine S M) (h : Parallel L M) : AreParallel P Q R S := by
  refine ⟨hPQ, hRS, fun L' M' hP' hQ' hR' hS' => ?_⟩
  rw [← line_unique hPQ hP hQ hP' hQ', ← line_unique hRS hR hS hR' hS']
  exact h

/-- "But straight lines which do not meet in either direction are parallel"
(Definition 23, as I.27 cites it): if no point of the straight line `AB` is on the
straight line `CD`, then `AB` is parallel to `CD`. -/
theorem AreParallel.of_not_meet (hAB : A ≠ B) (hCD : C ≠ D) (hA : OnLine A L) (hB : OnLine B L)
    (hC : OnLine C M) (hD : OnLine D M) (h : ∀ P : Point, OnLine P L → ¬ OnLine P M) :
    AreParallel A B C D :=
  AreParallel.of_parallel hAB hCD hA hB hC hD (Parallel.of_not_meet hA h)

/-- If `AB` is parallel to `CD`, then `CD` is parallel to `AB`. -/
theorem AreParallel.symm (h : AreParallel A B C D) : AreParallel C D A B :=
  ⟨h.2.1, h.1, fun L M hC hD hA hB => (h.2.2 M L hA hB hC hD).symm⟩

/-- "AB is parallel to CD" is the same as "BA is parallel to CD". -/
theorem AreParallel.swap_left (h : AreParallel A B C D) : AreParallel B A C D :=
  ⟨h.1.symm, h.2.1, fun L M hB hA hC hD => h.2.2 L M hA hB hC hD⟩

/-- "AB is parallel to CD" is the same as "AB is parallel to DC". -/
theorem AreParallel.swap_right (h : AreParallel A B C D) : AreParallel A B D C :=
  ⟨h.1, h.2.1.symm, fun L M hA hB hD hC => h.2.2 L M hA hB hC hD⟩

/-- An end of one parallel is off the other: if `AB` is parallel to `CD`, then `C`
is not on the straight line `AB`, and `ABC` is a triangle. (Turned round with
`AreParallel.symm` and `.swap_right`, the same holds of `D`, and of `A` and `B`
beside `CD`.) -/
theorem AreParallel.triangle (h : AreParallel A B C D) : Triangle A B C := by
  rintro ⟨L, hA, hB, hC⟩
  obtain ⟨M, hCM, hDM⟩ := Postulate1 C D h.2.1
  exact (h.parallel hA hB hCM hDM).not_onLine hC hCM

/-- The ends of one parallel lie on one side of the other: if `AB` is parallel to
`CD`, then `A` and `B` are on the same side of `CD` (`Parallel.sameSide`). -/
theorem AreParallel.sameSideOf (h : AreParallel A B C D) : SameSideOf A B C D := by
  refine ⟨h.2.1, fun M hC hD => ?_⟩
  obtain ⟨L, hA, hB⟩ := Postulate1 A B h.1
  exact (h.parallel hA hB hC hD).sameSide hA hB

/-! ## A straight line joining two parallels -/

/-- Joining two parallels. If `AB` is parallel to `CD`, and `B` and `D` lie on the
same side of `AC` (the two "in the same directions", as I.33 says), then `A` and `D`
lie on opposite sides of `BC`: the angles `ABC`, `BCD` are alternate.

Were `D` on `A`'s side of `BC`, it would lie within the angle `ACB`, and the straight
line `CD`, drawn within that angle, would cross `AB` (`crossbar`); but parallels do
not meet. -/
theorem AreParallel.oppositeSidesOf (h : AreParallel A B C D) (hBD : SameSideOf B D A C) :
    OppositeSidesOf A D B C := by
  have hBC : B ≠ C := h.triangle.ne₂₃
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B h.1
  obtain ⟨M, hC_M, hD_M⟩ := Postulate1 C D h.2.1
  obtain ⟨N, hB_N, hC_N⟩ := Postulate1 B C hBC
  have hpar : Parallel L M := h.parallel hA_L hB_L hC_M hD_M
  /- `A` is off `BC`, or `BC` would be `AB` and `C` on it; and `D` is off `BC`, or
     `BC` would be `CD` and `B` on it. -/
  have hA_N : ¬ OnLine A N := fun hA =>
    hpar.not_onLine ((line_unique h.1 hA hB_N hA_L hB_L) ▸ hC_N) hC_M
  have hD_N : ¬ OnLine D N := fun hD =>
    hpar.not_onLine hB_L ((line_unique h.2.1 hC_N hD hC_M hD_M) ▸ hB_N)
  refine OppositeSidesOf.of_line hBC hB_N hC_N ⟨hA_N, hD_N, fun hAD => ?_⟩
  /- Otherwise `D` lies within the angle `ACB`: on `B`'s side of `CA`, and on `A`'s
     side of `CB`. -/
  have hDA : SameSideOf D A C B := (SameSideOf.of_line hBC hB_N hC_N (same_side_symm hAD)).swap
  obtain ⟨X, hAXB, hX⟩ := crossbar hBD.symm.swap hDA
  exact hpar.not_onLine (on_line_of_between_ends hAXB hA_L hB_L) (hX.onLine hC_M hD_M)

/-! ## The figure of I.29 about any straight line falling on two parallels

To cite I.29, a proof needs Euclid's figure: the straight line `EF` falling on the
parallels `AB`, `CD` at `G` and `H`, each of `G` and `H` between two points, and `B`,
`D` on one side of `EF`. A later proof usually has a straight line falling on two
parallels at points it has already named, with no room on either side; these
lemmas produce the straight lines [Post. 2] to make that figure. -/

/-- The figure of I.29, about alternate angles. Let the straight line `PG` be
parallel to `HQ`, with `P` and `Q` on opposite sides of `GH`. Produce `PG` beyond
`G` to `B`, `QH` beyond `H` to `C`, and `GH` beyond each end to `E` and `F`. Then
`EF` falls on the parallels `PB`, `CQ` as in Euclid's figure, with `P` for his `A`
and `Q` for his `D`: the angles `PGH`, `GHQ` are its alternate angles, and `B` and `Q`
lie on one side of `EF`. -/
theorem AreParallel.figure_alternate (h : AreParallel P G H Q) (hPQ : OppositeSidesOf P Q G H) :
    ∃ B C E F : Point, Between P G B ∧ Between C H Q ∧ Between E G H ∧ Between G H F ∧
      AreParallel P B C Q ∧ SameSideOf B Q E F := by
  have hGH : G ≠ H := hPQ.1
  obtain ⟨B, hPGB⟩ := produce h.1
  obtain ⟨C, hQHC⟩ := produce h.2.1.symm
  obtain ⟨E, hHGE⟩ := produce hGH.symm
  obtain ⟨F, hGHF⟩ := produce hGH
  obtain ⟨L, hP_L, hG_L⟩ := Postulate1 P G h.1
  obtain ⟨M, hH_M, hQ_M⟩ := Postulate1 H Q h.2.1
  obtain ⟨T, hG_T, hH_T⟩ := Postulate1 G H hGH
  have hpar : AreParallel P B C Q :=
    AreParallel.of_parallel (ne_of_between_ends hPGB) (ne_of_between_ends hQHC).symm hP_L
      (on_line_of_between hPGB hP_L hG_L) (on_line_of_between hQHC hQ_M hH_M) hQ_M
      (h.parallel hP_L hG_L hH_M hQ_M)
  /- `B` is on the other side of `GH` from `P`, and so on `Q`'s side. -/
  have hBQ : SameSide B Q T := (hPQ.sameSideOf_of_between hPGB).sameSide hG_T hH_T
  have hEGF : Between E G F := between_of_between_right (between_symm hHGE) hGHF
  exact ⟨B, C, E, F, hPGB, between_symm hQHC, between_symm hHGE, hGHF, hpar,
    SameSideOf.of_line (ne_of_between_ends hEGF) (on_line_of_between hHGE hH_T hG_T)
      (on_line_of_between hGHF hG_T hH_T) hBQ⟩

/-- The figure of I.29, about interior angles on the same side. Let the straight line
`GP` be parallel to `HQ`, with `P` and `Q` on the same side of `GH`. Produce `PG`
beyond `G` to `A`, `QH` beyond `H` to `C`, and `GH` beyond each end to `E` and `F`.
Then `EF` falls on the parallels `AP`, `CQ` as in Euclid's figure, with `P` for his
`B` and `Q` for his `D`: the angles `PGH`, `GHQ` are its interior angles on the same
side, and `EGP` its exterior angle. -/
theorem AreParallel.figure_interior (h : AreParallel G P H Q) (hPQ : SameSideOf P Q G H) :
    ∃ A C E F : Point, Between A G P ∧ Between C H Q ∧ Between E G H ∧ Between G H F ∧
      AreParallel A P C Q ∧ SameSideOf P Q E F := by
  have hGH : G ≠ H := hPQ.1
  obtain ⟨A, hPGA⟩ := produce h.1.symm
  obtain ⟨C, hQHC⟩ := produce h.2.1.symm
  obtain ⟨E, hHGE⟩ := produce hGH.symm
  obtain ⟨F, hGHF⟩ := produce hGH
  obtain ⟨L, hG_L, hP_L⟩ := Postulate1 G P h.1
  obtain ⟨M, hH_M, hQ_M⟩ := Postulate1 H Q h.2.1
  obtain ⟨T, hG_T, hH_T⟩ := Postulate1 G H hGH
  have hpar : AreParallel A P C Q :=
    AreParallel.of_parallel (ne_of_between_ends hPGA).symm (ne_of_between_ends hQHC).symm
      (on_line_of_between hPGA hP_L hG_L) hP_L (on_line_of_between hQHC hQ_M hH_M) hQ_M
      (h.parallel hG_L hP_L hH_M hQ_M)
  have hEGF : Between E G F := between_of_between_right (between_symm hHGE) hGHF
  exact ⟨A, C, E, F, between_symm hPGA, between_symm hQHC, between_symm hHGE, hGHF, hpar,
    SameSideOf.of_line (ne_of_between_ends hEGF) (on_line_of_between hHGE hH_T hG_T)
      (on_line_of_between hGHF hG_T hH_T) (hPQ.sameSide hG_T hH_T)⟩

end Elements
