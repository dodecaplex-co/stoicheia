import Elements.Figure.Basics
import Elements.BookI.Prop28
import Elements.BookI.Prop30

/-!
# Book I: small steps about parallels that cite a proposition

From I.33 on, almost every proof draws a parallel and reads off its angles, and
several take the point where a straight line meets it. These steps cite I.28,
I.29 or I.30, so they cannot live in Book Zero; and `Helpers.lean`, which I.7, I.9,
I.18, I.19, I.20 and I.24 import, cannot import those propositions without the
imports going round in a circle. So they live here, in a file of their own, for
the propositions from I.31 on. Each is named after the proposition it cites.

The certificate walks through these steps as it walks through any helper, so a
proof that uses one is recorded as citing the proposition inside it. Those that
cite I.29 or I.30 rest on Postulate 5.
-/

namespace Elements.BookI

open Tacit

/-! ## Citing I.29 about any straight line falling on two parallels -/

/-- The alternate angles. If the straight line `PG` is parallel to `HQ`, and `P` and
`Q` lie on opposite sides of `GH`, then the alternate angles `PGH`, `GHQ` are equal.
Book Zero draws Euclid's figure about `GH` (`AreParallel.figure_alternate`), and I.29
does the rest. [I. 29] -/
theorem Prop29.alternate {P G H Q : Point} (hpar : AreParallel P G H Q)
    (hPQ : OppositeSidesOf P Q G H) : ∠ P G H = ∠ G H Q := by
  obtain ⟨B, C, E, F, h₁, h₂, h₃, h₄, hpar', hside⟩ := hpar.figure_alternate hPQ
  exact (Prop29 hpar' h₁ h₂ h₃ h₄ hside).1

/-- The interior angles on the same side. If the straight line `GP` is parallel to
`HQ`, and `P` and `Q` lie on one side of `GH`, then the angles `PGH`, `GHQ` are
equal to two right angles. [I. 29] -/
theorem Prop29.interior {P G H Q : Point} (hpar : AreParallel G P H Q)
    (hPQ : SameSideOf P Q G H) : ∠ P G H + ∠ G H Q = ∟ + ∟ := by
  obtain ⟨A, C, E, F, h₁, h₂, h₃, h₄, hpar', hside⟩ := hpar.figure_interior hPQ
  exact (Prop29 hpar' h₁ h₂ h₃ h₄ hside).2.2

/-- The exterior angle. If the straight line `GP` is parallel to `HQ`, `P` and `Q` lie
on one side of `GH`, and `E` lies on `HG` produced beyond `G`, then the exterior
angle `EGP` is equal to the interior and opposite angle `GHQ`. [I. 29] -/
theorem Prop29.exterior {P G H Q E : Point} (hpar : AreParallel G P H Q)
    (hPQ : SameSideOf P Q G H) (hEGH : Between E G H) : ∠ E G P = ∠ G H Q := by
  obtain ⟨A, C, E', F, h₁, h₂, h₃, h₄, hpar', hside⟩ := hpar.figure_interior hPQ
  have hE : OnRay E G E' := OnRay.of_between_between (between_symm h₃) (between_symm hEGH)
  rw [angle_onRay_left hE hpar.1.symm]
  exact (Prop29 hpar' h₁ h₂ h₃ h₄ hside).2.1

/-! ## A straight line meeting one of two parallels meets the other -/

/-- A straight line meeting one of two parallels meets the other. If `L` is parallel
to `M`, and a straight line `N`, other than `M`, passes through a point `P` of `M`,
then `N` meets `L`. Otherwise `N` would be parallel to `L` too, and by I.30 `M` and
`N` would be parallel to one another, though both pass through `P`.

Euclid uses this whenever he draws a parallel and then names the point where it
meets another straight line: `E` and `F` in I.37, `G` and `H` in I.38, `E` in I.39,
`F` in I.40, `F` and `G` in I.42, `H`, `L` and `M` in I.44, `E` in I.46 and `L` in
I.47. It is the uniqueness of the parallel through a point, often called
Playfair's axiom; Heath reports under I.31 that Proclus draws it from I.30.
`Prop30.unique`, a step inside I.30's own proof, gives the same uniqueness from
I.29; later proofs cite this one, Proclus' route through I.30. [I. 30] -/
theorem Prop30.meet {L M N : Line} {P : Point} (hLM : Parallel L M) (hPM : OnLine P M)
    (hPN : OnLine P N) (hNM : N ≠ M) : ∃ Q : Point, OnLine Q N ∧ OnLine Q L := by
  refine Classical.byContradiction fun hno => ?_
  have hNL : Parallel N L := Parallel.of_not_meet hPN fun Q hQN hQL => hno ⟨Q, hQN, hQL⟩
  obtain ⟨B, hB_M, hB⟩ := exists_point_on_line M [P]
  have hPB : P ≠ B := fun e => hB (e ▸ List.mem_singleton_self P)
  obtain ⟨C, hC_N, hC_M, -⟩ := exists_point_on_line_off_line hNM []
  have hCP : C ≠ P := fun e => hC_M (e ▸ hPM)
  obtain ⟨E, hE_L, -⟩ := exists_point_on_line L []
  obtain ⟨F, hF_L, hF⟩ := exists_point_on_line L [E]
  have hEF : E ≠ F := fun e => hF (e ▸ List.mem_singleton_self E)
  have h₁ : AreParallel P B E F := AreParallel.of_parallel hPB hEF hPM hB_M hE_L hF_L hLM.symm
  have h₂ : AreParallel C P E F := AreParallel.of_parallel hCP hEF hC_N hPN hE_L hF_L hNL
  have hC : ¬ Collinear P B C := fun ⟨K, hP_K, hB_K, hC_K⟩ =>
    hC_M ((line_unique hPB hP_K hB_K hPM hB_M) ▸ hC_K)
  exact ((Prop30 h₁ h₂ hC).parallel hPM hB_M hC_N hPN).not_onLine hPM hPN

/-- I.30 said of straight lines drawn and named: two different straight lines `L` and
`M`, each parallel to `N`, are parallel to one another. Euclid uses it without a
bracket in I.44 and I.47, where a straight line drawn "parallel to either" of two
parallels is parallel to both; in I.45 he brackets it. I.43 needs it too, to show
that the complements are parallelograms. [I. 30] -/
theorem Prop30.parallel {L M N : Line} (hL : Parallel L N) (hM : Parallel M N) (hLM : L ≠ M) :
    Parallel L M := by
  obtain ⟨A, hA_L, -⟩ := exists_point_on_line L []
  obtain ⟨B, hB_L, hB⟩ := exists_point_on_line L [A]
  have hAB : A ≠ B := fun e => hB (e ▸ List.mem_singleton_self A)
  obtain ⟨C, hC_M, hC_L, -⟩ := exists_point_on_line_off_line hLM.symm []
  obtain ⟨D, hD_M, hD⟩ := exists_point_on_line M [C]
  have hCD : C ≠ D := fun e => hD (e ▸ List.mem_singleton_self C)
  obtain ⟨E, hE_N, -⟩ := exists_point_on_line N []
  obtain ⟨F, hF_N, hF⟩ := exists_point_on_line N [E]
  have hEF : E ≠ F := fun e => hF (e ▸ List.mem_singleton_self E)
  have hC : ¬ Collinear A B C := fun ⟨K, hA_K, hB_K, hC_K⟩ =>
    hC_L ((line_unique hAB hA_K hB_K hA_L hB_L) ▸ hC_K)
  exact (Prop30 (AreParallel.of_parallel hAB hEF hA_L hB_L hE_N hF_N hL)
    (AreParallel.of_parallel hCD hEF hC_M hD_M hE_N hF_N hM) hC).parallel hA_L hB_L hC_M hD_M

/-! ## Parallels from right angles, and squares -/

/-- Two straight lines making the interior angles on one side of a third equal to
two right angles are parallel: if `D` and `C` lie on one side of `AB`, and the angles
`DAB`, `ABC` are equal to two right angles, then `AD` is parallel to `BC`. Produce
the four straight lines to make I.28's figure about `AB`. [I. 28] -/
theorem Prop28.interior {A B C D : Point} (hDC : SameSideOf D C A B)
    (h : ∠ D A B + ∠ A B C = ∟ + ∟) : AreParallel A D B C := by
  have hAB : A ≠ B := hDC.1
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hD_L : ¬ OnLine D L := not_on_line_of_same_side (hDC.sameSide hA_L hB_L)
  have hC_L : ¬ OnLine C L := not_on_line_of_same_side (same_side_symm (hDC.sameSide hA_L hB_L))
  have hDA : D ≠ A := fun e => hD_L (e ▸ hA_L)
  have hCB : C ≠ B := fun e => hC_L (e ▸ hB_L)
  obtain ⟨X, hDAX⟩ := produce hDA
  obtain ⟨Y, hCBY⟩ := produce hCB
  obtain ⟨E, hBAE⟩ := produce hAB.symm
  obtain ⟨F, hABF⟩ := produce hAB
  have hE_L : OnLine E L := on_line_of_between hBAE hB_L hA_L
  have hF_L : OnLine F L := on_line_of_between hABF hA_L hB_L
  have hEF : E ≠ F := ne_of_between_ends (between_of_between_right (between_symm hBAE) hABF)
  have hpar : AreParallel X D Y C :=
    Prop28 (between_symm hDAX) (between_symm hCBY) (between_symm hBAE) hABF
      (SameSideOf.of_line hEF hE_L hF_L (hDC.sameSide hA_L hB_L)) (Or.inr h)
  obtain ⟨M, hD_M, hA_M⟩ := Postulate1 D A hDA
  obtain ⟨N, hC_N, hB_N⟩ := Postulate1 C B hCB
  exact AreParallel.of_parallel hDA.symm hCB.symm hA_M hD_M hB_N hC_N
    (hpar.parallel (on_line_of_between hDAX hD_M hA_M) hD_M (on_line_of_between hCBY hC_N hB_N)
      hC_N)

/-- A square is a parallelogram. If `ABCD` is a square (Def. 22) whose far corners
`C`, `D` lie on one side of `AB`, its opposite sides are parallel: the right angles
at `A` and `B` make `AD` parallel to `BC`, and those at `B` and `C` make `AB` parallel
to `CD`. Euclid's squares are those I.46 describes, which are parallelograms by
construction; a square given in a statement has to be shown one. [I. 28] -/
theorem Prop28.square {A B C D : Point} (h : Square A B C D) (hCD : SameSideOf C D A B) :
    Parallelogram A B C D := by
  obtain ⟨-, -, -, hDAB, hABC, hBCD, -⟩ := h
  have hAD_BC : AreParallel A D B C := Prop28.interior hCD.symm (by rw [hDAB, hABC])
  have hBA_CD : AreParallel B A C D :=
    Prop28.interior hAD_BC.sameSideOf (by rw [hABC, hBCD])
  exact ⟨hBA_CD.swap_left, hAD_BC.symm.swap_right⟩

end Elements.BookI
