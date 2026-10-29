import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop27
import Elements.BookI.Prop29

/-!
# Book I, Proposition 33

Euclid's text, in Heath's translation: [`heath/I/33.md`](../../heath/I/33.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- The straight lines joining equal and parallel straight lines (at the extremities which are) in
the same directions (respectively) are themselves also equal and parallel. -/
theorem Prop33 {A B C D : Point} (hpar : AreParallel A B C D) (heq : ‖A B‖ = ‖C D‖)
    (hdir : SameSideOf B D A C) :
    ‖A C‖ = ‖B D‖ ∧ AreParallel A C B D := by
  -- Let AB, CD be equal and parallel, and let the straight lines AC, BD join them (at the
  -- extremities which are) in the same directions (respectively);
  have hABC : Triangle A B C := hpar.triangle
  have hCDB : Triangle C D B := hpar.symm.swap_right.triangle
  have hAC : A ≠ C := hdir.1
  have hBD : B ≠ D := hCDB.ne₂₃.symm
  -- I say that AC, BD are also equal and parallel.
  -- Let BC be joined.
  have hBC : B ≠ C := hABC.ne₂₃
  -- Then, since AB is parallel to CD,
  have hAB_CD : AreParallel A B C D := hpar
  -- and BC has fallen upon them,
  /- The ends joined in the same directions leave A and D on opposite sides
     of BC (`AreParallel.oppositeSidesOf`). -/
  have hAD : OppositeSidesOf A D B C := hAB_CD.oppositeSidesOf hdir
  -- the alternate angles ABC, BCD are equal to one another. [I. 29]
  have hABC_BCD : ∠ A B C = ∠ B C D := Prop29.alternate hAB_CD hAD
  -- And, since AB is equal to CD,
  have hAB_CD_eq : ‖A B‖ = ‖C D‖ := heq
  -- and BC is common,
  have hBC_CB : ‖B C‖ = ‖C B‖ := len_symm B C
  -- the two sides AB, BC are equal to the two sides DC, CB;
  have hBA_CD : ‖B A‖ = ‖C D‖ := (len_symm B A).trans hAB_CD_eq
  -- and the angle ABC is equal to the angle BCD;
  have hABC_DCB : ∠ A B C = ∠ D C B :=
    hABC_BCD.trans (angle_symm hBC hCDB.ne₁₂.symm)
  -- therefore the base AC is equal to the base BD,
  /- I.4 takes the corner of the given angle first: BAC and CDB pair B with C,
     A with D, and C with B. -/
  obtain ⟨hAC_DB, hBAC_CDB, -, hBCA_CBD⟩ :=
    Prop4 hABC.bac hCDB hBA_CD hBC_CB hABC_DCB
  have hAC_BD : ‖A C‖ = ‖B D‖ := hAC_DB.trans (len_symm D B)
  -- and the triangle ABC is equal to the triangle DCB,
  have : △ A B C = △ D C B := by
    rw [area_bac A B C, hBAC_CDB, area_bac C D B]
  -- and the remaining angles will be equal to the remaining angles respectively, namely those
  -- which the equal sides subtend; [I. 4]
  -- therefore the angle ACB is equal to the angle CBD.
  have hACB_CBD : ∠ A C B = ∠ C B D := (angle_symm hAC hBC).trans hBCA_CBD
  -- And, since the straight line BC falling on the two straight lines AC, BD has made the
  -- alternate angles equal to one another,
  /- Produce AC beyond C and DB beyond B (Post. 2), so BC falls between two
     points of each straight line, as I.27 asks. Heath gives these ends no letters. -/
  obtain ⟨C₁, hACC₁⟩ := produce hAC
  obtain ⟨B₁, hDBB₁⟩ := produce hBD.symm
  -- AC is parallel to BD. [I. 27]
  have h27 : AreParallel A C₁ B₁ D :=
    Prop27 hACC₁ (between_symm hDBB₁) hAD.swap hACB_CBD
  /- Parallelism belongs to the whole straight lines, whichever two points
     name each one. Postulate 1 names those through A, C and B, D. -/
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  obtain ⟨M, hB_M, hD_M⟩ := Postulate1 B D hBD
  have hC₁_L : OnLine C₁ L := on_line_of_between hACC₁ hA_L hC_L
  have hB₁_M : OnLine B₁ M := on_line_of_between hDBB₁ hD_M hB_M
  have hAC_BD_par : AreParallel A C B D :=
    AreParallel.of_parallel hAC hBD hA_L hC_L hB_M hD_M
      (h27.parallel hA_L hC₁_L hB₁_M hD_M)
  -- And it was also proved equal to it.
  -- Therefore etc.
  exact ⟨hAC_BD, hAC_BD_par⟩
  -- Q. E. D.

end Elements.BookI
