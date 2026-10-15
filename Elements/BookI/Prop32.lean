import Elements.Figure.Basics
import Elements.BookI.Prop13
import Elements.BookI.Prop29
import Elements.BookI.Prop31

/-!
# Book I, Proposition 32

Euclid's text, in Heath's translation: [`heath/I/32.md`](../../heath/I/32.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Euclid chooses the half of the parallel through `C` on `A`'s side of `BC`.
The two ends supplied by I.31 are on opposite sides of `BC`, since their straight
line crosses it at `C`; one must therefore lie on `A`'s side (System E, Pasch 3
and Same side 5). This choice uses no proposition. -/
theorem Prop32.choose_end {A B C P Q : Point} (hABC : Triangle A B C)
    (hPCQ : Between P C Q) (hpar : AreParallel P Q A B) :
    ∃ E : Point, AreParallel C E A B ∧ SameSideOf E A B C := by
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hABC.ne₁₂
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  obtain ⟨PQ, hP_PQ, hQ_PQ⟩ := Postulate1 P Q hpar.1
  have hC_PQ : OnLine C PQ := on_line_of_between_ends hPCQ hP_PQ hQ_PQ
  have hparallel : Parallel PQ AB := hpar.parallel hP_PQ hQ_PQ hA_AB hB_AB
  have hP_BC : ¬ OnLine P BC :=
    hparallel.off_transversal hC_PQ hB_AB hC_BC hB_BC hP_PQ (ne_of_between hPCQ)
  have hQ_BC : ¬ OnLine Q BC :=
    hparallel.off_transversal hC_PQ hB_AB hC_BC hB_BC hQ_PQ
      (ne_of_between (between_symm hPCQ))
  rcases same_side_or hP_BC hQ_BC (hABC.bca.off_line hB_BC hC_BC)
      (pasch3 hPCQ hC_BC) with hPA | hQA
  · exact ⟨P, AreParallel.of_parallel (ne_of_between hPCQ).symm hABC.ne₁₂
      hC_PQ hP_PQ hA_AB hB_AB hparallel,
      SameSideOf.of_line hABC.ne₂₃ hB_BC hC_BC hPA⟩
  · exact ⟨Q, AreParallel.of_parallel (ne_of_between (between_symm hPCQ)).symm
      hABC.ne₁₂ hC_PQ hQ_PQ hA_AB hB_AB hparallel,
      SameSideOf.of_line hABC.ne₂₃ hB_BC hC_BC hQA⟩

/-- In any triangle, if one of the sides be produced, the exterior angle is equal to the two
interior and opposite angles, and the three interior angles of the triangle are equal to two
right angles. -/
theorem Prop32 {A B C D : Point} (hABC : Triangle A B C) (hBCD : Between B C D) :
    ∠ A C D = ∠ C A B + ∠ A B C ∧ ∠ A B C + ∠ B C A + ∠ C A B = ∟ + ∟ := by
  -- Let ABC be a triangle, and let one side of it BC be produced to D;
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  have hD_BC : OnLine D BC := on_line_of_between hBCD hB_BC hC_BC
  have hCD : C ≠ D := (ne_of_between (between_symm hBCD)).symm
  -- I say that the exterior angle ACD is equal to the two interior and opposite angles CAB,
  -- ABC, and the three interior angles of the triangle ABC, BCA, CAB are equal to two right
  -- angles.
  -- For let CE be drawn through the point C parallel to the straight line AB. [I. 31]
  obtain ⟨P, Q, hPCQ, hPQ⟩ := Prop31 hABC.ne₁₂ hABC
  obtain ⟨E, hCE, hEA⟩ := Prop32.choose_end hABC hPCQ hPQ
  -- Then, since AB is parallel to CE,
  have hAB : AreParallel A B C E := hCE.symm
  -- and AC has fallen upon them,
  have hBE : OppositeSidesOf B E A C := hAB.swap_left.oppositeSidesOf hEA.symm
  obtain ⟨B₁, C₁, E₁, F₁, h₁, h₂, h₃, h₄, hpar₁, hside₁⟩ :=
    hAB.swap_left.figure_alternate hBE
  -- the alternate angles BAC, ACE are equal to one another. [I. 29]
  have hBAC_ACE : ∠ B A C = ∠ A C E := (Prop29 hpar₁ h₁ h₂ h₃ h₄ hside₁).1
  -- Again, since AB is parallel to CE,
  have hCE_BA : AreParallel C E B A := hCE.swap_right
  -- and the straight line BD has fallen upon them,
  obtain ⟨A₂, C₂, E₂, F₂, h₅, h₆, h₇, h₈, hpar₂, hside₂⟩ :=
    hCE_BA.figure_interior hEA.swap
  -- the exterior angle ECD is equal to the interior and opposite angle ABC. [I. 29]
  have hECD_ABC : ∠ E C D = ∠ A B C := by
    have h := (Prop29 hpar₂ h₅ h₆ h₇ h₈ hside₂).2.1
    rw [angle_onRay_left (OnRay.of_between_between hBCD (between_symm h₇))
      hCE.1.symm, angle_symm hCD.symm hCE.1.symm,
      angle_symm hABC.ne₂₃.symm hABC.ne₁₂] at h
    exact h
  -- But the angle ACE was also proved equal to the angle BAC;
  have hACE_BAC : ∠ A C E = ∠ B A C := hBAC_ACE.symm
  -- therefore the whole angle ACD is equal to the two interior and opposite angles BAC, ABC.
  /- `E` lies within `ACD`: both `E` and `D` are opposite `B` across `AC`,
     and `E` is on `A`'s side of the straight line `CD`, which is `BC`. -/
  have hED : SameSideOf E D C A :=
    (hBE.sameSideOf (OppositeSidesOf.of_between hABC.acb hBCD)).swap
  have hEA_CD : SameSideOf E A C D :=
    SameSideOf.of_line hCD hC_BC hD_BC (hEA.sameSide hB_BC hC_BC)
  have hACD : ∠ A C D = ∠ C A B + ∠ A B C := by
    rw [angle_add_of_within hED hEA_CD, hACE_BAC, hECD_ABC,
      angle_symm hABC.ne₁₂.symm hABC.ne₁₃.symm]
  -- Let the angle ACB be added to each;
  have hadd := CommonNotion2 hACD (Eq.refl (∠ A C B))
  -- therefore the angles ACD, ACB are equal to the three angles ABC, BCA, CAB.
  have hthree : ∠ A C D + ∠ A C B = ∠ A B C + ∠ B C A + ∠ C A B := by
    rw [hadd, angle_symm hABC.ne₁₃ hABC.ne₂₃,
      add_comm (∠ C A B), add_assoc, add_comm (∠ C A B), ← add_assoc]
  -- But the angles ACD, ACB are equal to two right angles; [I. 13]
  have hright : ∠ A C D + ∠ A C B = ∟ + ∟ := by
    rw [add_comm, angle_symm hABC.ne₁₃ hABC.ne₂₃]
    exact Prop13 hBCD (Triangle.of_line hB_BC hD_BC (ne_of_between_ends hBCD)
      (hABC.bca.off_line hB_BC hC_BC))
  -- therefore the angles ABC, BCA, CAB are also equal to two right angles.
  have hsum : ∠ A B C + ∠ B C A + ∠ C A B = ∟ + ∟ := hthree.symm.trans hright
  -- Therefore etc.
  exact ⟨hACD, hsum⟩
  -- Q. E. D.

end Elements.BookI
