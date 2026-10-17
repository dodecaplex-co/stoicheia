import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop05
import Elements.BookI.Helpers
import Elements.BookI.Prop16

/-!
# Book I, Proposition 18

Euclid's text, in Heath's translation: [`heath/I/18.md`](../../heath/I/18.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid cites I.3 and I.16. The step "the angle ADB is equal to the angle ABD,
since the side AB is equal to AD" is I.5, which he leaves uncited; the Lean
imports it.
-/

namespace Elements.BookI

open Tacit

/-- In any triangle the greater side subtends the greater angle. -/
theorem Prop18 {A B C : Point} (hABC : Triangle A B C) (h : ‖A B‖ < ‖A C‖) :
    ∠ B C A < ∠ A B C := by
  -- For let ABC be a triangle having the side AC greater than AB;
  have hA_B : A ≠ B := hABC.ne₁₂
  have hB_C : B ≠ C := hABC.ne₂₃
  have hA_C : A ≠ C := hABC.ne₁₃
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hA_C
  have hB_AC : ¬ OnLine B AC := hABC.acb.off_line hA_AC hC_AC
  -- I say that the angle ABC is also greater than the angle BCA.
  -- For, since AC is greater than AB, let AD be made equal to AB [I. 3], and let BD be joined.
  /- I.3 cuts off from AC, beginning at A, a straight line AD equal to AB; D lies
     between A and C. Joining BD is Postulate 1; Lean needs only the points. -/
  obtain ⟨D, hADC, hAD_AB⟩ := Prop3 hA_B h
  have hD_AC : OnLine D AC := on_line_of_between_ends hADC hA_AC hC_AC
  have hD_C : D ≠ C := (ne_of_between (between_symm hADC)).symm
  have hA_D : A ≠ D := ne_of_between hADC
  -- Then, since the angle ADB is an exterior angle of the triangle BCD,
  /- BCD is a triangle, since B is off the straight line AC on which C and D lie;
     and its side CD is produced to A, since D lies between C and A. -/
  have hBCD : Triangle B C D := (Triangle.of_line hC_AC hD_AC hD_C.symm hB_AC).cab
  have hCDA : Between C D A := between_symm hADC
  -- it is greater than the interior and opposite angle DCB. [I. 16]
  have hDCB_BDA : ∠ D C B < ∠ B D A := (Prop16 hBCD hCDA).1
  /- I.16 names the exterior angle BDA; read from the other arm, it is ADB. -/
  have hB_D : B ≠ D := fun e => hB_AC (e ▸ hD_AC)
  have hDCB_ADB : ∠ D C B < ∠ A D B := by
    rw [angle_symm hB_D hA_D] at hDCB_BDA
    exact hDCB_BDA
  -- But the angle ADB is equal to the angle ABD,
  -- since the side AB is equal to AD;
  /- This is I.5 (`Prop5.base`), for the isosceles triangle ABD. -/
  have hABD : Triangle A B D := (Triangle.of_line hA_AC hD_AC hA_D hB_AC).acb
  have hAB_AD : ‖A B‖ = ‖A D‖ := hAD_AB.symm
  have hABD_ADB : ∠ A B D = ∠ A D B := Prop5.base hABD hAB_AD
  -- therefore the angle ABD is also greater than the angle ACB;
  /- The angle DCB is the angle ACB, since D lies on the ray from C through A. -/
  have hDCB_ACB : ∠ D C B = ∠ A C B := angle_onRay_left (OnRay.of_between hCDA) hB_C
  have hACB_ABD : ∠ A C B < ∠ A B D := by
    rw [← hDCB_ACB, hABD_ADB]
    exact hDCB_ADB
  -- therefore the angle ABC is much greater than the angle ACB.
  /- The angle ABC is made up of ABD and DBC (`angle_add_of_between`), and DBC,
     an angle of the triangle DBC, is something (`Triangle.angle_pos`): the whole
     is greater than the part [C.N. 5]. -/
  have hABD_ABC : ∠ A B D < ∠ A B C := by
    rw [angle_add_of_between hABC.acb hADC]
    exact CommonNotion5 hBCD.cab.angle_pos
  have hACB_ABC : ∠ A C B < ∠ A B C := lt_trans hACB_ABD hABD_ABC
  -- Therefore etc.
  /- The angle ACB is the angle BCA, named from the other arm. -/
  rw [angle_symm hB_C hA_C]
  exact hACB_ABC
  -- Q. E. D.

end Elements.BookI
