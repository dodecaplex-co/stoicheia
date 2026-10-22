import Elements.Figure.Basics
import Elements.BookI.Prop08
import Elements.BookI.Prop11
import Elements.BookI.Prop28
import Elements.BookI.Prop46
import Elements.BookI.Prop47
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 48

Euclid's text, in Heath's translation: [`heath/I/48.md`](../../heath/I/48.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Each square is described on its side: its two far corners lie on one side of the
side it stands on (Def. I.22 alone does not say so). Either side will do.
-/

namespace Elements.BookI

open Tacit

/-- If in a triangle the square on one of the sides be equal to the squares on the remaining two
sides of the triangle, the angle contained by the remaining two sides of the triangle is right. -/
theorem Prop48 {A B C P Q R S T U : Point} (hABC : Triangle A B C)
    (hBC : Square B P Q C) (hPQ : SameSideOf P Q B C)
    (hBA : Square A B R S) (hRS : SameSideOf R S A B)
    (hAC : Square A C T U) (hTU : SameSideOf T U A C)
    (h : quadArea B P Q C = quadArea A B R S + quadArea A C T U) :
    ∠ B A C = ∟ := by
  -- For in the triangle ABC let the square on one side BC be equal to the squares on the sides
  -- BA, AC;
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hABC.ne₁₃
  -- I say that the angle BAC is right.
  -- For let AD be drawn from the point A at right angles to the straight line AC,
  /- On the other side of AC from B, as in Euclid's figure. I.11 gives a point
     D₀ on the perpendicular; D is then taken on the ray from A through D₀. -/
  obtain ⟨X, hXB, -⟩ := exists_oppositeSidesOf hABC.acb []
  obtain ⟨D₀, hD₀X, hright⟩ :=
    Prop11 hABC.ne₁₃ ⟨AC, hA_AC, hC_AC, hA_AC⟩ hXB.triangle
  -- let AD be made equal to BA,
  obtain ⟨D, hD, hAD⟩ := OnRay.exists_len_eq hABC.ne₁₂ hD₀X.triangle.ne₁₃
  -- and let DC be joined.
  have hDB : OppositeSidesOf D B A C := (SameSideOf.of_onRay hD hD₀X).trans_opposite hXB
  have hADC : Triangle A D C := hDB.triangle.acb
  have hDAC : ∠ D A C = ∟ := by
    rw [angle_symm hADC.ne₁₂.symm hADC.ne₁₃.symm, angle_onRay_right hD hABC.ne₁₃.symm]
    exact hright C ⟨AC, hA_AC, hC_AC, hC_AC⟩ hABC.ne₁₃.symm
  -- Since DA is equal to AB, the square on DA is also equal to the square on AB.
  /- Describe the square on DA away from C, so that I.47 will apply. -/
  obtain ⟨X₂, hX₂C, -⟩ := exists_oppositeSidesOf hADC.bac []
  obtain ⟨R', S', hsqDA, hR', hS'⟩ := Prop46 hADC.ne₁₂.symm hX₂C.triangle
  have hR'S' : SameSideOf R' S' A D := (hR'.trans hS'.symm).swap
  have hDA_AB : quadArea A D R' S' = quadArea A B R S :=
    Prop46.square_eq hsqDA.rotate.rotate.rotate hR'S' hBA hRS hAD
  -- Let the square on AC be added to each; therefore the squares on DA, AC are equal to the
  -- squares on BA, AC.
  /- The square on AC is described away from D. Its area is that of the given
     square on AC, whichever side that square occupies. -/
  obtain ⟨X₃, hX₃D, -⟩ := exists_oppositeSidesOf hADC.cab []
  obtain ⟨T', U', hsqAC, hT', hU'⟩ := Prop46 hADC.ne₁₃.symm hX₃D.triangle
  have hT'U' : SameSideOf T' U' A C := (hT'.trans hU'.symm).swap
  have hAC_AC : quadArea A C T' U' = quadArea A C T U :=
    Prop46.square_eq hsqAC.rotate.rotate.rotate hT'U' hAC hTU rfl
  have hsum : quadArea A D R' S' + quadArea A C T' U' =
      quadArea A B R S + quadArea A C T U := CommonNotion2 hDA_AB hAC_AC
  -- But the square on DC is equal to the squares on DA, AC, for the angle DAC is
  -- right; [I. 47] and the square on BC is equal to the squares on BA, AC, for this is the
  -- hypothesis; therefore the square on DC is equal to the square on BC, so that the side DC
  -- is also equal to BC.
  obtain ⟨X₁, hX₁A, -⟩ := exists_oppositeSidesOf hADC.bca []
  obtain ⟨P', Q', hsqDC, hP', hQ'⟩ := Prop46 hADC.ne₂₃ hX₁A.triangle
  have h47 : quadArea D P' Q' C = quadArea A D R' S' + quadArea A C T' U' :=
    Prop47 hADC hDAC hsqDC (hP'.trans_opposite hX₁A) (hQ'.trans_opposite hX₁A)
      hsqDA.rotate.rotate.rotate (hR'.trans_opposite hX₂C).swap (hS'.trans_opposite hX₂C).swap
      hsqAC.rotate.rotate.rotate (hT'.trans_opposite hX₃D).swap (hU'.trans_opposite hX₃D).swap
  have hBCsum : quadArea B P Q C = quadArea A B R S + quadArea A C T U := h
  have hDC_BC : quadArea D P' Q' C = quadArea B P Q C :=
    (h47.trans hsum).trans hBCsum.symm
  /- Read both squares from C to compare their sides CD and CB. I.28 makes
     them parallelograms, and a parallelogram has one area, whichever diameter
     measures it. -/
  have hP'Q' : SameSideOf P' Q' D C := hP'.trans hQ'.symm
  have hsq : quadArea C D P' Q' = quadArea C B P Q := by
    have hpDC : Parallelogram C D P' Q' :=
      Prop28.square hsqDC.rotate.rotate.rotate hP'Q'.swap
    have hpBC : Parallelogram C B P Q := Prop28.square hBC.rotate.rotate.rotate hPQ.swap
    rw [← hpDC.quadArea_rotate, ← hpBC.quadArea_rotate]
    exact hDC_BC
  have hDC : ‖C D‖ = ‖C B‖ :=
    Prop46.side_eq hsqDC.rotate.rotate.rotate hP'Q'.swap hBC.rotate.rotate.rotate hPQ.swap hsq
  -- And, since DA is equal to AB, and AC is common, the two sides DA, AC are equal to the two
  -- sides BA, AC; and the base DC is equal to the base BC; therefore the angle DAC is equal to
  -- the angle BAC. [I. 8]
  have h8 : ∠ D A C = ∠ B A C :=
    Prop8 hADC hABC hAD rfl (by rw [len_symm D C, hDC, len_symm C B])
  -- But the angle DAC is right; therefore the angle BAC is also right.
  have hBAC : ∠ B A C = ∟ := h8.symm.trans hDAC
  -- Therefore etc.
  exact hBAC
  -- Q. E. D.

end Elements.BookI
