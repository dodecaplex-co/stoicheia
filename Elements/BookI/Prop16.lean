import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop04
import Elements.BookI.Prop10
import Elements.BookI.Prop15

/-!
# Book I, Proposition 16

Euclid's text, in Heath's translation: [`heath/I/16.md`](../../heath/I/16.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid proves that the exterior angle `ACD` is greater than the angle `BAC`, and
then says "similarly" for the angle `ABC`, with `BC` bisected in place of `AC`.
So the Lean makes the argument once, for any triangle with a side produced, and
uses it twice.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- "Let BE be joined and produced in a straight line to F; let EF be made equal to
BE [I. 3]." I.3 cuts off from a greater straight line, and Postulate 2 produces `BE`
without saying how far. So first produce it beyond `E` to a point `X` with `EX`
greater than `BE`: produce `EB` beyond `B` to `P`, describe the circle with centre
`E` and distance `EP`, and take `X` where `BE` produced cuts it (System E,
Intersections 5). Then `EX` is equal to `EP` [Def. 15], which is greater than `EB`. -/
theorem Prop16.beyond {B E : Point} (h : B ≠ E) :
    ∃ X : Point, Between B E X ∧ ‖B E‖ < ‖E X‖ := by
  obtain ⟨P, hEBP⟩ := produce h.symm
  obtain ⟨α, hE_α, hP_α⟩ := Postulate3 E P (ne_of_between_ends hEBP)
  obtain ⟨L, hB_L, hE_L⟩ := Postulate1 B E h
  obtain ⟨X, hX_α, -, hXEB⟩ := line_circle_beyond (centre_inside hE_α) hE_L hB_L h
  refine ⟨X, between_symm hXEB, ?_⟩
  rw [len_symm B E, Definition15 hE_α hX_α hP_α]
  exact len_lt_of_between hEBP

/-- What Euclid sees in his figure: `F` lies within the angle `ECD`. It is on `D`'s
side of `AC`, because `AC` separates `B` from `F` (`E` is between them) and also `B`
from `D` (`C` is between them), and a straight line has only two sides. And it is on
`E`'s side of `BC`, because `BF` starts from `B` on `BC` and passes through `E`, off
it, on the way to `F` (System E, Pasch 2 and 3, Same side 5). -/
theorem Prop16.within {A B C D E F : Point} (hABC : Triangle A B C) (hBCD : Between B C D)
    (hAEC : Between A E C) (hBEF : Between B E F) :
    SameSideOf F D C E ∧ SameSideOf F E C D := by
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hABC.ne₁₃
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  obtain ⟨BE, hB_BE, hE_BE⟩ := Postulate1 B E (ne_of_between hBEF)
  have hE_AC : OnLine E AC := on_line_of_between_ends hAEC hA_AC hC_AC
  have hD_BC : OnLine D BC := on_line_of_between hBCD hB_BC hC_BC
  have hF_BE : OnLine F BE := on_line_of_between hBEF hB_BE hE_BE
  have hE_C : E ≠ C := (ne_of_between (between_symm hAEC)).symm
  have hC_D : C ≠ D := (ne_of_between (between_symm hBCD)).symm
  have hE_F : E ≠ F := (ne_of_between (between_symm hBEF)).symm
  /- Which points are off which straight lines. -/
  have hB_AC : ¬ OnLine B AC := hABC.acb.off_line hA_AC hC_AC
  have hA_BC : ¬ OnLine A BC := hABC.bca.off_line hB_BC hC_BC
  have hE_BC : ¬ OnLine E BC := fun h =>
    hA_BC ((line_unique hE_C hE_AC hC_AC h hC_BC) ▸ hA_AC)
  have hD_AC : ¬ OnLine D AC := fun h =>
    hB_AC ((line_unique hC_D hC_BC hD_BC hC_AC h) ▸ hB_BC)
  have hF_AC : ¬ OnLine F AC := fun h =>
    hB_AC ((line_unique hE_F hE_BE hF_BE hE_AC h) ▸ hB_BE)
  /- `AC` separates `B` from `F`, and `B` from `D`; so `F` and `D` are on one side. -/
  have hFD : SameSide F D AC := by
    rcases same_side_or hB_AC hF_AC hD_AC (pasch3 hBEF hE_AC) with h | h
    · exact absurd h (pasch3 hBCD hC_AC)
    · exact h
  /- `E` and `F` are on one side of `BC`. -/
  have hEF : SameSide E F BC := pasch2 hBEF hB_BC hE_BC
  exact ⟨SameSideOf.of_line hE_C.symm hC_AC hE_AC hFD,
    SameSideOf.of_line hC_D hC_BC hD_BC (same_side_symm hEF)⟩

/-- A straight line within an angle cuts it into two parts, each of them something. If
`F` lies within the angle `ECD` (on `D`'s side of `CE` and on `E`'s side of `CD`), the
angle `ECD` is made up of the angles `ECF` and `FCD` (System E, Diagram-angle 2), and
`FCD` is not nothing, since `F` is off the straight line `CD` (Diagram-angle 1). -/
theorem Prop16.part {C D E F : Point} (hFD : SameSideOf F D C E) (hFE : SameSideOf F E C D) :
    ∠ E C D = ∠ E C F + ∠ F C D ∧ 0 < ∠ F C D := by
  have hC_E : C ≠ E := hFD.1
  have hC_D : C ≠ D := hFE.1
  obtain ⟨L, hC_L, hE_L⟩ := Postulate1 C E hC_E
  obtain ⟨M, hC_M, hD_M⟩ := Postulate1 C D hC_D
  have hFD_L : SameSide F D L := hFD.sameSide hC_L hE_L
  have hFE_M : SameSide F E M := hFE.sameSide hC_M hD_M
  have hF_L : ¬ OnLine F L := not_on_line_of_same_side hFD_L
  have hF_M : ¬ OnLine F M := not_on_line_of_same_side hFE_M
  have hD_L : ¬ OnLine D L := not_on_line_of_same_side (same_side_symm hFD_L)
  have hLM : L ≠ M := fun e => hD_L (e ▸ hD_M)
  have hC_F : C ≠ F := fun e => hF_L (e ▸ hC_L)
  refine ⟨angle_add_of_inside hC_L hC_M hE_L hD_M hC_E hC_D hF_L hF_M hLM
    (same_side_symm hFE_M) (same_side_symm hFD_L), ?_⟩
  refine Magnitude.pos_of_ne_zero fun h0 => hF_M ?_
  rw [← angle_symm hC_D.symm hC_F.symm] at h0
  exact (same_ray_of_angle_eq_zero hC_D hC_F hC_M hD_M h0).1

/-- In any triangle, if one of the sides be produced, the exterior angle is greater than either of
the interior and opposite angles. -/
theorem Prop16 {A B C D : Point} (hABC : Triangle A B C) (hBCD : Between B C D) :
    ∠ C B A < ∠ A C D ∧ ∠ B A C < ∠ A C D := by
  -- Let ABC be a triangle, and let one side of it BC be produced to D;
  -- I say that the exterior angle ACD is greater than either of the interior and opposite
  -- angles CBA, BAC.
  /- Euclid proves the angle BAC less, and then says "similarly" for CBA. So we give
     his argument for every triangle with a side produced, in his letters, and use it
     twice below. It also hands back the point G on AC produced, which the "similarly"
     needs. -/
  have greater : ∀ {A B C D : Point}, Triangle A B C → Between B C D →
      ∃ G : Point, Between A C G ∧ ∠ B A C < ∠ A C D := by
    intro A B C D hABC hBCD
    have hA_C : A ≠ C := hABC.ne₁₃
    have hB_A : B ≠ A := hABC.ne₁₂.symm
    have hD_C : D ≠ C := ne_of_between (between_symm hBCD)
    obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hA_C
    have hB_AC : ¬ OnLine B AC := hABC.acb.off_line hA_AC hC_AC
    -- Let AC be bisected at E [I. 10], and let BE be joined and produced in a straight line to
    -- F;
    obtain ⟨E, hAEC, hAE_EC⟩ := Prop10 hA_C
    have hE_AC : OnLine E AC := on_line_of_between_ends hAEC hA_AC hC_AC
    have hB_E : B ≠ E := fun h => hB_AC (h ▸ hE_AC)
    obtain ⟨BE, hB_BE, hE_BE⟩ := Postulate1 B E hB_E
    /- Produced beyond E to a point X, far enough for I.3 to cut EF off from EX:
       `Prop16.beyond`. -/
    obtain ⟨X, hBEX, hBE_EX⟩ := Prop16.beyond hB_E
    -- let EF be made equal to BE [I. 3], let FC be joined [Post. 1], and let AC be drawn through
    -- to G [Post. 2].
    obtain ⟨F, hEFX, hEF_BE⟩ := Prop3 hB_E hBE_EX
    /- F lies between E and X, so E lies between B and F: BE produced reaches F. -/
    have hBEF : Between B E F :=
      between_symm (between_inner (between_symm hEFX) (between_symm hBEX))
    have hF_BE : OnLine F BE := on_line_of_between hBEF hB_BE hE_BE
    have hE_F : E ≠ F := (ne_of_between (between_symm hBEF)).symm
    have hF_AC : ¬ OnLine F AC := fun h =>
      hB_AC ((line_unique hE_F hE_BE hF_BE hE_AC h) ▸ hB_BE)
    have hF_C : F ≠ C := fun h => hF_AC (h ▸ hC_AC)
    obtain ⟨FC, hF_FC, hC_FC⟩ := Postulate1 F C hF_C
    obtain ⟨G, -, hACG, -⟩ := Postulate2 hA_AC hC_AC hA_C []
    -- Then, since AE is equal to EC, and BE to EF,
    have hBE_EF : ‖B E‖ = ‖E F‖ := hEF_BE.symm
    -- the two sides AE, EB are equal to the two sides CE, EF respectively;
    have hEA_EC : ‖E A‖ = ‖E C‖ := (len_symm E A).trans hAE_EC
    have hEB_EF : ‖E B‖ = ‖E F‖ := (len_symm E B).trans hBE_EF
    -- and the angle AEB is equal to the angle FEC,
    -- for they are vertical angles. [I. 15]
    /- AC and BF cut one another at E, and B is off AC. -/
    have hAEB_FEC : ∠ A E B = ∠ F E C := (Prop15 hAEC hBEF hABC.acb).1
    -- Therefore the base AB is equal to the base FC,
    /- I.4, applied to the triangles EAB and ECF: E and A, and E and C, lie on AC,
       with B and F off it. -/
    have hE_A : E ≠ A := (ne_of_between hAEC).symm
    have hE_C : E ≠ C := (ne_of_between (between_symm hAEC)).symm
    have hEAB : Triangle E A B := Triangle.of_line hE_AC hA_AC hE_A hB_AC
    have hECF : Triangle E C F := Triangle.of_line hE_AC hC_AC hE_C hF_AC
    have hAEB_CEF : ∠ A E B = ∠ C E F := hAEB_FEC.trans (angle_symm hE_F.symm hE_C.symm)
    obtain ⟨hAB_CF, hEAB_ECF, hEAB_ECF', hEBA_EFC⟩ := Prop4 hEAB hECF hEA_EC hEB_EF hAEB_CEF
    have hAB_FC : ‖A B‖ = ‖F C‖ := hAB_CF.trans (len_symm C F)
    -- and the triangle ABE is equal to the triangle CFE,
    have : △ A B E = △ C F E := by
      rw [area_rotate A B E, area_rotate C F E]
      exact hEAB_ECF
    -- and the remaining angles are equal to the remaining angles respectively, namely those
    -- which the equal sides subtend; [I. 4]
    have : ∠ E B A = ∠ E F C := hEBA_EFC
    -- therefore the angle BAE is equal to the angle ECF.
    have hBAE_ECF : ∠ B A E = ∠ E C F := (angle_symm hB_A hE_A).trans hEAB_ECF'
    -- But the angle ECD is greater than the angle ECF; [C.N. 5]
    /- Heath's figure shows F within the angle ECD (`Prop16.within`), so that the
       angle ECD is made up of the angles ECF and FCD, and FCD is something
       (`Prop16.part`). The whole is greater than the part. -/
    obtain ⟨hFD, hFE⟩ := Prop16.within hABC hBCD hAEC hBEF
    obtain ⟨hECD, hFCD⟩ := Prop16.part hFD hFE
    have hECF_ECD : ∠ E C F < ∠ E C D := by
      rw [hECD]
      exact CommonNotion5 hFCD
    -- therefore the angle ACD is greater than the angle BAE.
    /- The angle ECD is the angle ACD, since E lies on the ray from C through A
       (`angle_onRay_left`). -/
    have hBAE_ACD : ∠ B A E < ∠ A C D := by
      rw [hBAE_ECF, ← angle_onRay_left (OnRay.of_between (between_symm hAEC)) hD_C]
      exact hECF_ECD
    /- And the angle BAE is the angle BAC, since E lies on the ray from A through C. -/
    have hBAE_BAC : ∠ B A E = ∠ B A C := angle_onRay_right (OnRay.of_between hAEC) hB_A
    exact ⟨G, hACG, hBAE_BAC ▸ hBAE_ACD⟩
  /- Euclid's argument, in his own figure: the angle ACD is greater than the angle BAC,
     and AC is drawn through to G. -/
  obtain ⟨G, hACG, hBAC_ACD⟩ := greater hABC hBCD
  -- Similarly also, if BC be bisected, the angle BCG, that is, the angle ACD [I. 15], can be
  -- proved greater than the angle ABC as well.
  /- The same argument for the triangle BAC, with AC produced to G: now BC is bisected,
     and the exterior angle is BCG. -/
  obtain ⟨-, -, hABC_BCG⟩ := greater hABC.bac hACG
  /- AG and BD cut one another at C, and B is off AG: the vertical angles BCG and
     ACD are equal. [I. 15] -/
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hABC.ne₁₃
  have hAGB : Triangle A G B :=
    Triangle.of_line hA_AC (on_line_of_between hACG hA_AC hC_AC) (ne_of_between_ends hACG)
      (hABC.acb.off_line hA_AC hC_AC)
  have hBCG_ACD : ∠ B C G = ∠ A C D := (Prop15 hACG hBCD hAGB).2
  have hCBA_ACD : ∠ C B A < ∠ A C D := by
    rw [angle_symm hABC.ne₂₃.symm hABC.ne₁₂, ← hBCG_ACD]
    exact hABC_BCG
  -- Therefore etc.
  exact ⟨hCBA_ACD, hBAC_ACD⟩
  -- Q. E. D.

end Elements.BookI
