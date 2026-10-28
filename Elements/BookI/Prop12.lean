import Elements.Figure.Basics
import Elements.Figure.Circles
import Elements.BookI.Prop08
import Elements.BookI.Prop10

/-!
# Book I, Proposition 12

Euclid's text, in Heath's translation: [`heath/I/12.md`](../../heath/I/12.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid proves that the angles CHG and CHE are right. The statement asks for
more, as "perpendicular to the infinite straight line AB" does: a right angle
with every other point of AB. Book Zero's `OnRay.cases_of_between` closes the
gap: every point of the straight line other than H lies on the ray from H
through G or on the ray from H through E. This is why CH, making right
angles with HG and with HE, makes a right angle with the whole of AB.
-/

namespace Elements.BookI

open Tacit

/-- To a given infinite straight line, from a given point which is not on it, to draw a
perpendicular straight line. -/
theorem Prop12 {A B C : Point} (hAB : A ≠ B) (hC : ¬ Collinear A B C) :
    ∃ H : Point, Collinear A B H ∧ ∀ P : Point, Collinear A B P → P ≠ H → ∠ C H P = ∟ := by
  -- Let AB be the given infinite straight line, and C the given point which is not on it;
  /- The infinite straight line AB is the straight line through A and B
     (Postulate 1), and C is off it, so ABC is a triangle. -/
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hABC : Triangle A B C := hC
  have hC_AB : ¬ OnLine C AB := hABC.off_line hA_AB hB_AB
  -- thus it is required to draw to the given infinite straight line AB, from the given point C
  -- which is not on it, a perpendicular straight line.
  -- For let a point D be taken at random on the other side of the straight line AB, and with
  -- centre C and distance CD let the circle EFG be described; [Post. 3]
  /- "At random on the other side" is System E, Points 6, which Book Zero gives
     as `exists_oppositeSidesOf`. D is not C, since C is not on the other
     side of AB from itself. -/
  obtain ⟨D, hDC, -⟩ := exists_oppositeSidesOf hABC []
  have hCD_AB : OppositeSides C D AB := hDC.symm.oppositeSides hA_AB hB_AB
  have hCD : C ≠ D := by
    rintro rfl
    exact hCD_AB.2.2 (same_side_refl hC_AB)
  obtain ⟨EFG, hC_EFG, hD_EFG⟩ := Postulate3 C D hCD
  /- C and D lie on opposite sides of AB, so CD crosses AB at a point X between
     them. X lies between the centre C and the point D on the circle, so it is
     within the circle, and AB, passing through it, cuts the circle in two points
     (Intersection 3). Heath's figure calls them G and E. F, the third letter of
     the circle's name, is only a name: the proof never uses it. -/
  obtain ⟨X, hX_AB, hCXD⟩ := hCD_AB.exists_between
  obtain ⟨E, G, hEG, hE_AB, hE_EFG, hG_AB, hG_EFG⟩ :=
    line_meets_circle_of_inside (InsideCircle.of_between_centre hC_EFG hD_EFG hCXD) hX_AB
  -- let the straight line EG be bisected at H, [I. 10]
  obtain ⟨H, hEHG, hEH_HG⟩ := Prop10 hEG
  have hH_AB : OnLine H AB := on_line_of_between_ends hEHG hE_AB hG_AB
  have hHG : H ≠ G := (ne_of_between (between_symm hEHG)).symm
  have hHE : H ≠ E := (ne_of_between hEHG).symm
  have hCH : C ≠ H := fun e => hC_AB (e ▸ hH_AB)
  -- and let the straight lines CG, CH, CE be joined. [Post. 1]
  /- Our proof uses only the points; the straight lines are drawn for the eye.
     It does use the two triangles they make with HG and HE: C is off AB, and H,
     G, E are on it. -/
  have hHGC : Triangle H G C := Triangle.of_line hH_AB hG_AB hHG hC_AB
  have hHEC : Triangle H E C := Triangle.of_line hH_AB hE_AB hHE hC_AB
  -- I say that CH has been drawn perpendicular to the given infinite straight line AB from the
  -- given point C which is not on it.
  -- For, since GH is equal to HE,
  have hGH_HE : ‖G H‖ = ‖H E‖ := (len_symm G H).trans (hEH_HG.symm.trans (len_symm E H))
  -- and HC is common,
  have hHC : ‖H C‖ = ‖H C‖ := rfl
  -- the two sides GH, HC are equal to the two sides EH, HC respectively;
  have hHG_HE : ‖H G‖ = ‖H E‖ := (len_symm H G).trans hGH_HE
  -- and the base CG is equal to the base CE;
  /- Both are radii of the circle EFG. [Def. 15] -/
  have hCG_CE : ‖C G‖ = ‖C E‖ := Definition15 hC_EFG hG_EFG hE_EFG
  -- therefore the angle CHG is equal to the angle EHC. [I. 8]
  have hGHC_EHC : ∠ G H C = ∠ E H C :=
    Prop8 hHGC hHEC hHG_HE hHC ((len_symm G C).trans (hCG_CE.trans (len_symm C E)))
  -- And they are adjacent angles.
  /- Adjacent: H lies between G and E, so HG and HE make one straight line. -/
  have hGHE : Between G H E := between_symm hEHG
  -- But, when a straight line set up on a straight line makes the adjacent angles equal to one
  -- another, each of the equal angles is right, and the straight line standing on the other is
  -- called a perpendicular to that on which it stands. [Def. 10]
  /- Definition I.10 is `IsRightAngle`: the angle GHC is right, its neighbour being
     CHE, and so is EHC, its neighbour being CHG. Each is then the right angle `∟`
     (Post. 4, as in I.11). -/
  have hGHC_right : IsRightAngle G H C :=
    ⟨E, hGHE, hHGC.bac, hGHC_EHC.trans (angle_symm hHE.symm hCH)⟩
  have hEHC_right : IsRightAngle E H C :=
    ⟨G, hEHG, hHEC.bac, hGHC_EHC.symm.trans (angle_symm hHG.symm hCH)⟩
  have hCHG : ∠ C H G = ∟ := (angle_symm hCH hHG.symm).trans (Postulate4 hGHC_right)
  have hCHE : ∠ C H E = ∟ := (angle_symm hCH hHE.symm).trans (Postulate4 hEHC_right)
  -- Therefore CH has been drawn perpendicular to the given infinite straight line AB from the
  -- given point C which is not on it.
  /- Perpendicular to the whole infinite straight line: any other point P of AB
     lies on the ray from H through G or on the ray from H through E
     (`OnRay.cases_of_between`), and then the angle CHP is the angle CHG or the
     angle CHE (`angle_onRay_right`). -/
  refine ⟨H, ⟨AB, hA_AB, hB_AB, hH_AB⟩, fun P hP hPH => ?_⟩
  obtain ⟨L, hA_L, hB_L, hP_L⟩ := hP
  rw [line_unique hAB hA_L hB_L hA_AB hB_AB] at hP_L
  rcases OnRay.cases_of_between hGHE hG_AB hE_AB hP_L hPH with hPG | hPE
  · exact (angle_onRay_right hPG hCH).trans hCHG
  · exact (angle_onRay_right hPE hCH).trans hCHE
  -- Q. E. F.

end Elements.BookI
