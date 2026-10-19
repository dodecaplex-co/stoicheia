import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop11
import Elements.BookI.Prop23
import Elements.BookIII.Prop02
import Elements.BookIII.Prop16
import Elements.BookIII.Prop32

/-!
# Book III, Proposition 34

Euclid's text, in Heath's translation: [`heath/III/34.md`](../../heath/III/34.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- From a given circle to cut off a segment admitting an angle equal to a given rectilineal angle. -/
theorem Prop34 {D₁ D D₂ : Point} {ABC : Circle} (hABC : ∃ O : Point, Centre O ABC)
    (hD : Triangle D₁ D D₂) :
    ∃ A B C : Point, OnCircle A ABC ∧ OnCircle B ABC ∧ OnCircle C ABC ∧ Triangle B A C ∧
      ∠ B A C = ∠ D₁ D D₂ := by
  -- Let ABC be the given circle, and the angle at D the given rectilineal angle;
  obtain ⟨O, hO⟩ := hABC
  -- thus it is required to cut off from the circle ABC a segment admitting an angle equal to
  -- the given rectilineal angle, the angle at D.
  -- Let EF be drawn touching ABC at the point B,
  /- The straight line at right angles to the radius at B touches the circle
     (I.11 and III.16, Porism). -/
  obtain ⟨B, hB, -⟩ := exists_point_on_circle ABC []
  have hOB : O ≠ B := (ne_of_centre_of_on hO hB).symm
  obtain ⟨LO, hO_LO, hB_LO⟩ := Postulate1 O B hOB
  obtain ⟨Q, hQ, -⟩ := exists_off_line hOB []
  obtain ⟨F, hFQ, hF⟩ := BookI.Prop11 hOB ⟨LO, hO_LO, hB_LO, hB_LO⟩ hQ
  have hOBF : ∠ O B F = ∟ := hF O ⟨LO, hO_LO, hB_LO, hO_LO⟩ hOB
  have hOBF' : Triangle O B F := hFQ.triangle
  have htouch : Touches B F ABC := Prop16.porism hO hB hOBF' hOBF
  have hBF : B ≠ F := htouch.1
  obtain ⟨E, hFBE⟩ := produce hBF.symm
  obtain ⟨L, hB_L, hF_L⟩ := Postulate1 B F hBF
  have hE_L : OnLine E L := on_line_of_between hFBE hF_L hB_L
  have hEF : Touches E F ABC :=
    htouch.of_collinear ⟨L, hB_L, hF_L, hE_L⟩ ⟨L, hB_L, hF_L, hF_L⟩
      (ne_of_between_ends hFBE).symm
  have hEBF : Between E B F := between_symm hFBE
  have hO_L : ¬ OnLine O L := hOBF'.bca.off_line hB_L hF_L
  -- and on the straight line FB, and at the point B on it, let the angle FBC be constructed
  -- equal to the angle at D. [I. 23]
  /- We copy the given angle on the centre's side of EF. -/
  obtain ⟨C', F', hF', hC'O, hC'BF'⟩ := BookI.Prop23 hBF hD hOBF'.bca
  have hC'B : C' ≠ B := hC'O.triangle.ne₁₃.symm
  have hcopy : ∠ F B C' = ∠ D₁ D D₂ :=
    (angle_onRay_left hF' hC'B).symm.trans ((angle_symm hF'.2.1 hC'B).trans hC'BF')
  /- Euclid reads C off the figure. The straight line BC' passes within the circle
     by III.16, so it meets the circle again. -/
  obtain ⟨B', -, -, hB'OB⟩ :=
    line_circle_beyond (centre_inside hO) hO_LO hB_LO hOB.symm
  have hBOB' : Between B O B' := between_symm hB'OB
  have hB'ray : OnRay B' B O := OnRay.of_beyond hBOB'
  have hB'BF : ∠ B' B F = ∟ := by
    rw [angle_onRay_left hB'ray hBF.symm, hOBF]
  have hBB'F : Triangle B B' F := by
    rintro ⟨K, hB_K, hB'_K, hF_K⟩
    exact hOBF' ⟨K, on_line_of_between_ends hBOB' hB_K hB'_K, hB_K, hF_K⟩
  obtain ⟨Z, hZcol, hZin⟩ :=
    (Prop16 hO hB hBOB' hBB'F hB'BF).2 C' hC'O.triangle
  have hZB : Z ≠ B := fun e => inside_not_on hZin (e ▸ hB)
  obtain ⟨N, hB_N, hC'_N⟩ := Postulate1 B C' hC'B.symm
  have hZ_N : OnLine Z N := by
    obtain ⟨K, hB_K, hC'_K, hZ_K⟩ := hZcol
    exact (line_unique hC'B.symm hB_K hC'_K hB_N hC'_N) ▸ hZ_K
  obtain ⟨C, hC, hC_N, hCZB⟩ := line_circle_beyond hZin hZ_N hB_N hZB.symm
  have hCB : C ≠ B := ne_of_between_ends hCZB
  /- C lies on the centre's side of EF, as in III.32: otherwise the straight line OC
     would cross EF within the circle, although EF touches it. -/
  have hCO : SameSide C O L := by
    have hC_L : ¬ OnLine C L := fun h =>
      (hEF.2 L hE_L hF_L).2 ⟨B, C, hCB.symm, hB_L, hB, h, hC⟩
    refine Classical.byContradiction fun hs => ?_
    obtain ⟨W, hW_L, hCWO⟩ := OppositeSides.exists_between ⟨hC_L, hO_L, hs⟩
    exact htouch.not_inside ⟨L, hB_L, hF_L, hW_L⟩
      (InsideCircle.of_between_centre hO hC (between_symm hCWO))
  have hCC' : SameSideOf C C' B F :=
    SameSideOf.of_line hBF hB_L hF_L (same_side_trans (same_side_symm hCO)
      (same_side_symm (hC'O.sameSide hB_L hF_L)))
  have hCray : OnRay C B C' :=
    OnRay.of_sameSideOf hCC' ⟨N, hB_N, hC'_N, hC_N⟩ hCB
  -- Then, since a straight line EF touches the circle ABC,
  -- and BC has been drawn across from the point of contact at B,
  have hBCF : Triangle B C F := hCC'.triangle.acb
  -- the angle FBC is equal to the angle constructed in the alternate segment BAC. [III. 32]
  obtain ⟨A, hA, hAF⟩ := Prop2.oppositeSide hB hC hBCF
  have h32 : ∠ F B C = ∠ B A C :=
    (Prop32 ⟨O, hO⟩ hB hC hCB.symm hEF hEBF).1 A hA hAF
  -- But the angle FBC is equal to the angle at D;
  have hFBC : ∠ F B C = ∠ D₁ D D₂ := by
    rw [angle_onRay_right hCray hBF.symm, hcopy]
  -- therefore the angle in the segment BAC is equal to the angle at D.
  have hBAC : ∠ B A C = ∠ D₁ D D₂ := h32.symm.trans hFBC
  -- Therefore from the given circle ABC the segment BAC has been cut off admitting an angle
  -- equal to the given rectilineal angle, the angle at D.
  exact ⟨A, B, C, hA, hB, hC, hAF.triangle.acb, hBAC⟩
  -- Q. E. F.

end Elements.BookIII
