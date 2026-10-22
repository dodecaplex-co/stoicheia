import Elements.Figure.Convex.Facts

/-!
# Book Zero: a triangle with its sides, and a triangle cut in two

Two steps of brief 0013's route (section 8, rows A2 and A4 of its ledger). A closed triangle
is the three closed sides of its sides' straight lines, towards the opposite corners
(`closed_triangle_sides`, A2). A straight line from a corner to a point of the opposite side,
an end of it or between them, cuts the triangle into two that cover it and whose areas make
up its area (`triangle_cut_cover`, `area_cut_closed`, A4). No proof of the route cites A4:
the convex cut takes a crossing at an end of a side as a corner, and measures with the
library's `area_cut` (brief 0013, section 8, "The routes taken", C1).

The half-plane arguments follow the probe of 19 October (brief 0013, section 8). Nothing in
Book Zero cites a proposition of the *Elements*.
-/

namespace Elements.Figures

open Tacit

/-- **A closed triangle is three closed sides**: a point is within or on the triangle ABC
exactly when it is on the closed side of each side's straight line towards the opposite
corner. -/
theorem closed_triangle_sides {A B C X : Point} (h : Triangle A B C) :
    OnOrInsideTriangle X A B C ↔
      ClosedSide X A B C ∧ ClosedSide X B C A ∧ ClosedSide X C A B := by
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B h.ne₁₂
  obtain ⟨M, hBM, hCM⟩ := Postulate1 B C h.ne₂₃
  obtain ⟨N, hCN, hAN⟩ := Postulate1 C A h.ne₁₃.symm
  rw [closedSide_iff_half h.ne₂₃ hBM hCM, closedSide_iff_half h.ne₁₃.symm hCN hAN,
    closedSide_iff_half h.ne₁₂ hAL hBL]
  exact (triangle_halfplanes h hAL hBL hBM hCM hCN hAN).trans
    ⟨fun ⟨hL, hM, hN⟩ => ⟨hM, hN, hL⟩, fun ⟨hM, hN, hL⟩ => ⟨hL, hM, hN⟩⟩

/-- A triangle cut from a corner to a point of the opposite side, the point an end or between
the ends: the two parts make up its area. -/
theorem area_cut_closed {A B C D : Point} (h : OnFiniteLine D B C) :
    △ A B D + △ A D C = △ A B C := by
  rcases h with h | h | h
  · subst D
    rw [area_bca A B B, area_degenerate, add_comm 0, add_zero]
  · subst D
    rw [area_bca A C C, area_degenerate, add_zero]
  · exact area_cut h

/-- A triangle cut from a corner to a point of the opposite side: a point is within or on the
triangle exactly when it is within or on one of the two parts. -/
theorem triangle_cut_cover {A B C D X : Point} (hABC : Triangle A B C)
    (hD : OnFiniteLine D B C) :
    OnOrInsideTriangle X A B C ↔
      OnOrInsideTriangle X A B D ∨ OnOrInsideTriangle X A D C := by
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hABC.ne₁₂
  obtain ⟨M, hBM, hCM⟩ := Postulate1 B C hABC.ne₂₃
  obtain ⟨N, hCN, hAN⟩ := Postulate1 C A hABC.ne₁₃.symm
  have hAA : SameSide A A M := same_side_refl (hABC.bca.off_line hBM hCM)
  have hBB : SameSide B B N := same_side_refl (hABC.cab.off_line hCN hAN)
  have hCC : SameSide C C L := same_side_refl (hABC.off_line hAL hBL)
  have hDABC : OnOrInsideTriangle D A B C := by
    rcases hD with hD | hD | hD
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hD)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hD)))))
    · exact Or.inr (Or.inr (Or.inl hD))
  have hDL := closed_half hABC hAL hBL hDABC
  have hDM := closed_half hABC.bca hBM hCM (closed_rotate hDABC)
  have hDN := closed_half hABC.cab hCN hAN (closed_rotate (closed_rotate hDABC))
  constructor
  · intro hX
    rcases hD with hD | hD | hD
    · subst D
      exact Or.inr hX
    · subst D
      exact Or.inl hX
    have hDMline : OnLine D M := on_line_of_between_ends hD hBM hCM
    have hABD : Triangle A B D :=
      (Triangle.of_line hBM hDMline (ne_of_between hD)
        (hABC.bca.off_line hBM hCM)).cab
    have hADC : Triangle A D C :=
      (Triangle.of_line hDMline hCM (ne_of_between (between_symm hD)).symm
        (hABC.bca.off_line hBM hCM)).cab
    have hDC : SameSide D C L := hDL.resolve_left (hABD.off_line hAL hBL)
    have hDB : SameSide D B N := hDN.resolve_left (hADC.cab.off_line hCN hAN)
    obtain ⟨Q, hAQ, hDQ⟩ := Postulate1 A D hABD.ne₁₃
    obtain ⟨hXM, hXN, hXL⟩ := (closed_triangle_sides hABC).mp hX
    have hM := (closedSide_iff_half hABC.ne₂₃ hBM hCM).mp hXM
    have hN := (closedSide_iff_half hABC.ne₁₃.symm hCN hAN).mp hXN
    have hL := (closedSide_iff_half hABC.ne₁₂ hAL hBL).mp hXL
    have hleft (hQ : OnLine X Q ∨ SameSide X B Q) : OnOrInsideTriangle X A B D := by
      apply (closed_triangle_sides hABD).mpr
      refine ⟨(closedSide_iff_half hABD.ne₂₃ hBM hDMline).mpr hM,
        (closedSide_iff_half hABD.ne₁₃.symm hDQ hAQ).mpr hQ, ?_⟩
      apply (closedSide_iff_half hABD.ne₁₂ hAL hBL).mpr
      rcases hL with hL | hL
      · exact Or.inl hL
      · exact Or.inr (same_side_trans (same_side_symm hL) (same_side_symm hDC))
    have hright (hQ : OnLine X Q ∨ SameSide X C Q) : OnOrInsideTriangle X A D C := by
      apply (closed_triangle_sides hADC).mpr
      refine ⟨(closedSide_iff_half hADC.ne₂₃ hDMline hCM).mpr hM, ?_,
        (closedSide_iff_half hADC.ne₁₂ hAQ hDQ).mpr hQ⟩
      apply (closedSide_iff_half hADC.ne₁₃.symm hCN hAN).mpr
      rcases hN with hN | hN
      · exact Or.inl hN
      · exact Or.inr (same_side_trans (same_side_symm hN) (same_side_symm hDB))
    /- AD separates B and C by Pasch. A point on AD belongs to the first part;
    any other point is on B's side or C's side, which decides its part. -/
    by_cases hXQ : OnLine X Q
    · exact Or.inl (hleft (Or.inl hXQ))
    rcases same_side_or (hABD.acb.off_line hAQ hDQ) (hADC.off_line hAQ hDQ)
        hXQ (pasch3 hD hDQ) with hXB | hXC
    · exact Or.inl (hleft (Or.inr (same_side_symm hXB)))
    · exact Or.inr (hright (Or.inr (same_side_symm hXC)))
  · rintro (hX | hX)
    /- Each part's corners remain in the original three closed half-planes. This also
    covers a part with repeated corners when the cut ends at B or C. -/
    · apply (closed_triangle_sides hABC).mpr
      exact ⟨(closedSide_iff_half hABC.ne₂₃ hBM hCM).mpr
          (closed_in_half (Or.inr hAA) (Or.inl hBM) hDM hX),
        (closedSide_iff_half hABC.ne₁₃.symm hCN hAN).mpr
          (closed_in_half (Or.inl hAN) (Or.inr hBB) hDN hX),
        (closedSide_iff_half hABC.ne₁₂ hAL hBL).mpr
          (closed_in_half (Or.inl hAL) (Or.inl hBL) hDL hX)⟩
    · apply (closed_triangle_sides hABC).mpr
      exact ⟨(closedSide_iff_half hABC.ne₂₃ hBM hCM).mpr
          (closed_in_half (Or.inr hAA) hDM (Or.inl hCM) hX),
        (closedSide_iff_half hABC.ne₁₃.symm hCN hAN).mpr
          (closed_in_half (Or.inl hAN) hDN (Or.inl hCN) hX),
        (closedSide_iff_half hABC.ne₁₂ hAL hBL).mpr
          (closed_in_half (Or.inl hAL) hDL (Or.inr hCC) hX)⟩

end Elements.Figures
