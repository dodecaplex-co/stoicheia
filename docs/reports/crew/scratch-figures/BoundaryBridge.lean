import Elements.Figure.Angles

/-!
A scratch proof of brief 0013, kept unbuilt (docs/WORKFLOW.md, section 2): the probe of
19 October 2026 into I.45's and II.14's figures. From the root of a checkout that has built
`Elements`, `lake env lean` on this file checks it. Its arguments were carried into
`Staging/Figures/` (`ConvexFacts.lean`, `Closed.lean`, `ConvexAreaHelpers.lean`).
-/

namespace Elements.BoundaryProbe

open Tacit

/-- The closed side of a line containing R. This does not use a triangulation. -/
def Half (X R : Point) (L : Line) : Prop := OnLine X L ∨ SameSide X R L

theorem half_between {X Y Z R : Point} {L : Line}
    (hX : Half X R L) (hZ : Half Z R L) (h : Between X Y Z) : Half Y R L := by
  by_cases hY : OnLine Y L
  · exact Or.inl hY
  apply Or.inr
  rcases hX with hX | hX <;> rcases hZ with hZ | hZ
  · exact False.elim (hY (on_line_of_between_ends h hX hZ))
  · exact same_side_trans (same_side_symm (pasch2 h hX hY)) hZ
  · exact same_side_trans (same_side_symm (pasch2 (between_symm h) hZ hY)) hX
  · exact same_side_trans (pasch1 h
      (same_side_trans (same_side_symm hX) (same_side_symm hZ))) hX

theorem closed_rotate {X A B C : Point} (h : OnOrInsideTriangle X A B C) :
    OnOrInsideTriangle X B C A := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl ⟨h.2.1, h.2.2, h.1⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem closed_half {X A B C : Point} {L : Line}
    (hABC : Triangle A B C) (hA : OnLine A L) (hB : OnLine B L)
    (h : OnOrInsideTriangle X A B C) : Half X C L := by
  have hC : Half C C L := Or.inr (same_side_refl (hABC.off_line hA hB))
  rcases h with h | h | h | h | rfl | rfl | rfl
  · exact Or.inr (h.2.2.sameSide hA hB)
  · exact Or.inl (on_line_of_between_ends h hA hB)
  · exact half_between (Or.inl hB) hC h
  · exact half_between hC (Or.inl hA) h
  · exact Or.inl hA
  · exact Or.inl hB
  · exact hC

/-- On one side-line, the other two closed half-planes cut out the finite side. -/
theorem side_interval {X A B C : Point} {L M N : Line}
    (hABC : Triangle A B C) (hAL : OnLine A L) (hBL : OnLine B L)
    (hBM : OnLine B M) (hCM : OnLine C M)
    (hCN : OnLine C N) (hAN : OnLine A N)
    (hXL : OnLine X L) (hM : Half X A M) (hN : Half X B N) :
    OnFiniteLine X A B := by
  by_cases hXA : X = A
  · exact Or.inl hXA
  by_cases hXB : X = B
  · exact Or.inr (Or.inl hXB)
  have hXM : ¬ OnLine X M := fun h => hABC.bca.off_line hBM hCM
    ((line_unique hXB hXL hBL h hBM) ▸ hAL)
  have hXN : ¬ OnLine X N := fun h => hABC.cab.off_line hCN hAN
    ((line_unique hXA hXL hAL h hAN) ▸ hBL)
  have hsM := hM.resolve_left hXM
  have hsN := hN.resolve_left hXN
  rcases between_cases (Ne.symm hXA) hXB hABC.ne₁₂ hAL hXL hBL with h | h | h
  · exact Or.inr (Or.inr h)
  · exact False.elim (pasch3 h hAN hsN)
  · exact False.elim (pasch3 h hBM (same_side_symm hsM))

/-- A closed triangle is exactly the intersection of its three inward half-planes. -/
theorem triangle_halfplanes {X A B C : Point} {L M N : Line}
    (hABC : Triangle A B C) (hAL : OnLine A L) (hBL : OnLine B L)
    (hBM : OnLine B M) (hCM : OnLine C M)
    (hCN : OnLine C N) (hAN : OnLine A N) :
    OnOrInsideTriangle X A B C ↔ Half X C L ∧ Half X A M ∧ Half X B N := by
  constructor
  · intro h
    exact ⟨closed_half hABC hAL hBL h,
      closed_half hABC.bca hBM hCM (closed_rotate h),
      closed_half hABC.cab hCN hAN (closed_rotate (closed_rotate h))⟩
  · rintro ⟨hL, hM, hN⟩
    by_cases hXL : OnLine X L
    · rcases side_interval hABC hAL hBL hBM hCM hCN hAN hXL hM hN with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inl h)
    by_cases hXM : OnLine X M
    · rcases side_interval hABC.bca hBM hCM hCN hAN hAL hBL hXM hN hL with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      · exact Or.inr (Or.inr (Or.inl h))
    by_cases hXN : OnLine X N
    · rcases side_interval hABC.cab hCN hAN hAL hBL hBM hCM hXN hL hM with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    exact Or.inl ⟨SameSideOf.of_line hABC.ne₂₃ hBM hCM (hM.resolve_left hXM),
      SameSideOf.of_line hABC.ne₁₃.symm hCN hAN (hN.resolve_left hXN),
      SameSideOf.of_line hABC.ne₁₂ hAL hBL (hL.resolve_left hXL)⟩

theorem closed_in_half {X A B C R : Point} {L : Line}
    (hA : Half A R L) (hB : Half B R L) (hC : Half C R L)
    (h : OnOrInsideTriangle X A B C) : Half X R L := by
  rcases h with h | h | h | h | rfl | rfl | rfl
  · obtain ⟨Y, hBYC, hY⟩ := crossbar h.2.2 h.2.1.swap
    have hAX : A ≠ X := h.2.2.triangle.ne₁₃
    obtain ⟨M, hBM, hCM⟩ := Postulate1 B C h.1.1
    have hYM := on_line_of_between_ends hBYC hBM hCM
    have hXY : X ≠ Y := fun e =>
      not_on_line_of_same_side (h.1.sameSide hBM hCM) (e.symm ▸ hYM)
    obtain ⟨N, hAN, hXN, hYN⟩ := hY.2.2.1
    have hAXY : Between A X Y := by
      rcases between_cases hAX hXY hY.2.1.symm hAN hXN hYN with hb | hb | hb
      · exact hb
      · exact False.elim (hY.2.2.2 (between_symm hb))
      · exact False.elim (pasch3 hb hYM (same_side_symm (h.1.sameSide hBM hCM)))
    exact half_between hA (half_between hB hC hBYC) hAXY
  · exact half_between hA hB h
  · exact half_between hB hC h
  · exact half_between hC hA h
  · exact hA
  · exact hB
  · exact hC

/-- For a strictly convex quadrilateral given by its four supporting sides,
the two fan triangles fill exactly the intersection of the inward half-planes. -/
theorem quadrilateral_bridge {X A B C D : Point} {L M N P : Line}
    (hAB : SameSideOf C D A B) (hBC : SameSideOf D A B C)
    (hCD : SameSideOf A B C D) (hDA : SameSideOf B C D A)
    (hAL : OnLine A L) (hBL : OnLine B L)
    (hBM : OnLine B M) (hCM : OnLine C M)
    (hCN : OnLine C N) (hDN : OnLine D N)
    (hDP : OnLine D P) (hAP : OnLine A P) :
    (OnOrInsideTriangle X A B C ∨ OnOrInsideTriangle X A C D) ↔
      Half X C L ∧ Half X A M ∧ Half X A N ∧ Half X C P := by
  have hABC : Triangle A B C := hAB.triangle
  have hACD : Triangle A C D := hDA.symm.triangle.bca
  obtain ⟨Q, hAQ, hCQ⟩ := Postulate1 A C hABC.ne₁₃
  have hB : ¬ OnLine B Q := hABC.acb.off_line hAQ hCQ
  have hD : ¬ OnLine D Q := hACD.off_line hAQ hCQ
  have hBD : ¬ SameSide B D Q := triple_incidence1 hAL hAQ hAP hBL hCQ hDP
    (hAB.sameSide hAL hBL) (hDA.sameSide hDP hAP)
  constructor
  · intro h
    rcases h with h | h
    · exact ⟨closed_half hABC hAL hBL h,
        closed_half hABC.bca hBM hCM (closed_rotate h),
        closed_in_half (Or.inr (same_side_refl (hCD.triangle.off_line hCN hDN)))
          (Or.inr (same_side_symm (hCD.sameSide hCN hDN))) (Or.inl hCN) h,
        closed_in_half (Or.inl hAP) (Or.inr (hDA.sameSide hDP hAP))
          (Or.inr (same_side_refl (hDA.symm.triangle.off_line hDP hAP))) h⟩
    · exact ⟨closed_in_half (Or.inl hAL)
          (Or.inr (same_side_refl (hABC.off_line hAL hBL)))
          (Or.inr (same_side_symm (hAB.sameSide hAL hBL))) h,
        closed_in_half (Or.inr (same_side_refl (hBC.symm.triangle.off_line hBM hCM)))
          (Or.inl hCM) (Or.inr (hBC.sameSide hBM hCM)) h,
        closed_half hACD.bca hCN hDN (closed_rotate h),
        closed_half hACD.cab hDP hAP (closed_rotate (closed_rotate h))⟩
  · rintro ⟨hL, hM, hN, hP⟩
    by_cases hXQ : OnLine X Q
    · exact Or.inl ((triangle_halfplanes hABC hAL hBL hBM hCM hCQ hAQ).mpr
        ⟨hL, hM, Or.inl hXQ⟩)
    rcases same_side_or hB hD hXQ hBD with hXB | hXD
    · exact Or.inl ((triangle_halfplanes hABC hAL hBL hBM hCM hCQ hAQ).mpr
        ⟨hL, hM, Or.inr (same_side_symm hXB)⟩)
    · exact Or.inr ((triangle_halfplanes hACD hAQ hCQ hCN hDN hDP hAP).mpr
        ⟨Or.inr (same_side_symm hXD), hN, hP⟩)

end Elements.BoundaryProbe

#print axioms Elements.BoundaryProbe.triangle_halfplanes
#print axioms Elements.BoundaryProbe.quadrilateral_bridge
