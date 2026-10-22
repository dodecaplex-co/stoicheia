import Elements.Figure.Convex.Facts

/-!
# Book Zero: the fan of a convex outline covers its region

Step B3 of brief 0013's route (section 8): the boundary bridge for every strictly convex
outline. Its words, `ConvexOutline`, `ConvexRegion` and `fan`, are in
`Foundations/Figures.lean`. A convex outline stays convex read from another corner or the
other way round, and its region does not depend on the corner it is read from
(`convexRegion_rotate`). With at least four corners, cutting off the first
fan triangle leaves a smaller convex outline; the separating diagonal keeps the insides
apart (`fan_apart`) and places every point of the region in the first triangle or the
remaining fan, so the fan's triangles cover exactly the region (`fan_covers`).

Nothing in Book Zero cites a proposition of the *Elements*.
-/

namespace Elements.Figures

open Tacit

/-- A convex outline read from its second corner is convex. -/
theorem ConvexOutline.rotate {c : Point} {cs : List Point} (h : ConvexOutline (c :: cs)) :
    ConvexOutline (cs ++ [c]) := by
  exact (convexOutline_rotate_iff c cs).mpr h

/-- A convex outline read the other way round is convex. -/
theorem ConvexOutline.reverse {cs : List Point} (h : ConvexOutline cs) :
    ConvexOutline cs.reverse := by
  refine ⟨by simpa using h.1, ?_, ?_⟩
  · exact (List.reverse_perm cs).nodup_iff.mpr h.2.1
  · intro s hs P hP Q hQ hP₁ hP₂ hQ₁ hQ₂
    exact (h.2.2 s.swap ((mem_sides_reverse cs s).mp hs) P
      (List.mem_reverse.mp hP) Q (List.mem_reverse.mp hQ) hP₂ hP₁ hQ₂ hQ₁).swap

/-- The region does not depend on the corner the outline is read from. -/
theorem convexRegion_rotate (c : Point) (cs : List Point) (X : Point) :
    ConvexRegion (cs ++ [c]) X ↔ ConvexRegion (c :: cs) X := by
  constructor <;> intro h s hs P hP hP₁ hP₂
  · exact h s ((mem_sides_rotate c cs s).mpr hs) P
      (by simpa [or_comm] using hP) hP₁ hP₂
  · exact h s ((mem_sides_rotate c cs s).mp hs) P
      (by simpa [or_comm] using hP) hP₁ hP₂

/-- Each triangle of a convex outline's fan is a triangle. -/
theorem fan_triangle {cs : List Point} (h : ConvexOutline cs) :
    ∀ t ∈ fan cs, Triangle t.1 t.2.1 t.2.2 := by
  cases cs with
  | nil => simp [fan]
  | cons c cs =>
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    obtain ⟨h₁, h₂⟩ := segment_corners hs
    have hc := (List.nodup_cons.mp h.2.1).1
    have hn₁ : c ≠ s.1 := fun e => hc (e.symm ▸ h₁)
    have hn₂ : c ≠ s.2 := fun e => hc (e.symm ▸ h₂)
    exact (h.2.2 s (fan_base_side hs) c (by simp) c (by simp)
      hn₁ hn₂ hn₁ hn₂).triangle.cab

/-- No point is inside two triangles of a convex outline's fan. -/
theorem fan_apart {cs : List Point} (h : ConvexOutline cs) :
    (fan cs).Pairwise fun s s' => ∀ Y : Point,
      InsideTriangle Y s.1 s.2.1 s.2.2 → ¬ InsideTriangle Y s'.1 s'.2.1 s'.2.2 := by
  cases cs with
  | nil => simp [fan]
  | cons A bs =>
    induction bs with
    | nil => simp [fan, segments]
    | cons B bs ih =>
      cases bs with
      | nil => simp [fan, segments]
      | cons C ds =>
        cases ds with
        | nil => simp [fan, segments]
        | cons D ds =>
          /- The first triangle's interior is across AC from the remaining fan. -/
          have hcut := cut_convex h (by simp)
          change List.Pairwise _ ((A, B, C) :: fan (A :: C :: D :: ds))
          refine List.pairwise_cons.mpr ⟨?_, ih hcut⟩
          intro t ht Y hY hY'
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
          have ho := ear_opposite h (List.mem_cons_self (a := D) (l := ds))
          obtain ⟨N, hAN, hCN⟩ := Postulate1 A C ho.1
          have hBD := ho.oppositeSides hAN hCN
          have htail : ∀ P ∈ C :: D :: ds, Half P D N := by
            intro P hP
            rcases List.mem_cons.mp hP with rfl | hP
            · exact Or.inl hCN
            · exact Or.inr (((ear_opposite h hP).sameSideOf ho).sameSide hAN hCN)
          have hclosed := closed_in_half (Or.inl hAN)
            (htail s.1 (segment_corners hs).1) (htail s.2 (segment_corners hs).2)
            (Or.inl hY')
          have hYB := hY.2.1.swap.sameSide hAN hCN
          rcases hclosed with hclosed | hclosed
          · exact not_on_line_of_same_side hYB hclosed
          · exact hBD.2.2 (same_side_trans hYB hclosed)

/-- **The boundary bridge**: the fan's triangles cover exactly the region of the outline. -/
theorem fan_covers {cs : List Point} (h : ConvexOutline cs) (X : Point) :
    Covers (fan cs) X ↔ ConvexRegion cs X := by
  constructor
  · intro hx
    cases cs with
    | nil => simp [fan, Covers] at hx
    | cons A bs =>
      obtain ⟨t, ht, hx⟩ := hx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact triangle_in_region h (by simp)
        (List.mem_cons_of_mem _ (segment_corners hs).1)
        (List.mem_cons_of_mem _ (segment_corners hs).2) hx
  · intro hx
    cases cs with
    | nil => have he := h.1; simp at he
    | cons A bs =>
      induction bs with
      | nil => have he := h.1; simp at he
      | cons B bs ih =>
        cases bs with
        | nil => have he := h.1; simp at he
        | cons C ds =>
          have hABC : Triangle A B C := fan_triangle h (A, B, C) (by simp [fan, segments])
          obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hABC.ne₁₂
          obtain ⟨M, hBM, hCM⟩ := Postulate1 B C hABC.ne₂₃
          obtain ⟨N, hCN, hAN⟩ := Postulate1 C A hABC.ne₁₃.symm
          have hL : Half X C L := (closedSide_iff_half hABC.ne₁₂ hAL hBL).mp
            (hx (A, B) (by simp [sides, segments]) C (by simp)
              hABC.ne₁₃.symm hABC.ne₂₃.symm)
          have hM : Half X A M := (closedSide_iff_half hABC.ne₂₃ hBM hCM).mp
            (hx (B, C) (by simp [sides, segments]) A (by simp) hABC.ne₁₂ hABC.ne₁₃)
          have first : Half X B N → Covers (fan (A :: B :: C :: ds)) X := by
            intro hN
            exact ⟨(A, B, C), by simp [fan, segments],
              (triangle_halfplanes hABC hAL hBL hBM hCM hCN hAN).mpr ⟨hL, hM, hN⟩⟩
          /- On AC or towards B, the point is in ABC; across AC, use the smaller outline. -/
          by_cases hXB : Half X B N
          · exact first hXB
          have hXN : ¬ OnLine X N := fun hx => hXB (Or.inl hx)
          cases ds with
          | nil =>
            exact first ((closedSide_iff_half hABC.ne₁₃.symm hCN hAN).mp
              (hx (C, A) (by simp [sides, segments]) B (by simp)
                hABC.ne₂₃ hABC.ne₁₂.symm))
          | cons D ds =>
            have hcut := cut_convex h (by simp)
            have hxcut : ConvexRegion (A :: C :: D :: ds) X := by
              intro s hs P hP hP₁ hP₂
              change s ∈ (A, C) :: segments (C :: D :: ds ++ [A]) at hs
              rcases List.mem_cons.mp hs with rfl | hs
              · have hp : P ∈ D :: ds := by simpa [hP₁, hP₂] using hP
                have ho := (ear_opposite h hp).oppositeSides hAN hCN
                have hxp := (same_side_or ho.1 ho.2.1 hXN ho.2.2).resolve_left
                  (fun hx => hXB (Or.inr (same_side_symm hx)))
                exact Or.inr (SameSideOf.of_line hABC.ne₁₃ hAN hCN (same_side_symm hxp))
              · have hp : P ∈ A :: B :: C :: D :: ds := by
                  rcases List.mem_cons.mp hP with rfl | hP
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hP)
                exact hx s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
                  P hp hP₁ hP₂
            obtain ⟨t, ht, hXt⟩ := ih hcut hxcut
            exact ⟨t, List.mem_cons_of_mem _ ht, hXt⟩

end Elements.Figures
