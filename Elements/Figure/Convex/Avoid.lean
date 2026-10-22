import Elements.Figure.Convex.Facts

/-!
# Book Zero: points off finitely many straight lines

Step A3 of brief 0013's route (section 8). Arguments about figures often take a point "in
general position": off every straight line of a finite list (`Avoid`, in
`Foundations/Figures.lean`). Here such a point is found inside any triangle
(`triangle_point_avoiding`), and about any point a small triangle is found that stays on
the same side of finitely many straight lines as the point (`small_triangle`). The
shortening uses finite constructions and plane separation, with the facts about a triangle
that come first: a point between a corner and an inner point of the opposite side is inside
it (`inside_triangle_of_between`), every triangle has an inner point, and every point is
inside some triangle. The initial frame for `small_triangle` comes from `exists_off_line`,
whose proof draws circles and compares lengths. No coordinates or limiting argument is used.

These constructions support the route through David Hilbert's theory of content,
gratefully acknowledged in brief 0006. Nothing in Book Zero cites a proposition of the
*Elements*.
-/

namespace Elements.Figures

open Tacit

/-- A point between two points on one side of a straight line stays on that side: the open
form of `half_between`, for points strictly on the side. -/
theorem same_side_between {A B X P : Point} {L : Line}
    (h : Between A X B) (hA : SameSide A P L) (hB : SameSide B P L) :
    SameSide X P L := by
  have hAB := same_side_trans (same_side_symm hA) (same_side_symm hB)
  exact same_side_trans (pasch1 h hAB) hA

/-- Between a point on a straight line and a point off it, every point is on the
side of the latter. -/
theorem same_side_between_on {A B X : Point} {L : Line}
    (h : Between A X B) (hA : OnLine A L) (hB : ¬ OnLine B L) :
    SameSide X B L := by
  exact pasch2 h hA (fun hX => hB (on_line_of_between h hA hX))

/-- A segment starting off a straight line can be shortened to stay on its starting
side. If it crosses the line, take the new end before the crossing. -/
theorem shorten_off_line {A B : Point} {L : Line} (hAB : A ≠ B) (hA : ¬ OnLine A L) :
    ∃ C : Point, Between A C B ∧ SameSide C A L := by
  obtain ⟨M, hAM, hBM⟩ := Postulate1 A B hAB
  by_cases hB : OnLine B L
  · obtain ⟨C, -, hACB, -⟩ := exists_point_between hAM hBM hAB []
    exact ⟨C, hACB, same_side_between_on (between_symm hACB) hB hA⟩
  by_cases hs : SameSide A B L
  · obtain ⟨C, -, hACB, -⟩ := exists_point_between hAM hBM hAB []
    exact ⟨C, hACB, same_side_symm (pasch1 hACB hs)⟩
  obtain ⟨D, hDL, hADB⟩ := OppositeSides.exists_between ⟨hA, hB, hs⟩
  have hDM := on_line_of_between_ends hADB hAM hBM
  obtain ⟨C, -, hACD, -⟩ := exists_point_between hAM hDM (ne_of_between hADB) []
  exact ⟨C, between_of_between_left hADB hACD,
    same_side_between_on (between_symm hACD) hDL hA⟩

/-- A point between a corner and an inner point of the opposite side is inside
the triangle. -/
theorem inside_triangle_of_between {A B C D X : Point} (h : Triangle A B C)
    (hBDC : Between B D C) (hAXD : Between A X D) : InsideTriangle X A B C := by
  obtain ⟨L, hBL, hCL⟩ := Postulate1 B C h.ne₂₃
  obtain ⟨M, hCM, hAM⟩ := Postulate1 C A h.ne₁₃.symm
  obtain ⟨N, hAN, hBN⟩ := Postulate1 A B h.ne₁₂
  have hDL := on_line_of_between_ends hBDC hBL hCL
  have hDBM := same_side_between_on (between_symm hBDC) hCM (h.cab.off_line hCM hAM)
  have hDCN := same_side_between_on hBDC hBN (h.off_line hAN hBN)
  have hXDM := same_side_between_on hAXD hAM (not_on_line_of_same_side hDBM)
  have hXDN := same_side_between_on hAXD hAN (not_on_line_of_same_side hDCN)
  exact ⟨SameSideOf.of_line h.ne₂₃ hBL hCL
      (same_side_between_on (between_symm hAXD) hDL (h.bca.off_line hBL hCL)),
    SameSideOf.of_line h.ne₁₃.symm hCM hAM
      (same_side_trans (same_side_symm hXDM) hDBM),
    SameSideOf.of_line h.ne₁₂ hAN hBN
      (same_side_trans (same_side_symm hXDN) hDCN)⟩

/-- Every triangle contains an inner point, obtained by taking a point of a side
and then a point between it and the opposite corner. -/
theorem inside_exists {A B C : Point} (h : Triangle A B C) :
    ∃ X : Point, InsideTriangle X A B C := by
  obtain ⟨L, hB, hC⟩ := Postulate1 B C h.ne₂₃
  obtain ⟨D, hD, hBDC, -⟩ := exists_point_between hB hC h.ne₂₃ []
  have hAD : A ≠ D := fun e => h.bca.off_line hB hC (e ▸ hD)
  obtain ⟨M, hAM, hDM⟩ := Postulate1 A D hAD
  obtain ⟨X, -, hAXD, -⟩ := exists_point_between hAM hDM hAD []
  exact ⟨X, inside_triangle_of_between h hBDC hAXD⟩

/-- A triangle whose corners are on one side of a straight line lies wholly on that
side: extend an inner segment from a corner to the opposite side (`inside_through`). The open
form of `closed_in_half`, for corners strictly on the side. -/
theorem closed_same_side {A B C X P : Point} {L : Line}
    (hA : SameSide A P L) (hB : SameSide B P L) (hC : SameSide C P L)
    (hX : OnOrInsideTriangle X A B C) : SameSide X P L := by
  rcases hX with hX | hX | hX | hX | rfl | rfl | rfl
  · obtain ⟨D, hBXD, hADC⟩ := inside_through hX
    exact same_side_between hBXD hB (same_side_between hADC hA hC)
  · exact same_side_between hX hA hB
  · exact same_side_between hX hB hC
  · exact same_side_between hX hC hA
  · exact hA
  · exact hB
  · exact hC

/-- Shortening both sides from a corner retains a triangle whose inner points are
inside the original triangle. -/
theorem corner_triangle {A B C P Q : Point} (h : Triangle A B C)
    (hAPB : Between A P B) (hAQC : Between A Q C) :
    Triangle A P Q ∧ ∀ X, InsideTriangle X A P Q → InsideTriangle X A B C := by
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B h.ne₁₂
  obtain ⟨M, hCM, hAM⟩ := Postulate1 C A h.ne₁₃.symm
  obtain ⟨N, hBN, hCN⟩ := Postulate1 B C h.ne₂₃
  have hPL := on_line_of_between_ends hAPB hAL hBL
  have hQM := on_line_of_between_ends hAQC hAM hCM
  have hQCL := same_side_between_on hAQC hAL (h.off_line hAL hBL)
  have hPBM := same_side_between_on hAPB hAM (h.cab.off_line hCM hAM)
  have hAN : ¬ OnLine A N := h.bca.off_line hBN hCN
  have hPAN := same_side_between_on (between_symm hAPB) hBN hAN
  have hQAN := same_side_between_on (between_symm hAQC) hCN hAN
  refine ⟨Triangle.of_line hAL hPL (ne_of_between hAPB)
    (not_on_line_of_same_side hQCL), ?_⟩
  intro X hX
  exact ⟨SameSideOf.of_line h.ne₂₃ hBN hCN
      (closed_same_side (same_side_refl hAN) hPAN hQAN (Or.inl hX)),
    SameSideOf.of_line h.ne₁₃.symm hCM hAM
      (same_side_trans (same_side_symm (hX.2.1.sameSide hQM hAM)) hPBM),
    SameSideOf.of_line h.ne₁₂ hAL hBL
      (same_side_trans (same_side_symm (hX.2.2.sameSide hAL hPL)) hQCL)⟩

/-- **A point inside a triangle, off finitely many straight lines.** -/
theorem triangle_point_avoiding {A B C : Point} (h : Triangle A B C) (ls : List Line) :
    ∃ X : Point, InsideTriangle X A B C ∧ Avoid ls X := by
  induction ls generalizing A B C with
  | nil =>
      obtain ⟨X, hX⟩ := inside_exists h
      exact ⟨X, hX, by simp [Avoid]⟩
  | cons L ls ih =>
      have step {P Q R : Point} (ht : Triangle P Q R) (hP : ¬ OnLine P L) :
          ∃ X, InsideTriangle X P Q R ∧ Avoid (L :: ls) X := by
        obtain ⟨Q', hPQ'Q, hQ'⟩ := shorten_off_line ht.ne₁₂ hP
        obtain ⟨R', hPR'R, hR'⟩ := shorten_off_line ht.ne₁₃ hP
        obtain ⟨ht', hsub⟩ := corner_triangle ht hPQ'Q hPR'R
        obtain ⟨X, hX, havoid⟩ := ih ht'
        refine ⟨X, hsub X hX, ?_⟩
        intro M hM
        rcases List.mem_cons.mp hM with rfl | hM
        · exact not_on_line_of_same_side
            (closed_same_side (same_side_refl hP) hQ' hR' (Or.inl hX))
        · exact havoid M hM
      by_cases hA : OnLine A L
      · by_cases hB : OnLine B L
        · obtain ⟨X, hX, ha⟩ := step h.cab (h.off_line hA hB)
          exact ⟨X, ⟨hX.2.1, hX.2.2, hX.1⟩, ha⟩
        · obtain ⟨X, hX, ha⟩ := step h.bca hB
          exact ⟨X, ⟨hX.2.2, hX.1, hX.2.1⟩, ha⟩
      · exact step h hA

/-- Shorten a segment from X before each of finitely many straight lines. The new
end is on the prescribed side of every line, as X is. -/
theorem shorten_off_lines {X A : Point} (hXA : X ≠ A) (hs : List (Point × Line))
    (hX : ∀ s ∈ hs, SameSide X s.1 s.2) :
    ∃ B : Point, Between X B A ∧ ∀ s ∈ hs, SameSide B s.1 s.2 := by
  induction hs generalizing A with
  | nil =>
      obtain ⟨L, hXL, hAL⟩ := Postulate1 X A hXA
      obtain ⟨B, -, hXBA, -⟩ := exists_point_between hXL hAL hXA []
      exact ⟨B, hXBA, by simp⟩
  | cons s hs ih =>
      have hXs := hX s (List.mem_cons_self ..)
      have hXt : ∀ t ∈ hs, SameSide X t.1 t.2 :=
        fun t ht => hX t (List.mem_cons_of_mem s ht)
      obtain ⟨B, hXBA, hB⟩ := ih hXA hXt
      obtain ⟨C, hXCB, hCX⟩ := shorten_off_line (ne_of_between hXBA)
        (not_on_line_of_same_side hXs)
      refine ⟨C, between_of_between_left hXBA hXCB, ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact same_side_trans (same_side_symm hCX) hXs
      · exact same_side_between hXCB (hXt t ht) (hB t ht)

/-- Moving one corner towards an inner point, stopping before it, leaves that
point inside the triangle. Extend the inner segment to the opposite side
(`inside_through`). -/
theorem inside_shorten {A B C X P : Point} (hX : InsideTriangle X A B C)
    (hXP : Between X P A) : InsideTriangle X P B C := by
  obtain ⟨D, hAXD, hCDB⟩ := inside_through
    (show InsideTriangle X C A B from ⟨hX.2.2, hX.1, hX.2.1⟩)
  obtain ⟨L, hBL, hCL⟩ := Postulate1 B C hX.1.1
  have hXP_L := pasch1 hXP (hX.1.sameSide hBL hCL)
  have hP : Triangle P B C :=
    (Triangle.of_line hBL hCL hX.1.1
      (not_on_line_of_same_side (same_side_symm hXP_L))).cab
  exact inside_triangle_of_between hP (between_symm hCDB)
    (between_inner (between_symm hXP) hAXD)

/-- **Every point is inside some triangle.** Take a triangle with X as one corner, then
produce the segment from its opposite side through X. -/
theorem surrounding_triangle (X : Point) :
    ∃ A B C : Point, InsideTriangle X A B C := by
  obtain ⟨B, hB⟩ := exists_point [X]
  have hXB : X ≠ B := fun e => hB (e ▸ List.mem_singleton_self X)
  obtain ⟨C, hXBC, -⟩ := exists_off_line hXB []
  obtain ⟨L, hBL, hCL⟩ := Postulate1 B C hXBC.ne₂₃
  obtain ⟨D, hDL, hBDC, -⟩ := exists_point_between hBL hCL hXBC.ne₂₃ []
  have hXL := hXBC.bca.off_line hBL hCL
  have hXD : X ≠ D := fun e => hXL (e ▸ hDL)
  obtain ⟨A, hDXA⟩ := produce hXD.symm
  have hAL : ¬ OnLine A L := fun hAL =>
    hXL (on_line_of_between_ends hDXA hDL hAL)
  exact ⟨A, B, C, inside_triangle_of_between
    (Triangle.of_line hBL hCL hXBC.ne₂₃ hAL).cab hBDC (between_symm hDXA)⟩

/-- **A small triangle about a point**: given a point X on the same side as P of each of
finitely many straight lines L (the pairs `(P, L)`), there is a triangle with X inside
it, all of whose points, within or on it, are on those same sides. -/
theorem small_triangle {X : Point} (hs : List (Point × Line))
    (hX : ∀ s ∈ hs, SameSide X s.1 s.2) :
    ∃ A B C : Point, InsideTriangle X A B C ∧
      ∀ Y : Point, OnOrInsideTriangle Y A B C → ∀ s ∈ hs, SameSide Y s.1 s.2 := by
  obtain ⟨A, B, C, hABC⟩ := surrounding_triangle X
  have hXA : X ≠ A := hABC.2.2.triangle.ne₁₃.symm
  have hXB : X ≠ B := hABC.1.triangle.ne₁₃.symm
  have hXC : X ≠ C := hABC.2.1.triangle.ne₁₃.symm
  obtain ⟨A', hXA', hA'⟩ := shorten_off_lines hXA hs hX
  obtain ⟨B', hXB', hB'⟩ := shorten_off_lines hXB hs hX
  obtain ⟨C', hXC', hC'⟩ := shorten_off_lines hXC hs hX
  have hA'BC := inside_shorten hABC hXA'
  have hB'CA' := inside_shorten
    (show InsideTriangle X B C A' from ⟨hA'BC.2.1, hA'BC.2.2, hA'BC.1⟩) hXB'
  have hC'A'B' := inside_shorten
    (show InsideTriangle X C A' B' from ⟨hB'CA'.2.1, hB'CA'.2.2, hB'CA'.1⟩) hXC'
  refine ⟨A', B', C', ⟨hC'A'B'.2.1, hC'A'B'.2.2, hC'A'B'.1⟩, ?_⟩
  intro Y hY s hs'
  exact closed_same_side (hA' s hs') (hB' s hs') (hC' s hs') hY

end Elements.Figures
