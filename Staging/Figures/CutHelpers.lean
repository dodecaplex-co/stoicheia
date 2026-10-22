import Staging.Figures.ConvexCover
import Staging.Figures.ConvexArea
import Staging.Figures.Closed
import Staging.Figures.Avoid
import Staging.Figures.ExtHelpers

/-!
Finite fan identities and the side geometry used in cutting convex outlines. The
content route owes its guiding decomposition argument to David Hilbert. These
lemmas are proved; several restate, under the names the cut's proof uses, facts proved
in ConvexFacts.lean, ExtHelpers.lean and Avoid.lean, and are proved by citing them.
-/

namespace Elements.Figures

open Tacit

/-- The first triangle of a fan, followed by the remaining triangles. -/
theorem cut_fan_cons (O A B : Point) (ps : List Point) :
    fanSum (O :: A :: B :: ps) = △ O A B + fanSum (O :: B :: ps) := rfl

/-- Closing the chain of a fan adds its last triangle. -/
theorem cut_fan_close (O A B : Point) (ps : List Point) :
    fanSum (O :: ((B :: ps) ++ [A])) =
      fanSum (O :: B :: ps) + △ O (endOf B ps) A := by
  induction ps generalizing B with
  | nil => simp [fanSum, fan, segments, Magnitude.sum, endOf, add_zero, add_comm]
  | cons C ps ih =>
    change △ O B C + fanSum (O :: ((C :: ps) ++ [A])) =
      (△ O B C + fanSum (O :: C :: ps)) + △ O (endOf C ps) A
    rw [ih, add_assoc]

/-- Closed half-planes contain the finite segments between their points. -/
theorem cut_half_between {X Y Z R : Point} {L : Line}
    (hX : OnLine X L ∨ SameSide X R L) (hZ : OnLine Z L ∨ SameSide Z R L)
    (h : Between X Y Z) : OnLine Y L ∨ SameSide Y R L :=
  half_between hX hZ h

/-- A finite segment with one end strictly inside a half-plane is strict away from
its other end. -/
theorem cut_strict_between {X Y Z R : Point} {L : Line}
    (hX : SameSide X R L) (hZ : OnLine Z L ∨ SameSide Z R L)
    (h : Between X Y Z) : SameSide Y R L := by
  have hoff : ¬ OnLine Y L := by
    intro hY
    rcases hZ with hZ | hZ
    · exact not_on_line_of_same_side hX (on_line_of_between (between_symm h) hZ hY)
    · exact pasch3 h hY (same_side_trans (same_side_symm hX) (same_side_symm hZ))
  exact (cut_half_between (Or.inr hX) hZ h).resolve_left hoff

/-- An interior point of a triangle lies strictly between a corner and the
opposite side. This is the crossbar theorem in finite-segment form. -/
theorem cut_inside_crossbar {X A B C : Point} (h : InsideTriangle X A B C) :
    ∃ Y : Point, Between B Y C ∧ Between A X Y :=
  inside_between h

/-- A triangle contained in a closed half-plane, with its first corner strictly
on that side, has its whole interior strictly on that side. -/
theorem cut_inside_half {X A B C R : Point} {L : Line}
    (hA : SameSide A R L) (hB : OnLine B L ∨ SameSide B R L)
    (hC : OnLine C L ∨ SameSide C R L) (h : InsideTriangle X A B C) :
    SameSide X R L := by
  obtain ⟨Y, hBYC, hAXY⟩ := cut_inside_crossbar h
  exact cut_strict_between hA (cut_half_between hB hC hBYC) hAXY

/-- The ends of each segment occur in its corner list. -/
theorem cut_segment_mem {ps : List Point} {A B : Point} (h : (A, B) ∈ segments ps) :
    A ∈ ps ∧ B ∈ ps :=
  segment_corners h

/-- Every corner of a nonempty closed outline begins a side. -/
theorem cut_side_at {A : Point} {ps : List Point} {D : Point}
    (hD : D ∈ A :: ps) : ∃ E : Point, (D, E) ∈ sides (A :: ps) :=
  outgoing_side hD

/-- A corner cannot lie in the closed triangle of three different corners. A
supporting line through that corner excludes the triangle's interior and sides. -/
theorem cut_corner_not_closed {ps : List Point} (h : ConvexOutline ps)
    {A B C D : Point} (hABC : Triangle A B C)
    (hA : A ∈ ps) (hB : B ∈ ps) (hC : C ∈ ps) (hD : D ∈ ps)
    (hDA : D ≠ A) (hDB : D ≠ B) (hDC : D ≠ C) :
    ¬ OnOrInsideTriangle D A B C :=
  corner_not_in_triangle h hD hA hB hC hDA hDB hDC hABC

/-- The ear at the second corner has every later corner strictly beyond its
opposite side. -/
theorem cut_ear_separates {A B C : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: C :: ps)) {D : Point} (hD : D ∈ ps) :
    OppositeSidesOf B D A C :=
  ear_opposite h hD

/-- Removing the third corner of an outline with at least four corners leaves a
convex outline. Its new side is the diagonal opposite the removed ear. -/
theorem cut_remove_third {A B C D : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: C :: D :: ps)) :
    ConvexOutline (A :: B :: D :: ps) :=
  h.erase_third

/-- An interior point of a segment from a line lies on the side of its other end. -/
theorem cut_between_side {A X B : Point} {L : Line}
    (h : Between A X B) (hB : OnLine B L) (hA : ¬ OnLine A L) : SameSide X A L :=
  Avoid.same_side_between_on (between_symm h) hB hA

/-- A separating diagonal and the two opposite supporting sides put the crossing
on both finite diagonals, so the two triangle sums agree. -/
theorem cut_quad_flip {A B C D : Point}
    (hAC : OppositeSidesOf A C B D) (hAB : SameSideOf C D A B)
    (hCD : SameSideOf A B C D) :
    △ A B C + △ A C D = △ B C D + △ A B D := by
  obtain ⟨L, hBL, hDL⟩ := Postulate1 B D hAC.1
  obtain ⟨X, hXL, hAXC⟩ := (hAC.oppositeSides hBL hDL).exists_between
  obtain ⟨M, hAM, hBM⟩ := Postulate1 A B hAB.1
  obtain ⟨N, hCN, hDN⟩ := Postulate1 C D hCD.1
  have hXM : SameSide X D M := same_side_trans
    (same_side_symm (cut_between_side (between_symm hAXC) hAM
      (hAB.triangle.off_line hAM hBM))) (hAB.sameSide hAM hBM)
  have hXN : SameSide X B N := same_side_trans
    (same_side_symm (cut_between_side hAXC hCN
      (hCD.triangle.off_line hCN hDN))) (hCD.sameSide hCN hDN)
  have hBX : B ≠ X := fun e => not_on_line_of_same_side hXM (e ▸ hBM)
  have hXD : X ≠ D := fun e => not_on_line_of_same_side hXN (e.symm ▸ hDN)
  have hBXD : Between B X D := by
    rcases between_cases hBX hXD hAC.1 hBL hXL hDL with hb | hb | hb
    · exact hb
    · exact False.elim (pasch3 hb hBM hXM)
    · exact False.elim (pasch3 hb hDN (same_side_symm hXN))
  have heq := (quadArea_rotate_of_cross hAXC hBXD).symm
  simpa only [quadArea, area_cab B D A] using heq

/-- Removing an ear subtracts the same triangle from every fan based on the
first side, including a point strictly between its ends. -/
theorem cut_boundary_flip {A B C D X : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: C :: D :: ps)) (hX : Between A X B) :
    △ X B C + △ X C D = △ B C D + △ X B D := by
  have hABC : Triangle A B C := fan_triangle h (A, B, C) (List.mem_cons_self ..)
  have hACD : Triangle A C D := fan_triangle h (A, C, D)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hABD : Triangle A B D := fan_triangle (cut_remove_third h) (A, B, D)
    (List.mem_cons_self ..)
  have hBCD : Triangle B C D := fan_triangle h.rotate (B, C, D) (List.mem_cons_self ..)
  have hac : OppositeSidesOf A C B D :=
    (cut_ear_separates h.rotate (D := A) (by simp)).symm
  have hxbc : SameSideOf X A B D := by
    obtain ⟨L, hBL, hDL⟩ := Postulate1 B D hABD.ne₂₃
    exact SameSideOf.of_line hABD.ne₂₃ hBL hDL
      (cut_between_side hX hBL (hABD.bca.off_line hBL hDL))
  apply cut_quad_flip (hxbc.trans_opposite hac)
  · refine ⟨(ne_of_between (between_symm hX)).symm, ?_⟩
    intro L hXL hBL
    have hAL := on_line_of_between (between_symm hX) hBL hXL
    exact (h.2.2 (A, B) (List.mem_cons_self ..) C (by simp) D (by simp)
      hABC.ne₁₃.symm hABC.ne₂₃.symm hACD.ne₁₃.symm hABD.ne₂₃.symm).sameSide hAL hBL
  · obtain ⟨L, hCL, hDL⟩ := Postulate1 C D hBCD.ne₂₃
    have hab : SameSideOf A B C D := h.2.2 (C, D)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      A (by simp) B (by simp) hACD.ne₁₂ hACD.ne₁₃ hBCD.ne₁₂ hBCD.ne₁₃
    have hax := pasch1 hX (hab.sameSide hCL hDL)
    exact SameSideOf.of_line hBCD.ne₂₃ hCL hDL
      (same_side_trans hax (hab.sameSide hCL hDL))

/-- The first ear is the same triangle whichever diagonal measures the first
four corners. -/
theorem cut_vertex_flip {A B C D : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: C :: D :: ps)) :
    △ A B C + △ A C D = △ B C D + △ A B D := by
  have hABC : Triangle A B C := fan_triangle h (A, B, C) (List.mem_cons_self ..)
  have hACD : Triangle A C D := fan_triangle h (A, C, D)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hABD : Triangle A B D := fan_triangle (cut_remove_third h) (A, B, D)
    (List.mem_cons_self ..)
  have hBCD : Triangle B C D := fan_triangle h.rotate (B, C, D) (List.mem_cons_self ..)
  apply cut_quad_flip (cut_ear_separates h.rotate (D := A) (by simp)).symm
  · exact h.2.2 (A, B) (List.mem_cons_self ..) C (by simp) D (by simp)
      hABC.ne₁₃.symm hABC.ne₂₃.symm hACD.ne₁₃.symm hABD.ne₂₃.symm
  · exact h.2.2 (C, D)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      A (by simp) B (by simp) hACD.ne₁₂ hACD.ne₁₃ hBCD.ne₁₂ hBCD.ne₁₃

/-- Repeating a fan's apex at the start of its chain contributes nothing. -/
theorem cut_fan_repeat (A : Point) (ps : List Point) :
    fanSum (A :: A :: ps) = fanSum (A :: ps) := by
  cases ps with
  | nil => rfl
  | cons B ps =>
    rw [cut_fan_cons, area_degenerate, add_comm, add_zero]

/-- A fan splits at any named corner of its chain, with the splitting corner
present at the end of the first chain and the start of the second. -/
theorem cut_fan_split (O B : Point) (us vs : List Point) :
    fanSum (O :: (us ++ B :: vs)) =
      fanSum (O :: (us ++ [B])) + fanSum (O :: B :: vs) := by
  induction us with
  | nil =>
    change fanSum (O :: B :: vs) = 0 + fanSum (O :: B :: vs)
    rw [add_comm, add_zero]
  | cons A us ih =>
    cases us with
    | nil =>
      change △ O A B + fanSum (O :: B :: vs) =
        (△ O A B + 0) + fanSum (O :: B :: vs)
      rw [add_zero]
    | cons C us =>
      change △ O A C + fanSum (O :: (C :: us ++ B :: vs)) =
        (△ O A C + fanSum (O :: (C :: us ++ [B]))) + fanSum (O :: B :: vs)
      rw [ih, add_assoc]

/-- Reading a convex outline after any initial chain preserves convexity. -/
theorem cut_convex_rotate_append (us vs : List Point) (h : ConvexOutline (us ++ vs)) :
    ConvexOutline (vs ++ us) :=
  Ext.convex_rotate_prefix us vs h

/-- Reading a convex outline after any initial chain preserves its fan sum. -/
theorem cut_fan_rotate_append (us vs : List Point) (h : ConvexOutline (us ++ vs)) :
    fanSum (vs ++ us) = fanSum (us ++ vs) :=
  Ext.fanSum_rotate_prefix us vs h

/-- If a closed half-plane contains a triangle, its interior is strictly on that
side: at least one corner must be off the supporting line. -/
theorem cut_inside_closed_half {X A B C R : Point} {L : Line}
    (hA : OnLine A L ∨ SameSide A R L) (hB : OnLine B L ∨ SameSide B R L)
    (hC : OnLine C L ∨ SameSide C R L) (h : InsideTriangle X A B C) :
    SameSide X R L := by
  by_cases hAL : OnLine A L
  · by_cases hBL : OnLine B L
    · have hCL : ¬ OnLine C L := fun hc => h.1.symm.triangle ⟨L, hBL, hc, hAL⟩
      exact cut_inside_half (hC.resolve_left hCL) hA hB ⟨h.2.2, h.1, h.2.1⟩
    · exact cut_inside_half (hB.resolve_left hBL) hC hA ⟨h.2.1, h.2.2, h.1⟩
  · exact cut_inside_half (hA.resolve_left hAL) hB hC h

/-- A closed half-plane containing a triangle's corners contains the whole
closed triangle. -/
theorem cut_closed_half {X A B C R : Point} {L : Line}
    (hA : OnLine A L ∨ SameSide A R L) (hB : OnLine B L ∨ SameSide B R L)
    (hC : OnLine C L ∨ SameSide C R L) (h : OnOrInsideTriangle X A B C) :
    OnLine X L ∨ SameSide X R L :=
  closed_in_half hA hB hC h

/-- A closed half-plane containing the corners contains the convex region. -/
theorem cut_region_half {ps : List Point} (h : ConvexOutline ps)
    {R : Point} {L : Line} (hc : ∀ A ∈ ps, OnLine A L ∨ SameSide A R L)
    {X : Point} (hX : ConvexRegion ps X) : OnLine X L ∨ SameSide X R L := by
  obtain ⟨t, ht, hXt⟩ := (fan_covers h X).mpr hX
  cases ps with
  | nil => simp [fan] at ht
  | cons A ps =>
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hB, hC⟩ := cut_segment_mem hs
    exact cut_closed_half (hc A (List.mem_cons_self ..))
      (hc s.1 (List.mem_cons_of_mem _ hB)) (hc s.2 (List.mem_cons_of_mem _ hC)) hXt

/-- A point strictly inside every supporting side has a small triangle about it
contained in the region. All the side conditions are collected into one finite list. -/
theorem cut_core_neighbourhood {ps : List Point} {X : Point}
    (hX : ∀ s ∈ sides ps, ∀ A ∈ ps, A ≠ s.1 → A ≠ s.2 → SameSideOf X A s.1 s.2) :
    ∃ A B C : Point, InsideTriangle X A B C ∧
      ∀ Y : Point, OnOrInsideTriangle Y A B C → ConvexRegion ps Y := by
  classical
  let line (s : Point × Point) : Line := Classical.choose (collinear_of_two s.1 s.2)
  have hl (s : Point × Point) : OnLine s.1 (line s) ∧ OnLine s.2 (line s) :=
    Classical.choose_spec (collinear_of_two s.1 s.2)
  let hs : List (Point × Line) := (sides ps).flatMap fun s =>
    (ps.filter fun A => A ≠ s.1 ∧ A ≠ s.2).map fun A => (A, line s)
  have hxs : ∀ t ∈ hs, SameSide X t.1 t.2 := by
    intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp ht
    have ha := List.mem_filter.mp hA
    have hne : A ≠ s.1 ∧ A ≠ s.2 := by simpa using ha.2
    exact (hX s hs A ha.1 hne.1 hne.2).sameSide (hl s).1 (hl s).2
  obtain ⟨A, B, C, hi, ht⟩ := small_triangle hs hxs
  refine ⟨A, B, C, hi, ?_⟩
  intro Y hY s hs_mem D hD hD₁ hD₂
  have hd_mem : D ∈ ps.filter (fun D => D ≠ s.1 ∧ D ≠ s.2) := by
    simp only [List.mem_filter, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hD, hD₁, hD₂⟩
  have hpair : (D, line s) ∈ hs := List.mem_flatMap.mpr
    ⟨s, hs_mem, List.mem_map.mpr ⟨D, hd_mem, rfl⟩⟩
  exact Or.inr (SameSideOf.of_line (hX s hs_mem D hD hD₁ hD₂).1 (hl s).1 (hl s).2
    (ht Y hY (D, line s) hpair))

end Elements.Figures
