import Elements.Figure.Cells.CutHelpers
import Elements.Figure.Sums

/-!
# Book Zero: a convex outline as the common part of its sides' half-planes

Facts about lists of points and straight lines, in the namespace `CellFacts`, for cells that
tile a cell and for the common part of two cells (steps C2 and C3 of brief 0013's route:
section 8, "Content", steps 4 and 5). Each side of a convex outline has a straight line, and
the other corners lie on one side of it; so the outline's inside is the common part of
finitely many open half-planes, and its region the common part of the same closed
half-planes, each named by a straight line and one point on the inward side. The inside has
a point off any finitely many straight lines, inside the first triangle of the fan, and holds
every point between a point of the region and a point of the inside
(`ConvexCell.core_between`). The route follows David Hilbert's theory of content, gratefully
acknowledged in brief 0006.

Nothing in Book Zero cites a proposition of the *Elements*.
-/

namespace Elements.Figures

open Tacit

namespace CellFacts

/-- A point off the straight lines of two lists joined is off those of the first. -/
theorem avoid_left {l₁ l₂ : List Line} {X : Point} (h : Avoid (l₁ ++ l₂) X) : Avoid l₁ X :=
  fun L hL => h L (List.mem_append_left _ hL)

/-- A point off the straight lines of two lists joined is off those of the second. -/
theorem avoid_right {l₁ l₂ : List Line} {X : Point} (h : Avoid (l₁ ++ l₂) X) : Avoid l₂ X :=
  fun L hL => h L (List.mem_append_right _ hL)

/-- A convex outline has three corners at least, so it can be read as three corners and the
rest. -/
theorem three_corners {cs : List Point} (h : ConvexOutline cs) :
    ∃ A B C : Point, ∃ rest : List Point, cs = A :: B :: C :: rest := by
  have hl := h.1
  rcases cs with _ | ⟨A, _ | ⟨B, _ | ⟨C, rest⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp at hl
  · exact ⟨A, B, C, rest, rfl⟩

/-- **One side's half-planes**: the straight line of a side of a convex outline, with a third
corner, names the open half-plane holding the outline's inside, as the side's conditions in
`ConvexCell.Core` say, and the closed half-plane holding its region, as those in
`ConvexRegion` say. -/
theorem side_halfplane {cs : List Point} (h : ConvexOutline cs) {s : Point × Point}
    (hs : s ∈ sides cs) :
    ∃ (R : Point) (L : Line), ¬ OnLine R L ∧
      (∀ X : Point, (∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → SameSideOf X A s.1 s.2) ↔
        SameSide X R L) ∧
      (∀ X : Point, (∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → ClosedSide X A s.1 s.2) ↔
        Half X R L) := by
  obtain ⟨R, hR, hR₁, hR₂⟩ := convex_third h s
  have hRR := h.2.2 s hs R hR R hR hR₁ hR₂ hR₁ hR₂
  have hne : s.1 ≠ s.2 := hRR.1
  obtain ⟨L, h₁, h₂⟩ := Postulate1 s.1 s.2 hne
  have hRL : ¬ OnLine R L := not_on_line_of_same_side (hRR.sameSide h₁ h₂)
  have hAR {A : Point} (hA : A ∈ cs) (hA₁ : A ≠ s.1) (hA₂ : A ≠ s.2) : SameSide A R L :=
    (h.2.2 s hs A hA R hR hA₁ hA₂ hR₁ hR₂).sameSide h₁ h₂
  refine ⟨R, L, hRL, fun X => ⟨fun hX => (hX R hR hR₁ hR₂).sameSide h₁ h₂, ?_⟩,
    fun X => ⟨fun hX => ?_, ?_⟩⟩
  · intro hX A hA hA₁ hA₂
    exact SameSideOf.of_line hne h₁ h₂
      (same_side_trans (same_side_symm hX) (same_side_symm (hAR hA hA₁ hA₂)))
  · exact (closedSide_iff_half hne h₁ h₂).mp (hX R hR hR₁ hR₂)
  · intro hX A hA hA₁ hA₂
    apply (closedSide_iff_half hne h₁ h₂).mpr
    rcases hX with hX | hX
    · exact Or.inl hX
    · exact Or.inr (same_side_trans (same_side_symm hX) (same_side_symm (hAR hA hA₁ hA₂)))

/-- Several sides' half-planes at once, for any list of sides of a convex outline. -/
theorem sides_halfplanes {cs : List Point} (h : ConvexOutline cs) :
    ∀ ss : List (Point × Point), (∀ s ∈ ss, s ∈ sides cs) →
      ∃ hs : List (Point × Line), (∀ p ∈ hs, ¬ OnLine p.1 p.2) ∧
        (∀ X : Point, (∀ s ∈ ss, ∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → SameSideOf X A s.1 s.2) ↔
          ∀ p ∈ hs, SameSide X p.1 p.2) ∧
        (∀ X : Point, (∀ s ∈ ss, ∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → ClosedSide X A s.1 s.2) ↔
          ∀ p ∈ hs, Half X p.1 p.2)
  | [], _ => ⟨[], by simp, fun X => by simp, fun X => by simp⟩
  | s :: ss, hss => by
    obtain ⟨R, L, hRL, hopen, hclosed⟩ := side_halfplane h (hss s List.mem_cons_self)
    obtain ⟨hs, hoff, hopens, hcloseds⟩ :=
      sides_halfplanes h ss (fun t ht => hss t (List.mem_cons_of_mem s ht))
    refine ⟨(R, L) :: hs, ?_, fun X => ?_, fun X => ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hRL
      · exact hoff p hp
    · rw [List.forall_mem_cons, List.forall_mem_cons, hopen X, hopens X]
    · rw [List.forall_mem_cons, List.forall_mem_cons, hclosed X, hcloseds X]

/-- **A convex outline is the common part of its sides' half-planes**: finitely many straight
lines, each with a point off it, whose open sides make up the outline's inside, and whose
closed sides make up its region. -/
theorem outline_halfplanes {cs : List Point} (h : ConvexOutline cs) :
    ∃ hs : List (Point × Line), (∀ p ∈ hs, ¬ OnLine p.1 p.2) ∧
      (∀ X : Point, (∀ s ∈ sides cs, ∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → SameSideOf X A s.1 s.2) ↔
        ∀ p ∈ hs, SameSide X p.1 p.2) ∧
      (∀ X : Point, ConvexRegion cs X ↔ ∀ p ∈ hs, Half X p.1 p.2) :=
  sides_halfplanes h (sides cs) (fun _ hs => hs)

/-- **The inside of a convex outline has a point off any finitely many straight lines**: one
inside the first triangle of its fan, which is strictly on the inward side of every side. -/
theorem core_point_avoiding {cs : List Point} (h : ConvexOutline cs) (ls : List Line) :
    ∃ X : Point, Avoid ls X ∧
      ∀ s ∈ sides cs, ∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → SameSideOf X A s.1 s.2 := by
  obtain ⟨A, B, C, rest, rfl⟩ := three_corners h
  have hABC : Triangle A B C := fan_triangle h (A, B, C) (by simp [fan, segments])
  obtain ⟨X, hX, hXa⟩ := triangle_point_avoiding hABC ls
  refine ⟨X, hXa, fun s hs D hD hD₁ hD₂ => ?_⟩
  have hss := h.2.2 s hs D hD D hD hD₁ hD₂ hD₁ hD₂
  obtain ⟨L, h₁, h₂⟩ := Postulate1 s.1 s.2 hss.1
  exact SameSideOf.of_line hss.1 h₁ h₂ (cut_inside_closed_half
    (corner_half h hs hD hD₁ hD₂ (by simp) h₁ h₂)
    (corner_half h hs hD hD₁ hD₂ (by simp) h₁ h₂)
    (corner_half h hs hD hD₁ hD₂ (by simp) h₁ h₂) hX)

end CellFacts

/-! ## Between a cell's region and its inside -/

/-- A cell's inside holds every point between a point of its closed region and a point of
its inside: strictly within each side, by the closed side of the first and the open side of
the second. -/
theorem ConvexCell.core_between {Q : ConvexCell} {X W Z : Point} (hX : Q.Region X)
    (hZ : Q.Core Z) (hb : Between X W Z) : Q.Core W := by
  intro s hs A hA h1 h2
  have hne := convex_side_ne Q.convex hs
  obtain ⟨L, hL1, hL2⟩ := Postulate1 s.1 s.2 hne
  exact SameSideOf.of_line hne hL1 hL2 (Extreme.between_half_open
    ((closedSide_iff_half hne hL1 hL2).mp (hX s hs A hA h1 h2))
    ((hZ s hs A hA h1 h2).sameSide hL1 hL2) hb)

end Elements.Figures
