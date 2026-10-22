import Elements.Figure.Cells.CutHelpers
import Elements.Figure.Sums

/-!
# Staging: a convex outline as the common part of its sides' half-planes

Facts about lists of points and straight lines, for the common part of two cells and for
cells that tile a cell (brief 0013, section 8, "Content", steps 4 and 5). Each side of a
convex outline has a straight line, and the other corners lie on one side of it; so the
outline's inside is the common part of finitely many open half-planes, and its region the
common part of the same closed half-planes, each named by a straight line and one point on
the inward side. The inside has a point off any finitely many straight lines, inside the
first triangle of the fan. The route follows David Hilbert's theory of content, gratefully
acknowledged in brief 0006.
-/

namespace Elements.Figures

open Tacit

namespace CellFacts

/-- A point off the straight lines `l₁ ++ l₂` is off those of `l₁`. -/
theorem avoid_left {l₁ l₂ : List Line} {X : Point} (h : Avoid (l₁ ++ l₂) X) : Avoid l₁ X :=
  fun L hL => h L (List.mem_append_left _ hL)

/-- A point off the straight lines `l₁ ++ l₂` is off those of `l₂`. -/
theorem avoid_right {l₁ l₂ : List Line} {X : Point} (h : Avoid (l₁ ++ l₂) X) : Avoid l₂ X :=
  fun L hL => h L (List.mem_append_right _ hL)

/-- A sum whose terms are all nothing is nothing. -/
theorem sum_eq_zero {α : Type} {k : Kind} (l : List α) (f : α → Magnitude k)
    (h : ∀ a ∈ l, f a = 0) : Magnitude.sum (l.map f) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change f a + Magnitude.sum (l.map f) = 0
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb)), add_zero]

/-- Something holds of a member of a list's image exactly when it holds of the image of a
member. -/
theorem exists_mem_map_iff {α β : Type} (l : List α) (g : α → β) (p : β → Prop) :
    (∃ b ∈ l.map g, p b) ↔ ∃ a ∈ l, p (g a) := by
  constructor
  · rintro ⟨b, hb, hp⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact ⟨a, ha, hp⟩
  · rintro ⟨a, ha, hp⟩
    exact ⟨g a, List.mem_map.mpr ⟨a, ha, rfl⟩, hp⟩

/-- Something holds of a member of `a :: l` exactly when it holds of `a` or of a member of
`l`. -/
theorem exists_mem_cons_iff {α : Type} {a : α} {l : List α} {p : α → Prop} :
    (∃ b ∈ a :: l, p b) ↔ p a ∨ ∃ b ∈ l, p b := by
  constructor
  · rintro ⟨b, hb, hp⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl hp
    · exact Or.inr ⟨b, hb, hp⟩
  · rintro (hp | ⟨b, hb, hp⟩)
    · exact ⟨a, List.mem_cons_self, hp⟩
    · exact ⟨b, List.mem_cons_of_mem a hb, hp⟩

/-! ## Lists of things that may be missing

A piece of a cut may be nothing; the pieces present are counted by `filterMap id`. -/

/-- Replacing each member by another, nothing by nothing, does not add to the members
present. -/
theorem count_map_le {α : Type} (g : Option α → Option α) (hg : g none = none) :
    ∀ ts : List (Option α), ((ts.map g).filterMap id).length ≤ (ts.filterMap id).length
  | [] => Nat.le_refl 0
  | none :: ts => by
    simpa [List.filterMap_cons, hg] using count_map_le g hg ts
  | some a :: ts => by
    have ih := count_map_le g hg ts
    cases hga : g (some a) with
    | none =>
      simp only [List.map_cons, List.filterMap_cons, hga, id, List.length_cons]
      omega
    | some b =>
      simp only [List.map_cons, List.filterMap_cons, hga, id, List.length_cons]
      omega

/-- When no member is present, every member is nothing. -/
theorem all_none_of_count {α : Type} {ts : List (Option α)}
    (h : (ts.filterMap id).length = 0) : ∀ t ∈ ts, t = none := by
  intro t ht
  cases t with
  | none => rfl
  | some a =>
    have ha : a ∈ ts.filterMap id := List.mem_filterMap.mpr ⟨some a, ht, rfl⟩
    rw [List.eq_nil_of_length_eq_zero h] at ha
    simp at ha

/-- When some member is present, the list can be split at it. -/
theorem split_some {α : Type} {ts : List (Option α)} (h : ¬ ∀ t ∈ ts, t = none) :
    ∃ (pre : List (Option α)) (a : α) (post : List (Option α)), ts = pre ++ some a :: post := by
  have hex : ∃ t ∈ ts, t ≠ none :=
    Classical.byContradiction fun hn =>
      h fun t ht => Classical.byContradiction fun hne => hn ⟨t, ht, hne⟩
  obtain ⟨t, ht, hne⟩ := hex
  cases t with
  | none => exact absurd rfl hne
  | some a =>
    obtain ⟨pre, post, he⟩ := List.append_of_mem ht
    exact ⟨pre, a, post, he⟩

/-- Taking out one member present leaves one fewer. -/
theorem count_split {α : Type} (pre post : List (Option α)) (a : α) :
    ((pre ++ some a :: post).filterMap id).length = ((pre ++ post).filterMap id).length + 1 := by
  simp only [List.filterMap_append, List.filterMap_cons, id, List.length_append,
    List.length_cons]
  omega

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

/-- **A third corner**: given any two points, a convex outline has a corner that is neither. -/
theorem third_corner {cs : List Point} (h : ConvexOutline cs) (a b : Point) :
    ∃ R ∈ cs, R ≠ a ∧ R ≠ b := by
  obtain ⟨A, B, C, rest, rfl⟩ := three_corners h
  have hn := h.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at hn
  by_cases hA : A = a ∨ A = b
  · by_cases hB : B = a ∨ B = b
    · refine ⟨C, by simp, ?_, ?_⟩
      · rintro rfl
        rcases hA with rfl | rfl
        · exact hn.1.2.1 rfl
        · rcases hB with rfl | rfl
          · exact hn.2.1.1 rfl
          · exact hn.1.1 rfl
      · rintro rfl
        rcases hA with rfl | rfl
        · rcases hB with rfl | rfl
          · exact hn.1.1 rfl
          · exact hn.2.1.1 rfl
        · exact hn.1.2.1 rfl
    · simp only [not_or] at hB
      exact ⟨B, by simp, hB.1, hB.2⟩
  · simp only [not_or] at hA
    exact ⟨A, by simp, hA.1, hA.2⟩

/-- **One side's half-planes**: the straight line of a side of a convex outline, with a third
corner, names the open half-plane holding the outline's inside, as the side's conditions in
`ConvexCell.core` say, and the closed half-plane holding its region, as those in
`ConvexRegion` say. -/
theorem side_halfplane {cs : List Point} (h : ConvexOutline cs) {s : Point × Point}
    (hs : s ∈ sides cs) :
    ∃ (R : Point) (L : Line), ¬ OnLine R L ∧
      (∀ X : Point, (∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → SameSideOf X A s.1 s.2) ↔
        SameSide X R L) ∧
      (∀ X : Point, (∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → ClosedSide X A s.1 s.2) ↔
        Half X R L) := by
  obtain ⟨R, hR, hR₁, hR₂⟩ := third_corner h s.1 s.2
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

end Elements.Figures
