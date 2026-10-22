import Elements.Foundations.Figures
import Elements.Figure.Basics
import Elements.Figure.Rectilineal
import Elements.Figure.Convex.Avoid
import Elements.Figure.Convex.Closed
import Elements.Figure.Convex.Cover
import Elements.Figure.Cells.ExtHelpers

/-!
# Book Zero: facts about loops, for the boundary bridges of brief 0013

Helper lemmas, in the namespace `LoopFacts`, for the proofs in `Outlines.lean` (brief 0013,
section 8, "Ray parity and the region"; D1, and D4 with its convex bridges). Nothing in Book
Zero cites a proposition of the *Elements*.

* **Listing.** The sides of an outline read from another corner are the same sides in another
  order; read the other way round, each side is read backwards. Boundary, crossing counts,
  good rays and simplicity depend only on the sides up to order and direction (`transfer`).
* **A frame.** Three corners of a simple loop make a triangle (`simple_frame`): were all its
  corners on one straight line, each would lie between its neighbours, and a closed chain
  cannot run straight on all the way round. Finite avoidance (`triangle_point_avoiding`)
  then finds a good ray inside that triangle, with no circle drawn.
* **Convex outlines.** A point strictly within one side is off every other side's straight
  line, so at most two sides cross a straight line through no corner (`convex_at_most_two`).
  A good ray from a point strictly inside crosses exactly one side (`convex_count_inside`),
  and one from outside the region none or two (`convex_count_outside`). These give the
  convex and triangle bridges directly, without parity independence.
-/

namespace Elements.Figures

open Tacit

namespace LoopFacts

/-! ## The sides of a list of corners -/

/-- The first ends of a chain's segments are its points before the last. -/
theorem segments_map_fst (a : Point) (l : List Point) (b : Point) :
    (segments (a :: l ++ [b])).map Prod.fst = a :: l := by
  induction l generalizing a with
  | nil => simp [segments]
  | cons d l ih =>
    have he : segments (a :: d :: l ++ [b]) = (a, d) :: segments (d :: l ++ [b]) := rfl
    rw [he, List.map_cons, ih]

/-- The first ends of the sides are the corners, in order. -/
theorem sides_map_fst (ps : List Point) : (sides ps).map Prod.fst = ps := by
  cases ps with
  | nil => rfl
  | cons c cs => exact segments_map_fst c cs c

/-- No two sides of a list of distinct corners start at one corner. -/
theorem sides_pairwise_fst {ps : List Point} (h : ps.Nodup) :
    (sides ps).Pairwise (fun s t => s.1 ≠ t.1) := by
  have hm : ((sides ps).map Prod.fst).Nodup := by rw [sides_map_fst]; exact h
  exact List.pairwise_map.mp hm

/-- The sides of a list of distinct corners are distinct. -/
theorem sides_nodup {ps : List Point} (h : ps.Nodup) : (sides ps).Nodup :=
  List.Pairwise.imp (fun {s t} (hne : s.1 ≠ t.1) (he : s = t) => hne (by rw [he]))
    (sides_pairwise_fst h)

/-- Two members of a list related pairwise are equal or related one way or the other. -/
theorem pairwise_mem {α : Type} {R : α → α → Prop} {l : List α} (hl : l.Pairwise R)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) : a = b ∨ R a b ∨ R b a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · exact Or.inl (ha'.trans hb'.symm)
    · exact Or.inr (Or.inl (ha' ▸ hl.1 b hb'))
    · exact Or.inr (Or.inr (hb' ▸ hl.1 a ha'))
    · exact ih hl.2 ha' hb'

/-- Two sides of a list of distinct corners that start at one corner are one side. -/
theorem sides_fst_inj {ps : List Point} (h : ps.Nodup) {s t : Point × Point}
    (hs : s ∈ sides ps) (ht : t ∈ sides ps) (he : s.1 = t.1) : s = t := by
  rcases pairwise_mem (sides_pairwise_fst h) hs ht with e | e | e
  · exact e
  · exact False.elim (e he)
  · exact False.elim (e he.symm)

/-- Both ends of a side are corners. -/
theorem side_mem {ps : List Point} {s : Point × Point} (hs : s ∈ sides ps) :
    s.1 ∈ ps ∧ s.2 ∈ ps := by
  cases ps with
  | nil => simp [sides] at hs
  | cons c cs =>
    obtain ⟨h₁, h₂⟩ := segment_corners hs
    have hm : ∀ P, P ∈ c :: cs ++ [c] → P ∈ c :: cs := by
      intro P hP
      rcases List.mem_append.mp hP with hP | hP
      · exact hP
      · rw [List.mem_singleton.mp hP]; exact List.mem_cons_self
    exact ⟨hm _ h₁, hm _ h₂⟩

/-- Every point after the first ends a segment of a chain. -/
theorem incoming_segment (a : Point) (l : List Point) {D : Point} (hD : D ∈ l) :
    ∃ Z : Point, (Z, D) ∈ segments (a :: l) := by
  induction l generalizing a with
  | nil => simp at hD
  | cons b l ih =>
    rcases List.mem_cons.mp hD with rfl | hD
    · exact ⟨a, List.mem_cons_self⟩
    · obtain ⟨Z, hZ⟩ := ih b hD
      exact ⟨Z, List.mem_cons_of_mem _ hZ⟩

/-- Every corner ends one of the sides. -/
theorem incoming_side {ps : List Point} {D : Point} (hD : D ∈ ps) :
    ∃ Z : Point, (Z, D) ∈ sides ps := by
  cases ps with
  | nil => simp at hD
  | cons c cs =>
    apply incoming_segment c (cs ++ [c])
    rcases List.mem_cons.mp hD with rfl | hD
    · simp
    · exact List.mem_append_left _ hD

/-- Reading a closed outline from a later corner gives the same sides, in another order. -/
theorem sides_rotate_perm (ps qs : List Point) :
    (sides (ps ++ qs)).Perm (sides (qs ++ ps)) := by
  cases ps with
  | nil => simp
  | cons a as =>
    cases qs with
    | nil => simp
    | cons b bs =>
      have h₁ : sides (a :: as ++ b :: bs) =
          segments (a :: as ++ [b]) ++ segments (b :: bs ++ [a]) := by
        show segments ((a :: (as ++ b :: bs)) ++ [a]) = _
        rw [show (a :: (as ++ b :: bs)) ++ [a] = (a :: as) ++ b :: (bs ++ [a]) by simp,
          segments_join]
        rfl
      have h₂ : sides (b :: bs ++ a :: as) =
          segments (b :: bs ++ [a]) ++ segments (a :: as ++ [b]) := by
        show segments ((b :: (bs ++ a :: as)) ++ [b]) = _
        rw [show (b :: (bs ++ a :: as)) ++ [b] = (b :: bs) ++ a :: (as ++ [b]) by simp,
          segments_join]
        rfl
      rw [h₁, h₂]
      exact List.perm_append_comm

/-- Reading a closed outline the other way round reverses its sides. -/
theorem sides_reverse_perm (ps : List Point) :
    (sides ps.reverse).Perm ((sides ps).map Prod.swap) := by
  cases ps with
  | nil => simp [sides]
  | cons c cs =>
    rw [List.reverse_cons]
    refine (sides_rotate_perm cs.reverse [c]).trans ?_
    have he : sides ([c] ++ cs.reverse) = segments ((c :: cs ++ [c]).reverse) := by
      simp [sides]
    rw [he, segments_reverse]
    exact (List.reverse_perm _).map _

/-! ## A loop read another way: reversed, or from another corner -/

/-- A finite straight line read from either end. -/
theorem onFiniteLine_comm {X A B : Point} : OnFiniteLine X A B ↔ OnFiniteLine X B A := by
  unfold OnFiniteLine
  constructor <;> rintro (h | h | h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (between_symm h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (between_symm h))

/-- Every straight line through the ends of a finite straight line passes through its
points. -/
theorem onFiniteLine_onLine {X A B : Point} {L : Line} (h : OnFiniteLine X A B)
    (hA : OnLine A L) (hB : OnLine B L) : OnLine X L := by
  rcases h with rfl | rfl | h
  · exact hA
  · exact hB
  · exact on_line_of_between_ends h hA hB

section Transfer

variable {f : Point × Point → Point × Point} (hf : ∀ s, f s = s ∨ f s = s.swap)
include hf

/-- A side read either way has the same points. -/
theorem finite_transfer (X : Point) (s : Point × Point) :
    OnFiniteLine X (f s).1 (f s).2 ↔ OnFiniteLine X s.1 s.2 := by
  rcases hf s with e | e <;> rw [e]
  exact onFiniteLine_comm

/-- A side read either way has the same ends. -/
theorem ends_transfer (X : Point) (s : Point × Point) :
    (X = (f s).1 ∨ X = (f s).2) ↔ (X = s.1 ∨ X = s.2) := by
  rcases hf s with e | e <;> rw [e]
  exact or_comm

/-- A ray crosses a side read either way, or neither. -/
theorem crosses_transfer (X Q : Point) (s : Point × Point) :
    RayCrosses X Q (f s) ↔ RayCrosses X Q s := by
  rcases hf s with e | e <;> rw [e]
  constructor <;> rintro ⟨Y, hY, hb⟩ <;> exact ⟨Y, hY, between_symm hb⟩

/-- **The same sides give the same figure.** If the sides of `qs` are those of `ps`, each
read the same way or the other way, in some order, and the two lists have the same corners,
then the boundary, the crossing counts and the good rays agree. -/
theorem transfer {ps qs : List Point} (hperm : (sides qs).Perm ((sides ps).map f))
    (hmem : ∀ V, V ∈ qs ↔ V ∈ ps) :
    (∀ X, LoopBoundary qs X ↔ LoopBoundary ps X) ∧
      (∀ X Q, crossingCount qs X Q = crossingCount ps X Q) ∧
      (∀ X Q, GoodRay qs X Q ↔ GoodRay ps X Q) := by
  refine ⟨fun X => ?_, fun X Q => ?_, fun X Q => ?_⟩
  · unfold LoopBoundary
    constructor
    · rintro ⟨s, hs, hX⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (hperm.mem_iff.mp hs)
      exact ⟨t, ht, (finite_transfer hf X t).mp hX⟩
    · rintro ⟨t, ht, hX⟩
      exact ⟨f t, hperm.mem_iff.mpr (List.mem_map_of_mem ht), (finite_transfer hf X t).mpr hX⟩
  · unfold crossingCount
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, hperm.countP_eq,
      List.countP_map]
    apply List.countP_congr
    intro s _
    simp only [Function.comp, decide_eq_true_eq]
    exact crosses_transfer hf X Q s
  · unfold GoodRay
    constructor
    · rintro ⟨hXQ, hV⟩
      exact ⟨hXQ, fun V hVp => hV V ((hmem V).mpr hVp)⟩
    · rintro ⟨hXQ, hV⟩
      exact ⟨hXQ, fun V hVq => hV V ((hmem V).mp hVq)⟩

/-- **The same sides give a simple loop again**, when the corners are as many and distinct. -/
theorem simple_transfer {ps qs : List Point} (hperm : (sides qs).Perm ((sides ps).map f))
    (hlen : qs.length = ps.length) (hnd : ps.Nodup → qs.Nodup) (h : SimpleLoop ps) :
    SimpleLoop qs := by
  obtain ⟨h3, hn, hne, hpw⟩ := h
  refine ⟨hlen ▸ h3, hnd hn, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (hperm.mem_iff.mp hs)
    intro he
    rcases hf t with e | e <;> rw [e] at he
    · exact hne t ht he
    · exact hne t ht he.symm
  · refine (List.Perm.pairwise_iff ?_ hperm).mpr ?_
    · intro s t hst X hXs hXt
      exact (hst X hXt hXs).symm
    · rw [List.pairwise_map]
      refine hpw.imp ?_
      intro s t hst X hXs hXt
      rw [ends_transfer hf, ends_transfer hf]
      exact hst X ((finite_transfer hf X s).mp hXs) ((finite_transfer hf X t).mp hXt)

end Transfer

/-- The region is fixed by the boundary, the crossing counts and the good rays. -/
theorem region_transfer {ps qs : List Point}
    (hb : ∀ X, LoopBoundary qs X ↔ LoopBoundary ps X)
    (hc : ∀ X Q, crossingCount qs X Q = crossingCount ps X Q)
    (hg : ∀ X Q, GoodRay qs X Q ↔ GoodRay ps X Q) (X : Point) :
    LoopRegion qs X ↔ LoopRegion ps X := by
  unfold LoopRegion LoopInside
  simp only [hb, hc, hg]

/-! ## A frame of three corners -/

/-- In a chain whose segments are related pairwise, each segment is related to the next. -/
theorem segments_consecutive {R : Point × Point → Point × Point → Prop} :
    ∀ (l : List Point), (segments l).Pairwise R →
      ∀ t ∈ triples l, R (t.1, t.2.1) (t.2.1, t.2.2)
  | a :: b :: c :: rest, hpw, t, ht => by
      have hpw' : ((a, b) :: segments (b :: c :: rest)).Pairwise R := hpw
      have ht' : t ∈ (a, b, c) :: triples (b :: c :: rest) := ht
      rw [List.pairwise_cons] at hpw'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact hpw'.1 (b, c) List.mem_cons_self
      · exact segments_consecutive (b :: c :: rest) hpw'.2 t ht'
  | [], _, t, ht => by simp [triples] at ht
  | [_], _, t, ht => by simp [triples] at ht
  | [_, _], _, t, ht => by simp [triples] at ht

/-- The two segments of a consecutive triple belong to the chain. -/
theorem triples_segments :
    ∀ (l : List Point), ∀ t ∈ triples l,
      (t.1, t.2.1) ∈ segments l ∧ (t.2.1, t.2.2) ∈ segments l
  | a :: b :: c :: rest, t, ht => by
      have ht' : t ∈ (a, b, c) :: triples (b :: c :: rest) := ht
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      · obtain ⟨h₁, h₂⟩ := triples_segments (b :: c :: rest) t ht'
        exact ⟨List.mem_cons_of_mem _ h₁, List.mem_cons_of_mem _ h₂⟩
  | [], t, ht => by simp [triples] at ht
  | [_], t, ht => by simp [triples] at ht
  | [_, _], t, ht => by simp [triples] at ht

/-- **Two consecutive sides on one straight line run straight on.** If they meet only at
their common end, and their three ends are on one straight line, the common end is between
the others: otherwise the sides would overlap. -/
theorem straight_of_collinear {a b c : Point}
    (hR : ∀ X : Point, OnFiniteLine X a b → OnFiniteLine X b c →
      (X = a ∨ X = b) ∧ (X = b ∨ X = c))
    (hab : a ≠ b) (hbc : b ≠ c) (hcol : Collinear a b c) : Between a b c := by
  obtain ⟨L, ha, hb, hc⟩ := hcol
  have hac : a ≠ c := by
    intro e
    subst e
    obtain ⟨X, -, haXb, -⟩ := exists_point_between ha hb hab []
    rcases (hR X (Or.inr (Or.inr haXb)) (Or.inr (Or.inr (between_symm haXb)))).1 with e | e
    · exact ne_of_between haXb e.symm
    · exact ne_of_between (between_symm haXb) e.symm
  rcases between_cases hab hbc hac ha hb hc with h | h | h
  · exact h
  · rcases (hR a (Or.inl rfl) (Or.inr (Or.inr h))).2 with e | e
    · exact absurd e hab
    · exact absurd e hac
  · rcases (hR c (Or.inr (Or.inr h)) (Or.inr (Or.inl rfl))).1 with e | e
    · exact absurd e hac.symm
    · exact absurd e hbc.symm

/-- A chain whose consecutive triples all run straight on never comes back to a point
behind its first step. -/
theorem straight_chain_not_closed (x : Point) :
    ∀ (m : List Point) (a b : Point), Between x a b →
      (∀ t ∈ triples (a :: b :: m ++ [x]), Between t.1 t.2.1 t.2.2) → False
  | [], a, b, hx, ht => by
      have h := ht (a, b, x) (by simp [triples])
      exact not_between_of_between (between_symm hx) h
  | c :: m, a, b, hx, ht => by
      have h := ht (a, b, c) (by simp [triples])
      refine straight_chain_not_closed x m b c
        (between_symm (between_of_between_right (between_symm h) (between_symm hx))) ?_
      intro t htm
      exact ht t (List.mem_cons_of_mem _ htm)

/-- **A frame from simplicity**: three corners of a simple loop make a triangle. Were every
three corners on one straight line, each corner would lie between its neighbours, since two
neighbouring sides meet only at their common end; and a closed chain cannot run straight on
all the way round. -/
theorem simple_frame {ps : List Point} (h : SimpleLoop ps) :
    ∃ A ∈ ps, ∃ B ∈ ps, ∃ C ∈ ps, Triangle A B C := by
  refine Classical.byContradiction fun hno => ?_
  have hcol : ∀ A ∈ ps, ∀ B ∈ ps, ∀ C ∈ ps, Collinear A B C := fun A hA B hB C hC =>
    Classical.byContradiction fun hc => hno ⟨A, hA, B, hB, C, hC, hc⟩
  obtain ⟨h3, -, hne, hpw⟩ := h
  rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at h3
  · simp at h3
  · simp at h3
  have hstraight : ∀ t ∈ triples (a :: b :: c :: rest ++ [a]),
      Between t.1 t.2.1 t.2.2 := by
    intro t ht
    obtain ⟨h₁, h₂⟩ := triples_segments _ t ht
    exact straight_of_collinear
      (segments_consecutive _ hpw t ht) (hne _ h₁) (hne _ h₂)
      (hcol _ (side_mem h₁).1 _ (side_mem h₁).2 _ (side_mem h₂).2)
  have habc := hstraight (a, b, c) List.mem_cons_self
  exact straight_chain_not_closed a rest b c habc
    (fun t ht => hstraight t (List.mem_cons_of_mem _ ht))

/-! ## Convex outlines -/

/-- Three or more distinct corners include one other than any two given points. -/
theorem exists_other {ps : List Point} (hlen : 3 ≤ ps.length) (hnd : ps.Nodup)
    (A B : Point) : ∃ P ∈ ps, P ≠ A ∧ P ≠ B := by
  rcases ps with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  by_cases hx : x ≠ A ∧ x ≠ B
  · exact ⟨x, List.mem_cons_self, hx⟩
  by_cases hy : y ≠ A ∧ y ≠ B
  · exact ⟨y, List.mem_cons_of_mem _ List.mem_cons_self, hy⟩
  refine ⟨z, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
  grind

/-- **No side read backwards**: in a closed outline of three or more distinct corners, no
side is also a side read the other way. Read from its first end, a side's next corner is the
other end; were that the start of the reversed side, the corner after it would be the first
end again, and the corners would repeat. -/
theorem sides_no_swap {ps : List Point} (hlen : 3 ≤ ps.length) (hnd : ps.Nodup)
    {a b : Point} (hab : (a, b) ∈ sides ps) (hba : (b, a) ∈ sides ps) : False := by
  obtain ⟨us, vs, rfl⟩ := List.append_of_mem (side_mem hab).1
  have hperm := sides_rotate_perm us (a :: vs)
  have hab' := hperm.mem_iff.mp hab
  have hba' := hperm.mem_iff.mp hba
  have hnd' : (a :: vs ++ us).Nodup := List.perm_append_comm.nodup_iff.mp hnd
  have hlen' : 3 ≤ (a :: vs ++ us).length := by
    simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  rw [List.cons_append] at hab' hba' hnd' hlen'
  generalize vs ++ us = ws at hab' hba' hnd' hlen'
  rcases ws with _ | ⟨w, _ | ⟨x, rest⟩⟩
  · simp at hlen'
  · simp at hlen'
  have h₁ : (a, w) ∈ sides (a :: w :: x :: rest) := by simp [sides, segments]
  have h₂ : (w, x) ∈ sides (a :: w :: x :: rest) := by simp [sides, segments]
  have hbw : (a, b) = (a, w) := sides_fst_inj hnd' hab' h₁ rfl
  rw [Prod.mk.injEq] at hbw
  rw [hbw.2] at hba'
  have hax : (w, a) = (w, x) := sides_fst_inj hnd' hba' h₂ rfl
  rw [Prod.mk.injEq] at hax
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd'
  exact hnd'.1.2.1 hax.2

variable {cs : List Point}

/-- Only the ends of a side are corners on its straight line. -/
theorem convex_on_side_line (h : ConvexOutline cs) {s : Point × Point} (hs : s ∈ sides cs)
    {L : Line} (h₁ : OnLine s.1 L) (h₂ : OnLine s.2 L) {P : Point} (hP : P ∈ cs)
    (hPL : OnLine P L) : P = s.1 ∨ P = s.2 := by
  refine Classical.byContradiction fun hn => ?_
  rw [not_or] at hn
  exact not_on_line_of_same_side
    ((h.2.2 s hs P hP P hP hn.1 hn.2 hn.1 hn.2).sameSide h₁ h₂) hPL

/-- **A point within a side is off every other side's straight line.** Both ends of the
other side are on the closed side of the line towards the remaining corners; a point between
them on the line puts both ends on it, and only the side's own ends are corners there. -/
theorem convex_between_off (h : ConvexOutline cs) {s t : Point × Point}
    (hs : s ∈ sides cs) (ht : t ∈ sides cs) (hst : s ≠ t) {L : Line}
    (h₁ : OnLine s.1 L) (h₂ : OnLine s.2 L) {Y : Point} (hY : Between t.1 Y t.2) :
    ¬ OnLine Y L := by
  intro hYL
  obtain ⟨P, hP, hP₁, hP₂⟩ := convex_third h s
  have ht₁ := corner_half h hs hP hP₁ hP₂ (side_mem ht).1 h₁ h₂
  have ht₂ := corner_half h hs hP hP₁ hP₂ (side_mem ht).2 h₁ h₂
  obtain ⟨hl₁, hl₂⟩ := half_between_on_line ht₁ ht₂ hY hYL
  have hne := convex_side_ne h ht
  rcases convex_on_side_line h hs h₁ h₂ (side_mem ht).1 hl₁ with e₁ | e₁ <;>
    rcases convex_on_side_line h hs h₁ h₂ (side_mem ht).2 hl₂ with e₂ | e₂
  · exact hne (e₁.trans e₂.symm)
  · exact hst (Prod.ext e₁.symm e₂.symm)
  · have hswap : (s.2, s.1) ∈ sides cs := by
      rw [← e₁, ← e₂]
      exact ht
    exact sides_no_swap h.1 h.2.1 hs hswap
  · exact hne (e₁.trans e₂.symm)

/-- Two different sides have different points strictly within them. -/
theorem convex_crossing_ne (h : ConvexOutline cs) {a b : Point × Point}
    (ha : a ∈ sides cs) (hb : b ∈ sides cs) (hab : a ≠ b) {Ya Yb : Point}
    (hYa : Between a.1 Ya a.2) (hYb : Between b.1 Yb b.2) : Ya ≠ Yb := by
  intro e
  subst e
  obtain ⟨L, h₁, h₂⟩ := Postulate1 a.1 a.2 (convex_side_ne h ha)
  exact convex_between_off h ha hb hab h₁ h₂ hYb (on_line_of_between_ends hYa h₁ h₂)

/-- **A convex outline is simple**: two different sides meet only at a common end. -/
theorem convex_simple (h : ConvexOutline cs) : SimpleLoop cs := by
  refine ⟨h.1, h.2.1, fun s hs => convex_side_ne h hs, ?_⟩
  refine (sides_nodup h.2.1).imp_of_mem ?_
  intro s t hs ht hst X hXs hXt
  have endpoint {a b : Point × Point} (ha : a ∈ sides cs) (hb : b ∈ sides cs) (hab : a ≠ b)
      (hXa : OnFiniteLine X a.1 a.2) (hXb : OnFiniteLine X b.1 b.2) : X = b.1 ∨ X = b.2 := by
    rcases hXb with e | e | hbtw
    · exact Or.inl e
    · exact Or.inr e
    · obtain ⟨L, h₁, h₂⟩ := Postulate1 a.1 a.2 (convex_side_ne h ha)
      exact False.elim (convex_between_off h ha hb hab h₁ h₂ hbtw
        (onFiniteLine_onLine hXa h₁ h₂))
  exact ⟨endpoint ht hs (Ne.symm hst) hXt hXs, endpoint hs ht hst hXs hXt⟩

/-- The boundary of a convex outline lies in its closed region. -/
theorem convex_boundary_region (h : ConvexOutline cs) {X : Point}
    (hX : LoopBoundary cs X) : ConvexRegion cs X := by
  obtain ⟨t, ht, hXt⟩ := hX
  have h₁ := Extreme.corner_region h (side_mem ht).1
  have h₂ := Extreme.corner_region h (side_mem ht).2
  rcases hXt with e | e | hb
  · exact e ▸ h₁
  · exact e ▸ h₂
  · exact convex_region_between h h₁ h₂ hb

/-- **A supporting side**: a point of the closed region on a side's straight line is on
the finite side. Beyond either end it would cross the straight line of the neighbouring side
there, away from the side's other end. -/
theorem convex_supporting (h : ConvexOutline cs) {s : Point × Point} (hs : s ∈ sides cs)
    {X : Point} (hX : ConvexRegion cs X) (hcol : Collinear s.1 s.2 X) :
    OnFiniteLine X s.1 s.2 := by
  obtain ⟨A, B⟩ := s
  dsimp only at hcol ⊢
  have hAB : A ≠ B := convex_side_ne h hs
  have hA : A ∈ cs := (side_mem hs).1
  have hB : B ∈ cs := (side_mem hs).2
  obtain ⟨L, hAL, hBL, hXL⟩ := hcol
  by_cases hXA : X = A
  · exact Or.inl hXA
  by_cases hXB : X = B
  · exact Or.inr (Or.inl hXB)
  /- The sides that leave B and come into A. -/
  obtain ⟨W, hBW⟩ := outgoing_side hB
  obtain ⟨Z, hZA⟩ := incoming_side hA
  have hWA : W ≠ A := fun e => sides_no_swap h.1 h.2.1 hs (e ▸ hBW)
  have hZB : Z ≠ B := fun e => sides_no_swap h.1 h.2.1 hs (e ▸ hZA)
  have hBW' : B ≠ W := convex_side_ne h hBW
  have hZA' : Z ≠ A := convex_side_ne h hZA
  obtain ⟨M, hBM, hWM⟩ := Postulate1 B W hBW'
  obtain ⟨N, hZN, hAN⟩ := Postulate1 Z A hZA'
  have hXM : Half X A M := (closedSide_iff_half hBW' hBM hWM).mp
    (hX (B, W) hBW A hA hAB hWA.symm)
  have hXN : Half X B N := (closedSide_iff_half hZA' hZN hAN).mp
    (hX (Z, A) hZA B hB hZB.symm hAB.symm)
  have hAM : ¬ OnLine A M := not_on_line_of_same_side
    ((h.2.2 (B, W) hBW A hA A hA hAB hWA.symm hAB hWA.symm).sameSide hBM hWM)
  have hBN : ¬ OnLine B N := not_on_line_of_same_side
    ((h.2.2 (Z, A) hZA B hB B hB hZB.symm hAB.symm hZB.symm hAB.symm).sameSide hZN hAN)
  rcases between_cases (Ne.symm hXA) hXB hAB hAL hXL hBL with hb | hb | hb
  · exact Or.inr (Or.inr hb)
  · /- X beyond A: the straight line ZA separates X from B. -/
    rcases hXN with hXN | hXN
    · have he : N = L := line_unique hXA hXN hAN hXL hAL
      exact False.elim (hBN (he ▸ hBL))
    · exact False.elim (pasch3 hb hAN hXN)
  · /- X beyond B: the straight line BW separates X from A. -/
    rcases hXM with hXM | hXM
    · have he : M = L := line_unique hXB hXM hBM hXL hBL
      exact False.elim (hAM (he ▸ hAL))
    · exact False.elim (pasch3 (between_symm hb) hBM hXM)

/-- A point of the closed region off the boundary is strictly on the inner side of every
side's straight line. -/
theorem convex_strict (h : ConvexOutline cs) {X : Point} (hX : ConvexRegion cs X)
    (hXb : ¬ LoopBoundary cs X) {s : Point × Point} (hs : s ∈ sides cs) {P : Point}
    (hP : P ∈ cs) (hP₁ : P ≠ s.1) (hP₂ : P ≠ s.2) {L : Line} (h₁ : OnLine s.1 L)
    (h₂ : OnLine s.2 L) : SameSide X P L := by
  rcases (closedSide_iff_half (convex_side_ne h hs) h₁ h₂).mp (hX s hs P hP hP₁ hP₂) with
    hXL | hXP
  · exact False.elim (hXb ⟨s, hs, convex_supporting h hs hX ⟨L, h₁, h₂, hXL⟩⟩)
  · exact hXP

/-- From a point strictly inside a convex outline, a straight line that reaches a side's
straight line goes on outside the closed region. -/
theorem convex_beyond (h : ConvexOutline cs) {X Y Z : Point} (hX : ConvexRegion cs X)
    (hXb : ¬ LoopBoundary cs X) {s : Point × Point} (hs : s ∈ sides cs) {L : Line}
    (h₁ : OnLine s.1 L) (h₂ : OnLine s.2 L) (hY : OnLine Y L) (hb : Between X Y Z)
    (hZ : ConvexRegion cs Z) : False := by
  obtain ⟨P, hP, hP₁, hP₂⟩ := convex_third h s
  have hXP := convex_strict h hX hXb hs hP hP₁ hP₂ h₁ h₂
  rcases (closedSide_iff_half (convex_side_ne h hs) h₁ h₂).mp (hZ s hs P hP hP₁ hP₂) with
    hZL | hZP
  · exact not_on_line_of_same_side hXP (on_line_of_between (between_symm hb) hZL hY)
  · exact pasch3 hb hY (same_side_trans (same_side_symm hXP) (same_side_symm hZP))

/-- No point within one side lies between points within two other sides, on a straight
line: the middle side's straight line would separate the outer two, which lie on its inner
side. -/
theorem convex_no_middle (h : ConvexOutline cs) {r t u : Point × Point}
    (hr : r ∈ sides cs) (ht : t ∈ sides cs) (hu : u ∈ sides cs) (hrt : r ≠ t)
    (hut : u ≠ t) {Yr Yt Yu : Point} (hYr : Between r.1 Yr r.2)
    (hYt : Between t.1 Yt t.2) (hYu : Between u.1 Yu u.2) (hb : Between Yr Yt Yu) :
    False := by
  obtain ⟨L, h₁, h₂⟩ := Postulate1 t.1 t.2 (convex_side_ne h ht)
  have hYtL : OnLine Yt L := on_line_of_between_ends hYt h₁ h₂
  obtain ⟨P, hP, hP₁, hP₂⟩ := convex_third h t
  have inner {v : Point × Point} (hv : v ∈ sides cs) (hvt : v ≠ t) {Y : Point}
      (hY : Between v.1 Y v.2) : SameSide Y P L := by
    have hv₁ := corner_half h ht hP hP₁ hP₂ (side_mem hv).1 h₁ h₂
    have hv₂ := corner_half h ht hP hP₁ hP₂ (side_mem hv).2 h₁ h₂
    rcases half_between hv₁ hv₂ hY with hYL | hYP
    · exact False.elim (convex_between_off h ht hv (Ne.symm hvt) h₁ h₂ hY hYL)
    · exact hYP
  exact pasch3 hb hYtL
    (same_side_trans (same_side_symm (inner hr hrt hYr)) (same_side_symm (inner hu hut hYu)))

/-- **At most two sides cross a straight line.** Of three crossing points on it, one would
be between the others. -/
theorem convex_at_most_two (h : ConvexOutline cs) {ℓ : Line} {r t u : Point × Point}
    (hr : r ∈ sides cs) (ht : t ∈ sides cs) (hu : u ∈ sides cs) (hrt : r ≠ t)
    (hru : r ≠ u) (htu : t ≠ u) (cr : OppositeSides r.1 r.2 ℓ)
    (ct : OppositeSides t.1 t.2 ℓ) (cu : OppositeSides u.1 u.2 ℓ) : False := by
  obtain ⟨Yr, hYrℓ, hYr⟩ := cr.exists_between
  obtain ⟨Yt, hYtℓ, hYt⟩ := ct.exists_between
  obtain ⟨Yu, hYuℓ, hYu⟩ := cu.exists_between
  rcases between_cases (convex_crossing_ne h hr ht hrt hYr hYt)
      (convex_crossing_ne h ht hu htu hYt hYu) (convex_crossing_ne h hr hu hru hYr hYu)
      hYrℓ hYtℓ hYuℓ with hb | hb | hb
  · exact convex_no_middle h hr ht hu hrt (Ne.symm htu) hYr hYt hYu hb
  · exact convex_no_middle h ht hr hu (Ne.symm hrt) (Ne.symm hru) hYt hYr hYu hb
  · exact convex_no_middle h hr hu ht hru htu hYr hYu hYt hb

/-- **A triangle's closed region**: read as a convex outline, a triangle's corners have the
closed triangle as their region, the three closed sides of `closed_triangle_sides`. -/
theorem triangle_convexRegion {A B C X : Point} (h : Triangle A B C) :
    ConvexRegion [A, B, C] X ↔ OnOrInsideTriangle X A B C := by
  rw [closed_triangle_sides h]
  have hsides : sides [A, B, C] = [(A, B), (B, C), (C, A)] := rfl
  unfold ConvexRegion
  rw [hsides]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  constructor
  · rintro ⟨⟨-, -, hAB⟩, ⟨hBC, -, -⟩, ⟨-, hCA, -⟩⟩
    exact ⟨hBC h.ne₁₂ h.ne₁₃, hCA h.ne₂₃ h.ne₁₂.symm, hAB h.ne₁₃.symm h.ne₂₃.symm⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨fun e => absurd rfl e, fun _ e => absurd rfl e, fun _ _ => h₃⟩,
      ⟨fun _ _ => h₁, fun e => absurd rfl e, fun _ e => absurd rfl e⟩,
      ⟨fun _ e => absurd rfl e, fun _ _ => h₂, fun e => absurd rfl e⟩⟩

/-! ## Crossings of a straight line, and of a ray -/

/-- A finite straight line through a point of `ℓ`, with one end off it, joins points on
opposite sides of `ℓ`. -/
theorem crosses_of_between {A Y B : Point} {ℓ : Line} (hY : Between A Y B)
    (hYℓ : OnLine Y ℓ) (hA : ¬ OnLine A ℓ) : OppositeSides A B ℓ :=
  ⟨hA, fun hB => hA (on_line_of_between (between_symm hY) hB hYℓ), pasch3 hY hYℓ⟩

/-- Starting from a point with some property, a chain that reaches a point without it has
a segment that leaves the property. -/
theorem segment_change_down {p : Point → Prop} :
    ∀ (a : Point) (l : List Point), p a → (∃ e ∈ l, ¬ p e) →
      ∃ s ∈ segments (a :: l), p s.1 ∧ ¬ p s.2
  | _, [], _, ⟨_, he, _⟩ => absurd he List.not_mem_nil
  | a, b :: l, ha, ⟨e, he, hne⟩ => by
      by_cases hb : p b
      · have he' : e ∈ l := by
          rcases List.mem_cons.mp he with e' | e'
          · exact absurd (e' ▸ hb) hne
          · exact e'
        obtain ⟨s, hs, h₁, h₂⟩ := segment_change_down b l hb ⟨e, he', hne⟩
        exact ⟨s, List.mem_cons_of_mem _ hs, h₁, h₂⟩
      · exact ⟨(a, b), List.mem_cons_self, ha, hb⟩

/-- Ending at a point with some property, a chain that passes a point without it has a
segment that enters the property. -/
theorem segment_change_up {p : Point → Prop} :
    ∀ (l : List Point) (z : Point), p z → (∃ e ∈ l, ¬ p e) →
      ∃ s ∈ segments (l ++ [z]), ¬ p s.1 ∧ p s.2
  | [], _, _, ⟨_, he, _⟩ => absurd he List.not_mem_nil
  | a :: l, z, hz, ⟨e, he, hne⟩ => by
      by_cases hl : ∃ e ∈ l, ¬ p e
      · obtain ⟨s, hs, h₁, h₂⟩ := segment_change_up l z hz hl
        refine ⟨s, ?_, h₁, h₂⟩
        cases l with
        | nil => simp [segments] at hs
        | cons b l => exact List.mem_cons_of_mem _ hs
      · have ha : ¬ p a := by
          rcases List.mem_cons.mp he with e' | e'
          · exact e' ▸ hne
          · exact absurd ⟨e, e', hne⟩ hl
        cases l with
        | nil => exact ⟨(a, z), by simp [segments], ha, hz⟩
        | cons b l =>
          have hb : p b := Classical.byContradiction fun hb => hl ⟨b, List.mem_cons_self, hb⟩
          exact ⟨(a, b), List.mem_cons_self, ha, hb⟩

/-- **Two crossings**: if a straight line through no corner of a closed outline separates
two of its corners, two different sides cross it. Going round from the first corner, the
outline leaves that corner's side of the line and comes back to it. -/
theorem two_crossings {ps : List Point} {ℓ : Line} (hoff : ∀ V ∈ ps, ¬ OnLine V ℓ)
    {U V : Point} (hU : U ∈ ps) (hV : V ∈ ps) (hUV : OppositeSides U V ℓ) :
    ∃ s ∈ sides ps, ∃ t ∈ sides ps, s ≠ t ∧
      OppositeSides s.1 s.2 ℓ ∧ OppositeSides t.1 t.2 ℓ := by
  cases ps with
  | nil => simp at hU
  | cons c cs =>
    have hc : ¬ OnLine c ℓ := hoff c List.mem_cons_self
    have hpc : SameSide c c ℓ := same_side_refl hc
    have hex : ∃ e ∈ c :: cs, ¬ SameSide e c ℓ := by
      by_cases hUc : SameSide U c ℓ
      · exact ⟨V, hV, fun hVc =>
          hUV.2.2 (same_side_trans (same_side_symm hUc) (same_side_symm hVc))⟩
      · exact ⟨U, hU, hUc⟩
    have hex' : ∃ e ∈ cs ++ [c], ¬ SameSide e c ℓ := by
      obtain ⟨e, he, hne⟩ := hex
      refine ⟨e, ?_, hne⟩
      rcases List.mem_cons.mp he with e' | e'
      · exact List.mem_append_right _ (List.mem_singleton.mpr e')
      · exact List.mem_append_left _ e'
    obtain ⟨s, hs, hs₁, hs₂⟩ :=
      segment_change_down (p := fun W => SameSide W c ℓ) c (cs ++ [c]) hpc hex'
    obtain ⟨t, ht, ht₁, ht₂⟩ :=
      segment_change_up (p := fun W => SameSide W c ℓ) (c :: cs) c hpc hex
    have hs' : s ∈ sides (c :: cs) := hs
    have ht' : t ∈ sides (c :: cs) := ht
    refine ⟨s, hs', t, ht', fun e => ht₁ (e ▸ hs₁), ?_, ?_⟩
    · exact ⟨hoff _ (side_mem hs').1, hoff _ (side_mem hs').2,
        fun h12 => hs₂ (same_side_trans h12 hs₁)⟩
    · exact ⟨hoff _ (side_mem ht').1, hoff _ (side_mem ht').2,
        fun h12 => ht₁ (same_side_trans (same_side_symm h12) ht₂)⟩

/-- A point of a ray's straight line, other than its start, is on the ray or behind its
start. -/
theorem onRay_or_behind {X Q Z : Point} {ℓ : Line} (hXQ : X ≠ Q) (hX : OnLine X ℓ)
    (hQ : OnLine Q ℓ) (hZ : OnLine Z ℓ) (hZX : Z ≠ X) : OnRay Z X Q ∨ Between Z X Q := by
  by_cases hb : Between Z X Q
  · exact Or.inr hb
  · exact Or.inl ⟨hXQ, hZX, ⟨ℓ, hX, hQ, hZ⟩, hb⟩

/-- Two different points of a straight line, on one side of a third, are in order from
it. -/
theorem order_from {X Y Z : Point} {ℓ : Line} (hX : OnLine X ℓ) (hY : OnLine Y ℓ)
    (hZ : OnLine Z ℓ) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z) (hn : ¬ Between Y X Z) :
    Between X Y Z ∨ Between X Z Y := by
  rcases between_cases hXY hYZ hXZ hX hY hZ with hb | hb | hb
  · exact Or.inl hb
  · exact absurd hb hn
  · exact Or.inr hb

/-! ## Counting the crossings -/

/-- A filter of a list of distinct members that keeps exactly one of them has length one. -/
theorem filter_length_one {l : List (Point × Point)} (hnd : l.Nodup)
    {q : Point × Point → Bool} {s : Point × Point} (hs : s ∈ l) (hq : q s = true)
    (huniq : ∀ t ∈ l, q t = true → t = s) : (l.filter q).length = 1 := by
  have hperm : (l.filter q).Perm [s] := by
    rw [List.perm_ext_iff_of_nodup (hnd.sublist List.filter_sublist)
      (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)]
    intro t
    simp only [List.mem_filter, List.mem_singleton]
    constructor
    · rintro ⟨ht, hqt⟩
      exact huniq t ht hqt
    · rintro rfl
      exact ⟨hs, hq⟩
  exact hperm.length_eq

/-- A filter of a list of distinct members that keeps exactly two of them has length two. -/
theorem filter_length_two {l : List (Point × Point)} (hnd : l.Nodup)
    {q : Point × Point → Bool} {s t : Point × Point} (hs : s ∈ l) (ht : t ∈ l)
    (hst : s ≠ t) (hqs : q s = true) (hqt : q t = true)
    (hall : ∀ u ∈ l, q u = true → u = s ∨ u = t) : (l.filter q).length = 2 := by
  have hperm : (l.filter q).Perm [s, t] := by
    rw [List.perm_ext_iff_of_nodup (hnd.sublist List.filter_sublist)
      (List.nodup_cons.mpr ⟨by simpa using hst,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩)]
    intro u
    simp only [List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨hu, hqu⟩
      exact hall u hu hqu
    · rintro (rfl | rfl)
      · exact ⟨hs, hqs⟩
      · exact ⟨ht, hqt⟩
  exact hperm.length_eq

/-- One side crossed, and no other: the crossing count is one. -/
theorem crossingCount_eq_one {ps : List Point} (hnd : ps.Nodup) {X Q : Point}
    {s : Point × Point} (hs : s ∈ sides ps) (hc : RayCrosses X Q s)
    (huniq : ∀ t ∈ sides ps, RayCrosses X Q t → t = s) : crossingCount ps X Q = 1 := by
  unfold crossingCount
  exact filter_length_one (sides_nodup hnd) hs (by simpa using hc)
    (fun t ht hqt => huniq t ht (by simpa using hqt))

/-- Two sides crossed, and no other: the crossing count is two. -/
theorem crossingCount_eq_two {ps : List Point} (hnd : ps.Nodup) {X Q : Point}
    {s t : Point × Point} (hs : s ∈ sides ps) (ht : t ∈ sides ps) (hst : s ≠ t)
    (hcs : RayCrosses X Q s) (hct : RayCrosses X Q t)
    (hall : ∀ u ∈ sides ps, RayCrosses X Q u → u = s ∨ u = t) :
    crossingCount ps X Q = 2 := by
  unfold crossingCount
  exact filter_length_two (sides_nodup hnd) hs ht hst (by simpa using hcs)
    (by simpa using hct) (fun u hu hqu => hall u hu (by simpa using hqu))

/-- No side crossed: the crossing count is nought. -/
theorem crossingCount_eq_zero {ps : List Point} {X Q : Point}
    (hnone : ∀ s ∈ sides ps, ¬ RayCrosses X Q s) : crossingCount ps X Q = 0 := by
  unfold crossingCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro s hs
  simpa using hnone s hs

/-! ## A ray from a convex outline's inside, and from outside -/

/-- **From inside, one crossing.** A good ray from a point strictly inside a convex outline
crosses exactly one of its sides. The straight line of the ray has corners on both sides of
it, since the closed region is made of triangles on corners; so two sides cross it, and the
crossing points are on opposite sides of the point, for otherwise the nearer side's line
would separate the point from the farther. Two crossings on the ray would do the same. -/
theorem convex_count_inside (h : ConvexOutline cs) {X Q : Point} (hX : ConvexRegion cs X)
    (hXb : ¬ LoopBoundary cs X) (hQ : GoodRay cs X Q) : crossingCount cs X Q = 1 := by
  obtain ⟨hXQ, hgood⟩ := hQ
  obtain ⟨ℓ, hXℓ, hQℓ⟩ := Postulate1 X Q hXQ
  have hoff : ∀ V ∈ cs, ¬ OnLine V ℓ := fun V hV hVℓ => hgood V hV ⟨ℓ, hXℓ, hQℓ, hVℓ⟩
  have hneX {s : Point × Point} (hs : s ∈ sides cs) {Y : Point}
      (hY : Between s.1 Y s.2) : Y ≠ X := by
    intro e
    exact hXb ⟨s, hs, Or.inr (Or.inr (e ▸ hY))⟩
  have hbd {s : Point × Point} (hs : s ∈ sides cs) {Y : Point}
      (hY : Between s.1 Y s.2) : ConvexRegion cs Y :=
    convex_boundary_region h ⟨s, hs, Or.inr (Or.inr hY)⟩
  /- The corners are not all on one side of the ray's straight line. -/
  obtain ⟨c, hc⟩ : ∃ c, c ∈ cs := by
    obtain ⟨P, hP, -⟩ := exists_other h.1 h.2.1 X X
    exact ⟨P, hP⟩
  have hsplit : ∃ V ∈ cs, OppositeSides c V ℓ := by
    refine Classical.byContradiction fun hno => ?_
    have hall : ∀ V ∈ cs, SameSide V c ℓ := fun V hV => Classical.byContradiction fun hVc =>
      hno ⟨V, hV, hoff c hc, hoff V hV, fun hcV => hVc (same_side_symm hcV)⟩
    obtain ⟨t, ht, hXt⟩ := (fan_covers h X).mpr hX
    obtain ⟨h₁, h₂, h₃⟩ := Extreme.fan_mem ht
    exact not_on_line_of_same_side
      (closed_same_side (hall _ h₁) (hall _ h₂) (hall _ h₃) hXt) hXℓ
  obtain ⟨V, hV, hcV⟩ := hsplit
  obtain ⟨s, hs, t, ht, hst, cs₁, ct₁⟩ := two_crossings hoff hc hV hcV
  obtain ⟨Ys, hYsℓ, hYs⟩ := cs₁.exists_between
  obtain ⟨Yt, hYtℓ, hYt⟩ := ct₁.exists_between
  /- One of the two crossings is on the ray. -/
  have hray : ∃ r ∈ sides cs, RayCrosses X Q r := by
    rcases onRay_or_behind hXQ hXℓ hQℓ hYsℓ (hneX hs hYs) with hs' | hs'
    · exact ⟨s, hs, Ys, hs', hYs⟩
    rcases onRay_or_behind hXQ hXℓ hQℓ hYtℓ (hneX ht hYt) with ht' | ht'
    · exact ⟨t, ht, Yt, ht', hYt⟩
    have hn : ¬ Between Ys X Yt :=
      not_between_of_between_between (between_symm hs') (between_symm ht')
    rcases order_from hXℓ hYsℓ hYtℓ (hneX hs hYs).symm (hneX ht hYt).symm
        (convex_crossing_ne h hs ht hst hYs hYt) hn with hb | hb
    · obtain ⟨L, h₁, h₂⟩ := Postulate1 s.1 s.2 (convex_side_ne h hs)
      exact False.elim (convex_beyond h hX hXb hs h₁ h₂
        (on_line_of_between_ends hYs h₁ h₂) hb (hbd ht hYt))
    · obtain ⟨L, h₁, h₂⟩ := Postulate1 t.1 t.2 (convex_side_ne h ht)
      exact False.elim (convex_beyond h hX hXb ht h₁ h₂
        (on_line_of_between_ends hYt h₁ h₂) hb (hbd hs hYs))
  /- No other side is crossed by the ray. -/
  obtain ⟨r, hr, Y, hYray, hY⟩ := hray
  refine crossingCount_eq_one h.2.1 hr ⟨Y, hYray, hY⟩ ?_
  rintro u hu ⟨Z, hZray, hZ⟩
  refine Classical.byContradiction fun hur => ?_
  rcases order_from hXℓ (hYray.onLine hXℓ hQℓ) (hZray.onLine hXℓ hQℓ) hYray.2.1.symm
      hZray.2.1.symm (convex_crossing_ne h hr hu (Ne.symm hur) hY hZ)
      (hYray.not_between hZray) with hb | hb
  · obtain ⟨L, h₁, h₂⟩ := Postulate1 r.1 r.2 (convex_side_ne h hr)
    exact convex_beyond h hX hXb hr h₁ h₂ (on_line_of_between_ends hY h₁ h₂) hb (hbd hu hZ)
  · obtain ⟨L, h₁, h₂⟩ := Postulate1 u.1 u.2 (convex_side_ne h hu)
    exact convex_beyond h hX hXb hu h₁ h₂ (on_line_of_between_ends hZ h₁ h₂) hb (hbd hr hY)

/-- **From outside, none or two.** A good ray from a point outside the closed region of a
convex outline crosses none of its sides or exactly two. If it crosses one, its straight
line crosses another, and that crossing is on the ray too, for otherwise the point would lie
between two points of the region; and no third side crosses the line. -/
theorem convex_count_outside (h : ConvexOutline cs) {X Q : Point}
    (hX : ¬ ConvexRegion cs X) (hXb : ¬ LoopBoundary cs X) (hQ : GoodRay cs X Q) :
    crossingCount cs X Q = 0 ∨ crossingCount cs X Q = 2 := by
  obtain ⟨hXQ, hgood⟩ := hQ
  obtain ⟨ℓ, hXℓ, hQℓ⟩ := Postulate1 X Q hXQ
  have hoff : ∀ V ∈ cs, ¬ OnLine V ℓ := fun V hV hVℓ => hgood V hV ⟨ℓ, hXℓ, hQℓ, hVℓ⟩
  have hbd {s : Point × Point} (hs : s ∈ sides cs) {Y : Point}
      (hY : Between s.1 Y s.2) : ConvexRegion cs Y :=
    convex_boundary_region h ⟨s, hs, Or.inr (Or.inr hY)⟩
  by_cases hany : ∃ s ∈ sides cs, RayCrosses X Q s
  · obtain ⟨s, hs, Ys, hYsray, hYs⟩ := hany
    have hYsℓ := hYsray.onLine hXℓ hQℓ
    have cs₁ : OppositeSides s.1 s.2 ℓ :=
      crosses_of_between hYs hYsℓ (hoff _ (side_mem hs).1)
    obtain ⟨a, ha, b, hb, hab, ca, cb⟩ :=
      two_crossings hoff (side_mem hs).1 (side_mem hs).2 cs₁
    /- A crossing side other than s. -/
    obtain ⟨t, ht, hts, ct⟩ : ∃ t ∈ sides cs, t ≠ s ∧ OppositeSides t.1 t.2 ℓ := by
      by_cases has : a = s
      · exact ⟨b, hb, fun e => hab (has.trans e.symm), cb⟩
      · exact ⟨a, ha, has, ca⟩
    obtain ⟨Yt, hYtℓ, hYt⟩ := ct.exists_between
    have hYtX : Yt ≠ X := fun e => hXb ⟨t, ht, Or.inr (Or.inr (e ▸ hYt))⟩
    have htray : OnRay Yt X Q := by
      rcases onRay_or_behind hXQ hXℓ hQℓ hYtℓ hYtX with h' | h'
      · exact h'
      · exact False.elim (hX (convex_region_between h (hbd ht hYt) (hbd hs hYs)
          (hYsray.between h')))
    right
    refine crossingCount_eq_two h.2.1 hs ht (Ne.symm hts) ⟨Ys, hYsray, hYs⟩
      ⟨Yt, htray, hYt⟩ ?_
    rintro u hu ⟨Yu, hYuray, hYu⟩
    refine Classical.byContradiction fun hn => ?_
    rw [not_or] at hn
    exact convex_at_most_two h hs ht hu (Ne.symm hts) (Ne.symm hn.1) (Ne.symm hn.2) cs₁ ct
      (crosses_of_between hYu (hYuray.onLine hXℓ hQℓ) (hoff _ (side_mem hu).1))
  · left
    exact crossingCount_eq_zero fun s hs hc => hany ⟨s, hs, hc⟩

end LoopFacts

end Elements.Figures
