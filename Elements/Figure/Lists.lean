/-!
# Book Zero: lists, counts and sums of natural numbers

A figure of brief 0013 is given by lists: of corners, of contours, of sides, of triangles and
of cells. These are the facts about finite lists alone that its proofs share: where two
members of a list stand, and how a list splits or turns round; one unbroken run of members
that pass a test; lists with nothing in some places; how many members pass a test; and sums
of natural numbers over a list. None mentions a point, a straight line or a magnitude; sums
of magnitudes are in `Sums.lean`.

Natural numbers count members of lists; they measure nothing. Nothing in Book Zero cites a
proposition of the *Elements*.
-/

namespace Elements.Figures

/-! ## Members of a list -/

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

/-- Three or more distinct members of a list include one other than any two given. -/
theorem exists_other {α : Type} {ps : List α} (hlen : 3 ≤ ps.length) (hnd : ps.Nodup)
    (A B : α) : ∃ P ∈ ps, P ≠ A ∧ P ≠ B := by
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

/-- Something holds of a member of a list exactly when it holds of the first member or of a
member of the rest. -/
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

/-- A nonempty list can be read as an initial list followed by its last member: Lean's
`List.eq_nil_or_concat`, for a list known to be nonempty, with `concat` read as appending. -/
theorem split_last {α : Type} (ps : List α) (h : ps ≠ []) :
    ∃ us V, ps = us ++ [V] := by
  rcases List.eq_nil_or_concat ps with he | ⟨us, V, he⟩
  · exact False.elim (h he)
  · exact ⟨us, V, by simpa using he⟩

/-- Reading a list from a later point is a rotation. -/
theorem rotate_split {α : Type} {ps us vs : List α} (he : ps = us ++ vs) (hv : vs ≠ [])
    (hlen : 2 ≤ ps.length) : ps.rotateLeft us.length = vs ++ us := by
  have hlt : us.length < ps.length := by
    rw [he, List.length_append]
    have : vs.length ≠ 0 := fun h0 => hv (List.eq_nil_of_length_eq_zero h0)
    omega
  unfold List.rotateLeft
  dsimp only
  split
  · omega
  · rw [Nat.mod_eq_of_lt hlt, he, List.drop_left, List.take_left]

/-- A rotation of a rotation is a rotation. -/
theorem rotate_compose {α : Type} {cs pre post l₁ l₂ : List α} (hc : cs = pre ++ post)
    (hr : post ++ pre = l₁ ++ l₂) :
    ∃ pre' post' : List α, cs = pre' ++ post' ∧ post' ++ pre' = l₂ ++ l₁ := by
  rcases List.append_eq_append_iff.mp hr with ⟨a', h₁, h₂⟩ | ⟨c', h₁, h₂⟩
  · exact ⟨a', l₂ ++ post, by rw [hc, h₂]; simp, by rw [h₁]; simp⟩
  · exact ⟨pre ++ l₁, c', by rw [hc, h₁]; simp, by rw [h₂]; simp⟩

/-- A list of values of a partial map has no repetition, when no two members take one value. -/
theorem nodup_filterMap_of {α β : Type} (f : α → Option β) : ∀ l : List α,
    l.Pairwise (fun a b => ∀ x, f a = some x → f b ≠ some x) → (l.filterMap f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    cases hfa : f a with
    | none =>
      simp only [List.filterMap_cons, hfa]
      exact nodup_filterMap_of f l h.2
    | some x =>
      simp only [List.filterMap_cons, hfa]
      refine List.nodup_cons.mpr ⟨fun hx => ?_, nodup_filterMap_of f l h.2⟩
      obtain ⟨b, hb, hfb⟩ := List.mem_filterMap.mp hx
      exact h.1 b hb x hfa hfb

/-- Lists joined end to end have no repetition, when none has and no two share a member. -/
theorem nodup_flatMap_of {α β : Type} (f : α → List β) : ∀ l : List α,
    (∀ a ∈ l, (f a).Nodup) → l.Pairwise (fun a b => ∀ x, x ∈ f a → x ∉ f b) →
      (l.flatMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h₁, h₂ => by
    rw [List.pairwise_cons] at h₂
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨h₁ a List.mem_cons_self,
      nodup_flatMap_of f l (fun b hb => h₁ b (List.mem_cons_of_mem _ hb)) h₂.2, ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hy
    exact h₂.1 b hb x hx hxb

/-! ## One unbroken run -/

/-- The first member of a list that fails a test. -/
theorem first_fail {α : Type} (p : α → Prop) :
    ∀ l : List α, (∃ x ∈ l, ¬ p x) →
      ∃ (T : List α) (x : α) (D : List α), l = T ++ x :: D ∧ (∀ y ∈ T, p y) ∧ ¬ p x
  | [], ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, ⟨x, hx, hpx⟩ => by
    by_cases ha : p a
    · have hxl : x ∈ l := (List.mem_cons.mp hx).resolve_left (fun e => hpx (e ▸ ha))
      obtain ⟨T, y, D, he, hT, hy⟩ := first_fail p l ⟨x, hxl, hpx⟩
      refine ⟨a :: T, y, D, by rw [he]; rfl, fun z hz => ?_, hy⟩
      rcases List.mem_cons.mp hz with e | hz
      · exact e ▸ ha
      · exact hT z hz
    · exact ⟨[], a, l, rfl, fun _ h => absurd h List.not_mem_nil, ha⟩

/-- Four members, one from each of four lists, are in order in the lists joined. -/
theorem sub4 {α : Type} {a b c d : α} {l₁ l₂ l₃ l₄ : List α} (ha : a ∈ l₁) (hb : b ∈ l₂)
    (hc : c ∈ l₃) (hd : d ∈ l₄) : [a, b, c, d].Sublist (l₁ ++ l₂ ++ l₃ ++ l₄) := by
  have hs := (((List.singleton_sublist.mpr ha).append (List.singleton_sublist.mpr hb)).append
    (List.singleton_sublist.mpr hc)).append (List.singleton_sublist.mpr hd)
  simpa using hs

/-- **One unbroken run.** If no four members of a list, in order, alternate between passing
and failing a test, and some pass and some fail, then the list, read from a suitable member,
is a run that passes followed by a run that fails. -/
theorem block {α : Type} (p : α → Prop) (l : List α) (hp : ∃ x ∈ l, p x)
    (hn : ∃ x ∈ l, ¬ p x)
    (h₁ : ∀ a b c d, [a, b, c, d].Sublist l → p a → ¬ p b → p c → ¬ p d → False)
    (h₂ : ∀ a b c d, [a, b, c, d].Sublist l → ¬ p a → p b → ¬ p c → p d → False) :
    ∃ pre post Ps Ns : List α, l = pre ++ post ∧ post ++ pre = Ps ++ Ns ∧ Ps ≠ [] ∧
      Ns ≠ [] ∧ (∀ x ∈ Ps, p x) ∧ ∀ x ∈ Ns, ¬ p x := by
  obtain ⟨T, x, D, hl, hT, hx⟩ := first_fail p l hn
  cases T with
  | cons t T =>
    have ht := hT t List.mem_cons_self
    by_cases hD : ∃ y ∈ D, p y
    · obtain ⟨N, y, D₂, hD', hN, hy⟩ := first_fail (fun z => ¬ p z) D (by
        obtain ⟨y, hy, hpy⟩ := hD
        exact ⟨y, hy, Classical.not_not.mpr hpy⟩)
      have hy' : p y := Classical.not_not.mp hy
      have hD₂ : ∀ z ∈ D₂, p z := by
        intro z hz
        by_cases hpz : p z
        · exact hpz
        · exfalso
          apply h₁ t x y z _ ht hx hy' hpz
          rw [hl, hD']
          simpa using sub4 (l₁ := t :: T) (l₂ := x :: N) (l₃ := [y]) (l₄ := D₂)
            List.mem_cons_self List.mem_cons_self List.mem_cons_self hz
      refine ⟨t :: T ++ x :: N, y :: D₂, y :: D₂ ++ t :: T, x :: N, ?_, by simp,
        by simp, by simp, ?_, ?_⟩
      · rw [hl, hD']
        simp
      · intro z hz
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hz
        rcases hz with e | hz | e | hz
        · exact e ▸ hy'
        · exact hD₂ z hz
        · exact e ▸ ht
        · exact hT z (List.mem_cons_of_mem _ hz)
      · intro z hz
        rcases List.mem_cons.mp hz with e | hz
        · exact e ▸ hx
        · exact hN z hz
    · refine ⟨[], t :: T ++ x :: D, t :: T, x :: D, by simp [hl], by simp, by simp, by simp,
        hT, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with e | hz
      · exact e ▸ hx
      · exact fun hpz => hD ⟨z, hz, hpz⟩
  | nil =>
    simp only [List.nil_append] at hl
    obtain ⟨N, y, D₂, hD', hN, hy⟩ := first_fail (fun z => ¬ p z) D (by
      obtain ⟨y, hy, hpy⟩ := hp
      rw [hl] at hy
      rcases List.mem_cons.mp hy with e | hy
      · exact absurd (e ▸ hpy) hx
      · exact ⟨y, hy, Classical.not_not.mpr hpy⟩)
    have hy' : p y := Classical.not_not.mp hy
    by_cases hD₂ : ∃ z ∈ D₂, ¬ p z
    · obtain ⟨Q, z, D₃, hD₂', hQ, hz⟩ := first_fail p D₂ hD₂
      have hD₃ : ∀ w ∈ D₃, ¬ p w := by
        intro w hw hpw
        apply h₂ x y z w _ hx hy' hz hpw
        rw [hl, hD', hD₂']
        simpa using sub4 (l₁ := [x]) (l₂ := N ++ [y]) (l₃ := Q ++ [z]) (l₄ := D₃)
          List.mem_cons_self (by simp) (by simp) hw
      refine ⟨x :: N, y :: Q ++ z :: D₃, y :: Q, z :: D₃ ++ x :: N, ?_, by simp,
        by simp, by simp, ?_, ?_⟩
      · rw [hl, hD', hD₂']
        simp
      · intro w hw
        rcases List.mem_cons.mp hw with e | hw
        · exact e ▸ hy'
        · exact hQ w hw
      · intro w hw
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hw
        rcases hw with e | hw | e | hw
        · exact e ▸ hz
        · exact hD₃ w hw
        · exact e ▸ hx
        · exact hN w hw
    · refine ⟨x :: N, y :: D₂, y :: D₂, x :: N, ?_, by simp, by simp, by simp, ?_, ?_⟩
      · rw [hl, hD']
        simp
      · intro w hw
        rcases List.mem_cons.mp hw with e | hw
        · exact e ▸ hy'
        · by_cases hpw : p w
          · exact hpw
          · exact absurd ⟨w, hw, hpw⟩ hD₂
      · intro w hw
        rcases List.mem_cons.mp hw with e | hw
        · exact e ▸ hx
        · exact hN w hw

/-! ## Lists with nothing in some places

A piece of a cut may be nothing, so a list of pieces may hold nothing in some places; the
members present are counted by `filterMap id`. -/

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
theorem count_split_some {α : Type} (pre post : List (Option α)) (a : α) :
    ((pre ++ some a :: post).filterMap id).length = ((pre ++ post).filterMap id).length + 1 := by
  simp only [List.filterMap_append, List.filterMap_cons, id, List.length_append,
    List.length_cons]
  omega

/-! ## Counting the members that pass a test -/

/-- Splitting a count by a second test. -/
theorem countP_and_add {α : Type} (l : List α) (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] :
    l.countP (fun x => decide (P x ∧ Q x)) + l.countP (fun x => decide (P x ∧ ¬ Q x)) =
      l.countP (fun x => decide (P x)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, decide_eq_true_eq]
    by_cases hP : P a <;> by_cases hQ : Q a <;>
      simp only [hP, hQ, and_true, and_false, not_true_eq_false, not_false_eq_true, ite_true,
        ite_false] <;> omega

/-- A test passed only by one member of a list of distinct members counts at most one. -/
theorem countP_le_one {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, l.Nodup → (∀ z ∈ l, p z = true → z = x) → l.countP p ≤ 1
  | [], _, _ => Nat.zero_le _
  | a :: l, hnd, h => by
    rw [List.nodup_cons] at hnd
    rw [List.countP_cons]
    cases ha : p a
    · have := countP_le_one hnd.2 (fun z hz => h z (List.mem_cons_of_mem _ hz))
      simp only [Bool.false_eq_true, ite_false]
      omega
    · have hax := h a List.mem_cons_self ha
      have hl : l.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro z hz hpz
        have hzx := h z (List.mem_cons_of_mem _ hz) hpz
        exact hnd.1 (hax ▸ hzx ▸ hz)
      simp only [hl, ite_true]
      omega

/-- A test that no two members pass together keeps at most one. -/
theorem count_le_one {α : Type} (p : α → Bool) : ∀ l : List α,
    l.Pairwise (fun a b => ¬ (p a = true ∧ p b = true)) → (l.filter p).length ≤ 1
  | [], _ => by simp
  | b :: l, h => by
    rw [List.pairwise_cons] at h
    simp only [List.filter_cons]
    by_cases hb : p b = true
    · have he : l.filter p = [] :=
        List.filter_eq_nil_iff.mpr fun x hx hpx => h.1 x hx ⟨hb, hpx⟩
      simp [hb, he]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact count_le_one p l h.2

/-- A filter of a list of distinct members that keeps exactly one of them has length one. -/
theorem filter_length_one {α : Type} {l : List α} (hnd : l.Nodup) {q : α → Bool} {s : α}
    (hs : s ∈ l) (hq : q s = true)
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

/-- A test passed by exactly two distinct members of a list of distinct members counts two. -/
theorem countP_two {α : Type} {l : List α} (hnd : l.Nodup) {p : α → Bool} {x y : α}
    (hxy : x ≠ y) (h : ∀ z, (z ∈ l ∧ p z = true) ↔ (z = x ∨ z = y)) : l.countP p = 2 := by
  rw [List.countP_eq_length_filter]
  have hnd' : (l.filter p).Nodup := List.Pairwise.filter p hnd
  have hxy' : [x, y].Nodup := by simp [hxy]
  have hperm : (l.filter p).Perm [x, y] := by
    rw [List.perm_ext_iff_of_nodup hnd' hxy']
    intro z
    rw [List.mem_filter, h z]
    simp
  rw [hperm.length_eq]
  rfl

/-- Two different members of a list passing a test count at least two. -/
theorem two_le_countP {α : Type} {l : List α} {p : α → Bool} {x y : α} (hx : x ∈ l)
    (hy : y ∈ l) (hxy : x ≠ y) (hpx : p x = true) (hpy : p y = true) : 2 ≤ l.countP p := by
  rw [List.countP_eq_length_filter]
  have hsub : [x, y] ⊆ l.filter p := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact List.mem_filter.mpr ⟨hx, hpx⟩
    · exact List.mem_filter.mpr ⟨hy, hpy⟩
  exact List.Nodup.length_le_of_subset (by simp [hxy]) hsub

/-- A test that implies another, and fails somewhere the other passes, counts strictly less. -/
theorem countP_lt {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      (∃ x ∈ l, q x = true ∧ p x = false) → l.countP p < l.countP q
  | [], _, ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | a :: l, hpq, ⟨x, hx, hqx, hpx⟩ => by
    have hle : l.countP p ≤ l.countP q :=
      List.countP_mono_left fun y hy => hpq y (List.mem_cons_of_mem _ hy)
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [hqx, hpx, Bool.false_eq_true, ite_false, ite_true]
      omega
    · have hlt := countP_lt (fun y hy => hpq y (List.mem_cons_of_mem _ hy)) ⟨x, hx, hqx, hpx⟩
      cases hpa : p a
      · cases q a <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
      · simp only [hpq a List.mem_cons_self hpa, ite_true]
        omega

/-- Two tests agreeing on a list of distinct members, except at one member, which passes the
first and fails the second, count one more for the first. -/
theorem countP_succ {α : Type} (p q : α → Bool) :
    ∀ (l : List α) (s : α), l.Nodup → s ∈ l → p s = true → q s = false →
      (∀ t ∈ l, t ≠ s → p t = q t) → l.countP p = l.countP q + 1
  | [], _, _, hs, _, _, _ => absurd hs List.not_mem_nil
  | a :: l, s, hnd, hs, hp, hq, h => by
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hs with e | hs'
    · subst e
      have hl : l.countP p = l.countP q := List.countP_congr fun t ht => by
        rw [h t (List.mem_cons_of_mem _ ht) (fun e => hnd.1 (e ▸ ht))]
      simp only [List.countP_cons, hp, hq, hl]
      simp
    · have hne : a ≠ s := fun e => hnd.1 (e ▸ hs')
      have ih := countP_succ p q l s hnd.2 hs' hp hq
        (fun t ht => h t (List.mem_cons_of_mem _ ht))
      simp only [List.countP_cons, h a List.mem_cons_self hne, ih]
      omega

/-- A filter by a test that is one of two exclusive tests has the two filters' lengths
together. -/
theorem filter_or_length {α : Type} (p q r : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, (p x = true ↔ q x = true ∨ r x = true) ∧
        ¬ (q x = true ∧ r x = true)) →
      (l.filter p).length = (l.filter q).length + (l.filter r).length
  | [], _ => rfl
  | a :: l, h => by
    have ih := filter_or_length p q r l fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨h₁, h₂⟩ := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> cases hr : r a <;>
      simp only [hp, hq, hr] at h₁ h₂ <;> simp at h₁ h₂ <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

/-- Two pairs of tests on each member of a list, the first pair agreeing exactly when the
second pair agrees, give totals of the same parity. -/
theorem countP_parity {α : Type} (l : List α) (p q u v : α → Bool)
    (h : ∀ x ∈ l, (p x = q x ↔ u x = v x)) :
    (l.countP p + l.countP q) % 2 = (l.countP u + l.countP v) % 2 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.countP_cons]
    cases hp : p a <;> cases hq : q a <;> cases hu : u a <;> cases hv : v a <;>
      simp only [hp, hq, hu, hv] at ha <;> simp at ha ⊢ <;> omega

/-- Two tests agreeing on every member but one, where they disagree, keep numbers of members
of opposite parity, in a list without repetition. -/
theorem count_flip {α : Type} (p q : α → Bool) {a : α} :
    ∀ l : List α, l.Nodup → a ∈ l → p a = !q a → (∀ x ∈ l, x ≠ a → p x = q x) →
      ((l.filter p).length + (l.filter q).length) % 2 = 1
  | [], _, ha, _, _ => absurd ha List.not_mem_nil
  | b :: l, hnd, ha, hpa, hsame => by
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons]
    by_cases hba : b = a
    · subst hba
      have he : l.filter p = l.filter q := List.filter_congr fun x hx =>
        hsame x (List.mem_cons_of_mem _ hx) fun e => hnd.1 (e ▸ hx)
      rw [he, hpa]
      cases q b <;>
        simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
          List.length_cons] <;> omega
    · have ha' : a ∈ l := (List.mem_cons.mp ha).resolve_left fun e => hba e.symm
      have ih := count_flip p q l hnd.2 ha' hpa fun x hx => hsame x (List.mem_cons_of_mem _ hx)
      rw [hsame b List.mem_cons_self hba]
      cases q b <;>
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

/-- Two tests agreeing on all but one member of a list, and disagreeing there: one of the two
counts is odd. -/
theorem countP_flip {α : Type} (pre post : List α) (a : α) (p q : α → Bool)
    (h : ∀ x ∈ pre ++ post, p x = q x) (ha : p a = true ↔ q a = false) :
    (pre ++ a :: post).countP p % 2 = 1 ∨ (pre ++ a :: post).countP q % 2 = 1 := by
  have e1 : pre.countP p = pre.countP q := List.countP_congr fun x hx => by
    rw [h x (List.mem_append_left _ hx)]
  have e2 : post.countP p = post.countP q := List.countP_congr fun x hx => by
    rw [h x (List.mem_append_right _ hx)]
  simp only [List.countP_append, List.countP_cons, e1, e2]
  cases hp : p a <;> cases hq : q a <;> simp only [hp, hq] at ha <;> simp at ha ⊢ <;> omega

/-! ## Sums of natural numbers -/

/-- Adding two numbers at each place and then summing gives the sum of the two totals. -/
theorem sum_add_nat {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

/-- A sum whose terms are all nought is nought. -/
theorem sum_eq_zero_of {α : Type} (l : List α) (f : α → Nat) (h : ∀ x ∈ l, f x = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- A sum of sums, exchanged. -/
theorem sum_exchange_nat {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    (xs.map fun x => (ys.map fun y => f x y).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact (sum_eq_zero_of ys _ fun _ _ => rfl).symm
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    exact (sum_add_nat ys (fun y => f x y) (fun y => (xs.map fun x => f x y).sum)).symm

open Classical in
/-- The sum of the values of a test that passes once in a list, counting from where it
passes. -/
theorem sum_single {α : Type} (r : α → α → Prop) (f : α → Nat) (x : α) :
    ∀ (D : List α), (∃ e ∈ D, r x e) →
      (D.Pairwise fun d e => ∀ z, r z d → ¬ r z e) → (∀ e, r x e → f e = f x) →
      (D.map fun e => (if r x e then 1 else 0) * f e).sum = f x
  | [], ⟨_, h, _⟩, _, _ => absurd h List.not_mem_nil
  | d :: D, ⟨e, he, hxe⟩, hpw, hf => by
    rw [List.pairwise_cons] at hpw
    simp only [List.map_cons, List.sum_cons]
    by_cases hxd : r x d
    · have hrest : (D.map fun e => (if r x e then 1 else 0) * f e).sum = 0 := by
        refine sum_eq_zero_of D _ fun e' he' => ?_
        simp only [hpw.1 e' he' x hxd, ite_false, Nat.zero_mul]
      rw [hrest, ite_eq_left hxd, hf d hxd]
      omega
    · rcases List.mem_cons.mp he with rfl | he
      · exact absurd hxe hxd
      rw [ite_eq_right hxd, sum_single r f x D ⟨e, he, hxe⟩ hpw.2 hf]
      omega

open Classical in
/-- **Regrouping a sum.** If every member of M is related to some member of D, the members of D
pairwise unrelated to a common member, and f constant on related members, then the sum of f
over M is the sum over D of f, each member of D counted as often as M names it. -/
theorem sum_regroup {α : Type} (r : α → α → Prop) (f : α → Nat) (D : List α)
    (hD : D.Pairwise fun d e => ∀ z, r z d → ¬ r z e) :
    ∀ (M : List α), (∀ x ∈ M, ∃ e ∈ D, r x e) → (∀ x e, r x e → f e = f x) →
      (M.map f).sum = (D.map fun e => M.countP (fun x => decide (r x e)) * f e).sum
  | [], _, _ => by
    simp only [List.map_nil, List.sum_nil, List.countP_nil, Nat.zero_mul]
    exact (sum_eq_zero_of D _ fun _ _ => rfl).symm
  | x :: M, hM, hf => by
    have ih := sum_regroup r f D hD M (fun y hy => hM y (List.mem_cons_of_mem _ hy)) hf
    have hpt : ∀ e ∈ D, (x :: M).countP (fun y => decide (r y e)) * f e =
        (if r x e then 1 else 0) * f e + M.countP (fun y => decide (r y e)) * f e := by
      intro e _
      rw [List.countP_cons, Nat.add_mul, Nat.add_comm]
      simp only [decide_eq_true_eq]
    rw [List.map_congr_left hpt, sum_add_nat,
      sum_single r f x D (hM x List.mem_cons_self) hD (fun e h => hf x e h),
      List.map_cons, List.sum_cons, ih]

/-- A count, as a sum of ones and noughts. -/
theorem countP_eq_sum {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] :
    l.countP (fun x => decide (p x)) = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, ih, decide_eq_true_eq]
    omega

/-- Counting the members whose number is odd gives the parity of the sum. -/
theorem countP_odd_sum {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → Nat)
    (h : ∀ x ∈ l, p x ↔ f x % 2 = 1) :
    l.countP (fun x => decide (p x)) % 2 = (l.map f).sum % 2 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h a List.mem_cons_self
    simp only [List.countP_cons, List.map_cons, List.sum_cons, decide_eq_true_eq]
    by_cases hp : p a
    · have := ha.mp hp
      simp only [hp, ite_true]
      omega
    · have : f a % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one (f a) with e | e
        · exact e
        · exact absurd (ha.mpr e) hp
      simp only [hp, ite_false]
      omega

/-- Termwise equal parities give sums of equal parity. -/
theorem sum_mod_two {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x % 2 = g x % 2) : (l.map f).sum % 2 = (l.map g).sum % 2 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    omega

end Elements.Figures
