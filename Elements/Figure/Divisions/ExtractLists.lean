import Elements.Figure.Outlines.Parity
import Elements.Figure.Lists

/-!
# Book Zero: closed walks through a boundary of even degree

Helper lemmas, in the namespace `Extract`, for `apart_has_outline`, in `Divisions.lean`
(brief 0013, section 8, "The arrangement and general division"; D10): the third step of
`Divisions/Extract.lean`. Pure bookkeeping of finite lists: no geometry is used. Nothing in
Book Zero cites a proposition of the *Elements*.

* **Finite straight lines read either way** (`Same`): two pairs of points name the same
  finite straight line when they have the same ends, in either order.
* **Regrouping a sum** (`sum_regroup`, in `Figure/Lists.lean`): a sum over a list of pairs,
  each naming one of a list of distinct finite straight lines, is a sum over those lines, each
  counted as often as it is named.
* **Simple closed walks** (`cycles`). Take finitely many points and a symmetric joining
  relation, each join carrying a class, such that at every point the joins of each class are
  even in number. Then the joins are the sides of finitely many closed walks, each through
  distinct points, at least three, all of its sides of one class, every join a side of
  exactly one walk, read once. Grow a chain of distinct points by joins of one class at its
  first point: the first point has a second join of the class, which leads either to a new
  point or back into the chain, closing a walk. Remove the walk's joins: every count drops
  by none or two, and the rest follows by induction on the number of joins.

Natural numbers count points, joins and crossings; they measure nothing.
-/

namespace Elements.Figures

namespace Extract

open Classical

/-! ## Finite straight lines read either way -/

/-- Two pairs of points name the same finite straight line: the same ends, in either order. -/
def Same (s t : Point × Point) : Prop := s = t ∨ s = t.swap

theorem same_refl (s : Point × Point) : Same s s := Or.inl rfl

theorem same_symm {s t : Point × Point} (h : Same s t) : Same t s := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Prod.swap_swap t).symm

theorem same_trans {s t u : Point × Point} (h₁ : Same s t) (h₂ : Same t u) : Same s u := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (Prod.swap_swap u)

/-! ## Distinct points, and pairs of them -/

/-- A list's members, each once. -/
noncomputable def nub : List Point → List Point
  | [] => []
  | x :: l => if x ∈ l then nub l else x :: nub l

theorem mem_nub {x : Point} : ∀ {l : List Point}, x ∈ nub l ↔ x ∈ l
  | [] => Iff.rfl
  | a :: l => by
    unfold nub
    by_cases ha : a ∈ l
    · rw [ite_eq_left ha, mem_nub, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact ha
        · exact h
    · rw [ite_eq_right ha, List.mem_cons, List.mem_cons, mem_nub]

theorem nodup_nub : ∀ (l : List Point), (nub l).Nodup
  | [] => List.nodup_nil
  | a :: l => by
    unfold nub
    by_cases ha : a ∈ l
    · rw [ite_eq_left ha]
      exact nodup_nub l
    · rw [ite_eq_right ha, List.nodup_cons, mem_nub]
      exact ⟨ha, nodup_nub l⟩

/-- All ordered pairs of points of a list. -/
def allPairs (vs : List Point) : List (Point × Point) :=
  vs.flatMap fun P => vs.map fun Q => (P, Q)

theorem mem_allPairs {vs : List Point} {e : Point × Point} :
    e ∈ allPairs vs ↔ e.1 ∈ vs ∧ e.2 ∈ vs := by
  unfold allPairs
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨P, hP, Q, hQ, rfl⟩
    exact ⟨hP, hQ⟩
  · intro h
    exact ⟨e.1, h.1, e.2, h.2, rfl⟩

/-- One of each pair of points named either way round: a pair is dropped when it, or its
reverse, comes later in the list. -/
noncomputable def oneWay : List (Point × Point) → List (Point × Point)
  | [] => []
  | e :: l => if ∃ d ∈ l, Same e d then oneWay l else e :: oneWay l

theorem oneWay_sub : ∀ {l : List (Point × Point)} {e : Point × Point}, e ∈ oneWay l → e ∈ l
  | [], _, h => h
  | a :: l, e, h => by
    unfold oneWay at h
    by_cases ha : ∃ d ∈ l, Same a d
    · rw [ite_eq_left ha] at h
      exact List.mem_cons_of_mem _ (oneWay_sub h)
    · rw [ite_eq_right ha] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (oneWay_sub h)

theorem oneWay_cover : ∀ {l : List (Point × Point)} {e : Point × Point}, e ∈ l →
    ∃ d ∈ oneWay l, Same e d
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, e, h => by
    unfold oneWay
    by_cases ha : ∃ d ∈ l, Same a d
    · rw [ite_eq_left ha]
      rcases List.mem_cons.mp h with rfl | h
      · obtain ⟨d, hd, hed⟩ := ha
        obtain ⟨d', hd', hdd'⟩ := oneWay_cover hd
        exact ⟨d', hd', same_trans hed hdd'⟩
      · exact oneWay_cover h
    · rw [ite_eq_right ha]
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨e, List.mem_cons_self, same_refl e⟩
      · obtain ⟨d, hd, hed⟩ := oneWay_cover h
        exact ⟨d, List.mem_cons_of_mem _ hd, hed⟩

theorem oneWay_pairwise : ∀ (l : List (Point × Point)),
    (oneWay l).Pairwise fun d e => ¬ Same d e
  | [] => List.Pairwise.nil
  | a :: l => by
    unfold oneWay
    by_cases ha : ∃ d ∈ l, Same a d
    · rw [ite_eq_left ha]
      exact oneWay_pairwise l
    · rw [ite_eq_right ha, List.pairwise_cons]
      exact ⟨fun d hd had => ha ⟨d, oneWay_sub hd, had⟩, oneWay_pairwise l⟩

/-- Pairwise unrelated in the sense of `sum_regroup`. -/
theorem pairwise_same {D : List (Point × Point)} (h : D.Pairwise fun d e => ¬ Same d e) :
    D.Pairwise fun d e => ∀ z, Same z d → ¬ Same z e :=
  h.imp fun hde _ hzd hze => hde (same_trans (same_symm hzd) hze)

/-! ## The neighbours of a corner of a closed walk -/

/-- The sides of a closed walk of three or more distinct corners name distinct finite straight
lines. -/
theorem sides_pairwise_same {L : List Point} (hlen : 3 ≤ L.length) (hnd : L.Nodup) :
    (sides L).Pairwise fun s t => ¬ Same s t := by
  have h := LoopFacts.sides_nodup hnd
  refine (List.Pairwise.and h (LoopFacts.sides_pairwise_fst hnd)).imp_of_mem ?_
  intro s t hs ht hst hsame
  rcases hsame with e | e
  · exact hst.1 e
  · have hs' : (t.2, t.1) ∈ sides L := by
      have : s = (t.2, t.1) := e
      rw [← this]
      exact hs
    exact LoopFacts.sides_no_swap hlen hnd ht hs'

/-- A corner of a closed walk of three or more distinct corners is an end of exactly two of its
sides, which lead to two different corners. -/
theorem loop_nbrs {L : List Point} (hlen : 3 ≤ L.length) (hnd : L.Nodup) {V : Point}
    (hV : V ∈ L) :
    ∃ x y : Point, x ≠ y ∧ ∀ W : Point, (∃ s ∈ sides L, Same s (V, W)) ↔ (W = x ∨ W = y) := by
  obtain ⟨E, hE⟩ := outgoing_side hV
  obtain ⟨Z, hZ⟩ := LoopFacts.incoming_side hV
  refine ⟨E, Z, fun hEZ => ?_, fun W => ⟨?_, ?_⟩⟩
  · rw [hEZ] at hE
    exact LoopFacts.sides_no_swap hlen hnd hE hZ
  · rintro ⟨s, hs, hsW | hsW⟩
    · have := LoopFacts.sides_fst_inj hnd hs hE (by rw [hsW])
      rw [hsW, Prod.mk.injEq] at this
      exact Or.inl this.2
    · have := Parity.sides_snd_inj hnd hs hZ (by rw [hsW]; rfl)
      rw [hsW] at this
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at this
      exact Or.inr this.1
  · rintro (rfl | rfl)
    · exact ⟨_, hE, same_refl _⟩
    · exact ⟨_, hZ, Or.inr rfl⟩

/-- A point that is no corner is an end of no side. -/
theorem not_nbr {L : List Point} {V : Point} (hV : V ∉ L) (W : Point) :
    ¬ ∃ s ∈ sides L, Same s (V, W) := by
  rintro ⟨s, hs, hsW | hsW⟩
  · have h := (LoopFacts.side_mem hs).1
    rw [hsW] at h
    exact hV h
  · have h := (LoopFacts.side_mem hs).2
    rw [hsW] at h
    exact hV h

/-! ## A simple closed walk of one class -/

section Walks

variable {κ : Type} (vs : List Point) (adj : Point → Point → Prop) (c : Point → Point → κ)

/-- One step of `find_cycle`: the first point has a second join of class k; if it leads to a
new point the chain grows, and the hypothesis on a longer chain gives a walk; otherwise it
closes a walk. -/
theorem find_cycle_step (k : κ) (hvs : vs.Nodup) (hsymm : ∀ P Q, adj P Q → adj Q P)
    (hc : ∀ P Q, c P Q = c Q P) (hirr : ∀ P, ¬ adj P P) (hmem : ∀ P Q, adj P Q → Q ∈ vs)
    (heven : ∀ V, (vs.countP fun W => decide (adj V W ∧ c V W = k)) % 2 = 0)
    (v0 v1 : Point) (rest : List Point) (hnd : (v0 :: v1 :: rest).Nodup)
    (hseg : ∀ s ∈ segments (v0 :: v1 :: rest), adj s.1 s.2 ∧ c s.1 s.2 = k)
    (hgrow : ∀ w, w ∈ vs → w ∉ v0 :: v1 :: rest → adj v0 w → c v0 w = k →
      ∃ L : List Point, 3 ≤ L.length ∧ L.Nodup ∧ ∀ s ∈ sides L, adj s.1 s.2 ∧ c s.1 s.2 = k) :
    ∃ L : List Point, 3 ≤ L.length ∧ L.Nodup ∧ ∀ s ∈ sides L, adj s.1 s.2 ∧ c s.1 s.2 = k := by
  have h01 := hseg (v0, v1) List.mem_cons_self
  /- A second join of class k at v0. -/
  obtain ⟨w, ⟨hw, hwc⟩, hwv1⟩ : ∃ w, (adj v0 w ∧ c v0 w = k) ∧ w ≠ v1 := by
    refine Classical.byContradiction fun hno => ?_
    have hall : ∀ z ∈ vs, decide (adj v0 z ∧ c v0 z = k) = true → z = v1 := by
      intro z _ hz
      refine Classical.byContradiction fun hzv => hno ⟨z, of_decide_eq_true hz, hzv⟩
    have hle := countP_le_one hvs hall
    have hpos : 0 < vs.countP fun W => decide (adj v0 W ∧ c v0 W = k) :=
      List.countP_pos_iff.mpr ⟨v1, hmem v0 v1 h01.1, by simpa using h01⟩
    have := heven v0
    omega
  have hwvs := hmem v0 w hw
  by_cases hwp : w ∈ v0 :: v1 :: rest
  · /- The join leads back into the chain, past v1: close the walk there. -/
    have hwv0 : w ≠ v0 := fun e => hirr v0 (e ▸ hw)
    have hwr : w ∈ rest := by
      rcases List.mem_cons.mp hwp with e | hwp
      · exact absurd e hwv0
      rcases List.mem_cons.mp hwp with e | hwp
      · exact absurd e hwv1
      exact hwp
    obtain ⟨r1, r2, rfl⟩ := List.append_of_mem hwr
    refine ⟨v0 :: v1 :: (r1 ++ [w]), by simp, ?_, ?_⟩
    · have hsub : (v0 :: v1 :: (r1 ++ [w])).Sublist (v0 :: v1 :: (r1 ++ w :: r2)) := by
        have : r1 ++ w :: r2 = (r1 ++ [w]) ++ r2 := by simp
        rw [this]
        exact ((List.sublist_append_left _ _).cons_cons v1).cons_cons v0
      exact hnd.sublist hsub
    · intro s hs
      have hsides : sides (v0 :: v1 :: (r1 ++ [w])) =
          segments (v0 :: v1 :: r1 ++ [w]) ++ [(w, v0)] := by
        have := segments_join (v0 :: v1 :: r1) [v0] w
        show segments (v0 :: v1 :: (r1 ++ [w]) ++ [v0]) = _
        have e : v0 :: v1 :: (r1 ++ [w]) ++ [v0] = v0 :: v1 :: r1 ++ w :: [v0] := by simp
        rw [e, this]
        rfl
      rw [hsides, List.mem_append] at hs
      rcases hs with hs | hs
      · have hs' : s ∈ segments ((v0 :: v1 :: r1 ++ [w]) ++ r2) := segment_mem_append hs r2
        apply hseg
        simpa using hs'
      · rw [List.mem_singleton] at hs
        rw [hs]
        exact ⟨hsymm v0 w hw, (hc w v0).trans hwc⟩
  · exact hgrow w hwvs hwp hw hwc

/-- **Closing a walk.** A chain of distinct points joined by joins of class k, with an even
number of joins of class k at every point, grows at its first point until a join of class k
leads back into it, closing a walk of at least three distinct points. -/
theorem find_cycle (k : κ) (hvs : vs.Nodup) (hsymm : ∀ P Q, adj P Q → adj Q P)
    (hc : ∀ P Q, c P Q = c Q P) (hirr : ∀ P, ¬ adj P P) (hmem : ∀ P Q, adj P Q → Q ∈ vs)
    (heven : ∀ V, (vs.countP fun W => decide (adj V W ∧ c V W = k)) % 2 = 0) :
    ∀ (m : Nat) (v0 v1 : Point) (rest : List Point),
      vs.length ≤ (v0 :: v1 :: rest).length + m → (v0 :: v1 :: rest).Nodup →
      (∀ x ∈ v0 :: v1 :: rest, x ∈ vs) →
      (∀ s ∈ segments (v0 :: v1 :: rest), adj s.1 s.2 ∧ c s.1 s.2 = k) →
      ∃ L : List Point, 3 ≤ L.length ∧ L.Nodup ∧ ∀ s ∈ sides L, adj s.1 s.2 ∧ c s.1 s.2 = k := by
  intro m
  induction m with
  | zero =>
    intro v0 v1 rest hlen hnd hin hseg
    refine find_cycle_step vs adj c k hvs hsymm hc hirr hmem heven v0 v1 rest hnd hseg ?_
    intro w hw hwp _ _
    have hsub : (w :: v0 :: v1 :: rest) ⊆ vs := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact hin x hx
    have := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hwp, hnd⟩) hsub
    simp only [List.length_cons] at this hlen
    omega
  | succ m ih =>
    intro v0 v1 rest hlen hnd hin hseg
    refine find_cycle_step vs adj c k hvs hsymm hc hirr hmem heven v0 v1 rest hnd hseg ?_
    intro w hw hwp hadj hcl
    refine ih w v0 (v1 :: rest) (by simp only [List.length_cons] at hlen ⊢; omega)
      (List.nodup_cons.mpr ⟨hwp, hnd⟩) ?_ ?_
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact hin x hx
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨hsymm v0 w hadj, (hc w v0).trans hcl⟩
      · exact hseg s hs

end Walks

/-- Removing the sides of a closed walk of joins of class k keeps every count of joins at a
point even: a corner of the walk loses exactly two joins, both of class k. -/
theorem even_remove {κ : Type} (vs : List Point) (hvs : vs.Nodup) (adj : Point → Point → Prop)
    (c : Point → Point → κ) (hc : ∀ P Q, c P Q = c Q P) (hsymm : ∀ P Q, adj P Q → adj Q P)
    (hmem : ∀ P Q, adj P Q → P ∈ vs ∧ Q ∈ vs)
    (heven : ∀ V k, (vs.countP fun W => decide (adj V W ∧ c V W = k)) % 2 = 0)
    {L : List Point} (hL3 : 3 ≤ L.length) (hLnd : L.Nodup) {k : κ}
    (hLs : ∀ s ∈ sides L, adj s.1 s.2 ∧ c s.1 s.2 = k) (V : Point) (k' : κ) :
    (vs.countP fun W => decide ((adj V W ∧ ¬ ∃ s ∈ sides L, Same s (V, W)) ∧ c V W = k')) % 2
      = 0 := by
  have hcongr : (vs.countP fun W => decide ((adj V W ∧ ¬ ∃ s ∈ sides L, Same s (V, W)) ∧
      c V W = k')) = vs.countP fun W => decide ((adj V W ∧ c V W = k') ∧
        ¬ ∃ s ∈ sides L, Same s (V, W)) := by
    refine List.countP_congr fun W _ => ?_
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  have hsplit := countP_and_add vs (fun W => adj V W ∧ c V W = k')
    (fun W => ∃ s ∈ sides L, Same s (V, W))
  have hboth : (vs.countP fun W => decide ((adj V W ∧ c V W = k') ∧
      ∃ s ∈ sides L, Same s (V, W))) % 2 = 0 := by
    /- A neighbour along the walk is joined to V by a join of class k. -/
    have hnb : ∀ W, (∃ s ∈ sides L, Same s (V, W)) → adj V W ∧ c V W = k := by
      rintro W ⟨s, hs, hsW | hsW⟩
      · have := hLs s hs
        rw [hsW] at this
        exact this
      · have := hLs s hs
        rw [hsW] at this
        exact ⟨hsymm _ _ this.1, (hc V W).trans this.2⟩
    by_cases hV : V ∈ L
    · obtain ⟨x, y, hxy, hnbr⟩ := loop_nbrs hL3 hLnd hV
      by_cases hk : k' = k
      · subst hk
        rw [countP_two hvs hxy]
        intro z
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨-, -, hq⟩
          exact (hnbr z).mp hq
        · intro hz
          have hq := (hnbr z).mpr hz
          exact ⟨(hmem V z (hnb z hq).1).2, hnb z hq, hq⟩
      · have : (vs.countP fun W => decide ((adj V W ∧ c V W = k') ∧
            ∃ s ∈ sides L, Same s (V, W))) = 0 := by
          rw [List.countP_eq_zero]
          intro z _ hz
          simp only [decide_eq_true_eq] at hz
          exact hk (hz.1.2.symm.trans (hnb z hz.2).2)
        rw [this]
    · have : (vs.countP fun W => decide ((adj V W ∧ c V W = k') ∧
          ∃ s ∈ sides L, Same s (V, W))) = 0 := by
        rw [List.countP_eq_zero]
        intro z _ hz
        simp only [decide_eq_true_eq] at hz
        exact not_nbr hV z hz.2
      rw [this]
  have := heven V k'
  rw [hcongr]
  omega

/-- **Simple closed walks.** Finitely many distinct points, a symmetric joining relation among
them, each join with a class, and at every point the joins of each class even in number: the
joins are the sides of finitely many closed walks, each of three or more distinct points with
all its sides of one class, every join a side of exactly one walk, read once. -/
theorem cycles {κ : Type} (vs : List Point) (hvs : vs.Nodup) (c : Point → Point → κ)
    (hc : ∀ P Q, c P Q = c Q P) :
    ∀ (n : Nat) (adj : Point → Point → Prop),
      (allPairs vs).countP (fun e => decide (adj e.1 e.2)) ≤ n →
      (∀ P Q, adj P Q → adj Q P) → (∀ P, ¬ adj P P) → (∀ P Q, adj P Q → P ∈ vs ∧ Q ∈ vs) →
      (∀ V k, (vs.countP fun W => decide (adj V W ∧ c V W = k)) % 2 = 0) →
      ∃ loops : List (List Point),
        (∀ L ∈ loops, 3 ≤ L.length ∧ L.Nodup ∧
          ∃ k, ∀ s ∈ sides L, adj s.1 s.2 ∧ c s.1 s.2 = k) ∧
        (loops.flatMap sides).Pairwise (fun s t => ¬ Same s t) ∧
        (∀ P Q, adj P Q → ∃ L ∈ loops, ∃ s ∈ sides L, Same s (P, Q)) := by
  intro n
  induction n with
  | zero =>
    intro adj hn _ _ hmem _
    have hno : ∀ P Q, ¬ adj P Q := by
      intro P Q h
      have hpos : 0 < (allPairs vs).countP (fun e => decide (adj e.1 e.2)) :=
        List.countP_pos_iff.mpr ⟨(P, Q), mem_allPairs.mpr (hmem P Q h), by simpa using h⟩
      omega
    exact ⟨[], by simp, List.Pairwise.nil, fun P Q h => absurd h (hno P Q)⟩
  | succ n ih =>
    intro adj hn hsymm hirr hmem heven
    by_cases hex : ¬ ∃ P Q, adj P Q
    · exact ⟨[], by simp, List.Pairwise.nil, fun P Q h => absurd ⟨P, Q, h⟩ hex⟩
    obtain ⟨P0, Q0, h0⟩ := Classical.not_not.mp hex
    have hPQ : P0 ≠ Q0 := fun e => hirr P0 (by rw [← e] at h0; exact h0)
    /- A closed walk of class c P0 Q0. -/
    obtain ⟨L, hL3, hLnd, hLs⟩ := find_cycle vs adj c (c P0 Q0) hvs hsymm hc hirr
      (fun P Q h => (hmem P Q h).2) (fun V => heven V (c P0 Q0)) vs.length P0 Q0 []
      (by simp) (by simpa using hPQ)
      (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact (hmem _ _ h0).1
        · exact (hmem _ _ h0).2)
      (by
        intro s hs
        simp only [segments, List.mem_singleton] at hs
        rw [hs]
        exact ⟨h0, rfl⟩)
    /- Remove its sides. -/
    obtain ⟨adj', hadj'⟩ : ∃ adj' : Point → Point → Prop,
        ∀ P Q, adj' P Q ↔ (adj P Q ∧ ¬ ∃ s ∈ sides L, Same s (P, Q)) :=
      ⟨_, fun _ _ => Iff.rfl⟩
    have hsymm' : ∀ P Q, adj' P Q → adj' Q P := by
      intro P Q h
      obtain ⟨h, hn⟩ := (hadj' P Q).mp h
      refine (hadj' Q P).mpr ⟨hsymm P Q h, fun ⟨s, hs, hsame⟩ => hn ⟨s, hs, ?_⟩⟩
      rcases hsame with e | e
      · exact Or.inr e
      · exact Or.inl e
    have hlt : (allPairs vs).countP (fun e => decide (adj' e.1 e.2)) <
        (allPairs vs).countP (fun e => decide (adj e.1 e.2)) := by
      obtain ⟨E, hE⟩ := outgoing_side (List.head_mem (List.ne_nil_of_length_pos (by omega)) :
        L.head (List.ne_nil_of_length_pos (by omega)) ∈ L)
      refine countP_lt (fun e _ he => ?_) ⟨_, mem_allPairs.mpr (hmem _ _ (hLs _ hE).1), ?_⟩
      · simp only [decide_eq_true_eq] at he ⊢
        exact ((hadj' _ _).mp he).1
      · simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        exact ⟨(hLs _ hE).1, fun h => ((hadj' _ _).mp h).2 ⟨_, hE, same_refl _⟩⟩
    have heven' : ∀ V k', (vs.countP fun W => decide (adj' V W ∧ c V W = k')) % 2 = 0 := by
      intro V k'
      have h := even_remove vs hvs adj c hc hsymm hmem heven hL3 hLnd hLs V k'
      rwa [List.countP_congr (q := fun W => decide (adj' V W ∧ c V W = k'))] at h
      intro W _
      simp only [decide_eq_true_eq, hadj']
    obtain ⟨loops, hl1, hl2, hl3⟩ := ih adj' (by omega) hsymm'
      (fun P h => hirr P ((hadj' P P).mp h).1) (fun P Q h => hmem P Q ((hadj' P Q).mp h).1)
      heven'
    refine ⟨L :: loops, ?_, ?_, ?_⟩
    · intro L' hL'
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact ⟨hL3, hLnd, c P0 Q0, hLs⟩
      · obtain ⟨h3, hnd, k, hk⟩ := hl1 L' hL'
        exact ⟨h3, hnd, k, fun s hs => ⟨((hadj' _ _).mp (hk s hs).1).1, (hk s hs).2⟩⟩
    · rw [List.flatMap_cons, List.pairwise_append]
      refine ⟨sides_pairwise_same hL3 hLnd, hl2, ?_⟩
      intro s hs t ht hst
      obtain ⟨L', hL', ht'⟩ := List.mem_flatMap.mp ht
      obtain ⟨-, -, k, hk⟩ := hl1 L' hL'
      exact ((hadj' _ _).mp (hk t ht').1).2 ⟨s, hs, hst⟩
    · intro P Q h
      by_cases hin : ∃ s ∈ sides L, Same s (P, Q)
      · obtain ⟨s, hs, hsame⟩ := hin
        exact ⟨L, List.mem_cons_self, s, hs, hsame⟩
      · obtain ⟨L', hL', s, hs, hsame⟩ := hl3 P Q ((hadj' P Q).mpr ⟨h, hin⟩)
        exact ⟨L', List.mem_cons_of_mem _ hL', s, hs, hsame⟩

end Extract

end Elements.Figures
