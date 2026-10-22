import Elements.Figure.Divisions.ExtractEdges

/-!
# Book Zero: the outline of triangles that lie apart

The proof, in the namespace `Extract`, of `apart_has_outline`, in `Divisions.lean` (brief
0013, section 8, "The arrangement and general division"; D10): every figure given as
triangles that lie apart (`Apart`) has an outline with exactly its closed coverage, holes,
separate pieces and contacts at corners included. Nothing in Book Zero cites a proposition
of the *Elements*.

**The route.** Not the route the brief sketches, which traces the boundary round each corner
and splits closed walks where they return; this one examines no sector at a corner. Nor does
it cut the sides at all their intersections, as the brief proposes: cutting them at the
triangles' corners alone suffices, since two sides never cross (`no_cross`).

1. Cut the triangles' sides at all their corners into elementary finite straight lines
   (`ExtractEdges.lean`). One lies along the sides of one triangle or of two, never three; it
   is a **boundary line** (`Bdry`) when along one only.
2. Two triangles along one elementary line are **linked** (`Linked`), and linking classes the
   boundary lines (`Cls`). At each corner, the boundary lines of each class are even in number
   (`even_degree`): every triangle through the corner has two elementary lines there, and an
   elementary line along two triangles joins two of one class.
3. So the boundary lines are the sides of finitely many simple closed walks, each of one class
   (`cycles`, in `ExtractLists.lean`). These are the contours.
4. A contour B has one inside-status on all the closed triangles of a class off it
   (`linked_status`): no inner point of a triangle is on B, and two triangles along one
   elementary line share a point of it off B. Every point of a contour A off B lies on a
   closed triangle of A's class, so A lies wholly inside or wholly outside B, off B; and two
   such contours are compatible (`compatible_of_status`, in `ExtractRay.lean`).
5. Off the triangles' sides, the contours' crossings along a ray through no corner are the
   boundary lines' crossings, and the triangles' crossings count every elementary line once
   or twice, the boundary lines once (`tri_parity`). So the depth is odd exactly where a
   triangle's inside is (`parity_at`); on an elementary line along two triangles, the depth is
   that of a nearby inner point.

Natural numbers count corners, sides, triangles and crossings; they measure nothing.
-/

namespace Elements.Figures

namespace Extract

open Tacit Classical

section Assembly

variable (R : Apart)

/-- **A boundary line**: an elementary finite straight line along the sides of exactly one
triangle. -/
def Bdry (P Q : Point) : Prop := Elem R P Q ∧ mult R (P, Q) = 1

theorem bdry_symm {P Q : Point} (h : Bdry R P Q) : Bdry R Q P :=
  ⟨elem_symm R h.1, (mult_of_same R (Or.inr rfl)).symm.trans h.2⟩

theorem bdry_of_same {e e' : Point × Point} (h : Same e e') (he : Bdry R e.1 e.2) :
    Bdry R e'.1 e'.2 :=
  ⟨elem_of_same R h he.1, (mult_of_same R h).symm.trans he.2⟩

/-- A boundary line lies along exactly one triangle. -/
theorem bdry_tri {P Q : Point} (h : Bdry R P Q) :
    ∃ t ∈ R.pieces, InSide (P, Q) t ∧ ∀ t' ∈ R.pieces, InSide (P, Q) t' → t' = t := by
  obtain ⟨-, -, -, ⟨t, ht, hin⟩, -⟩ := h.1
  refine ⟨t, ht, hin, fun t' ht' hin' => Classical.byContradiction fun hne => ?_⟩
  have := two_le_countP (p := fun t => decide (InSide (P, Q) t)) ht ht' (Ne.symm hne)
    (decide_eq_true hin) (decide_eq_true hin')
  have h2 := h.2
  unfold mult at h2
  omega

/-- No inner point of a triangle is on an elementary line. -/
theorem inside_off_elem {t : Point × Point × Point} (ht : t ∈ R.pieces) {X : Point}
    (hX : InsideTriangle X t.1 t.2.1 t.2.2) {P Q : Point} (he : Elem R P Q) :
    ¬ OnFiniteLine X P Q := by
  obtain ⟨-, -, -, ⟨t', ht', s, hs, hPs, hQs⟩, -⟩ := he
  intro hXPQ
  exact int_not_on_side R ht ht' hX hs (onFinite_within hPs hQs hXPQ)

/-- No inner point of a triangle is on a loop of elementary lines. -/
theorem inside_off_loop {B : List Point} (hBs : ∀ s ∈ sides B, Elem R s.1 s.2)
    {t : Point × Point × Point} (ht : t ∈ R.pieces) {X : Point}
    (hX : InsideTriangle X t.1 t.2.1 t.2.2) : ¬ LoopBoundary B X := by
  rintro ⟨s, hs, hXs⟩
  exact inside_off_elem R ht hX (hBs s hs) hXs

/-- **One status on a closed triangle.** Points within or on a triangle, off a loop of
elementary lines, are inside it together: join each to an inner point of the triangle, by a
finite straight line through no corner of the loop, which meets no elementary line. -/
theorem triangle_status {B : List Point} (hB : SimpleLoop B) (hBs : ∀ s ∈ sides B, Elem R s.1 s.2)
    {t : Point × Point × Point} (ht : t ∈ R.pieces) {X X' : Point}
    (hX : OnOrInsideTriangle X t.1 t.2.1 t.2.2) (hX' : OnOrInsideTriangle X' t.1 t.2.1 t.2.2)
    (hXB : ¬ LoopBoundary B X) (hX'B : ¬ LoopBoundary B X') :
    LoopInside B X ↔ LoopInside B X' := by
  have htri := R.triangle t ht
  obtain ⟨K, hXK⟩ := exists_line_through X
  obtain ⟨K', hX'K⟩ := exists_line_through X'
  obtain ⟨W, hW, hWa⟩ := triangle_point_avoiding htri
    (K :: K' :: ((B.map fun V => Classical.choose (collinear_of_two X V)) ++
      B.map fun V => Classical.choose (collinear_of_two X' V)))
  have hWB := inside_off_loop R hBs ht hW
  have step : ∀ {Y : Point} {KY : Line}, OnOrInsideTriangle Y t.1 t.2.1 t.2.2 →
      ¬ LoopBoundary B Y → OnLine Y KY → ¬ OnLine W KY →
      Avoid (B.map fun V => Classical.choose (collinear_of_two Y V)) W →
      (LoopInside B Y ↔ LoopInside B W) := by
    intro Y KY hY hYB hYK hWK hj
    have hYW : Y ≠ W := fun e => hWK (e ▸ hYK)
    obtain ⟨ℓ, hYℓ, hWℓ⟩ := Postulate1 Y W hYW
    exact CoverFacts.inside_of_segment hB hYW hYℓ hWℓ
      (CoverFacts.joins_off hj (not_mem_of_off hYB) hYℓ hWℓ) hYB hWB
      (fun U hU => inside_off_loop R hBs ht (Extreme.between_triangle_open htri hY hW hU))
  have e1 := step hX hXB hXK (hWa K List.mem_cons_self)
    (fun L hL => hWa L (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left _ hL))))
  have e2 := step hX' hX'B hX'K (hWa K' (List.mem_cons_of_mem _ List.mem_cons_self))
    (fun L hL => hWa L (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ hL))))
  exact e1.trans e2.symm

/-! ## Linked triangles -/

/-- Two triangles of the division along one elementary line. -/
def Adj (t u : Point × Point × Point) : Prop :=
  t ∈ R.pieces ∧ u ∈ R.pieces ∧ ∃ P Q, Elem R P Q ∧ InSide (P, Q) t ∧ InSide (P, Q) u

theorem adj_symm {t u : Point × Point × Point} (h : Adj R t u) : Adj R u t := by
  obtain ⟨ht, hu, P, Q, he, h1, h2⟩ := h
  exact ⟨hu, ht, P, Q, he, h2, h1⟩

/-- **Linked triangles**: joined by a chain of triangles, each along one elementary line with
the next. -/
inductive Linked (R : Apart) : (Point × Point × Point) → (Point × Point × Point) → Prop
  | refl (t : Point × Point × Point) : Linked R t t
  | step {t u v : Point × Point × Point} : Linked R t u → Adj R u v → Linked R t v

theorem Linked.head {t u v : Point × Point × Point} (ha : Adj R t u) (h : Linked R u v) :
    Linked R t v := by
  induction h with
  | refl => exact Linked.step (Linked.refl t) ha
  | step _ hb ih => exact Linked.step ih hb

theorem Linked.symm {t u : Point × Point × Point} (h : Linked R t u) : Linked R u t := by
  induction h with
  | refl => exact Linked.refl _
  | step _ ha ih => exact Linked.head R (adj_symm R ha) ih

theorem Linked.trans {t u v : Point × Point × Point} (h₁ : Linked R t u) (h₂ : Linked R u v) :
    Linked R t v := by
  induction h₂ with
  | refl => exact h₁
  | step _ ha ih => exact Linked.step ih ha

/-- An elementary line along two different triangles is no boundary line, nor the same as one. -/
theorem not_same_bdry {P Q : Point} {t u : Point × Point × Point} (ht : t ∈ R.pieces)
    (hu : u ∈ R.pieces) (hne : t ≠ u) (h1 : InSide (P, Q) t) (h2 : InSide (P, Q) u)
    {e : Point × Point} (he : Bdry R e.1 e.2) : ¬ Same e (P, Q) := by
  intro hs
  have := two_le_countP (p := fun t => decide (InSide (P, Q) t)) ht hu hne
    (decide_eq_true h1) (decide_eq_true h2)
  have h := (mult_of_same R hs).symm.trans he.2
  unfold mult at h
  omega

/-- **One status on linked triangles.** For a loop of boundary lines, points within or on two
linked triangles, off the loop, are inside it together. -/
theorem linked_status {B : List Point} (hB : SimpleLoop B) (hBs : ∀ s ∈ sides B, Bdry R s.1 s.2)
    {t u : Point × Point × Point} (hl : Linked R t u) (ht : t ∈ R.pieces) {X : Point}
    (hX : OnOrInsideTriangle X t.1 t.2.1 t.2.2) (hXB : ¬ LoopBoundary B X) :
    ∀ X', OnOrInsideTriangle X' u.1 u.2.1 u.2.2 → ¬ LoopBoundary B X' →
      (LoopInside B X ↔ LoopInside B X') := by
  have hBe : ∀ s ∈ sides B, Elem R s.1 s.2 := fun s hs => (hBs s hs).1
  induction hl with
  | refl => exact fun X' hX' hX'B => triangle_status R hB hBe ht hX hX' hXB hX'B
  | @step u v _ ha ih =>
    obtain ⟨hu, hv, P, Q, he, h1, h2⟩ := ha
    intro X' hX' hX'B
    by_cases huv : u = v
    · subst huv
      exact ih X' hX' hX'B
    obtain ⟨ℓ, hPℓ, hQℓ⟩ := Postulate1 P Q he.1
    obtain ⟨M, -, hM, -⟩ := exists_point_between hPℓ hQℓ he.1 []
    have hMcl : ∀ {w : Point × Point × Point}, InSide (P, Q) w →
        OnOrInsideTriangle M w.1 w.2.1 w.2.2 := fun ⟨s, hs, hPs, hQs⟩ =>
      closed_of_onSeg hs (onFinite_within hPs hQs (Or.inr (Or.inr hM)))
    have hMB : ¬ LoopBoundary B M := by
      rintro ⟨s, hs, hMs⟩
      have hmeet := elem_meet R (hBs s hs).1 he (not_same_bdry R hu hv huv h1 h2 (hBs s hs))
        hMs (Or.inr (Or.inr hM))
      rcases hmeet.2 with e | e
      · exact ne_of_between hM e.symm
      · exact ne_of_between (between_symm hM) e.symm
    exact (ih M (hMcl h1) hMB).trans (triangle_status R hB hBe hv (hMcl h2) hX' hMB hX'B)

/-! ## Classes of boundary lines -/

/-- The triangles linked to t. -/
def TCls (t : Point × Point × Point) : (Point × Point × Point) → Prop := fun u => Linked R t u

/-- **The class of an elementary line**: the triangles linked to one along it. -/
def Cls (P Q : Point) : (Point × Point × Point) → Prop :=
  fun u => ∃ t ∈ R.pieces, InSide (P, Q) t ∧ Linked R t u

theorem cls_symm (P Q : Point) : Cls R P Q = Cls R Q P := by
  funext u
  apply propext
  unfold Cls
  constructor
  · rintro ⟨t, ht, hin, hl⟩
    exact ⟨t, ht, (inSide_of_same (Or.inr rfl) t).mp hin, hl⟩
  · rintro ⟨t, ht, hin, hl⟩
    exact ⟨t, ht, (inSide_of_same (Or.inr rfl) t).mp hin, hl⟩

/-- A boundary line has the class of its triangle. -/
theorem cls_bdry {P Q : Point} {t : Point × Point × Point} (ht : t ∈ R.pieces)
    (hin : InSide (P, Q) t) (huniq : ∀ t' ∈ R.pieces, InSide (P, Q) t' → t' = t) :
    Cls R P Q = TCls R t := by
  funext u
  apply propext
  constructor
  · rintro ⟨t', ht', hin', hl⟩
    rw [huniq t' ht' hin'] at hl
    exact hl
  · intro hl
    exact ⟨t, ht, hin, hl⟩

theorem tcls_eq {t u : Point × Point × Point} (h : TCls R t = TCls R u) : Linked R t u := by
  have := congrFun h u
  unfold TCls at this
  rw [this]
  exact Linked.refl u

theorem tcls_of_linked {t u : Point × Point × Point} (h : Linked R t u) :
    TCls R t = TCls R u := by
  funext v
  apply propext
  exact ⟨fun h' => (Linked.symm R h).trans R h', fun h' => h.trans R h'⟩

/-! ## Even degree -/

/-- At a corner, each triangle has two elementary lines along its sides, or none. -/
theorem tri_count_even (V : Point) {t : Point × Point × Point} (ht : t ∈ R.pieces) :
    ((nub (verts R)).countP fun W => decide (Elem R V W ∧ InSide (V, W) t)) % 2 = 0 := by
  by_cases hon : V ∈ verts R ∧ ∃ s ∈ triSides t, OnSeg V s
  · obtain ⟨hV, s, hs, hVs⟩ := hon
    obtain ⟨W₁, W₂, hne, hiff⟩ := two_at R hV ht hs hVs
    rw [countP_two (nodup_nub _) hne]
    intro z
    rw [decide_eq_true_eq, hiff z]
    constructor
    · exact fun h => h.2
    · intro hz
      exact ⟨mem_nub.mpr ((hiff z).mpr hz).1.2.2.1, hz⟩
  · have : ((nub (verts R)).countP fun W => decide (Elem R V W ∧ InSide (V, W) t)) = 0 := by
      rw [List.countP_eq_zero]
      intro W _ hW
      rw [decide_eq_true_eq] at hW
      obtain ⟨s, hs, hVs, -⟩ := hW.2
      exact hon ⟨hW.1.2.1, s, hs, hVs⟩
    rw [this]

/-- The triangles of one class along an elementary line, counted: as many, modulo two, as it
is a boundary line of that class. -/
theorem elem_tri_parity (V W : Point) (k : (Point × Point × Point) → Prop) :
    (R.pieces.countP fun t => decide (TCls R t = k ∧ Elem R V W ∧ InSide (V, W) t)) % 2 =
      (if Bdry R V W ∧ Cls R V W = k then 1 else 0) % 2 := by
  by_cases hne : ¬ Elem R V W
  · have he := hne
    have : (R.pieces.countP fun t => decide (TCls R t = k ∧ Elem R V W ∧ InSide (V, W) t))
        = 0 := by
      rw [List.countP_eq_zero]
      intro t _ ht
      rw [decide_eq_true_eq] at ht
      exact he ht.2.1
    rw [this, ite_one_neg (fun h => he h.1.1)]
  have he : Elem R V W := Classical.not_not.mp hne
  have hpos := mult_pos R he
  have hle := mult_le_two R he.1
  by_cases h1 : mult R (V, W) = 1
  · obtain ⟨t0, ht0, hin0, huniq⟩ := bdry_tri R ⟨he, h1⟩
    have hc := cls_bdry R ht0 hin0 huniq
    by_cases hk : TCls R t0 = k
    · have hcount : (R.pieces.countP fun t => decide (TCls R t = k ∧ Elem R V W ∧
          InSide (V, W) t)) = 1 := by
        have hle1 := countP_le_one (x := t0) (pieces_nodup R)
          (p := fun t => decide (TCls R t = k ∧ Elem R V W ∧ InSide (V, W) t))
          (fun z hz hpz => huniq z hz (of_decide_eq_true hpz).2.2)
        have hpos1 : 0 < (R.pieces.countP fun t => decide (TCls R t = k ∧ Elem R V W ∧
            InSide (V, W) t)) :=
          List.countP_pos_iff.mpr ⟨t0, ht0, decide_eq_true ⟨hk, he, hin0⟩⟩
        omega
      rw [hcount, ite_one_pos (p := Bdry R V W ∧ Cls R V W = k) ⟨⟨he, h1⟩, hc.trans hk⟩]
    · have hcount : (R.pieces.countP fun t => decide (TCls R t = k ∧ Elem R V W ∧
          InSide (V, W) t)) = 0 := by
        rw [List.countP_eq_zero]
        intro t ht htk
        rw [decide_eq_true_eq] at htk
        exact hk (huniq t ht htk.2.2 ▸ htk.1)
      rw [hcount, ite_one_neg (fun h => hk (hc.symm.trans h.2))]
  · have h2 : mult R (V, W) = 2 := by omega
    rw [ite_one_neg (fun h => h1 h.1.2)]
    /- The two triangles along it are linked, so of one class. -/
    have hF : (R.pieces.filter fun t => decide (InSide (V, W) t)).length = 2 := by
      unfold mult at h2
      rw [List.countP_eq_length_filter] at h2
      exact h2
    have hnd : (R.pieces.filter fun t => decide (InSide (V, W) t)).Nodup :=
      List.Pairwise.filter _ (pieces_nodup R)
    have hmem : ∀ t, t ∈ (R.pieces.filter fun t => decide (InSide (V, W) t)) ↔
        t ∈ R.pieces ∧ InSide (V, W) t := fun t => by
      rw [List.mem_filter, decide_eq_true_eq]
    generalize (R.pieces.filter fun t => decide (InSide (V, W) t)) = F at hF hnd hmem
    match F, hF, hnd, hmem with
    | [t₁, t₂], _, hnd, hmem =>
      have hne : t₁ ≠ t₂ := by simpa using hnd
      obtain ⟨ht₁, hi₁⟩ := (hmem t₁).mp (by simp)
      obtain ⟨ht₂, hi₂⟩ := (hmem t₂).mp (by simp)
      have hl : TCls R t₁ = TCls R t₂ :=
        tcls_of_linked R (Linked.step (Linked.refl t₁) ⟨ht₁, ht₂, V, W, he, hi₁, hi₂⟩)
      by_cases hk : TCls R t₁ = k
      · rw [countP_two (pieces_nodup R) hne]
        intro z
        rw [decide_eq_true_eq]
        constructor
        · rintro ⟨hz, -, -, hzi⟩
          have := (hmem z).mpr ⟨hz, hzi⟩
          simpa using this
        · rintro (rfl | rfl)
          · exact ⟨ht₁, hk, he, hi₁⟩
          · exact ⟨ht₂, hl ▸ hk, he, hi₂⟩
      · have : (R.pieces.countP fun t => decide (TCls R t = k ∧ Elem R V W ∧
            InSide (V, W) t)) = 0 := by
          rw [List.countP_eq_zero]
          intro z hz hzk
          rw [decide_eq_true_eq] at hzk
          have := (hmem z).mpr ⟨hz, hzk.2.2⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at this
          rcases this with rfl | rfl
          · exact hk hzk.1
          · exact hk (hl.trans hzk.1)
        rw [this]

/-- **Even degree.** At every point, the boundary lines of each class are even in number. -/
theorem even_degree (V : Point) (k : (Point × Point × Point) → Prop) :
    ((nub (verts R)).countP fun W => decide (Bdry R V W ∧ Cls R V W = k)) % 2 = 0 := by
  have h1 : ((nub (verts R)).countP fun W => decide (Bdry R V W ∧ Cls R V W = k)) % 2 =
      ((nub (verts R)).map fun W => (R.pieces.map fun t =>
        if TCls R t = k ∧ Elem R V W ∧ InSide (V, W) t then 1 else 0).sum).sum % 2 := by
    rw [countP_eq_sum]
    refine sum_mod_two _ _ _ fun W _ => ?_
    rw [← countP_eq_sum R.pieces (fun t => TCls R t = k ∧ Elem R V W ∧ InSide (V, W) t)]
    exact (elem_tri_parity R V W k).symm
  rw [h1, sum_exchange_nat]
  have h3 := sum_mod_two R.pieces (fun t => ((nub (verts R)).map fun W =>
      if TCls R t = k ∧ Elem R V W ∧ InSide (V, W) t then 1 else 0).sum) (fun _ => 0)
    (fun t ht => by
      rw [← countP_eq_sum (nub (verts R)) (fun W => TCls R t = k ∧ Elem R V W ∧
        InSide (V, W) t)]
      by_cases hk : TCls R t = k
      · have := tri_count_even R V ht
        rw [List.countP_congr (q := fun W => decide (Elem R V W ∧ InSide (V, W) t))]
        · exact this
        · intro W _
          simp only [decide_eq_true_eq, hk, true_and]
      · have : ((nub (verts R)).countP fun W => decide (TCls R t = k ∧ Elem R V W ∧
            InSide (V, W) t)) = 0 := by
          rw [List.countP_eq_zero]
          intro W _ hW
          rw [decide_eq_true_eq] at hW
          exact hk hW.1
        rw [this])
  rw [h3, sum_eq_zero_of _ _ fun _ _ => rfl]

/-! ## Counting crossings -/

/-- The elementary lines, each named once. -/
noncomputable def elems : List (Point × Point) :=
  oneWay ((allPairs (nub (verts R))).filter fun e => decide (Elem R e.1 e.2))

theorem elems_elem {e : Point × Point} (he : e ∈ elems R) : Elem R e.1 e.2 := by
  have := oneWay_sub he
  rw [List.mem_filter, decide_eq_true_eq] at this
  exact this.2

theorem elems_cover {P Q : Point} (h : Elem R P Q) : ∃ d ∈ elems R, Same (P, Q) d :=
  oneWay_cover (List.mem_filter.mpr ⟨mem_allPairs.mpr ⟨mem_nub.mpr h.2.1, mem_nub.mpr h.2.2.1⟩,
    decide_eq_true h⟩)

theorem elems_pairwise : (elems R).Pairwise fun d e => ¬ Same d e := oneWay_pairwise _

theorem nodup_of_same {l : List (Point × Point)} (h : l.Pairwise fun d e => ¬ Same d e) :
    l.Nodup := by
  refine List.Pairwise.imp ?_ h
  intro d e hde hdeq
  subst hdeq
  exact hde (same_refl d)

/-- In a list of pairwise different finite straight lines, one the same as a given one is
unique. -/
theorem eq_of_same {l : List (Point × Point)} (h : l.Pairwise fun d e => ¬ Same d e)
    {a b c : Point × Point} (ha : a ∈ l) (hb : b ∈ l) (hac : Same a c) (hbc : Same b c) :
    a = b := by
  rcases LoopFacts.pairwise_mem h ha hb with e | h' | h'
  · exact e
  · exact absurd (same_trans hac (same_symm hbc)) h'
  · exact absurd (same_trans hbc (same_symm hac)) h'

theorem crosses_of_same {X Q : Point} {e e' : Point × Point} (h : Same e e') :
    RayCrosses X Q e ↔ RayCrosses X Q e' := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · constructor
    · rintro ⟨Y, hY, hb⟩
      exact ⟨Y, hY, between_symm hb⟩
    · rintro ⟨Y, hY, hb⟩
      exact ⟨Y, hY, between_symm hb⟩

/-- **A side's crossing is one elementary line's.** Along a ray whose straight line passes
through no corner, a side is crossed exactly when one of the elementary lines along it is, and
then only one. -/
theorem side_count {t : Point × Point × Point} (ht : t ∈ R.pieces) {s : Point × Point}
    (hs : s ∈ triSides t) {X Q : Point} {ℓ : Line} (hXℓ : OnLine X ℓ) (hQℓ : OnLine Q ℓ)
    (hoff : ∀ V ∈ verts R, ¬ OnLine V ℓ) :
    (if RayCrosses X Q s then 1 else 0) =
      (elems R).countP fun e => decide (Within e s ∧ RayCrosses X Q e) := by
  by_cases hc : RayCrosses X Q s
  · obtain ⟨Y, hYr, hYb⟩ := hc
    have hYℓ : OnLine Y ℓ := hYr.onLine hXℓ hQℓ
    have hYv : Y ∉ verts R := fun h => hoff Y h hYℓ
    have hs1 : ¬ OnLine s.1 ℓ := hoff _ (side_ends_mem R ht hs).1
    obtain ⟨P, P', he, hw, hPY⟩ := side_elem R ht hs hYb hYv
    obtain ⟨e0, he0, hs0⟩ := elems_cover R he
    rw [ite_one_pos (p := RayCrosses X Q s) ⟨Y, hYr, hYb⟩]
    have hle := countP_le_one (x := e0) (nodup_of_same (elems_pairwise R))
      (p := fun e => decide (Within e s ∧ RayCrosses X Q e)) (by
        intro z hz hpz
        rw [decide_eq_true_eq] at hpz
        obtain ⟨hzw, Y', hY'r, hY'b⟩ := hpz
        have hY's := between_within hzw.1 hzw.2 hY'b
        have hYY' := OutlineFacts.cross_unique hs1 hYℓ (hY'r.onLine hXℓ hQℓ) hYb hY's
        rw [← hYY'] at hY'b
        exact eq_of_same (elems_pairwise R) hz he0
          (same_trans (elem_overlap R (elems_elem R hz) he hY'b hPY) hs0) (same_refl e0))
    have hpos : 0 < (elems R).countP fun e => decide (Within e s ∧ RayCrosses X Q e) :=
      List.countP_pos_iff.mpr ⟨e0, he0, decide_eq_true ⟨(within_of_same hs0).mp hw,
        (crosses_of_same hs0).mp ⟨Y, hYr, hPY⟩⟩⟩
    omega
  · rw [ite_one_neg hc]
    symm
    rw [List.countP_eq_zero]
    intro e _ hpe
    rw [decide_eq_true_eq] at hpe
    obtain ⟨hw, Y, hYr, hYb⟩ := hpe
    exact hc ⟨Y, hYr, between_within hw.1 hw.2 hYb⟩

/-- A finite straight line with two ends lies along at most one side of a triangle. -/
theorem within_two_sides {t : Point × Point × Point} (h : Triangle t.1 t.2.1 t.2.2)
    {e s₁ s₂ : Point × Point} (he : e.1 ≠ e.2) (h₁ : s₁ ∈ triSides t) (h₂ : s₂ ∈ triSides t)
    (hw₁ : Within e s₁) (hw₂ : Within e s₂) : s₁ = s₂ := by
  obtain ⟨u, v, w, rfl, hr⟩ := rot_side h h₁
  have htri := hr.tri
  obtain ⟨N, huN, hvN⟩ := Postulate1 u v htri.ne₁₂
  have h1N := LoopFacts.onFiniteLine_onLine hw₁.1 huN hvN
  have h2N := LoopFacts.onFiniteLine_onLine hw₁.2 huN hvN
  rcases (hr.sides s₂).mp h₂ with rfl | rfl | rfl
  · rfl
  · obtain ⟨L, hvL, hwL⟩ := Postulate1 v w htri.ne₂₃
    have hNL := line_unique he h1N h2N (LoopFacts.onFiniteLine_onLine hw₂.1 hvL hwL)
      (LoopFacts.onFiniteLine_onLine hw₂.2 hvL hwL)
    exact absurd ⟨N, huN, hvN, hNL ▸ hwL⟩ htri
  · obtain ⟨L, hwL, huL⟩ := Postulate1 w u htri.ne₁₃.symm
    have hNL := line_unique he h1N h2N (LoopFacts.onFiniteLine_onLine hw₂.1 hwL huL)
      (LoopFacts.onFiniteLine_onLine hw₂.2 hwL huL)
    exact absurd ⟨N, huN, hvN, hNL ▸ hwL⟩ htri

theorem side_count_one {t : Point × Point × Point} (ht : t ∈ R.pieces) {e : Point × Point}
    (he : e.1 ≠ e.2) :
    (triSides t).countP (fun s => decide (Within e s)) = if InSide e t then 1 else 0 := by
  have htri := R.triangle t ht
  by_cases hin : InSide e t
  · obtain ⟨s0, hs0, hw0⟩ := hin
    rw [ite_one_pos (p := InSide e t) ⟨s0, hs0, hw0⟩]
    have hnd : (triSides t).Nodup := LoopFacts.sides_nodup (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨htri.ne₁₂, htri.ne₁₃⟩, htri.ne₂₃, fun h => h, List.nodup_nil⟩)
    have hle := countP_le_one (x := s0) hnd (p := fun s => decide (Within e s))
      (fun z hz hpz => within_two_sides htri he hz hs0 (of_decide_eq_true hpz) hw0)
    have hpos : 0 < (triSides t).countP (fun s => decide (Within e s)) :=
      List.countP_pos_iff.mpr ⟨s0, hs0, decide_eq_true hw0⟩
    omega
  · rw [ite_one_neg hin, List.countP_eq_zero]
    intro s hs hw
    exact hin ⟨s, hs, of_decide_eq_true hw⟩

theorem crossingCount_tri (t : Point × Point × Point) (X Q : Point) :
    crossingCount [t.1, t.2.1, t.2.2] X Q =
      (triSides t).countP fun s => decide (RayCrosses X Q s) := by
  unfold crossingCount
  rw [List.countP_eq_length_filter]
  rfl

theorem crossingCount_eq (L : List Point) (X Q : Point) :
    crossingCount L X Q = (sides L).countP fun s => decide (RayCrosses X Q s) := by
  unfold crossingCount
  rw [List.countP_eq_length_filter]

/-- **The triangles' crossings**: every elementary line counted once for each triangle along
it. -/
theorem tri_crossings {X Q : Point} {ℓ : Line} (hXℓ : OnLine X ℓ) (hQℓ : OnLine Q ℓ)
    (hoff : ∀ V ∈ verts R, ¬ OnLine V ℓ) :
    (R.pieces.map fun t => crossingCount [t.1, t.2.1, t.2.2] X Q).sum =
      ((elems R).map fun e => mult R e * (if RayCrosses X Q e then 1 else 0)).sum := by
  have h1 : ∀ t ∈ R.pieces, crossingCount [t.1, t.2.1, t.2.2] X Q =
      ((elems R).map fun e => ((triSides t).map fun s =>
        if Within e s ∧ RayCrosses X Q e then 1 else 0).sum).sum := by
    intro t ht
    rw [crossingCount_tri, countP_eq_sum]
    rw [List.map_congr_left (fun s hs => side_count R ht hs hXℓ hQℓ hoff)]
    have := sum_exchange_nat (triSides t) (elems R)
      (fun s e => if Within e s ∧ RayCrosses X Q e then 1 else 0)
    simp only [countP_eq_sum] at this ⊢
    exact this
  rw [List.map_congr_left h1, sum_exchange_nat]
  refine congrArg List.sum (List.map_congr_left fun e he => ?_)
  have hne := (elems_elem R he).1
  by_cases hc : RayCrosses X Q e
  · simp only [hc, and_true, ite_true, Nat.mul_one]
    unfold mult
    rw [countP_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [← countP_eq_sum, side_count_one R ht hne]
  · simp only [hc, and_false, ite_false, Nat.mul_zero]
    exact sum_eq_zero_of _ _ fun t _ => sum_eq_zero_of _ _ fun s _ => rfl

/-- **The triangles' crossings, modulo two, are the boundary lines'.** -/
theorem tri_parity {X Q : Point} {ℓ : Line} (hXℓ : OnLine X ℓ) (hQℓ : OnLine Q ℓ)
    (hoff : ∀ V ∈ verts R, ¬ OnLine V ℓ) :
    (R.pieces.map fun t => crossingCount [t.1, t.2.1, t.2.2] X Q).sum % 2 =
      ((elems R).map fun e => (if Bdry R e.1 e.2 then 1 else 0) *
        (if RayCrosses X Q e then 1 else 0)).sum % 2 := by
  rw [tri_crossings R hXℓ hQℓ hoff]
  refine sum_mod_two _ _ _ fun e he => ?_
  have hel := elems_elem R he
  have hpos : 0 < mult R e := mult_pos R hel
  have hle : mult R e ≤ 2 := mult_le_two R hel.1
  generalize (if RayCrosses X Q e then 1 else 0) = c
  by_cases h1 : mult R e = 1
  · rw [h1, ite_one_pos (p := Bdry R e.1 e.2) ⟨hel, h1⟩]
  · have h2 : mult R e = 2 := by omega
    have hb : ¬ Bdry R e.1 e.2 := fun h => h1 h.2
    rw [h2, ite_one_neg hb]
    omega

/-- **The contours' crossings are the boundary lines'**, when the contours' sides are the
boundary lines, each once. -/
theorem loop_crossings {loops : List (List Point)}
    (hside : ∀ L ∈ loops, ∀ s ∈ sides L, Bdry R s.1 s.2)
    (hpw : (loops.flatMap sides).Pairwise fun s t => ¬ Same s t)
    (hcov : ∀ P Q, Bdry R P Q → ∃ L ∈ loops, ∃ s ∈ sides L, Same s (P, Q)) (X Q : Point) :
    (loops.map fun L => crossingCount L X Q).sum =
      ((elems R).map fun e => (if Bdry R e.1 e.2 then 1 else 0) *
        (if RayCrosses X Q e then 1 else 0)).sum := by
  have hflat : ∀ s ∈ loops.flatMap sides, Bdry R s.1 s.2 := by
    intro s hs
    obtain ⟨L, hL, hs⟩ := List.mem_flatMap.mp hs
    exact hside L hL s hs
  have h1 : (loops.map fun L => crossingCount L X Q).sum =
      ((loops.flatMap sides).map fun s => if RayCrosses X Q s then 1 else 0).sum := by
    rw [← countP_eq_sum, List.countP_flatMap]
    exact congrArg List.sum (List.map_congr_left fun L _ => crossingCount_eq L X Q)
  rw [h1, sum_regroup Same (fun s => if RayCrosses X Q s then 1 else 0) (elems R)
    (pairwise_same (elems_pairwise R)) (loops.flatMap sides)
    (fun s hs => elems_cover R (hflat s hs).1)
    (fun x e h => by simp only [crosses_of_same h])]
  refine congrArg List.sum (List.map_congr_left fun e he => ?_)
  congr 1
  by_cases hb : Bdry R e.1 e.2
  · rw [ite_one_pos hb]
    obtain ⟨L, hL, s, hs, hse⟩ := hcov e.1 e.2 hb
    have hsf : s ∈ loops.flatMap sides := List.mem_flatMap.mpr ⟨L, hL, hs⟩
    have hle := countP_le_one (x := s) (nodup_of_same hpw)
      (p := fun x => decide (Same x e)) (fun z hz hpz =>
        eq_of_same hpw hz hsf (of_decide_eq_true hpz) hse)
    have hpos : 0 < (loops.flatMap sides).countP (fun x => decide (Same x e)) :=
      List.countP_pos_iff.mpr ⟨s, hsf, decide_eq_true hse⟩
    omega
  · rw [ite_one_neg hb, List.countP_eq_zero]
    intro x hx hxe
    exact hb (bdry_of_same R (of_decide_eq_true hxe) (hflat x hx))

/-! ## Depth off the sides -/

/-- A point off every side is no corner. -/
theorem off_sides_not_vert {X : Point} (hX : ∀ t ∈ R.pieces, ∀ s ∈ triSides t, ¬ OnSeg X s) :
    X ∉ verts R := by
  intro hv
  unfold verts at hv
  obtain ⟨t, ht, hXt⟩ := List.mem_flatMap.mp hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hXt
  rcases hXt with rfl | rfl | rfl
  · exact hX t ht _ (mem_triSides.mpr (Or.inl rfl)) (Or.inl rfl)
  · exact hX t ht _ (mem_triSides.mpr (Or.inl rfl)) (Or.inr (Or.inl rfl))
  · exact hX t ht _ (mem_triSides.mpr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl))

/-- A point within or on a triangle, off its sides, is inside it. -/
theorem inside_of_closed {t : Point × Point × Point} {X : Point}
    (hXt : OnOrInsideTriangle X t.1 t.2.1 t.2.2) (hX : ∀ s ∈ triSides t, ¬ OnSeg X s) :
    InsideTriangle X t.1 t.2.1 t.2.2 := by
  have h1 := hX _ (mem_triSides.mpr (Or.inl rfl))
  have h2 := hX _ (mem_triSides.mpr (Or.inr (Or.inl rfl)))
  have h3 := hX _ (mem_triSides.mpr (Or.inr (Or.inr rfl)))
  rcases hXt with h | h | h | h | h | h | h
  · exact h
  · exact absurd (Or.inr (Or.inr h)) h1
  · exact absurd (Or.inr (Or.inr h)) h2
  · exact absurd (Or.inr (Or.inr h)) h3
  · exact absurd (Or.inl h) h1
  · exact absurd (Or.inl h) h2
  · exact absurd (Or.inl h) h3

/-- Off every side, a point is covered exactly when it is inside a triangle. -/
theorem covers_iff_inside {X : Point} (hX : ∀ t ∈ R.pieces, ∀ s ∈ triSides t, ¬ OnSeg X s) :
    Covers R.pieces X ↔ ∃ t ∈ R.pieces, InsideTriangle X t.1 t.2.1 t.2.2 := by
  constructor
  · rintro ⟨t, ht, hXt⟩
    exact ⟨t, ht, inside_of_closed hXt (hX t ht)⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, Or.inl h⟩

/-- Off every side, along a ray through no corner, a triangle's inside is decided by the
parity of its crossings. -/
theorem inside_iff_count {t : Point × Point × Point} (ht : t ∈ R.pieces) {X Q : Point}
    {ℓ : Line} (hX : ∀ t ∈ R.pieces, ∀ s ∈ triSides t, ¬ OnSeg X s) (hXQ : X ≠ Q)
    (hXℓ : OnLine X ℓ) (hQℓ : OnLine Q ℓ) (hoff : ∀ V ∈ verts R, ¬ OnLine V ℓ) :
    InsideTriangle X t.1 t.2.1 t.2.2 ↔ crossingCount [t.1, t.2.1, t.2.2] X Q % 2 = 1 := by
  obtain ⟨hsimple, hreg⟩ := triangle_region (R.triangle t ht)
  have hXb : ¬ LoopBoundary [t.1, t.2.1, t.2.2] X := fun ⟨s, hs, hXs⟩ => hX t ht s hs hXs
  have hg : GoodRay [t.1, t.2.1, t.2.2] X Q :=
    OutlineFacts.good_of_line hXQ hXℓ hQℓ fun V hV => hoff V (corner_mem R ht (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hV
      exact hV))
  rw [← loop_inside_iff hsimple hXb hg]
  constructor
  · intro h
    rcases (hreg X).mpr (Or.inl h) with hb | hi
    · exact absurd hb hXb
    · exact hi
  · intro h
    exact inside_of_closed ((hreg X).mp (Or.inr h)) (hX t ht)

/-- **The depth off the sides.** For contours whose sides are the boundary lines, each once, a
point off every side is inside an odd number of contours exactly when it is covered. -/
theorem parity_at {loops : List (List Point)} (hsimple : ∀ L ∈ loops, SimpleLoop L)
    (hside : ∀ L ∈ loops, ∀ s ∈ sides L, Bdry R s.1 s.2)
    (hpw : (loops.flatMap sides).Pairwise fun s t => ¬ Same s t)
    (hcov : ∀ P Q, Bdry R P Q → ∃ L ∈ loops, ∃ s ∈ sides L, Same s (P, Q))
    {X : Point} (hX : ∀ t ∈ R.pieces, ∀ s ∈ triSides t, ¬ OnSeg X s) :
    (loops.countP fun L => decide (LoopInside L X)) % 2 = 1 ↔ Covers R.pieces X := by
  obtain ⟨t0, ht0⟩ := List.exists_mem_of_ne_nil R.pieces R.ne
  obtain ⟨Q, ℓ, hXQ, hXℓ, hQℓ, hoff⟩ :=
    line_avoiding (off_sides_not_vert R hX) (R.triangle t0 ht0)
  /- Each contour, along the ray. -/
  have hL : ∀ L ∈ loops, LoopInside L X ↔ crossingCount L X Q % 2 = 1 := by
    intro L hLm
    have hXL : ¬ LoopBoundary L X := by
      rintro ⟨s, hs, hXs⟩
      obtain ⟨-, -, -, ⟨t, ht, s', hs', h1, h2⟩, -⟩ := (hside L hLm s hs).1
      exact hX t ht s' hs' (onFinite_within h1 h2 hXs)
    have hg : GoodRay L X Q := OutlineFacts.good_of_line hXQ hXℓ hQℓ fun V hV => by
      obtain ⟨E, hE⟩ := outgoing_side hV
      exact hoff V (hside L hLm _ hE).1.2.1
    exact loop_inside_iff (hsimple L hLm) hXL hg
  have e1 := Parity.countP_odd_sum loops (fun L => LoopInside L X) (fun L => crossingCount L X Q) hL
  rw [loop_crossings R hside hpw hcov X Q] at e1
  rw [← tri_parity R hXℓ hQℓ hoff] at e1
  have e2 := Parity.countP_odd_sum R.pieces (fun t => InsideTriangle X t.1 t.2.1 t.2.2)
    (fun t => crossingCount [t.1, t.2.1, t.2.2] X Q)
    (fun t ht => inside_iff_count R ht hX hXQ hXℓ hQℓ hoff)
  rw [e1, ← e2, covers_iff_inside R hX]
  /- At most one triangle has X inside. -/
  by_cases hex : ∃ t ∈ R.pieces, InsideTriangle X t.1 t.2.1 t.2.2
  · obtain ⟨t, ht, hXt⟩ := hex
    have hle := countP_le_one (x := t) (pieces_nodup R)
      (p := fun u => decide (InsideTriangle X u.1 u.2.1 u.2.2)) (fun u hu hpu =>
        Classical.byContradiction fun hne =>
          apart_ne R ht hu (Ne.symm hne) hXt (of_decide_eq_true hpu))
    have hpos : 0 < R.pieces.countP (fun u => decide (InsideTriangle X u.1 u.2.1 u.2.2)) :=
      List.countP_pos_iff.mpr ⟨t, ht, decide_eq_true hXt⟩
    exact ⟨fun _ => ⟨t, ht, hXt⟩, fun _ => by omega⟩
  · have h0 : R.pieces.countP (fun u => decide (InsideTriangle X u.1 u.2.1 u.2.2)) = 0 := by
      rw [List.countP_eq_zero]
      intro u hu hpu
      exact hex ⟨u, hu, of_decide_eq_true hpu⟩
    rw [h0]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h hex⟩

/-! ## The outline -/

/-- A point of a side of a contour of boundary lines is covered. -/
theorem covers_of_loop {L : List Point} (hside : ∀ s ∈ sides L, Bdry R s.1 s.2) {X : Point}
    (hX : LoopBoundary L X) : Covers R.pieces X := by
  obtain ⟨s, hs, hXs⟩ := hX
  obtain ⟨-, -, -, ⟨t, ht, s', hs', h1, h2⟩, -⟩ := (hside s hs).1
  exact ⟨t, ht, closed_of_onSeg hs' (onFinite_within h1 h2 hXs)⟩

/-- **A contour lies wholly inside or wholly outside another, off it**: all of a contour's sides
are of one class, and the other contour has one status on the closed triangles of a class. -/
theorem loop_status {A B : List Point} (hA3 : 3 ≤ A.length)
    (hAs : ∃ k, ∀ s ∈ sides A, Bdry R s.1 s.2 ∧ Cls R s.1 s.2 = k)
    (hB : SimpleLoop B) (hBs : ∀ s ∈ sides B, Bdry R s.1 s.2) :
    ∃ sA : Prop, ∀ P, LoopBoundary A P → ¬ LoopBoundary B P → (LoopInside B P ↔ sA) := by
  obtain ⟨k, hk⟩ := hAs
  have hne : A ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨E, hE⟩ := outgoing_side (List.head_mem hne)
  obtain ⟨t0, ht0, hin0, hu0⟩ := bdry_tri R (hk _ hE).1
  have hc0 := cls_bdry R ht0 hin0 hu0
  obtain ⟨W0, hW0⟩ := inside_exists (R.triangle t0 ht0)
  have hW0B := inside_off_loop R (fun s hs => (hBs s hs).1) ht0 hW0
  refine ⟨LoopInside B W0, fun P ⟨a, ha, hPa⟩ hPB => ?_⟩
  obtain ⟨ta, hta, hina, hua⟩ := bdry_tri R (hk a ha).1
  have hca := cls_bdry R hta hina hua
  have hl : Linked R ta t0 := tcls_eq R (hca.symm.trans ((hk a ha).2.trans
    ((hk _ hE).2.symm.trans hc0)))
  obtain ⟨s', hs', h1, h2⟩ := hina
  exact linked_status R hB hBs hl hta (closed_of_onSeg hs' (onFinite_within h1 h2 hPa)) hPB
    W0 (Or.inl hW0) hW0B

/-- **Every figure given as triangles that lie apart has an outline with exactly its closed
coverage.** -/
theorem apart_outline : ∃ F : Outline, ∀ X : Point, Covers R.pieces X ↔ F.Region X := by
  obtain ⟨loops, hl1, hl2, hl3⟩ := cycles (nub (verts R)) (nodup_nub _) (Cls R) (cls_symm R) _
    (Bdry R) (Nat.le_refl _) (fun P Q h => bdry_symm R h) (fun P h => h.1.1 rfl)
    (fun P Q h => ⟨mem_nub.mpr h.1.2.1, mem_nub.mpr h.1.2.2.1⟩) (even_degree R)
  have hside : ∀ L ∈ loops, ∀ s ∈ sides L, Bdry R s.1 s.2 := fun L hL s hs => by
    obtain ⟨-, -, k, hk⟩ := hl1 L hL
    exact (hk s hs).1
  have hpw := List.pairwise_flatMap.mp hl2
  /- Each contour is simple. -/
  have hsimple : ∀ L ∈ loops, SimpleLoop L := by
    intro L hL
    obtain ⟨h3, hnd, -⟩ := hl1 L hL
    refine ⟨h3, hnd, fun s hs => (hside L hL s hs).1.1, ?_⟩
    refine (hpw.1 L hL).imp_of_mem fun hs ht hst X hX hX' => ?_
    exact elem_meet R (hside L hL _ hs).1 (hside L hL _ ht).1 hst hX hX'
  /- There is a contour: some boundary line exists, or no point would be covered. -/
  have hne : loops ≠ [] := by
    intro h
    subst h
    obtain ⟨t0, ht0⟩ := List.exists_mem_of_ne_nil R.pieces R.ne
    obtain ⟨X0, hX0⟩ := inside_exists (R.triangle t0 ht0)
    have hcov : ∀ P Q, Bdry R P Q → ∃ L ∈ ([] : List (List Point)), ∃ s ∈ sides L,
        Same s (P, Q) := hl3
    have := (parity_at R (by simp) (by simp) (by simp) hcov
      (fun t ht s hs hs' => int_not_on_side R ht0 ht hX0 hs hs')).mpr ⟨t0, ht0, Or.inl hX0⟩
    simp at this
  /- Any two contours are compatible. -/
  have hcompat : loops.Pairwise CompatibleLoops := by
    refine hpw.2.imp_of_mem fun {A B} hA hB hAB => ?_
    have hmeet : ∀ X, LoopBoundary A X → LoopBoundary B X → X ∈ A ∨ X ∈ B := by
      rintro X ⟨a, ha, hXa⟩ ⟨b, hb, hXb⟩
      rcases (elem_meet R (hside A hA a ha).1 (hside B hB b hb).1 (hAB a ha b hb) hXa
        hXb).1 with e | e
      · exact Or.inl (e ▸ (LoopFacts.side_mem ha).1)
      · exact Or.inl (e ▸ (LoopFacts.side_mem ha).2)
    obtain ⟨sA, hsA⟩ := loop_status R (hl1 _ hA).1 (hl1 _ hA).2.2 (hsimple _ hB) (hside _ hB)
    obtain ⟨sB, hsB⟩ := loop_status R (hl1 _ hB).1 (hl1 _ hB).2.2 (hsimple _ hA) (hside _ hA)
    exact compatible_of_status (hsimple _ hA) (hsimple _ hB) hmeet sA hsA sB hsB
  let F : Outline := ⟨loops, hne, hsimple, hcompat⟩
  have hdepth : ∀ X, F.depth X = loops.countP fun L => decide (LoopInside L X) := by
    intro X
    unfold Outline.depth
    rw [List.countP_eq_length_filter]
  refine ⟨F, fun X => ⟨fun hX => ?_, fun hX => ?_⟩⟩
  · /- A covered point is on a contour, or at odd depth like a nearby inner point. -/
    by_cases hb : F.Boundary X
    · exact Or.inl hb
    refine Or.inr ⟨hb, ?_⟩
    obtain ⟨t, ht, hXt⟩ := hX
    obtain ⟨W, hW⟩ := inside_exists (R.triangle t ht)
    have hsame : ∀ L ∈ F.loops, LoopInside L X ↔ LoopInside L W := fun L hL =>
      triangle_status R (hsimple L hL) (fun s hs => (hside L hL s hs).1) ht hXt (Or.inl hW)
        (fun h => hb ⟨L, hL, h⟩) (inside_off_loop R (fun s hs => (hside L hL s hs).1) ht hW)
    rw [CoverFacts.depth_congr F hsame, hdepth]
    exact (parity_at R hsimple hside hl2 hl3
      (fun t' ht' s hs hs' => int_not_on_side R ht ht' hW hs hs')).mpr ⟨t, ht, Or.inl hW⟩
  · rcases hX with ⟨L, hL, hXL⟩ | ⟨hb, hodd⟩
    · exact covers_of_loop R (hside L hL) hXL
    · by_cases hsd : ∃ t ∈ R.pieces, ∃ s ∈ triSides t, OnSeg X s
      · obtain ⟨t, ht, s, hs, hXs⟩ := hsd
        exact ⟨t, ht, closed_of_onSeg hs hXs⟩
      · rw [hdepth] at hodd
        exact (parity_at R hsimple hside hl2 hl3
          (fun t ht s hs hXs => hsd ⟨t, ht, s, hs, hXs⟩)).mp hodd

end Assembly

end Extract

end Elements.Figures
