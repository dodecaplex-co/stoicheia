import Elements.Figure.Cells
import Elements.Figure.Outlines.LoopFacts
import Elements.Figure.Convex.Area
import Elements.Figure.Lists

/-!
# Book Zero: helpers for the enclosure and the arrangement

Helper lemmas, in the namespace `Arrangement`, for `Arrangements.lean` (brief 0013, section
8, "The arrangement and general division"; D2, D8 and the enclosure of D9); the diagonal
route of `Arrangements/Diagonal.lean` uses the enclosure too (`enclose_list`). Nothing in
Book Zero cites a proposition of the *Elements*, and nothing here uses Postulate 5 or
superposition.

* **A point added to a convex outline.** A point outside a convex outline, and off every
  side's straight line, is strictly beyond some sides and strictly within others: were it
  beyond every side, cutting off ears would leave a triangle with a point beyond all three of
  its sides, which no point is (`not_all_outer`). Where a side it is beyond meets a side it is
  within, the straight line from the corner to the point leaves the whole region on one side
  (`tangent_same_side`). So the point, with the run of corners from one such corner to the
  next whose sides it is within, makes a convex outline holding the old region
  (`insert_point`). This is not a hull: the point added need not be one of the given points,
  only beyond it.
* **A ray that crosses nothing.** From a point outside a convex region holding every corner
  of a loop, a ray leaving the region's side line behind crosses no side of the loop
  (`outside_ray`).
* **Cells cut by a straight line**, keeping both pieces (`cut_cells`).

With thanks to David Hilbert, whose theory of content guides this route.
-/

namespace Elements.Figures

open Tacit

namespace Arrangement

/-! ## Sides -/

/-- Two points on one side of the straight line AB are not on opposite sides of it. -/
theorem not_same_opposite {P Q A B : Point} (hs : SameSideOf P Q A B)
    (ho : OppositeSidesOf P Q A B) : False := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B hs.1
  exact (ho.oppositeSides hA hB).2.2 (hs.sameSide hA hB)

/-! ## Runs of segments -/

/-- **The first failing segment** of a chain: the chain runs through segments that pass a
test, up to a corner Y whose next segment fails it. -/
theorem first_seg (q : Point × Point → Prop) : ∀ l : List Point,
    (∃ s ∈ segments l, ¬ q s) →
    ∃ (M : List Point) (Y Y₂ : Point) (B : List Point), l = M ++ Y :: Y₂ :: B ∧
      (∀ s ∈ segments (M ++ [Y]), q s) ∧ ¬ q (Y, Y₂)
  | [], ⟨s, hs, _⟩ => by simp [segments] at hs
  | [a], ⟨s, hs, _⟩ => by simp [segments] at hs
  | a :: b :: l, ⟨s, hs, hq⟩ => by
    by_cases hab : q (a, b)
    · have hs' : s ∈ segments (b :: l) := by
        rcases List.mem_cons.mp hs with rfl | hs
        · exact absurd hab hq
        · exact hs
      obtain ⟨M, Y, Y₂, B, he, hall, hY⟩ := first_seg q (b :: l) ⟨s, hs', hq⟩
      refine ⟨a :: M, Y, Y₂, B, by rw [he]; rfl, ?_, hY⟩
      intro t ht
      cases M with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at he
        rw [he.1] at hab
        simp only [List.nil_append, List.cons_append, segments, List.mem_cons,
          List.not_mem_nil, or_false] at ht
        rw [ht]
        exact hab
      | cons m M =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        change t ∈ (a, b) :: segments (b :: M ++ [Y]) at ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hab
        · exact hall t ht
    · exact ⟨[], a, b, l, rfl, by simp [segments], hab⟩

/-- A chain ending in two points has the segment joining them. -/
theorem last_seg {M : List Point} (hM : M ≠ []) (X : Point) :
    ∃ W : Point, (W, X) ∈ segments (M ++ [X]) := by
  obtain ⟨M', W, rfl⟩ := split_last M hM
  exact ⟨W, by simpa using Extreme.closing_segment X W M'⟩

/-- **A junction**: when some sides of an outline of distinct corners pass a test and some
fail it, some side failing it is followed by a side passing it. -/
theorem junction {cs : List Point} (hnd : cs.Nodup) (p : Point × Point → Prop)
    (hyes : ∃ s ∈ sides cs, p s) (hno : ∃ s ∈ sides cs, ¬ p s) :
    ∃ W X X₂ : Point, (W, X) ∈ sides cs ∧ ¬ p (W, X) ∧ (X, X₂) ∈ sides cs ∧ p (X, X₂) := by
  obtain ⟨⟨Z₀, Z₁⟩, hz, hpz⟩ := hno
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem (LoopFacts.side_mem hz).1
  have hrot (s : Point × Point) : s ∈ segments (Z₀ :: (post ++ pre) ++ [Z₀]) ↔ s ∈ sides cs := by
    rw [hcs]
    exact Pieces.mem_sides_rotate_prefix pre (Z₀ :: post) s
  obtain ⟨s, hs, hps⟩ := hyes
  obtain ⟨M, X, X₂, B, he, hall, hX⟩ := first_seg (fun s => ¬ p s)
    (Z₀ :: (post ++ pre) ++ [Z₀]) ⟨s, (hrot s).mpr hs, fun hn => hn hps⟩
  have hX₂ : (X, X₂) ∈ sides cs := (hrot _).mp (by rw [he]; exact Pieces.pair_mem_segments M B X X₂)
  have hpX : p (X, X₂) := Classical.byContradiction hX
  cases M with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
    have heq := LoopFacts.sides_fst_inj hnd hz hX₂ he.1
    exact absurd (heq ▸ hpX) hpz
  | cons m M =>
    obtain ⟨W, hW⟩ := last_seg (List.cons_ne_nil m M) X
    have hWs : (W, X) ∈ sides cs := (hrot _).mp (by
      rw [he]
      have := segment_mem_append hW (X₂ :: B)
      simpa using this)
    exact ⟨W, X, X₂, hWs, hall _ hW, hX₂, hpX⟩

/-! ## A point beyond the sides of a convex outline -/

/-- **Beyond two sides at a corner.** A point across ac from b and across cb from a is on c's
side of ab. Produced through c, the straight line from the point enters the angle acb, and so
meets ab between a and b (the crossbar); c lies between the point and that meeting point. -/
theorem outer_two {P a c b : Point} (hacb : Triangle a c b)
    (h₁ : OppositeSidesOf P b a c) (h₂ : OppositeSidesOf P a c b) :
    SameSideOf P c a b := by
  obtain ⟨M, haM, hcM⟩ := Postulate1 a c hacb.ne₁₂
  obtain ⟨N, hcN, hbN⟩ := Postulate1 c b hacb.ne₂₃
  obtain ⟨K, haK, hbK⟩ := Postulate1 a b hacb.ne₁₃
  have hPM := h₁.oppositeSides haM hcM
  have hPN := h₂.oppositeSides hcN hbN
  have hPc : P ≠ c := fun e => hPM.1 (e ▸ hcM)
  obtain ⟨W, hPcW⟩ := produce hPc
  have hWM : ¬ OnLine W M := fun hW =>
    hPM.1 (on_line_of_between (between_symm hPcW) hW hcM)
  have hWN : ¬ OnLine W N := fun hW =>
    hPN.1 (on_line_of_between (between_symm hPcW) hW hcN)
  have hWb : SameSide W b M :=
    same_side_of_opposite_sides ⟨hPM.1, hWM, pasch3 hPcW hcM⟩ hPM
  have hWa : SameSide W a N :=
    same_side_of_opposite_sides ⟨hPN.1, hWN, pasch3 hPcW hcN⟩ hPN
  obtain ⟨E, haEb, hE⟩ := crossbar (A := c) (B := a) (C := b)
    (SameSideOf.of_line hacb.ne₁₂.symm hcM haM hWb)
    (SameSideOf.of_line hacb.ne₂₃ hcN hbN hWa)
  have hPcE : Between P c E := hE.between hPcW
  have hEK : OnLine E K := on_line_of_between_ends haEb haK hbK
  have hcK : ¬ OnLine c K := hacb.acb.off_line haK hbK
  exact SameSideOf.of_line hacb.ne₁₃ haK hbK
    (same_side_symm (pasch2 (between_symm hPcE) hEK hcK))

/-- **No point is beyond every side of a convex outline.** Beyond the two sides at the second
corner, a point is beyond the diagonal that cuts off that corner's ear (`outer_two`); so it is
beyond every side of the smaller outline, down to a triangle, beyond all three of whose sides
no point lies. -/
theorem not_all_outer {P : Point} : ∀ (ds : List Point) {a b c : Point},
    ConvexOutline (a :: b :: c :: ds) →
    (∀ s ∈ sides (a :: b :: c :: ds), ∀ R ∈ a :: b :: c :: ds, R ≠ s.1 → R ≠ s.2 →
      OppositeSidesOf P R s.1 s.2) → False := by
  intro ds
  induction ds with
  | nil =>
    intro a b c h hall
    have hn := h.2.1
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil] at hn
    have hab : OppositeSidesOf P c a b := hall (a, b) (by simp [sides, segments]) c
      (by simp) (Ne.symm hn.1.2.1) (Ne.symm hn.2.1.1)
    have hbc : OppositeSidesOf P a b c := hall (b, c) (by simp [sides, segments]) a
      (by simp) hn.1.1 hn.1.2.1
    have hca : OppositeSidesOf P b c a := hall (c, a) (by simp [sides, segments]) b
      (by simp) hn.2.1.1 (Ne.symm hn.1.1)
    have htri : Triangle a b c := (h.2.2 (a, b) (by simp [sides, segments]) c (by simp) c
      (by simp) (Ne.symm hn.1.2.1) (Ne.symm hn.2.1.1) (Ne.symm hn.1.2.1)
      (Ne.symm hn.2.1.1)).triangle
    exact not_same_opposite (outer_two htri hab hbc) hca.swap
  | cons d ds ih =>
    intro a b c h hall
    have hn := h.2.1
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    have hab : OppositeSidesOf P c a b := hall (a, b) (by simp [sides, segments]) c
      (by simp) (Ne.symm hn.1.2.1) (Ne.symm hn.2.1.1)
    have hbc : OppositeSidesOf P a b c := hall (b, c) (by simp [sides, segments]) a
      (by simp) hn.1.1 hn.1.2.1
    have htri : Triangle a b c := (h.2.2 (a, b) (by simp [sides, segments]) c (by simp) c
      (by simp) (Ne.symm hn.1.2.1) (Ne.symm hn.2.1.1) (Ne.symm hn.1.2.1)
      (Ne.symm hn.2.1.1)).triangle
    have hPb := outer_two htri hab hbc
    have hcut := cut_convex h (List.cons_ne_nil d ds)
    apply ih hcut
    intro s hs R hR hR₁ hR₂
    change s ∈ (a, c) :: segments (c :: d :: ds ++ [a]) at hs
    have hRm : R ∈ a :: b :: c :: d :: ds := by
      simp only [List.mem_cons] at hR ⊢
      rcases hR with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    rcases List.mem_cons.mp hs with rfl | hs
    · have hRds : R ∈ d :: ds := by
        simp only [List.mem_cons] at hR ⊢
        rcases hR with h | h | h
        · exact absurd h hR₁
        · exact absurd h hR₂
        · exact h
      exact hPb.trans_opposite (ear_opposite h hRds)
    · exact hall s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs)) R hRm hR₁ hR₂

/-- **A tangent from a point outside.** At a corner X of a convex outline, a point P
beyond the straight line of one side through X and within that of another sees the whole
region, but X, strictly on one side of the straight line XP. A point of the region on
XP would lie towards P from X, beyond the first side, or away from it, beyond the
second; and a straight line between points on both sides of XP would cross it at such a
point, or at X, which is between no two points of the region. -/
theorem tangent_same_side {cs : List Point} (h : ConvexOutline cs) {X P : Point} (hX : X ∈ cs)
    {s t : Point × Point} (hs : s ∈ sides cs) (ht : t ∈ sides cs)
    (hXs : X = s.1 ∨ X = s.2) (hXt : X = t.1 ∨ X = t.2)
    {Rs Rt : Point} (hRs : Rs ∈ cs) (hRs₁ : Rs ≠ s.1) (hRs₂ : Rs ≠ s.2)
    (hRt : Rt ∈ cs) (hRt₁ : Rt ≠ t.1) (hRt₂ : Rt ≠ t.2)
    (hout : OppositeSidesOf P Rs s.1 s.2) (hin : SameSideOf P Rt t.1 t.2)
    {Z₁ Z₂ : Point} (h₁ : ConvexRegion cs Z₁) (h₂ : ConvexRegion cs Z₂)
    (hZ₁ : Z₁ ≠ X) (hZ₂ : Z₂ ≠ X) : SameSideOf Z₁ Z₂ X P := by
  obtain ⟨M, hM₁, hM₂⟩ := Postulate1 s.1 s.2 (convex_side_ne h hs)
  obtain ⟨N, hN₁, hN₂⟩ := Postulate1 t.1 t.2 (convex_side_ne h ht)
  have hXM : OnLine X M := by rcases hXs with e | e <;> rw [e] <;> assumption
  have hXN : OnLine X N := by rcases hXt with e | e <;> rw [e] <;> assumption
  have hPM := hout.oppositeSides hM₁ hM₂
  have hPN := hin.sameSide hN₁ hN₂
  have hPN' : ¬ OnLine P N := not_on_line_of_same_side hPN
  have hXP : X ≠ P := fun e => hPM.1 (e ▸ hXM)
  obtain ⟨K, hXK, hPK⟩ := Postulate1 X P hXP
  have halfM {Z : Point} (hZ : ConvexRegion cs Z) : Half Z Rs M :=
    Pieces.region_half h hs hM₁ hM₂ hRs hRs₁ hRs₂ hZ
  have halfN {Z : Point} (hZ : ConvexRegion cs Z) : Half Z Rt N :=
    Pieces.region_half h ht hN₁ hN₂ hRt hRt₁ hRt₂ hZ
  /- No point of the region but X is on XP. -/
  have off {Y : Point} (hY : ConvexRegion cs Y) (hYX : Y ≠ X) (hYK : OnLine Y K) : False := by
    have hYM : ¬ OnLine Y M := fun hy =>
      hPM.1 ((line_unique hYX hYK hXK hy hXM) ▸ hPK)
    have hYN : ¬ OnLine Y N := fun hy =>
      hPN' ((line_unique hYX hYK hXK hy hXN) ▸ hPK)
    have hYP : Y ≠ P := by
      rintro rfl
      rcases halfM hY with hy | hy
      · exact hPM.1 hy
      · exact hPM.2.2 hy
    have beyondM (hs' : SameSide Y P M) : False := by
      rcases halfM hY with hy | hy
      · exact hYM hy
      · exact hPM.2.2 (same_side_trans hs' hy)
    rcases between_cases hYX hXP hYP hYK hXK hPK with hb | hb | hb
    · rcases halfN hY with hy | hy
      · exact hYN hy
      · exact pasch3 hb hXN (same_side_trans (same_side_symm hy) (same_side_symm hPN))
    · exact beyondM (pasch2 hb hXM hYM)
    · exact beyondM (same_side_symm (pasch2 (between_symm hb) hXM hPM.1))
  refine SameSideOf.of_line hXP hXK hPK ?_
  have hZ₁K : ¬ OnLine Z₁ K := off h₁ hZ₁
  have hZ₂K : ¬ OnLine Z₂ K := off h₂ hZ₂
  refine Classical.byContradiction fun hns => ?_
  obtain ⟨Y, hYK, hb⟩ := OppositeSides.exists_between ⟨hZ₁K, hZ₂K, hns⟩
  have hY := convex_region_between h h₁ h₂ hb
  by_cases hYX : Y = X
  · exact Extreme.corner_not_between h hX h₁ h₂ (hYX ▸ hb)
  · exact off hY hYX hYK

/-- **A point between two others, off finitely many straight lines**, when none of them
holds both. Shorten the segment before each straight line that it meets. -/
theorem between_avoiding : ∀ (ls : List Line) {A B : Point}, A ≠ B →
    (∀ L ∈ ls, ¬ (OnLine A L ∧ OnLine B L)) → ∃ C : Point, Between A C B ∧ Avoid ls C
  | [], A, B, hAB, _ => by
    obtain ⟨L, hA, hB⟩ := Postulate1 A B hAB
    obtain ⟨C, -, hACB, -⟩ := exists_point_between hA hB hAB []
    exact ⟨C, hACB, fun L hL => absurd hL List.not_mem_nil⟩
  | L :: ls, A, B, hAB, hno => by
    obtain ⟨C₁, hb₁, ha₁⟩ := between_avoiding ls hAB
      (fun L' hL' => hno L' (List.mem_cons_of_mem L hL'))
    by_cases hC₁ : OnLine C₁ L
    · obtain ⟨C, hb, ha⟩ := between_avoiding ls (ne_of_between hb₁)
        (fun L' hL' hh => hno L' (List.mem_cons_of_mem L hL')
          ⟨hh.1, on_line_of_between hb₁ hh.1 hh.2⟩)
      refine ⟨C, between_of_between_left hb₁ hb, fun L' hL' hCL' => ?_⟩
      rcases List.mem_cons.mp hL' with rfl | hL'
      · have hA := on_line_of_between (between_symm hb) hC₁ hCL'
        exact hno L' List.mem_cons_self ⟨hA, on_line_of_between hb₁ hA hC₁⟩
      · exact ha L' hL' hCL'
    · refine ⟨C₁, hb₁, fun L' hL' => ?_⟩
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact hC₁
      · exact ha₁ L' hL'

/-! ## A point added to a convex outline -/

/-- The sides of a point followed by a chain of corners: the two sides at the point, and the
chain's segments. -/
theorem mem_sides_cone {V X Y : Point} {M : List Point} {s : Point × Point} :
    s ∈ sides (V :: X :: (M ++ [Y])) ↔
      s = (V, X) ∨ s ∈ segments (X :: (M ++ [Y])) ∨ s = (Y, V) := by
  have hj := segments_join (X :: M) [V] Y
  have he : sides (V :: X :: (M ++ [Y])) =
      (V, X) :: (segments (X :: (M ++ [Y])) ++ [(Y, V)]) := by
    change (V, X) :: segments (X :: (M ++ [Y]) ++ [V]) = _
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hj ⊢
    rw [hj]
    rfl
  rw [he]
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]

/-- **The outline of a point and a run of corners.** A point V outside a convex outline,
within the straight line of each side of a run of its corners from X to Y, and with the
region (but X, and but Y) on one side of XV and of YV, makes with that run a convex
outline, whose region holds every corner of the old one. -/
theorem cone_outline {cs : List Point} (h : ConvexOutline cs) {V X Y : Point}
    {M : List Point} (hV : ¬ ConvexRegion cs V)
    (hnd : (X :: (M ++ [Y])).Nodup) (hmem : ∀ c ∈ X :: (M ++ [Y]), c ∈ cs)
    (hsides : ∀ s ∈ segments (X :: (M ++ [Y])), s ∈ sides cs)
    (hinv : ∀ s ∈ segments (X :: (M ++ [Y])), ∀ R ∈ cs, R ≠ s.1 → R ≠ s.2 →
      SameSideOf V R s.1 s.2)
    (htX : ∀ Z₁ Z₂ : Point, ConvexRegion cs Z₁ → ConvexRegion cs Z₂ → Z₁ ≠ X → Z₂ ≠ X →
      SameSideOf Z₁ Z₂ X V)
    (htY : ∀ Z₁ Z₂ : Point, ConvexRegion cs Z₁ → ConvexRegion cs Z₂ → Z₁ ≠ Y → Z₂ ≠ Y →
      SameSideOf Z₁ Z₂ Y V) :
    ConvexOutline (V :: X :: (M ++ [Y])) ∧
      ∀ c ∈ cs, ConvexRegion (V :: X :: (M ++ [Y])) c := by
  have hVc : V ∉ X :: (M ++ [Y]) := fun hm => hV (Extreme.corner_region h (hmem V hm))
  have hreg {c : Point} (hc : c ∈ X :: (M ++ [Y])) : ConvexRegion cs c :=
    Extreme.corner_region h (hmem c hc)
  have hcases {P : Point} (hP : P ∈ V :: X :: (M ++ [Y])) :
      P = V ∨ P ∈ X :: (M ++ [Y]) := List.mem_cons.mp hP
  have hVV {s : Point × Point} (hs : s ∈ segments (X :: (M ++ [Y]))) :
      SameSideOf V V s.1 s.2 := by
    obtain ⟨R, hR, h₁, h₂⟩ := convex_third h s
    have hVR := hinv s hs R hR h₁ h₂
    exact hVR.trans hVR.symm
  refine ⟨⟨by simp, List.nodup_cons.mpr ⟨hVc, hnd⟩, ?_⟩, ?_⟩
  · intro s hs P hP Q hQ hP₁ hP₂ hQ₁ hQ₂
    rcases mem_sides_cone.mp hs with rfl | hs' | rfl
    · exact (htX P Q (hreg ((hcases hP).resolve_left hP₁)) (hreg ((hcases hQ).resolve_left hQ₁))
        hP₂ hQ₂).swap
    · rcases hcases hP with hPV | hP' <;> rcases hcases hQ with hQV | hQ'
      · rw [hPV, hQV]
        exact hVV hs'
      · rw [hPV]
        exact hinv s hs' Q (hmem Q hQ') hQ₁ hQ₂
      · rw [hQV]
        exact (hinv s hs' P (hmem P hP') hP₁ hP₂).symm
      · exact h.2.2 s (hsides s hs') P (hmem P hP') Q (hmem Q hQ') hP₁ hP₂ hQ₁ hQ₂
    · exact htY P Q (hreg ((hcases hP).resolve_left hP₂)) (hreg ((hcases hQ).resolve_left hQ₂))
        hP₁ hQ₁
  · intro c hc s hs P hP hP₁ hP₂
    have hcr := Extreme.corner_region h hc
    rcases mem_sides_cone.mp hs with rfl | hs' | rfl
    · by_cases hcX : c = X
      · obtain ⟨L, h₁, h₂⟩ := collinear_of_two V X
        exact Or.inl ⟨L, h₁, h₂, hcX ▸ h₂⟩
      · exact Or.inr (htX c P hcr (hreg ((hcases hP).resolve_left hP₁)) hcX hP₂).swap
    · rcases hcases hP with hPV | hP'
      · by_cases hc₁ : c = s.1
        · obtain ⟨L, h₁, h₂⟩ := collinear_of_two s.1 s.2
          exact Or.inl ⟨L, h₁, h₂, hc₁ ▸ h₁⟩
        by_cases hc₂ : c = s.2
        · obtain ⟨L, h₁, h₂⟩ := collinear_of_two s.1 s.2
          exact Or.inl ⟨L, h₁, h₂, hc₂ ▸ h₂⟩
        rw [hPV]
        exact Or.inr (hinv s hs' c hc hc₁ hc₂).symm
      · exact hcr s (hsides s hs') P (hmem P hP') hP₁ hP₂
    · by_cases hcY : c = Y
      · obtain ⟨L, h₁, h₂⟩ := collinear_of_two Y V
        exact Or.inl ⟨L, h₁, h₂, hcY ▸ h₁⟩
      · exact Or.inr (htY c P hcr (hreg ((hcases hP).resolve_left hP₂)) hcY hP₁)

/-- **One point added to a convex outline.** For any point V there is a convex outline whose
region holds the old region and V. If V is outside, take V' beyond V from a point O
inside, off every side's straight line. Some sides have V' beyond them, as it is outside, and
some within, by `not_all_outer`; where a side with V' beyond it is followed by one with V'
within, at the corner X, run on from X to the first corner Y whose next side has V'
beyond it. The point V' and the run from X to Y make the outline (`cone_outline`), the
straight lines XV' and YV' being tangents (`tangent_same_side`); and V lies between O and V'. -/
theorem insert_point {cs : List Point} (h : ConvexOutline cs) (V : Point) :
    ∃ ds : List Point, ConvexOutline ds ∧
      (∀ X : Point, ConvexRegion cs X → ConvexRegion ds X) ∧ ConvexRegion ds V := by
  classical
  by_cases hV : ConvexRegion cs V
  · exact ⟨cs, h, fun _ hX => hX, hV⟩
  /- A point inside, and a point beyond V off every side's straight line. -/
  obtain ⟨O, -, hO⟩ := CellFacts.core_point_avoiding h []
  have hOr : ConvexRegion cs O := fun s hs A hA h₁ h₂ => Or.inr (hO s hs A hA h₁ h₂)
  have hOV : O ≠ V := fun e => hV (e ▸ hOr)
  obtain ⟨W, hOVW⟩ := produce hOV
  let line (s : Point × Point) : Line := Classical.choose (collinear_of_two s.1 s.2)
  have hline (s : Point × Point) : OnLine s.1 (line s) ∧ OnLine s.2 (line s) :=
    Classical.choose_spec (collinear_of_two s.1 s.2)
  have hOoff : ∀ s ∈ sides cs, ¬ OnLine O (line s) := by
    intro s hs hOL
    obtain ⟨R, hR, h₁, h₂⟩ := convex_third h s
    exact not_on_line_of_same_side ((hO s hs R hR h₁ h₂).sameSide (hline s).1 (hline s).2) hOL
  obtain ⟨V', hVV'W, hV'a⟩ := between_avoiding ((sides cs).map line)
    (ne_of_between (between_symm hOVW)).symm (by
      intro L hL hVW
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hL
      exact hOoff s hs (on_line_of_between (between_symm hOVW) hVW.2 hVW.1))
  have hOVV' : Between O V V' := between_cut hOVW hVV'W
  have hV'off : ∀ s ∈ sides cs, ∀ L : Line, OnLine s.1 L → OnLine s.2 L → ¬ OnLine V' L := by
    intro s hs L h₁ h₂ hV'L
    have he := line_unique (convex_side_ne h hs) (hline s).1 (hline s).2 h₁ h₂
    exact hV'a (line s) (List.mem_map_of_mem hs) (he ▸ hV'L)
  have hV'r : ¬ ConvexRegion cs V' := fun hr => hV (convex_region_between h hOr hr hOVV')
  /- Within a side's straight line, or strictly beyond it. -/
  let p (s : Point × Point) : Prop :=
    ∀ R ∈ cs, R ≠ s.1 → R ≠ s.2 → SameSideOf V' R s.1 s.2
  have hstrict : ∀ s ∈ sides cs, ¬ p s → ∀ R ∈ cs, R ≠ s.1 → R ≠ s.2 →
      OppositeSidesOf V' R s.1 s.2 := by
    intro s hs hnp R hR h₁ h₂
    have hne := convex_side_ne h hs
    obtain ⟨L, hL₁, hL₂⟩ := Postulate1 s.1 s.2 hne
    refine OppositeSidesOf.of_line hne hL₁ hL₂ ⟨hV'off s hs L hL₁ hL₂,
      Pieces.corner_off h hs hL₁ hL₂ hR h₁ h₂, fun hsame => hnp ?_⟩
    intro R' hR' h₁' h₂'
    exact SameSideOf.of_line hne hL₁ hL₂ (same_side_trans (same_side_symm hsame)
      ((h.2.2 s hs R hR R' hR' h₁ h₂ h₁' h₂').sameSide hL₁ hL₂))
  have hvis : ∃ s ∈ sides cs, ¬ p s := by
    refine Classical.byContradiction fun hn => hV'r ?_
    intro s hs R hR h₁ h₂
    have hp : p s := Classical.byContradiction fun hnp => hn ⟨s, hs, hnp⟩
    exact Or.inr (hp R hR h₁ h₂)
  have hinvis : ∃ s ∈ sides cs, p s := by
    refine Classical.byContradiction fun hn => ?_
    have hall : ∀ s ∈ sides cs, ∀ R ∈ cs, R ≠ s.1 → R ≠ s.2 → OppositeSidesOf V' R s.1 s.2 :=
      fun s hs => hstrict s hs (fun hp => hn ⟨s, hs, hp⟩)
    obtain ⟨a, b, c, rest, rfl⟩ := CellFacts.three_corners h
    exact not_all_outer rest h hall
  /- The junction X, and the run of sides from it with V' within them. -/
  obtain ⟨W₀, X, X₂, hWX, hnpWX, hXX₂, hpXX₂⟩ := junction h.2.1 p hinvis hvis
  have hX : X ∈ cs := (LoopFacts.side_mem hWX).2
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hX
  have hrot (s : Point × Point) :
      s ∈ segments (X :: (post ++ pre) ++ [X]) ↔ s ∈ sides cs := by
    rw [hcs]
    exact Pieces.mem_sides_rotate_prefix pre (X :: post) s
  have hperm : (X :: (post ++ pre)).Perm cs := by
    rw [hcs]
    exact (List.perm_append_comm (l₁ := pre) (l₂ := X :: post)).symm.trans
      (by simp)
  obtain ⟨M₂, Y, Y₂, B₂, he₂, hall₂, hY⟩ :=
    first_seg p (X :: (post ++ pre) ++ [X]) ⟨(W₀, X), (hrot _).mpr hWX, hnpWX⟩
  have hYY₂ : (Y, Y₂) ∈ sides cs :=
    (hrot _).mp (by rw [he₂]; exact Pieces.pair_mem_segments M₂ B₂ Y Y₂)
  cases M₂ with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at he₂
    have heq := LoopFacts.sides_fst_inj h.2.1 hXX₂ hYY₂ he₂.1
    exact absurd (heq ▸ hpXX₂) hY
  | cons m M =>
    simp only [List.cons_append, List.cons.injEq] at he₂
    obtain ⟨rfl, he₂⟩ := he₂
    /- The run, from X to Y. -/
    obtain ⟨R', z, hR'⟩ := split_last (Y₂ :: B₂) (List.cons_ne_nil _ _)
    have hl : post ++ pre = M ++ Y :: R' := by
      rw [hR'] at he₂
      have := List.append_inj' (s₁ := post ++ pre) (t₁ := [X]) (s₂ := M ++ Y :: R') (t₂ := [z])
        (by simpa using he₂) rfl
      exact this.1
    have hsub : (X :: (M ++ [Y])).Sublist (X :: (post ++ pre)) := by
      rw [hl]
      exact List.Sublist.cons_cons X (List.Sublist.append_left
        (List.Sublist.cons_cons Y (List.nil_sublist R')) M)
    have hnd : (X :: (M ++ [Y])).Nodup := (hperm.nodup_iff.mpr h.2.1).sublist hsub
    have hmem : ∀ c ∈ X :: (M ++ [Y]), c ∈ cs := fun c hc => hperm.subset (hsub.subset hc)
    have hsides : ∀ s ∈ segments (X :: (M ++ [Y])), s ∈ sides cs := by
      intro s hs
      apply (hrot s).mp
      have he : X :: (post ++ pre) ++ [X] = X :: (M ++ [Y]) ++ (Y₂ :: B₂) := by
        simp [he₂]
      rw [he]
      exact segment_mem_append hs _
    /- The tangents at X and at Y. -/
    have htX : ∀ Z₁ Z₂ : Point, ConvexRegion cs Z₁ → ConvexRegion cs Z₂ → Z₁ ≠ X → Z₂ ≠ X →
        SameSideOf Z₁ Z₂ X V' := by
      intro Z₁ Z₂ h₁ h₂ hZ₁ hZ₂
      obtain ⟨Rs, hRs, hRs₁, hRs₂⟩ := convex_third h (W₀, X)
      obtain ⟨Rt, hRt, hRt₁, hRt₂⟩ := convex_third h (X, X₂)
      exact tangent_same_side h hX hWX hXX₂ (Or.inr rfl) (Or.inl rfl) hRs hRs₁ hRs₂ hRt hRt₁ hRt₂
        (hstrict _ hWX hnpWX Rs hRs hRs₁ hRs₂) (hpXX₂ Rt hRt hRt₁ hRt₂) h₁ h₂ hZ₁ hZ₂
    have hYm : Y ∈ cs := (LoopFacts.side_mem hYY₂).1
    obtain ⟨Y₀, hY₀⟩ := last_seg (List.cons_ne_nil X M) Y
    have hY₀' : (Y₀, Y) ∈ segments (X :: (M ++ [Y])) := by simpa using hY₀
    have htY : ∀ Z₁ Z₂ : Point, ConvexRegion cs Z₁ → ConvexRegion cs Z₂ → Z₁ ≠ Y → Z₂ ≠ Y →
        SameSideOf Z₁ Z₂ Y V' := by
      intro Z₁ Z₂ h₁ h₂ hZ₁ hZ₂
      have hY₀Y := hsides _ hY₀'
      obtain ⟨Rs, hRs, hRs₁, hRs₂⟩ := convex_third h (Y, Y₂)
      obtain ⟨Rt, hRt, hRt₁, hRt₂⟩ := convex_third h (Y₀, Y)
      exact tangent_same_side h hYm hYY₂ hY₀Y (Or.inl rfl) (Or.inr rfl) hRs hRs₁ hRs₂ hRt hRt₁ hRt₂
        (hstrict _ hYY₂ hY Rs hRs hRs₁ hRs₂)
        (hall₂ _ (by simpa using hY₀) Rt hRt hRt₁ hRt₂) h₁ h₂ hZ₁ hZ₂
    obtain ⟨hconv, hcorners⟩ := cone_outline h hV'r hnd hmem hsides
      (fun s hs => hall₂ s (by simpa using hs)) htX htY
    have hincl : ∀ Z : Point, ConvexRegion cs Z → ConvexRegion (V' :: X :: (M ++ [Y])) Z :=
      fun Z hZ => Pieces.region_subset hconv h hcorners hZ
    exact ⟨V' :: X :: (M ++ [Y]), hconv, hincl,
      convex_region_between hconv (hincl O hOr)
        (Extreme.corner_region hconv List.mem_cons_self) hOVV'⟩

/-- **Finitely many points added to a convex outline**, one after another. -/
theorem enclose_list : ∀ (qs : List Point) {cs : List Point}, ConvexOutline cs →
    ∃ ds : List Point, ConvexOutline ds ∧
      (∀ X : Point, ConvexRegion cs X → ConvexRegion ds X) ∧ ∀ V ∈ qs, ConvexRegion ds V
  | [], cs, h => ⟨cs, h, fun _ hX => hX, fun _ hV => absurd hV List.not_mem_nil⟩
  | V :: qs, _, h => by
    obtain ⟨cs₁, h₁, hin₁, hV₁⟩ := insert_point h V
    obtain ⟨ds, hds, hin, hqs⟩ := enclose_list qs h₁
    refine ⟨ds, hds, fun X hX => hin X (hin₁ X hX), fun U hU => ?_⟩
    rcases List.mem_cons.mp hU with rfl | hU
    · exact hin U hV₁
    · exact hqs U hU

/-! ## An enclosure with the region strictly inside -/

/-- When every corner of a convex outline is inside a cell, so is its whole region, which is
made of triangles on its corners (`fan_covers`). -/
theorem region_in_core {cs : List Point} (h : ConvexOutline cs) {Q : ConvexCell}
    (hc : ∀ c ∈ cs, Q.Core c) {Z : Point} (hZ : ConvexRegion cs Z) : Q.Core Z := by
  obtain ⟨t, ht, hZt⟩ := (fan_covers h Z).mpr hZ
  obtain ⟨h₁, h₂, h₃⟩ := Extreme.fan_mem ht
  intro s hs A hA hA₁ hA₂
  have hne := convex_side_ne Q.convex hs
  obtain ⟨L, hL₁, hL₂⟩ := Postulate1 s.1 s.2 hne
  exact SameSideOf.of_line hne hL₁ hL₂ (closed_same_side
    ((hc _ h₁ s hs A hA hA₁ hA₂).sameSide hL₁ hL₂)
    ((hc _ h₂ s hs A hA hA₁ hA₂).sameSide hL₁ hL₂)
    ((hc _ h₃ s hs A hA hA₁ hA₂).sameSide hL₁ hL₂) hZt)

/-- **An enclosure with room to spare.** For any cell there is a cell whose inside holds the
first's whole region: produce the straight line from a point inside through each corner, and
add the points beyond the corners (`enclose_list`). The point inside stays inside, and each
corner lies between it and a point of the new region. -/
theorem strict_enclosure (P : ConvexCell) :
    ∃ Q : ConvexCell, ∀ X : Point, P.Region X → Q.Core X := by
  classical
  obtain ⟨O, -, hO⟩ := CellFacts.core_point_avoiding P.convex []
  have hOc : ∀ c ∈ P.corners, O ≠ c := by
    intro c hc hOc
    obtain ⟨E, hE⟩ := outgoing_side hc
    obtain ⟨R, hR, h₁, h₂⟩ := convex_third P.convex (c, E)
    have hs := hO (c, E) hE R hR h₁ h₂
    obtain ⟨L, hL₁, hL₂⟩ := Postulate1 c E hs.1
    exact not_on_line_of_same_side (hs.sameSide hL₁ hL₂) (hOc ▸ hL₁)
  let push (c : Point) : Point := if hc : O ≠ c then Classical.choose (produce hc) else c
  have hpush : ∀ c ∈ P.corners, Between O c (push c) := by
    intro c hc
    have hne := hOc c hc
    simp only [push, hne, ne_eq, not_false_eq_true, ↓reduceDIte]
    exact Classical.choose_spec (produce hne)
  obtain ⟨ds, hds, hin, hqs⟩ := enclose_list (P.corners.map push) P.convex
  let Q : ConvexCell := ⟨ds, hds⟩
  have hOQ : Q.Core O := Pieces.core_mono hds hin hO
  have hcQ : ∀ c ∈ P.corners, Q.Core c := fun c hc =>
    ConvexCell.core_between (Q := Q) (hqs _ (List.mem_map_of_mem hc)) hOQ
      (between_symm (hpush c hc))
  exact ⟨Q, fun X hX => region_in_core P.convex hcQ hX⟩

/-! ## A ray that crosses nothing -/

/-- **A ray that crosses nothing.** From a point X outside a convex region that holds every
corner of a loop, some good ray crosses no side of the loop. X is beyond the straight line
L of a side of the region; take Z on that side, off the straight lines from X to the
corners, and produce ZX beyond X. The ray from X onwards stays strictly on X's side
of L, its straight line meeting L only at Z, behind X; and every side of the loop is
within L's other closed side. -/
theorem outside_ray {ps cs : List Point} (hc : ConvexOutline cs)
    (hin : ∀ V ∈ ps, ConvexRegion cs V) {X : Point} (hX : ¬ ConvexRegion cs X) :
    ∃ Q : Point, GoodRay ps X Q ∧ crossingCount ps X Q = 0 := by
  classical
  have hside : ∃ s ∈ sides cs, ∃ R ∈ cs, R ≠ s.1 ∧ R ≠ s.2 ∧ ¬ ClosedSide X R s.1 s.2 := by
    refine Classical.byContradiction fun hn => hX ?_
    intro s hs R hR h₁ h₂
    exact Classical.byContradiction fun hcl => hn ⟨s, hs, R, hR, h₁, h₂, hcl⟩
  obtain ⟨s, hs, R, hR, h₁, h₂, hcl⟩ := hside
  have hne := convex_side_ne hc hs
  obtain ⟨L, hL₁, hL₂⟩ := Postulate1 s.1 s.2 hne
  have hXL : ¬ OnLine X L := fun hx => hcl (Or.inl ⟨L, hL₁, hL₂, hx⟩)
  have hXR : ¬ SameSide X R L := fun hx => hcl (Or.inr (SameSideOf.of_line hne hL₁ hL₂ hx))
  have hhalf {V : Point} (hV : ConvexRegion cs V) : Half V R L :=
    Pieces.region_half hc hs hL₁ hL₂ hR h₁ h₂ hV
  have hVX : ∀ V ∈ ps, V ≠ X := fun V hV e => hX (e ▸ hin V hV)
  /- The straight lines from X to the corners, and a point Z of the side off them. -/
  let line (V : Point) : Line := Classical.choose (collinear_of_two X V)
  have hline (V : Point) : OnLine X (line V) ∧ OnLine V (line V) :=
    Classical.choose_spec (collinear_of_two X V)
  obtain ⟨Z, hZb, hZa⟩ := between_avoiding (ps.map line) hne (by
    intro M hM h12
    obtain ⟨V, -, rfl⟩ := List.mem_map.mp hM
    have he := line_unique hne h12.1 h12.2 hL₁ hL₂
    exact hXL (he ▸ (hline V).1))
  have hZL : OnLine Z L := on_line_of_between_ends hZb hL₁ hL₂
  have hZX : Z ≠ X := fun e => hXL (e ▸ hZL)
  obtain ⟨Q, hZXQ⟩ := produce hZX
  have hXQ : X ≠ Q := (ne_of_between (between_symm hZXQ)).symm
  obtain ⟨J, hZJ, hXJ⟩ := Postulate1 Z X hZX
  have hQJ : OnLine Q J := on_line_of_between hZXQ hZJ hXJ
  have hJL : J ≠ L := fun e => hXL (e ▸ hXJ)
  have hZonly : ∀ T : Point, OnLine T J → OnLine T L → T = Z := fun T hTJ hTL =>
    Classical.byContradiction fun hTZ => hJL (line_unique hTZ hTJ hZJ hTL hZL)
  /- Every point of the ray is strictly on X's side of L. -/
  have hray : ∀ Y : Point, OnRay Y X Q → SameSide Y X L := by
    intro Y hY
    have hYJ : OnLine Y J := hY.onLine hXJ hQJ
    have hYL : ¬ OnLine Y L := by
      intro hYL
      have hYZ := hZonly Y hYJ hYL
      rw [hYZ] at hY
      exact hY.2.2.2 hZXQ
    refine Classical.byContradiction fun hns => ?_
    obtain ⟨T, hTL, hYTX⟩ := OppositeSides.exists_between ⟨hYL, hXL, hns⟩
    have hTZ := hZonly T (on_line_of_between_ends hYTX hYJ hXJ) hTL
    rw [hTZ] at hYTX
    exact hY.2.2.2 (between_symm
      (between_of_between_right (between_symm hZXQ) (between_symm hYTX)))
  refine ⟨Q, ⟨hXQ, fun V hV hcol => ?_⟩, ?_⟩
  · obtain ⟨K, hXK, hQK, hVK⟩ := hcol
    have hKJ : K = J := line_unique hXQ hXK hQK hXJ hQJ
    have hKl : K = line V := line_unique (hVX V hV).symm hXK hVK (hline V).1 (hline V).2
    rw [hKJ] at hKl
    exact hZa (line V) (List.mem_map_of_mem hV) (hKl ▸ hZJ)
  · apply LoopFacts.crossingCount_eq_zero
    rintro t ht ⟨Y, hY, hb⟩
    have hm := LoopFacts.side_mem ht
    rcases half_between (hhalf (hin _ hm.1)) (hhalf (hin _ hm.2)) hb with hy | hy
    · exact not_on_line_of_same_side (hray Y hY) hy
    · exact hXR (same_side_trans (hray Y hY) hy)

/-! ## Cells cut by one straight line -/

/-- Two points on opposite sides of any straight line: one inside a cell, off the line, and
one taken on its other side. -/
theorem opposite_pair (P : ConvexCell) (L : Line) : ∃ A B : Point, OppositeSides A B L := by
  obtain ⟨A, hA, -⟩ := CellFacts.core_point_avoiding P.convex [L]
  obtain ⟨B, hB, -⟩ := exists_point_opposite_side (hA L List.mem_cons_self) []
  exact ⟨A, B, Pieces.opposite_symm hB⟩

/-- **Each cell cut by one straight line, keeping both pieces** (`convex_cut`): the pieces of
a cell make up its region exactly; each piece's inside is within its cell's inside, and on one
side of the line; and no point is inside both pieces of one cell. -/
theorem cut_cells {L : Line} {A B : Point} (hAB : OppositeSides A B L) :
    ∃ f : ConvexCell → List ConvexCell, ∀ Q : ConvexCell,
      (∀ X : Point, Q.Region X ↔ ∃ R ∈ f Q, R.Region X) ∧
      (∀ R ∈ f Q, ∀ X : Point, R.Core X → Q.Core X) ∧
      (∀ R ∈ f Q, ∀ X Y : Point, R.Core X → R.Core Y → SameSide X Y L) ∧
      (f Q).Pairwise (fun R S => ∀ X : Point, R.Core X → ¬ S.Core X) := by
  have hcut (Q : ConvexCell) : ∃ uv : Cell × Cell, Clips Q L A uv.1 ∧ Clips Q L B uv.2 ∧
      ∀ X : Point, Q.Region X ↔ CellRegion uv.1 X ∨ CellRegion uv.2 X := by
    obtain ⟨U, V, hU, hV, hr, -⟩ := convex_cut Q hAB
    exact ⟨(U, V), hU, hV, hr⟩
  obtain ⟨g, hg⟩ := Classical.axiomOfChoice hcut
  have hreg (c : Cell) (X : Point) : CellRegion c X ↔ ∃ R ∈ c.toList, R.Region X := by
    cases c with
    | none => simp [CellRegion]
    | some R => simp [CellRegion]
  have hcore {c : Cell} {R : ConvexCell} (hR : R ∈ c.toList) (X : Point) :
      CellCore c X ↔ R.Core X := by
    rw [Option.mem_toList] at hR
    subst hR
    rfl
  refine ⟨fun Q => (g Q).1.toList ++ (g Q).2.toList, fun Q => ⟨fun X => ?_, ?_, ?_, ?_⟩⟩
  · rw [(hg Q).2.2 X, hreg, hreg]
    simp only [List.mem_append]
    constructor
    · rintro (⟨R, hR, hX⟩ | ⟨R, hR, hX⟩)
      · exact ⟨R, Or.inl hR, hX⟩
      · exact ⟨R, Or.inr hR, hX⟩
    · rintro ⟨R, hR | hR, hX⟩
      · exact Or.inl ⟨R, hR, hX⟩
      · exact Or.inr ⟨R, hR, hX⟩
  · intro R hR X hX
    rcases List.mem_append.mp hR with hR | hR
    · exact (((hg Q).1.1 X).mp ((hcore hR X).mpr hX)).1
    · exact (((hg Q).2.1.1 X).mp ((hcore hR X).mpr hX)).1
  · intro R hR X Y hX hY
    rcases List.mem_append.mp hR with hR | hR
    · exact same_side_trans (same_side_symm (((hg Q).1.1 X).mp ((hcore hR X).mpr hX)).2)
        (same_side_symm (((hg Q).1.1 Y).mp ((hcore hR Y).mpr hY)).2)
    · exact same_side_trans (same_side_symm (((hg Q).2.1.1 X).mp ((hcore hR X).mpr hX)).2)
        (same_side_symm (((hg Q).2.1.1 Y).mp ((hcore hR Y).mpr hY)).2)
  · have hone (c : Cell) : c.toList.Pairwise (fun R S => ∀ X : Point, R.Core X → ¬ S.Core X) := by
      cases c <;> simp
    refine List.pairwise_append.mpr ⟨hone _, hone _, fun R hR S hS X hRX hSX => ?_⟩
    exact Pieces.not_both hAB (((hg Q).1.1 X).mp ((hcore hR X).mpr hRX)).2
      (((hg Q).2.1.1 X).mp ((hcore hS X).mpr hSX)).2

end Arrangement

end Elements.Figures
