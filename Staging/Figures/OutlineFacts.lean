import Staging.Figures.Parity

/-!
# Staging: facts about outlines, for the boundary bridges of brief 0013

Helper lemmas for `region_with_holes`, `outline_boundary`, `same_boundary_region`,
`outline_normalise` and `outline_bounded` in `Outline.lean` (brief 0013, section 8, "Ray parity
and the region"). No proposition of the Elements is cited, and neither Postulate 5 nor
superposition is used. What `outline_bounded` uses beyond this file, a triangle holding every
corner, is found with Postulate 5 and I.23 in `OutlineBound.lean`.

* **Sides of finitely many straight lines.** A point off a finite straight line has a straight
  line between them (`sep_segment`); so a point off every side of a loop has finitely many
  such lines, and any point on its side of all of them is off every side (`sep_all`). The
  points on prescribed sides of finitely many straight lines (`Sat`) hold every point between
  two of them.
* **Inside, near a point.** Two points on prescribed sides of such straight lines, all off the
  boundary, are both inside or both not: a good ray from one through a point near both runs on
  past it with the same crossings (`seg_inside`, `inside_const`). So inside a loop does not
  change near a point off its boundary (`const_near`), and near a point strictly within one
  side it changes exactly across that side's straight line (`half_near`): the open finite
  straight line from one side to the other crosses that side and no other.
* **Many contours.** The figure's depth then changes parity across a side of one contour,
  since contours share no segment (`boundary_witness`); this identifies the contours with the
  boundary of the region. Along one good ray, each crossing is a point of the boundary, read
  as a point set, on exactly one side of one contour; so the total crossing count, and with
  it the parity of the depth, depends only on that point set (`depth_parity_eq`).
* **Contacts survive normalisation.** Where two contours meet at a point strictly within a side
  of each, their sides either overlap, giving infinitely many contacts, or cross, giving points
  inside one and not the other in all four combinations (`contact_vertex`).
* **An enclosing triangle.** A triangle holding every corner holds the region
  (`bounded_of_enclosure`). That some triangle holds them is `enclosing_triangle`, in
  `OutlineBound.lean`.

Natural numbers count sides, corners and contours only; they measure nothing.
-/

namespace Elements.Figures

open Tacit

namespace OutlineFacts

/-! ## Prescribed sides of finitely many straight lines -/

/-- `Y` lies on the side of each straight line `c.2` where `c.1` is. -/
def Sat (cs : List (Point × Line)) (Y : Point) : Prop := ∀ c ∈ cs, SameSide Y c.1 c.2

theorem sat_append {cs ds : List (Point × Line)} {Y : Point} :
    Sat (cs ++ ds) Y ↔ Sat cs Y ∧ Sat ds Y := by
  unfold Sat
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
      fun c hc => h c (List.mem_append_right _ hc)⟩
  · rintro ⟨h₁, h₂⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h₁ c hc
    · exact h₂ c hc

/-- A point between two points on the prescribed sides is on them too. -/
theorem sat_between {cs : List (Point × Line)} {Y Z P : Point} (hY : Sat cs Y)
    (hZ : Sat cs Z) (h : Between Y P Z) : Sat cs P :=
  fun c hc => Avoid.same_side_between h (hY c hc) (hZ c hc)

/-- **A straight line to separate a point from a finite straight line** it is not on: the
point is off it, and no point of the finite straight line is on the point's side. Off the
finite straight line's own straight line, that line serves; on it, beyond one end, a straight
line through a point between it and the nearer end. -/
theorem sep_segment {X a b : Point} (hab : a ≠ b) (hX : ¬ OnFiniteLine X a b) :
    ∃ M : Line, ¬ OnLine X M ∧ ∀ P : Point, OnFiniteLine P a b → ¬ SameSide P X M := by
  obtain ⟨L, haL, hbL⟩ := Postulate1 a b hab
  by_cases hXL : OnLine X L
  · have hXa : X ≠ a := fun e => hX (Or.inl e)
    have hXb : X ≠ b := fun e => hX (Or.inr (Or.inl e))
    have hnb : ¬ Between a X b := fun h => hX (Or.inr (Or.inr h))
    have key : ∀ {c d : Point}, OnLine c L → OnLine d L → c ≠ d → X ≠ c → Between X c d →
        ∃ M : Line, ¬ OnLine X M ∧ ∀ P, OnFiniteLine P c d → ¬ SameSide P X M := by
      intro c d hcL hdL hcd hXc hXcd
      obtain ⟨U, hUL, hXUc, -⟩ := exists_point_between hXL hcL hXc []
      obtain ⟨R, hcdR, -⟩ := exists_off_line hcd []
      have hRL : ¬ OnLine R L := hcdR.off_line hcL hdL
      have hUR : U ≠ R := fun e => hRL (e ▸ hUL)
      obtain ⟨M, hUM, hRM⟩ := Postulate1 U R hUR
      have hML : M ≠ L := fun e => hRL (e ▸ hRM)
      have off : ∀ {Y : Point}, OnLine Y L → Y ≠ U → ¬ OnLine Y M := fun hYL hYU hYM =>
        hML (line_unique hYU hYM hUM hYL hUL)
      have hXM : ¬ OnLine X M := off hXL (ne_of_between hXUc)
      have hcM : ¬ OnLine c M := off hcL (ne_of_between (between_symm hXUc))
      have hXc' : ¬ SameSide X c M := pasch3 hXUc hUM
      have hcd' : SameSide c d M := pasch2 (between_inner hXUc hXcd) hUM hcM
      refine ⟨M, hXM, fun P hP hPX => ?_⟩
      have hPc : SameSide P c M := by
        rcases hP with e | e | hP
        · rw [e]
          exact same_side_refl hcM
        · rw [e]
          exact same_side_symm hcd'
        · exact same_side_symm (pasch1 hP hcd')
      exact hXc' (same_side_trans hPX hPc)
    rcases between_cases hXa hab hXb hXL haL hbL with h | h | h
    · exact key haL hbL hab hXa h
    · exact absurd h hnb
    · obtain ⟨M, hXM, hM⟩ := key hbL haL hab.symm hXb h
      exact ⟨M, hXM, fun P hP => hM P (LoopFacts.onFiniteLine_comm.mp hP)⟩
  · exact ⟨L, hXL, fun P hP hPX =>
      not_on_line_of_same_side hPX (LoopFacts.onFiniteLine_onLine hP haL hbL)⟩

/-- **Away from finitely many finite straight lines.** A point off each of them is on a
prescribed side of finitely many straight lines, and every point on those sides is off each of
them. -/
theorem sep_all (X : Point) : ∀ (l : List (Point × Point)),
    (∀ s ∈ l, s.1 ≠ s.2 ∧ ¬ OnFiniteLine X s.1 s.2) →
    ∃ cs : List (Point × Line), Sat cs X ∧
      ∀ Y, Sat cs Y → ∀ s ∈ l, ¬ OnFiniteLine Y s.1 s.2
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ _ _ h => absurd h List.not_mem_nil⟩
  | s :: l, h => by
    obtain ⟨cs, hX, hcs⟩ := sep_all X l fun t ht => h t (List.mem_cons_of_mem _ ht)
    obtain ⟨hs₁, hs₂⟩ := h s List.mem_cons_self
    obtain ⟨M, hXM, hM⟩ := sep_segment hs₁ hs₂
    refine ⟨(X, M) :: cs, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with e | hc
      · rw [e]
        exact same_side_refl hXM
      · exact hX c hc
    · intro Y hY t ht hYt
      rcases List.mem_cons.mp ht with e | ht
      · rw [e] at hYt
        exact hM Y hYt (hY (X, M) List.mem_cons_self)
      · exact hcs Y (fun c hc => hY c (List.mem_cons_of_mem _ hc)) t ht hYt

/-- A point near a point of a finite straight line, strictly within it, on the prescribed
sides, and other than finitely many given points. -/
theorem near_side {a b X : Point} (hab : a ≠ b) (hX : OnFiniteLine X a b)
    {cs : List (Point × Line)} (hXc : Sat cs X) (avoid : List Point) :
    ∃ W : Point, Between a W b ∧ Sat cs W ∧ W ∉ avoid := by
  have key : ∀ {E : Point}, X ≠ E → (∀ W, Between X W E → Between a W b) →
      ∃ W : Point, Between a W b ∧ Sat cs W ∧ W ∉ avoid := by
    intro E hXE hin
    obtain ⟨W', hXW'E, hW'c⟩ := Avoid.shorten_sides hXE cs hXc
    obtain ⟨L, hXL, hW'L⟩ := Postulate1 X W' (ne_of_between hXW'E)
    obtain ⟨W, -, hXWW', hWav⟩ := exists_point_between hXL hW'L (ne_of_between hXW'E) avoid
    exact ⟨W, hin W (between_of_between_left hXW'E hXWW'), sat_between hXc hW'c hXWW', hWav⟩
  rcases hX with e | e | hX
  · subst e
    exact key hab fun W hW => hW
  · subst e
    exact key hab.symm fun W hW => between_symm hW
  · exact key (ne_of_between (between_symm hX)).symm fun W hW =>
      between_symm (between_of_between_left (between_symm hX) (between_symm hW))

/-- Two points on opposite sides of a straight line through a point, both on the prescribed
sides. -/
theorem opposite_pair {W : Point} {N : Line} (hWN : OnLine W N) {cs : List (Point × Line)}
    (hW : Sat cs W) :
    ∃ Y Z : Point, Sat cs Y ∧ Sat cs Z ∧ ¬ OnLine Y N ∧ ¬ OnLine Z N ∧ ¬ SameSide Y Z N := by
  obtain ⟨U, hUN, hU⟩ := exists_point_on_line N [W]
  have hWU : W ≠ U := fun e => hU (e ▸ List.mem_singleton_self W)
  obtain ⟨R, hWUR, -⟩ := exists_off_line hWU []
  have hRN : ¬ OnLine R N := hWUR.off_line hWN hUN
  have hWR : W ≠ R := fun e => hRN (e ▸ hWN)
  obtain ⟨R', hRWR'⟩ := produce hWR.symm
  have hR'N : ¬ OnLine R' N := fun h => hRN (on_line_of_between (between_symm hRWR') h hWN)
  have hWR' : W ≠ R' := (ne_of_between (between_symm hRWR')).symm
  obtain ⟨Y, hWYR, hY⟩ := Avoid.shorten_sides hWR cs hW
  obtain ⟨Z, hWZR', hZ⟩ := Avoid.shorten_sides hWR' cs hW
  have hYN : ¬ OnLine Y N := fun h => hRN (on_line_of_between hWYR hWN h)
  have hZN : ¬ OnLine Z N := fun h => hR'N (on_line_of_between hWZR' hWN h)
  have hYR : SameSide Y R N := pasch2 hWYR hWN hYN
  have hZR' : SameSide Z R' N := pasch2 hWZR' hWN hZN
  refine ⟨Y, Z, hY, hZ, hYN, hZN, fun hYZ => pasch3 hRWR' hWN ?_⟩
  exact same_side_trans (same_side_trans hYZ hYR) hZR'

/-- The prescribed sides of a triangle's straight lines, towards its corners: a point on them
all is inside it. -/
theorem tri_sat {X A B C : Point} (hX : InsideTriangle X A B C) :
    ∃ cs : List (Point × Line), Sat cs X ∧ ∀ Y, Sat cs Y → InsideTriangle Y A B C := by
  obtain ⟨h₁, h₂, h₃⟩ := hX
  obtain ⟨L₁, hB₁, hC₁⟩ := Postulate1 B C h₁.1
  obtain ⟨L₂, hC₂, hA₂⟩ := Postulate1 C A h₂.1
  obtain ⟨L₃, hA₃, hB₃⟩ := Postulate1 A B h₃.1
  refine ⟨[(A, L₁), (B, L₂), (C, L₃)], ?_, fun Y hY => ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with e | e | e <;> rw [e]
    · exact h₁.sameSide hB₁ hC₁
    · exact h₂.sameSide hC₂ hA₂
    · exact h₃.sameSide hA₃ hB₃
  · exact ⟨SameSideOf.of_line h₁.1 hB₁ hC₁ (hY (A, L₁) (by simp)),
      SameSideOf.of_line h₂.1 hC₂ hA₂ (hY (B, L₂) (by simp)),
      SameSideOf.of_line h₃.1 hA₃ hB₃ (hY (C, L₃) (by simp))⟩

/-! ## A ray read on past a point -/

/-- The open finite straight line YZ crosses the side strictly within it. -/
def SegCrosses (Y Z : Point) (s : Point × Point) : Prop :=
  ∃ P : Point, Between Y P Z ∧ Between s.1 P s.2

/-- The number of sides the open finite straight line YZ crosses. -/
noncomputable def segCount (ps : List Point) (Y Z : Point) : Nat := by
  classical
  exact ((sides ps).filter fun s => decide (SegCrosses Y Z s)).length

/-- **A ray read on past a point.** With Z between Y and Q, a side with an end off the
straight line, and not through Z, crosses the ray from Y through Z exactly when it crosses
the open finite straight line YZ or the ray from Z through Q; never both, since it meets the
straight line once. -/
theorem ray_split {Y Z Q : Point} {ℓ : Line} (hYZQ : Between Y Z Q) (hYℓ : OnLine Y ℓ)
    (hZℓ : OnLine Z ℓ) {s : Point × Point} (hs : ¬ OnLine s.1 ℓ)
    (hZs : ¬ Between s.1 Z s.2) :
    (RayCrosses Y Z s ↔ SegCrosses Y Z s ∨ RayCrosses Z Q s) ∧
      ¬ (SegCrosses Y Z s ∧ RayCrosses Z Q s) := by
  have hYZ : Y ≠ Z := ne_of_between hYZQ
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨P, hP, hsP⟩
    have hPℓ : OnLine P ℓ := hP.onLine hYℓ hZℓ
    by_cases hPZ : P = Z
    · rw [hPZ] at hsP
      exact absurd hsP hZs
    rcases between_cases hYZ (Ne.symm hPZ) hP.2.1.symm hYℓ hZℓ hPℓ with h | h | h
    · exact Or.inr ⟨P, OnRay.of_between_between hYZQ h, hsP⟩
    · exact absurd (between_symm h) hP.2.2.2
    · exact Or.inl ⟨P, h, hsP⟩
  · rintro (⟨P, hP, hsP⟩ | ⟨P, hP, hsP⟩)
    · exact ⟨P, OnRay.of_between hP, hsP⟩
    · exact ⟨P, OnRay.of_beyond (hP.between hYZQ), hsP⟩
  · rintro ⟨⟨P, hP, hsP⟩, ⟨R, hR, hsR⟩⟩
    have hYZR : Between Y Z R := hR.between hYZQ
    have hPR : P ≠ R := by
      rintro rfl
      exact ne_of_between (between_symm (between_of_between_left hYZR hP)) rfl
    obtain ⟨N, h₁, h₂⟩ := Postulate1 s.1 s.2 (ne_of_between_ends hsP)
    have he : ℓ = N := line_unique hPR (on_line_of_between_ends hP hYℓ hZℓ)
      (on_line_of_between hYZR hYℓ hZℓ) (on_line_of_between_ends hsP h₁ h₂)
      (on_line_of_between_ends hsR h₁ h₂)
    exact hs (he ▸ h₁)

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

/-- **The count read on past a point.** The crossings of the ray from Y through Z are those of
the open finite straight line YZ and those of the ray from Z on through Q. -/
theorem count_split {ps : List Point} {Y Z Q : Point} {ℓ : Line} (hYZQ : Between Y Z Q)
    (hYℓ : OnLine Y ℓ) (hZℓ : OnLine Z ℓ) (hoff : ∀ V ∈ ps, ¬ OnLine V ℓ)
    (hZ : ¬ loopBoundary ps Z) :
    crossingCount ps Y Z = segCount ps Y Z + crossingCount ps Z Q := by
  classical
  unfold crossingCount segCount
  apply filter_or_length
  intro s hs
  have hsp := ray_split hYZQ hYℓ hZℓ (hoff _ (LoopFacts.side_mem hs).1)
    (fun hb => hZ ⟨s, hs, Or.inr (Or.inr hb)⟩)
  simp only [decide_eq_true_eq]
  exact hsp

/-! ## Inside, near a point -/

/-- `loop_inside_iff`, read here from `Parity.parity_independent` (`Outline.lean`, which states
it, imports this file). -/
theorem inside_iff {ps : List Point} (h : SimpleLoop ps) {X Q : Point}
    (hX : ¬ loopBoundary ps X) (hQ : GoodRay ps X Q) :
    loopInside ps X ↔ crossingCount ps X Q % 2 = 1 := by
  constructor
  · rintro ⟨_, R, hR, hodd⟩
    exact (Parity.parity_independent h hX hQ hR).trans hodd
  · intro hodd
    exact ⟨hX, Q, hQ, hodd⟩

/-- Inside is the region off the boundary. -/
theorem inside_iff_region {ps : List Point} {X : Point} :
    loopInside ps X ↔ loopRegion ps X ∧ ¬ loopBoundary ps X := by
  constructor
  · intro h
    exact ⟨Or.inr h, h.1⟩
  · rintro ⟨hr, hb⟩
    exact hr.resolve_left hb

/-- Every corner is on the boundary. -/
theorem vertex_boundary {ps : List Point} {V : Point} (hV : V ∈ ps) : loopBoundary ps V := by
  obtain ⟨E, hE⟩ := outgoing_side hV
  exact ⟨(V, E), hE, Or.inl rfl⟩

/-- A ray along a straight line through no corner is good. -/
theorem good_of_line {ps : List Point} {X Z : Point} {ℓ : Line} (hXZ : X ≠ Z)
    (hXℓ : OnLine X ℓ) (hZℓ : OnLine Z ℓ) (hoff : ∀ V ∈ ps, ¬ OnLine V ℓ) :
    GoodRay ps X Z :=
  ⟨hXZ, fun V hV ⟨M, hXM, hZM, hVM⟩ =>
    hoff V hV (by rw [← line_unique hXZ hXM hZM hXℓ hZℓ]; exact hVM)⟩

/-- A good ray's straight line passes through no corner. -/
theorem off_of_good {ps : List Point} {X Z : Point} {ℓ : Line} (h : GoodRay ps X Z)
    (hXℓ : OnLine X ℓ) (hZℓ : OnLine Z ℓ) : ∀ V ∈ ps, ¬ OnLine V ℓ :=
  fun V hV hVℓ => h.2 V hV ⟨ℓ, hXℓ, hZℓ, hVℓ⟩

/-- No side crossed: the count of the open finite straight line is nought. -/
theorem segCount_zero {ps : List Point} {Y Z : Point}
    (h : ∀ s ∈ sides ps, ¬ SegCrosses Y Z s) : segCount ps Y Z = 0 := by
  classical
  unfold segCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro s hs
  simpa using h s hs

/-- **Along a finite straight line that crosses no side.** Its ends are inside together: the
good ray from one through the other, read on past it, has the same crossings. -/
theorem seg_inside {ps : List Point} (h : SimpleLoop ps) {X Z : Point} (hXZ : GoodRay ps X Z)
    (hX : ¬ loopBoundary ps X) (hZ : ¬ loopBoundary ps Z)
    (hseg : ∀ P, Between X P Z → ¬ loopBoundary ps P) :
    loopInside ps X ↔ loopInside ps Z := by
  obtain ⟨ℓ, hXℓ, hZℓ⟩ := Postulate1 X Z hXZ.1
  have hoff := off_of_good hXZ hXℓ hZℓ
  obtain ⟨Q, hXZQ⟩ := produce hXZ.1
  have hQℓ := on_line_of_between hXZQ hXℓ hZℓ
  have hZQ : GoodRay ps Z Q :=
    good_of_line (ne_of_between (between_symm hXZQ)).symm hZℓ hQℓ hoff
  have h0 : segCount ps X Z = 0 := segCount_zero fun s hs ⟨P, hP, hsP⟩ =>
    hseg P hP ⟨s, hs, Or.inr (Or.inr hsP)⟩
  rw [inside_iff h hX hXZ, inside_iff h hZ hZQ, count_split hXZQ hXℓ hZℓ hoff hZ, h0,
    Nat.zero_add]

/-- A loop has a corner. -/
theorem exists_vertex {ps : List Point} (h : SimpleLoop ps) : ∃ V, V ∈ ps := by
  rcases ps with _ | ⟨V, _⟩
  · exact absurd h.1 (by simp)
  · exact ⟨V, List.mem_cons_self⟩

/-- **Inside is constant on prescribed sides off the boundary.** Two such points both see a
third, near the first and on the same sides, along good rays that cross no side. -/
theorem inside_const {ps : List Point} (h : SimpleLoop ps) {cs : List (Point × Line)}
    (hcs : ∀ Y, Sat cs Y → ¬ loopBoundary ps Y) {Y Y' : Point} (hY : Sat cs Y)
    (hY' : Sat cs Y') : loopInside ps Y ↔ loopInside ps Y' := by
  obtain ⟨A, B, C, hABC, hcl⟩ := small_triangle cs hY
  have htri : Triangle A B C := hABC.1.symm.triangle.cab
  let line (U V : Point) : Line := Classical.choose (collinear_of_two U V)
  have hline (U V : Point) : OnLine U (line U V) ∧ OnLine V (line U V) :=
    Classical.choose_spec (collinear_of_two U V)
  obtain ⟨Z, hZ, hZav⟩ := triangle_point_avoiding htri (ps.map (line Y) ++ ps.map (line Y'))
  have hZs : Sat cs Z := hcl Z (Or.inl hZ)
  obtain ⟨V₀, hV₀⟩ := exists_vertex h
  have good : ∀ {U : Point}, Sat cs U → (∀ V ∈ ps, ¬ OnLine Z (line U V)) →
      GoodRay ps U Z := by
    intro U hU hav
    have hUV : ∀ V ∈ ps, U ≠ V := fun V hV e => hcs U hU (e ▸ vertex_boundary hV)
    refine ⟨fun e => hav V₀ hV₀ (e ▸ (hline U V₀).1), fun V hV ⟨M, hUM, hZM, hVM⟩ => ?_⟩
    apply hav V hV
    rw [line_unique (hUV V hV) (hline U V).1 (hline U V).2 hUM hVM]
    exact hZM
  have hYZ : GoodRay ps Y Z := good hY fun V hV hZV =>
    hZav _ (List.mem_append_left _ (List.mem_map_of_mem hV)) hZV
  have hY'Z : GoodRay ps Y' Z := good hY' fun V hV hZV =>
    hZav _ (List.mem_append_right _ (List.mem_map_of_mem hV)) hZV
  have e₁ := seg_inside h hYZ (hcs Y hY) (hcs Z hZs) fun P hP => hcs P (sat_between hY hZs hP)
  have e₂ := seg_inside h hY'Z (hcs Y' hY') (hcs Z hZs) fun P hP =>
    hcs P (sat_between hY' hZs hP)
  exact e₁.trans e₂.symm

/-- **Near a point off the boundary, inside does not change.** -/
theorem const_near {ps : List Point} (h : SimpleLoop ps) {X : Point}
    (hX : ¬ loopBoundary ps X) :
    ∃ cs : List (Point × Line), Sat cs X ∧
      ∀ Y, Sat cs Y → ¬ loopBoundary ps Y ∧ (loopInside ps Y ↔ loopInside ps X) := by
  obtain ⟨cs, hXc, hcs⟩ := sep_all X (sides ps) fun s hs =>
    ⟨h.2.2.1 s hs, fun hXs => hX ⟨s, hs, hXs⟩⟩
  have hb : ∀ Y, Sat cs Y → ¬ loopBoundary ps Y := fun Y hY ⟨s, hs, hYs⟩ => hcs Y hY s hs hYs
  exact ⟨cs, hXc, fun Y hY => ⟨hb Y hY, inside_const h hb hY hXc⟩⟩

/-- The same, for finitely many loops at once. -/
theorem const_near_all {X : Point} : ∀ (l : List (List Point)),
    (∀ qs ∈ l, SimpleLoop qs ∧ ¬ loopBoundary qs X) →
    ∃ cs : List (Point × Line), Sat cs X ∧
      ∀ Y, Sat cs Y → ∀ qs ∈ l, ¬ loopBoundary qs Y ∧ (loopInside qs Y ↔ loopInside qs X)
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ _ _ h => absurd h List.not_mem_nil⟩
  | qs :: l, h => by
    obtain ⟨cs, hX, hcs⟩ := const_near_all l fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨h₁, h₂⟩ := h qs List.mem_cons_self
    obtain ⟨ds, hXd, hds⟩ := const_near h₁ h₂
    refine ⟨ds ++ cs, sat_append.mpr ⟨hXd, hX⟩, fun Y hY q hq => ?_⟩
    obtain ⟨hYd, hYc⟩ := sat_append.mp hY
    rcases List.mem_cons.mp hq with e | hq
    · rw [e]
      exact hds Y hYd
    · exact hcs Y hYc q hq

/-- Two statements that do not agree: one holds exactly when the other fails. -/
theorem iff_not_of_not_iff {a b : Prop} (h : ¬ (a ↔ b)) : a ↔ ¬ b :=
  ⟨fun ha hb => h ⟨fun _ => hb, fun _ => ha⟩,
    fun hnb => Classical.byContradiction fun hna =>
      h ⟨fun ha => absurd ha hna, fun hb => absurd hb hnb⟩⟩

/-- A point strictly within one side of a simple loop is on no other side, and is not a
corner. -/
theorem within_side {ps : List Point} (h : SimpleLoop ps) {s : Point × Point}
    (hs : s ∈ sides ps) {W : Point} (hW : Between s.1 W s.2) :
    (∀ t ∈ sides ps, t ≠ s → ¬ OnFiniteLine W t.1 t.2) ∧ W ∉ ps := by
  have hother : ∀ t ∈ sides ps, t ≠ s → ¬ OnFiniteLine W t.1 t.2 := by
    intro t ht hts hWt
    rcases (Parity.side_meet h hs ht (Ne.symm hts) W (Or.inr (Or.inr hW)) hWt).1 with e | e
    · exact ne_of_between hW e.symm
    · exact ne_of_between (between_symm hW) e.symm
  refine ⟨hother, fun hWv => ?_⟩
  obtain ⟨E, hE⟩ := outgoing_side hWv
  by_cases hEs : (W, E) = s
  · rw [← hEs] at hW
    exact ne_of_between hW rfl
  · exact hother _ hE hEs (Or.inl rfl)

/-- **Near a point strictly within a side, inside changes exactly across its straight line.**
On prescribed sides of finitely many straight lines, off the side's straight line N, two points
are inside together exactly when they are on one side of N. A good ray from one side to the
other, near the point, crosses that side and no other on the way. -/
theorem half_near {ps : List Point} (h : SimpleLoop ps) {s : Point × Point}
    (hs : s ∈ sides ps) {W : Point} (hW : Between s.1 W s.2) {N : Line}
    (h₁ : OnLine s.1 N) (h₂ : OnLine s.2 N) :
    ∃ cs : List (Point × Line), Sat cs W ∧
      (∀ Y, Sat cs Y → ¬ OnLine Y N → ¬ loopBoundary ps Y) ∧
      ∀ Y Y', Sat cs Y → Sat cs Y' → ¬ OnLine Y N → ¬ OnLine Y' N →
        ((loopInside ps Y ↔ loopInside ps Y') ↔ SameSide Y Y' N) := by
  classical
  have hWN : OnLine W N := on_line_of_between_ends hW h₁ h₂
  obtain ⟨hother, hWv⟩ := within_side h hs hW
  obtain ⟨cs, hWc, hcs⟩ := sep_all W ((sides ps).filter fun t => decide (t ≠ s)) fun t ht => by
    obtain ⟨ht, hts⟩ := List.mem_filter.mp ht
    exact ⟨h.2.2.1 t ht, hother t ht (by simpa using hts)⟩
  have hbd : ∀ Y, Sat cs Y → ¬ OnLine Y N → ¬ loopBoundary ps Y := by
    rintro Y hY hYN ⟨t, ht, hYt⟩
    by_cases hts : t = s
    · rw [hts] at hYt
      exact hYN (LoopFacts.onFiniteLine_onLine hYt h₁ h₂)
    · exact hcs Y hY t (List.mem_filter.mpr ⟨ht, by simpa using hts⟩) hYt
  /- On one side of N, inside does not change. -/
  have same : ∀ Y Y', Sat cs Y → Sat cs Y' → SameSide Y Y' N →
      (loopInside ps Y ↔ loopInside ps Y') := by
    intro Y Y' hY hY' hYY'
    refine inside_const h (cs := (Y, N) :: cs) ?_ ?_ ?_
    · intro P hP
      exact hbd P (fun c hc => hP c (List.mem_cons_of_mem _ hc))
        (not_on_line_of_same_side (hP (Y, N) List.mem_cons_self))
    · intro c hc
      rcases List.mem_cons.mp hc with e | hc
      · rw [e]
        exact same_side_refl (not_on_line_of_same_side hYY')
      · exact hY c hc
    · intro c hc
      rcases List.mem_cons.mp hc with e | hc
      · rw [e]
        exact same_side_symm hYY'
      · exact hY' c hc
  /- Two points on opposite sides, on a good ray through W, with different insides. -/
  obtain ⟨Y₁, Y₂, hY₁, hY₂, hY₁N, hY₂N, hopp, hdiff⟩ : ∃ Y₁ Y₂ : Point, Sat cs Y₁ ∧
      Sat cs Y₂ ∧ ¬ OnLine Y₁ N ∧ ¬ OnLine Y₂ N ∧ ¬ SameSide Y₁ Y₂ N ∧
      (loopInside ps Y₁ ↔ ¬ loopInside ps Y₂) := by
    obtain ⟨A, -, B, -, C, -, hABC⟩ := LoopFacts.simple_frame h
    let line (V : Point) : Line := Classical.choose (collinear_of_two W V)
    have hline (V : Point) : OnLine W (line V) ∧ OnLine V (line V) :=
      Classical.choose_spec (collinear_of_two W V)
    obtain ⟨R, -, hR⟩ := triangle_point_avoiding hABC (N :: ps.map line)
    have hRN : ¬ OnLine R N := hR N List.mem_cons_self
    have hWR : W ≠ R := fun e => hRN (e ▸ hWN)
    obtain ⟨ℓ, hWℓ, hRℓ⟩ := Postulate1 W R hWR
    have hoff : ∀ V ∈ ps, ¬ OnLine V ℓ := by
      intro V hV hVℓ
      have hWV : W ≠ V := fun e => hWv (e ▸ hV)
      apply hR (line V) (List.mem_cons_of_mem _ (List.mem_map_of_mem hV))
      rw [line_unique hWV (hline V).1 (hline V).2 hWℓ hVℓ]
      exact hRℓ
    obtain ⟨R', hRWR'⟩ := produce hWR.symm
    have hR'ℓ : OnLine R' ℓ := on_line_of_between hRWR' hRℓ hWℓ
    have hWR' : W ≠ R' := (ne_of_between (between_symm hRWR')).symm
    obtain ⟨Y₁, hWY₁R, hY₁⟩ := Avoid.shorten_sides hWR cs hWc
    obtain ⟨Y₂, hWY₂R', hY₂⟩ := Avoid.shorten_sides hWR' cs hWc
    have hR'WY₁ : Between R' W Y₁ := (OnRay.of_between hWY₁R).between (between_symm hRWR')
    have hY₁WY₂ : Between Y₁ W Y₂ := (OnRay.of_between hWY₂R').between (between_symm hR'WY₁)
    have hY₁ℓ : OnLine Y₁ ℓ := on_line_of_between_ends hWY₁R hWℓ hRℓ
    have hY₂ℓ : OnLine Y₂ ℓ := on_line_of_between_ends hWY₂R' hWℓ hR'ℓ
    have hℓN : ℓ ≠ N := fun e => hRN (e ▸ hRℓ)
    have hY₁N : ¬ OnLine Y₁ N := fun hY =>
      hℓN (line_unique (ne_of_between hWY₁R) hWℓ hY₁ℓ hWN hY)
    have hY₂N : ¬ OnLine Y₂ N := fun hY =>
      hℓN (line_unique (ne_of_between hWY₂R') hWℓ hY₂ℓ hWN hY)
    have hY₁Y₂ : Y₁ ≠ Y₂ := ne_of_between_ends hY₁WY₂
    obtain ⟨Q, hY₁Y₂Q⟩ := produce hY₁Y₂
    have hQℓ : OnLine Q ℓ := on_line_of_between hY₁Y₂Q hY₁ℓ hY₂ℓ
    have hg₁ : GoodRay ps Y₁ Y₂ := good_of_line hY₁Y₂ hY₁ℓ hY₂ℓ hoff
    have hg₂ : GoodRay ps Y₂ Q :=
      good_of_line (ne_of_between (between_symm hY₁Y₂Q)).symm hY₂ℓ hQℓ hoff
    have hb₁ := hbd Y₁ hY₁ hY₁N
    have hb₂ := hbd Y₂ hY₂ hY₂N
    have hsplit := count_split hY₁Y₂Q hY₁ℓ hY₂ℓ hoff hb₂
    have h1 : segCount ps Y₁ Y₂ = 1 := by
      unfold segCount
      refine LoopFacts.filter_length_one (LoopFacts.sides_nodup h.2.1) hs
        (by simp only [decide_eq_true_eq]; exact ⟨W, hY₁WY₂, hW⟩) fun t ht hqt => ?_
      refine Classical.byContradiction fun hts => ?_
      obtain ⟨P, hP, htP⟩ : SegCrosses Y₁ Y₂ t := by simpa using hqt
      exact hcs P (sat_between hY₁ hY₂ hP) t (List.mem_filter.mpr ⟨ht, by simpa using hts⟩)
        (Or.inr (Or.inr htP))
    refine ⟨Y₁, Y₂, hY₁, hY₂, hY₁N, hY₂N, pasch3 hY₁WY₂ hWN, ?_⟩
    rw [inside_iff h hb₁ hg₁, inside_iff h hb₂ hg₂, hsplit, h1]
    omega
  refine ⟨cs, hWc, hbd, fun Y Y' hY hY' hYN hY'N => ?_⟩
  by_cases hs' : SameSide Y Y' N
  · exact ⟨fun _ => hs', fun _ => same Y Y' hY hY' hs'⟩
  · refine iff_of_false (fun he => ?_) hs'
    rcases same_side_or hY₁N hY₂N hYN hopp with h₁ | h₁ <;>
      rcases same_side_or hY₁N hY₂N hY'N hopp with h₂ | h₂
    · exact hs' (same_side_trans h₁ h₂)
    · have e₁ := same Y₁ Y hY₁ hY h₁
      have e₂ := same Y₂ Y' hY₂ hY' h₂
      exact iff_not_self ((e₁.trans (he.trans e₂.symm)).symm.trans hdiff)
    · have e₁ := same Y₂ Y hY₂ hY h₁
      have e₂ := same Y₁ Y' hY₁ hY' h₂
      exact iff_not_self ((e₂.trans (he.symm.trans e₁.symm)).symm.trans hdiff)
    · exact hs' (same_side_trans h₁ h₂)

/-! ## Many contours: across a side of one -/

/-- **Across a side of one contour.** Near a point of one contour's boundary, on prescribed
sides of finitely many straight lines, there are two points off every contour's boundary, on
opposite sides of one side's straight line, one inside that contour and the other not, and
alike for every other contour. The point is moved strictly within a side, away from every
corner; there no other contour passes, since contours meet only at corners. -/
theorem boundary_witness {ls : List (List Point)} (hsimple : ∀ qs ∈ ls, SimpleLoop qs)
    {ps : List Point} (hps : ps ∈ ls)
    (hcontact : ∀ qs ∈ ls, qs ≠ ps → ∀ P, loopBoundary ps P → loopBoundary qs P →
      P ∈ ps ∨ P ∈ qs)
    {X : Point} (hX : loopBoundary ps X) {cs : List (Point × Line)} (hXc : Sat cs X) :
    ∃ Y Z : Point, Sat cs Y ∧ Sat cs Z ∧
      (∀ qs ∈ ls, ¬ loopBoundary qs Y ∧ ¬ loopBoundary qs Z) ∧
      (loopInside ps Y ↔ ¬ loopInside ps Z) ∧
      ∀ qs ∈ ls, qs ≠ ps → (loopInside qs Y ↔ loopInside qs Z) := by
  classical
  obtain ⟨s, hs, hXs⟩ := hX
  have h := hsimple ps hps
  have hne := h.2.2.1 s hs
  obtain ⟨W, hW, hWc, hWv⟩ := near_side hne hXs hXc ls.flatten
  have hWv' : ∀ qs ∈ ls, W ∉ qs := fun qs hq hWq => hWv (List.mem_flatten.mpr ⟨qs, hq, hWq⟩)
  have hoff : ∀ qs ∈ ls.filter (fun qs => decide (qs ≠ ps)),
      SimpleLoop qs ∧ ¬ loopBoundary qs W := by
    intro qs hq
    obtain ⟨hq, hqp⟩ := List.mem_filter.mp hq
    have hqp' : qs ≠ ps := by simpa using hqp
    refine ⟨hsimple qs hq, fun hb => ?_⟩
    rcases hcontact qs hq hqp' W ⟨s, hs, Or.inr (Or.inr hW)⟩ hb with e | e
    · exact hWv' ps hps e
    · exact hWv' qs hq e
  obtain ⟨N, h₁, h₂⟩ := Postulate1 s.1 s.2 hne
  have hWN : OnLine W N := on_line_of_between_ends hW h₁ h₂
  obtain ⟨cp, hWp, hbp, hinp⟩ := half_near h hs hW h₁ h₂
  obtain ⟨co, hWo, hco⟩ := const_near_all _ hoff
  obtain ⟨Y, Z, hY, hZ, hYN, hZN, hopp⟩ :=
    opposite_pair hWN (sat_append.mpr ⟨sat_append.mpr ⟨hWc, hWp⟩, hWo⟩)
  obtain ⟨hYcp, hYo⟩ := sat_append.mp hY
  obtain ⟨hYc, hYp⟩ := sat_append.mp hYcp
  obtain ⟨hZcp, hZo⟩ := sat_append.mp hZ
  obtain ⟨hZc, hZp⟩ := sat_append.mp hZcp
  have hmem : ∀ qs ∈ ls, qs ≠ ps → qs ∈ ls.filter (fun qs => decide (qs ≠ ps)) :=
    fun qs hq hqp => List.mem_filter.mpr ⟨hq, by simpa using hqp⟩
  refine ⟨Y, Z, hYc, hZc, fun qs hq => ?_, ?_, fun qs hq hqp => ?_⟩
  · by_cases hqp : qs = ps
    · rw [hqp]
      exact ⟨hbp Y hYp hYN, hbp Z hZp hZN⟩
    · exact ⟨(hco Y hYo qs (hmem qs hq hqp)).1, (hco Z hZo qs (hmem qs hq hqp)).1⟩
  · have hn : ¬ (loopInside ps Y ↔ loopInside ps Z) := fun e =>
      hopp ((hinp Y Z hYp hZp hYN hZN).mp e)
    exact iff_not_of_not_iff hn
  · exact (hco Y hYo qs (hmem qs hq hqp)).2.trans (hco Z hZo qs (hmem qs hq hqp)).2.symm

/-- **Near a point of one loop's boundary**, on prescribed sides, are a point inside it and a
point outside its region. -/
theorem near_boundary {ps : List Point} (h : SimpleLoop ps) {X : Point}
    (hX : loopBoundary ps X) {cs : List (Point × Line)} (hXc : Sat cs X) :
    ∃ Y Z : Point, Sat cs Y ∧ Sat cs Z ∧ loopInside ps Y ∧ ¬ loopRegion ps Z := by
  obtain ⟨Y, Z, hY, hZ, hbd, hdiff, -⟩ := boundary_witness (ls := [ps])
    (fun qs hq => (List.mem_singleton.mp hq) ▸ h) List.mem_cons_self
    (fun qs hq hqp => absurd (List.mem_singleton.mp hq) hqp) hX hXc
  obtain ⟨hbY, hbZ⟩ := hbd ps List.mem_cons_self
  by_cases hiY : loopInside ps Y
  · exact ⟨Y, Z, hY, hZ, hiY, fun hr => hdiff.mp hiY (hr.resolve_left hbZ)⟩
  · have hiZ : loopInside ps Z := Classical.byContradiction fun hiZ => hiY (hdiff.mpr hiZ)
    exact ⟨Z, Y, hZ, hY, hiZ, fun hr => hiY (hr.resolve_left hbY)⟩

/-! ## Counting contours -/

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

/-- No simple loop is compatible with itself: a point strictly within a side, away from the
corners, is on its boundary twice over. -/
theorem not_compatible_self {ps : List Point} (h : SimpleLoop ps) : ¬ CompatibleLoops ps ps := by
  intro hc
  obtain ⟨V, hV⟩ := exists_vertex h
  obtain ⟨E, hE⟩ := outgoing_side hV
  obtain ⟨L, hVL, hEL⟩ := Postulate1 V E (h.2.2.1 _ hE)
  obtain ⟨W, -, hW, hWps⟩ := exists_point_between hVL hEL (h.2.2.1 _ hE) ps
  have hb : loopBoundary ps W := ⟨(V, E), hE, Or.inr (Or.inr hW)⟩
  rcases hc.1 W hb hb with e | e <;> exact hWps e

/-- **The contours of a figure are different.** -/
theorem loops_nodup (F : Outline) : F.loops.Nodup :=
  F.compatible.imp_of_mem fun {a _} ha _ hab e => by
    subst e
    exact not_compatible_self (F.simple a ha) hab

/-- Two contours of a figure meet only at corners. -/
theorem outline_contact (F : Outline) {ps : List Point} (hps : ps ∈ F.loops) :
    ∀ qs ∈ F.loops, qs ≠ ps → ∀ P, loopBoundary ps P → loopBoundary qs P →
      P ∈ ps ∨ P ∈ qs := by
  intro qs hqs hqp P hp hq
  rcases LoopFacts.pairwise_mem F.compatible hps hqs with e | hc | hc
  · exact absurd e.symm hqp
  · exact hc.1 P hp hq
  · exact (hc.1 P hq hp).symm

/-- Off the boundary, the region is odd depth. -/
theorem region_off {F : Outline} {X : Point} (hX : ¬ F.boundary X) :
    F.region X ↔ F.depth X % 2 = 1 := by
  unfold Outline.region Outline.inside
  simp only [hX, false_or, not_false_eq_true, true_and]

/-- Two points off the boundary, inside the same contours, are in the region together. -/
theorem region_congr (F : Outline) {X U : Point} (hX : ¬ F.boundary X)
    (h : ∀ qs ∈ F.loops, ¬ loopBoundary qs U ∧ (loopInside qs U ↔ loopInside qs X)) :
    F.region U ↔ F.region X := by
  classical
  have hU : ¬ F.boundary U := fun ⟨qs, hq, hb⟩ => (h qs hq).1 hb
  have hd : F.depth U = F.depth X := by
    unfold Outline.depth
    congr 1
    exact List.filter_congr fun qs hq => by
      simp only [decide_eq_decide]
      exact (h qs hq).2
  rw [region_off hU, region_off hX, hd]

/-- **On a contour, every triangle about the point meets the region and its complement.**
The point itself is in the region; near it, across a side of its contour, the depth changes
parity, so one of two nearby points off the boundary is outside. -/
theorem boundary_regionBoundary (F : Outline) {X : Point} (hX : F.boundary X) :
    RegionBoundary F.region X := by
  classical
  obtain ⟨ps, hps, hXp⟩ := hX
  intro A B C _ hABC
  obtain ⟨cs, hXc, hcs⟩ := tri_sat hABC
  obtain ⟨Y, Z, hY, hZ, hbd, hdiff, hsame⟩ :=
    boundary_witness F.simple hps (outline_contact F hps) hXp hXc
  have hpar : (F.depth Y + F.depth Z) % 2 = 1 := by
    unfold Outline.depth
    refine count_flip _ _ _ (loops_nodup F) hps ?_ ?_
    · by_cases hz : loopInside ps Z
      · have hy : ¬ loopInside ps Y := fun hy => hdiff.mp hy hz
        simp [hy, hz]
      · have hy : loopInside ps Y := hdiff.mpr hz
        simp [hy, hz]
    · intro qs hq hqp
      simp only [decide_eq_decide]
      exact hsame qs hq hqp
  have offY : ¬ F.boundary Y := fun ⟨qs, hq, hb⟩ => (hbd qs hq).1 hb
  have offZ : ¬ F.boundary Z := fun ⟨qs, hq, hb⟩ => (hbd qs hq).2 hb
  have hXr : F.region X := Or.inl ⟨ps, hps, hXp⟩
  by_cases hYe : F.depth Y % 2 = 1
  · refine ⟨X, Z, hABC, hcs Z hZ, hXr, fun hr => ?_⟩
    have := (region_off offZ).mp hr
    omega
  · exact ⟨X, Y, hABC, hcs Y hY, hXr, fun hr => hYe ((region_off offY).mp hr)⟩

/-- **Off the contours, some triangle about the point lies wholly in the region or wholly
outside it**: near the point no contour's inside changes. -/
theorem not_regionBoundary (F : Outline) {X : Point} (hX : ¬ F.boundary X) :
    ¬ RegionBoundary F.region X := by
  intro hR
  have hoff : ∀ qs ∈ F.loops, SimpleLoop qs ∧ ¬ loopBoundary qs X :=
    fun qs hq => ⟨F.simple qs hq, fun hb => hX ⟨qs, hq, hb⟩⟩
  obtain ⟨cs, hXc, hcs⟩ := const_near_all F.loops hoff
  obtain ⟨A, B, C, hABC, hcl⟩ := small_triangle cs hXc
  obtain ⟨Y, Z, hY, hZ, hrY, hrZ⟩ := hR A B C hABC.1.symm.triangle.cab hABC
  have key : ∀ U, Sat cs U → (F.region U ↔ F.region X) :=
    fun U hU => region_congr F hX (hcs U hU)
  exact hrZ ((key Z (hcl Z (Or.inl hZ))).mpr ((key Y (hcl Y (Or.inl hY))).mp hrY))

/-- **One outer contour with unnested holes.** On the boundary, a point is in the outer
region, a hole's boundary lying in it, and is inside no hole: inside is unchanged near it,
while near a point of a hole's boundary are points inside that hole, and near a point of the
outer contour are points outside the outer region. Off the boundary, the depth counts the
outer contour and at most one hole. -/
theorem region_holes (F : Outline) (outer : List Point) (holes : List (List Point))
    (hl : F.loops = outer :: holes)
    (hin : ∀ ps ∈ holes, ∀ X : Point, loopRegion ps X → loopRegion outer X)
    (hapart : holes.Pairwise (fun ps qs =>
      ∀ X : Point, loopInside ps X → ¬ loopInside qs X))
    (X : Point) :
    F.region X ↔ loopRegion outer X ∧ ∀ ps ∈ holes, ¬ loopInside ps X := by
  classical
  have hsimple : ∀ ps ∈ outer :: holes, SimpleLoop ps := by
    rw [← hl]
    exact F.simple
  have hout : SimpleLoop outer := hsimple outer List.mem_cons_self
  have hhole : ∀ ps ∈ holes, SimpleLoop ps :=
    fun ps hps => hsimple ps (List.mem_cons_of_mem _ hps)
  have hbF : F.boundary X ↔ loopBoundary outer X ∨ ∃ ps ∈ holes, loopBoundary ps X := by
    unfold Outline.boundary
    rw [hl]
    simp only [List.mem_cons, exists_eq_or_imp]
  by_cases hb : F.boundary X
  · refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => Or.inl hb⟩
    · rcases hbF.mp hb with h | ⟨ps, hps, h⟩
      · exact Or.inl h
      · exact hin ps hps X (Or.inl h)
    · intro ps hps hiX
      obtain ⟨cs, hXc, hcs⟩ := const_near (hhole ps hps) hiX.1
      rcases hbF.mp hb with hq | ⟨qs, hqs, hq⟩
      · obtain ⟨Y, Z, -, hZ, -, hrZ⟩ := near_boundary hout hq hXc
        exact hrZ (hin ps hps Z (Or.inr ((hcs Z hZ).2.mpr hiX)))
      · by_cases hqp : qs = ps
        · rw [hqp] at hq
          exact hiX.1 hq
        · obtain ⟨Y, Z, hY, -, hiY, -⟩ := near_boundary (hhole qs hqs) hq hXc
          have hiY' : loopInside ps Y := (hcs Y hY).2.mpr hiX
          rcases LoopFacts.pairwise_mem hapart hps hqs with e | hd | hd
          · exact hqp e.symm
          · exact hd Y hiY' hiY
          · exact hd Y hiY hiY'
  · have hbo : ¬ loopBoundary outer X := fun h => hb (hbF.mpr (Or.inl h))
    have hdepth : F.depth X = (if loopInside outer X then 1 else 0) +
        (holes.filter fun ps => decide (loopInside ps X)).length := by
      unfold Outline.depth
      rw [hl]
      by_cases hio : loopInside outer X <;> simp [hio] <;> omega
    rw [region_off hb, hdepth]
    by_cases hh : ∃ ps ∈ holes, loopInside ps X
    · obtain ⟨ps, hps, hiX⟩ := hh
      have hio : loopInside outer X := inside_iff_region.mpr ⟨hin ps hps X (Or.inr hiX), hbo⟩
      have hle := count_le_one (fun ps => decide (loopInside ps X)) holes
        (hapart.imp fun {a b} hab ⟨ha, hb⟩ => hab X (by simpa using ha) (by simpa using hb))
      have hpos : 0 < (holes.filter fun ps => decide (loopInside ps X)).length :=
        List.length_pos_of_mem (List.mem_filter.mpr ⟨hps, by simpa using hiX⟩)
      simp only [hio, ↓reduceIte]
      exact iff_of_false (by omega) fun ⟨_, h⟩ => h ps hps hiX
    · have hh' : ∀ ps ∈ holes, ¬ loopInside ps X := fun ps hps h => hh ⟨ps, hps, h⟩
      have hzero : (holes.filter fun ps => decide (loopInside ps X)).length = 0 := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro ps hps
        simpa using hh' ps hps
      rw [hzero]
      by_cases hio : loopInside outer X
      · simp only [hio, ↓reduceIte]
        exact iff_of_true trivial ⟨Or.inr hio, hh'⟩
      · simp only [hio, ↓reduceIte]
        exact iff_of_false (by decide) fun ⟨hr, _⟩ => hio (inside_iff_region.mpr ⟨hr, hbo⟩)

/-! ## The crossings of one good ray, as points of the boundary -/

/-- The point where a ray crosses a side, if it does. -/
noncomputable def crossPt (X Q : Point) (t : Point × Point) : Option Point := by
  classical
  exact if h : RayCrosses X Q t then some (Classical.choose h) else none

theorem crossPt_some {X Q P : Point} {t : Point × Point} (h : crossPt X Q t = some P) :
    OnRay P X Q ∧ Between t.1 P t.2 := by
  classical
  unfold crossPt at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    exact Classical.choose_spec hc
  · exact absurd h (by simp)

theorem crossPt_isSome {X Q : Point} {t : Point × Point} :
    (crossPt X Q t).isSome ↔ RayCrosses X Q t := by
  classical
  unfold crossPt
  split
  · rename_i hc
    exact iff_of_true rfl hc
  · rename_i hc
    exact iff_of_false (by simp) hc

/-- A side with an end off a straight line meets it at one point at most. -/
theorem cross_unique {P P' : Point} {ℓ : Line} {t : Point × Point} (ht : ¬ OnLine t.1 ℓ)
    (hP : OnLine P ℓ) (hP' : OnLine P' ℓ) (h₁ : Between t.1 P t.2) (h₂ : Between t.1 P' t.2) :
    P = P' := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨N, hN₁, hN₂⟩ := Postulate1 t.1 t.2 (ne_of_between_ends h₁)
  exact ht ((line_unique hne hP hP' (on_line_of_between_ends h₁ hN₁ hN₂)
    (on_line_of_between_ends h₂ hN₁ hN₂)) ▸ hN₁)

theorem crossPt_eq {X Q P : Point} {ℓ : Line} (hXℓ : OnLine X ℓ) (hQℓ : OnLine Q ℓ)
    {t : Point × Point} (ht : ¬ OnLine t.1 ℓ) (hP : OnRay P X Q) (hb : Between t.1 P t.2) :
    crossPt X Q t = some P := by
  obtain ⟨P', hP'⟩ := Option.isSome_iff_exists.mp (crossPt_isSome.mpr ⟨P, hP, hb⟩)
  obtain ⟨hr, hb'⟩ := crossPt_some hP'
  rw [hP', cross_unique ht (hr.onLine hXℓ hQℓ) (hP.onLine hXℓ hQℓ) hb' hb]

/-- The crossing points of a loop are as many as its crossings. -/
theorem crossPts_length (ps : List Point) (X Q : Point) :
    ((sides ps).filterMap (crossPt X Q)).length = crossingCount ps X Q := by
  classical
  unfold crossingCount
  rw [List.length_filterMap_eq_countP, List.countP_eq_length_filter]
  congr 1
  exact List.filter_congr fun t _ => Bool.eq_iff_iff.mpr (by
    rw [crossPt_isSome]
    simp)

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

/-- The number of members with an odd count has the parity of the total count. -/
theorem count_odd_sum {α : Type} (c : α → Nat) : ∀ l : List α,
    (l.filter fun a => decide (c a % 2 = 1)).length % 2 = (l.map c).sum % 2
  | [] => rfl
  | a :: l => by
    have ih := count_odd_sum c l
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases h : c a % 2 = 1
    · simp only [h, decide_true, ↓reduceIte, List.length_cons]
      omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      omega

/-- **One good ray for a whole figure.** Along a straight line through no corner of any
contour, the crossing points of all the contours, listed contour by contour, are without
repetition, and are exactly the points of the ray on the boundary; their number has the parity
of the depth. A crossing point is strictly within its side, so on no other side of its
contour, and on no other contour, which it could meet only at a corner. -/
theorem family_count (K : Outline) {X Q : Point} {ℓ : Line} (hXQ : X ≠ Q) (hXℓ : OnLine X ℓ)
    (hQℓ : OnLine Q ℓ) (hK : ∀ ps ∈ K.loops, ∀ V ∈ ps, ¬ OnLine V ℓ)
    (hX : ¬ K.boundary X) :
    K.depth X % 2 = (K.loops.flatMap fun ps => (sides ps).filterMap (crossPt X Q)).length % 2 ∧
      (∀ P, P ∈ (K.loops.flatMap fun ps => (sides ps).filterMap (crossPt X Q)) ↔
        OnRay P X Q ∧ K.boundary P) ∧
      (K.loops.flatMap fun ps => (sides ps).filterMap (crossPt X Q)).Nodup := by
  classical
  have hgood : ∀ ps ∈ K.loops, GoodRay ps X Q :=
    fun ps hps => good_of_line hXQ hXℓ hQℓ (hK ps hps)
  have hoffX : ∀ ps ∈ K.loops, ¬ loopBoundary ps X := fun ps hps hb => hX ⟨ps, hps, hb⟩
  refine ⟨?_, fun P => ?_, ?_⟩
  · have hd : K.depth X =
        (K.loops.filter fun ps => decide (crossingCount ps X Q % 2 = 1)).length := by
      unfold Outline.depth
      congr 1
      exact List.filter_congr fun ps hps => by
        simp only [decide_eq_decide]
        exact inside_iff (K.simple ps hps) (hoffX ps hps) (hgood ps hps)
    rw [hd, count_odd_sum, List.length_flatMap]
    congr 2
    exact List.map_congr_left fun ps _ => (crossPts_length ps X Q).symm
  · constructor
    · intro hP
      obtain ⟨ps, hps, hP⟩ := List.mem_flatMap.mp hP
      obtain ⟨t, ht, hPt⟩ := List.mem_filterMap.mp hP
      obtain ⟨hr, hb⟩ := crossPt_some hPt
      exact ⟨hr, ps, hps, t, ht, Or.inr (Or.inr hb)⟩
    · rintro ⟨hr, ps, hps, t, ht, hPt⟩
      have hPℓ : OnLine P ℓ := hr.onLine hXℓ hQℓ
      have h₁ : ¬ OnLine t.1 ℓ := hK ps hps _ (LoopFacts.side_mem ht).1
      have h₂ : ¬ OnLine t.2 ℓ := hK ps hps _ (LoopFacts.side_mem ht).2
      have hb : Between t.1 P t.2 := by
        rcases hPt with e | e | hb
        · exact absurd (e ▸ hPℓ) h₁
        · exact absurd (e ▸ hPℓ) h₂
        · exact hb
      exact List.mem_flatMap.mpr ⟨ps, hps,
        List.mem_filterMap.mpr ⟨t, ht, crossPt_eq hXℓ hQℓ h₁ hr hb⟩⟩
  · refine nodup_flatMap_of _ _ (fun ps hps => ?_) ?_
    · refine nodup_filterMap_of _ _ ?_
      refine (LoopFacts.sides_nodup (K.simple ps hps).2.1).imp_of_mem ?_
      intro a b ha hb hab x hxa hxb
      obtain ⟨-, hxa'⟩ := crossPt_some hxa
      obtain ⟨-, hxb'⟩ := crossPt_some hxb
      rcases (Parity.side_meet (K.simple ps hps) ha hb hab x (Or.inr (Or.inr hxa'))
          (Or.inr (Or.inr hxb'))).1 with e | e
      · exact ne_of_between hxa' e.symm
      · exact ne_of_between (between_symm hxa') e.symm
    · refine K.compatible.imp_of_mem ?_
      intro ps qs hps hqs hc x hx hx'
      obtain ⟨t, ht, htx⟩ := List.mem_filterMap.mp hx
      obtain ⟨u, hu, hux⟩ := List.mem_filterMap.mp hx'
      obtain ⟨hr, hbt⟩ := crossPt_some htx
      obtain ⟨-, hbu⟩ := crossPt_some hux
      have hxℓ : OnLine x ℓ := hr.onLine hXℓ hQℓ
      rcases hc.1 x ⟨t, ht, Or.inr (Or.inr hbt)⟩ ⟨u, hu, Or.inr (Or.inr hbu)⟩ with e | e
      · exact hK ps hps x e hxℓ
      · exact hK qs hqs x e hxℓ

/-- **The same boundary, the same depth parity.** One good ray, through no corner of either
description, crosses the boundary at the same points; each description counts each of them
once. -/
theorem depth_parity_eq (F G : Outline) (h : ∀ X, F.boundary X ↔ G.boundary X) {X : Point}
    (hX : ¬ F.boundary X) : F.depth X % 2 = G.depth X % 2 := by
  have hXG : ¬ G.boundary X := fun hg => hX ((h X).mpr hg)
  let vs : List Point := F.loops.flatten ++ G.loops.flatten
  have hXv : ∀ V ∈ vs, X ≠ V := by
    intro V hV e
    rcases List.mem_append.mp hV with hV | hV
    · obtain ⟨ps, hps, hVp⟩ := List.mem_flatten.mp hV
      exact hX ⟨ps, hps, e ▸ vertex_boundary hVp⟩
    · obtain ⟨ps, hps, hVp⟩ := List.mem_flatten.mp hV
      exact hXG ⟨ps, hps, e ▸ vertex_boundary hVp⟩
  obtain ⟨ps₀, hps₀⟩ : ∃ ps, ps ∈ F.loops := List.exists_mem_of_ne_nil _ F.ne
  obtain ⟨A, -, B, -, C, -, hABC⟩ := LoopFacts.simple_frame (F.simple ps₀ hps₀)
  let line (V : Point) : Line := Classical.choose (collinear_of_two X V)
  have hline (V : Point) : OnLine X (line V) ∧ OnLine V (line V) :=
    Classical.choose_spec (collinear_of_two X V)
  obtain ⟨L₀, hXL₀⟩ := exists_line_through X
  obtain ⟨Q, -, hQ⟩ := triangle_point_avoiding hABC (L₀ :: vs.map line)
  have hXQ : X ≠ Q := fun e => hQ L₀ List.mem_cons_self (e ▸ hXL₀)
  obtain ⟨ℓ, hXℓ, hQℓ⟩ := Postulate1 X Q hXQ
  have hoff : ∀ V ∈ vs, ¬ OnLine V ℓ := by
    intro V hV hVℓ
    apply hQ (line V) (List.mem_cons_of_mem _ (List.mem_map_of_mem hV))
    rw [line_unique (hXv V hV) (hline V).1 (hline V).2 hXℓ hVℓ]
    exact hQℓ
  have hF : ∀ ps ∈ F.loops, ∀ V ∈ ps, ¬ OnLine V ℓ := fun ps hps V hV =>
    hoff V (List.mem_append_left _ (List.mem_flatten.mpr ⟨ps, hps, hV⟩))
  have hG : ∀ ps ∈ G.loops, ∀ V ∈ ps, ¬ OnLine V ℓ := fun ps hps V hV =>
    hoff V (List.mem_append_right _ (List.mem_flatten.mpr ⟨ps, hps, hV⟩))
  obtain ⟨dF, mF, nF⟩ := family_count F hXQ hXℓ hQℓ hF hX
  obtain ⟨dG, mG, nG⟩ := family_count G hXQ hXℓ hQℓ hG hXG
  have hperm := (List.perm_ext_iff_of_nodup nF nG).mpr fun P => by
    rw [mF, mG, h P]
  rw [dF, dG, hperm.length_eq]

/-! ## Contacts survive normalisation -/

/-- Two finite straight lines on one straight line, each with a given point strictly within
it, share a point strictly within both, other than finitely many given points: go from the
given point towards the nearer of two ends on one side of it. -/
theorem common_point {a₁ a₂ b₁ b₂ X : Point} {N : Line} (ha₁ : OnLine a₁ N)
    (hb₁ : OnLine b₁ N) (hb₂ : OnLine b₂ N) (ha : Between a₁ X a₂) (hb : Between b₁ X b₂)
    (avoid : List Point) : ∃ Y, Between a₁ Y a₂ ∧ Between b₁ Y b₂ ∧ Y ∉ avoid := by
  have near : ∀ {c d Y : Point}, Between c X d → Between X Y c → Between c Y d :=
    fun hcd hY => between_of_between_left hcd (between_symm hY)
  have hXN : OnLine X N := on_line_of_between_ends hb hb₁ hb₂
  have ha₁X : a₁ ≠ X := ne_of_between ha
  have key : ∀ {b b' : Point}, Between b X b' → OnLine b N → OnRay a₁ X b →
      ∃ Y, Between a₁ Y a₂ ∧ Between b Y b' ∧ Y ∉ avoid := by
    intro b b' hbb' hbN hray
    have hXb : X ≠ b := hray.1
    by_cases e : a₁ = b
    · subst e
      obtain ⟨Y, -, hY, hYav⟩ := exists_point_between hXN ha₁ ha₁X.symm avoid
      exact ⟨Y, near ha hY, near hbb' hY, hYav⟩
    rcases between_cases ha₁X.symm e hXb hXN ha₁ hbN with h | h | h
    · obtain ⟨Y, -, hY, hYav⟩ := exists_point_between hXN ha₁ ha₁X.symm avoid
      exact ⟨Y, near ha hY, near hbb' (between_of_between_left h hY), hYav⟩
    · exact absurd h hray.2.2.2
    · obtain ⟨Y, -, hY, hYav⟩ := exists_point_between hXN hbN hXb avoid
      exact ⟨Y, near ha (between_of_between_left h hY), near hbb' hY, hYav⟩
  rcases OnRay.cases_of_between hb hb₁ hb₂ ha₁ ha₁X with h | h
  · exact key hb hb₁ h
  · obtain ⟨Y, h₁, h₂, h₃⟩ := key (between_symm hb) hb₂ h
    exact ⟨Y, h₁, between_symm h₂, h₃⟩

/-- **A point in a chosen quarter.** Near a point where two straight lines cross, on
prescribed sides, there is a point on the side of the first straight line where a given point
of the second is, and on the side of the second where a given point of the first is. -/
theorem quadrant {X α β : Point} {N M : Line} (hXN : OnLine X N) (hXM : OnLine X M)
    (hαM : OnLine α M) (hαN : ¬ OnLine α N) (hβN : OnLine β N) (hβM : ¬ OnLine β M)
    {cs : List (Point × Line)} (hX : Sat cs X) :
    ∃ Y, Sat cs Y ∧ SameSide Y α N ∧ SameSide Y β M := by
  have hαβ : α ≠ β := fun e => hαN (e ▸ hβN)
  obtain ⟨L, hαL, hβL⟩ := Postulate1 α β hαβ
  obtain ⟨D, -, hαDβ, -⟩ := exists_point_between hαL hβL hαβ []
  have hDN : ¬ OnLine D N := fun h => hαN (on_line_of_between (between_symm hαDβ) hβN h)
  have hDM : ¬ OnLine D M := fun h => hβM (on_line_of_between hαDβ hαM h)
  have hDα : SameSide D α N := pasch2 (between_symm hαDβ) hβN hDN
  have hDβ : SameSide D β M := pasch2 hαDβ hαM hDM
  have hXD : X ≠ D := fun e => hDN (e ▸ hXN)
  obtain ⟨Y, hXYD, hY⟩ := Avoid.shorten_sides hXD cs hX
  have hYN : ¬ OnLine Y N := fun h => hDN (on_line_of_between hXYD hXN h)
  have hYM : ¬ OnLine Y M := fun h => hDM (on_line_of_between hXYD hXM h)
  exact ⟨Y, hY, same_side_trans (same_side_symm (pasch2 hXYD hXN hYN)) hDα,
    same_side_trans (same_side_symm (pasch2 hXYD hXM hYM)) hDβ⟩

/-- Four quarters, the first test fixed by the row and changing between rows, the second fixed
by the column and changing between columns: every combination of the two tests occurs. -/
theorem four_quarters {p₁₁ p₁₂ p₂₁ p₂₂ q₁₁ q₁₂ q₂₁ q₂₂ : Prop}
    (hp₁ : p₁₁ ↔ p₁₂) (hp₂ : p₂₁ ↔ p₂₂) (hp : p₁₁ ↔ ¬ p₂₁)
    (hq₁ : q₁₁ ↔ q₂₁) (hq₂ : q₁₂ ↔ q₂₂) (hq : q₁₁ ↔ ¬ q₁₂) :
    ((p₁₁ ∧ q₁₁) ∨ (p₁₂ ∧ q₁₂) ∨ (p₂₁ ∧ q₂₁) ∨ (p₂₂ ∧ q₂₂)) ∧
      ((p₁₁ ∧ ¬ q₁₁) ∨ (p₁₂ ∧ ¬ q₁₂) ∨ (p₂₁ ∧ ¬ q₂₁) ∨ (p₂₂ ∧ ¬ q₂₂)) ∧
      ((¬ p₁₁ ∧ q₁₁) ∨ (¬ p₁₂ ∧ q₁₂) ∨ (¬ p₂₁ ∧ q₂₁) ∨ (¬ p₂₂ ∧ q₂₂)) := by
  by_cases a : p₁₁ <;> by_cases b : q₁₁
  · have a₂ : ¬ p₂₁ := hp.mp a
    have b₂ : ¬ q₁₂ := hq.mp b
    exact ⟨Or.inl ⟨a, b⟩, Or.inr (Or.inl ⟨hp₁.mp a, b₂⟩),
      Or.inr (Or.inr (Or.inl ⟨a₂, hq₁.mp b⟩))⟩
  · have a₂ : ¬ p₂₁ := hp.mp a
    have b₂ : q₁₂ := Classical.byContradiction fun h => b (hq.mpr h)
    exact ⟨Or.inr (Or.inl ⟨hp₁.mp a, b₂⟩), Or.inl ⟨a, b⟩,
      Or.inr (Or.inr (Or.inr ⟨fun h => a₂ (hp₂.mpr h), hq₂.mp b₂⟩))⟩
  · have a₂ : p₂₁ := Classical.byContradiction fun h => a (hp.mpr h)
    have b₂ : ¬ q₁₂ := hq.mp b
    exact ⟨Or.inr (Or.inr (Or.inl ⟨a₂, hq₁.mp b⟩)),
      Or.inr (Or.inr (Or.inr ⟨hp₂.mp a₂, fun h => b₂ (hq₂.mpr h)⟩)), Or.inl ⟨a, b⟩⟩
  · have a₂ : p₂₁ := Classical.byContradiction fun h => a (hp.mpr h)
    have b₂ : q₁₂ := Classical.byContradiction fun h => b (hq.mpr h)
    exact ⟨Or.inr (Or.inr (Or.inr ⟨hp₂.mp a₂, hq₂.mp b₂⟩)),
      Or.inr (Or.inr (Or.inl ⟨a₂, fun h => b (hq₁.mpr h)⟩)),
      Or.inr (Or.inl ⟨fun h => a (hp₁.mpr h), b₂⟩)⟩

/-- A point of a loop's boundary that is not a corner is strictly within a side. -/
theorem strictly_within {ps : List Point} {X : Point} (hX : loopBoundary ps X) (hXv : X ∉ ps) :
    ∃ s ∈ sides ps, Between s.1 X s.2 := by
  obtain ⟨s, hs, hXs⟩ := hX
  rcases hXs with e | e | hb
  · exact absurd (e ▸ (LoopFacts.side_mem hs).1) hXv
  · exact absurd (e ▸ (LoopFacts.side_mem hs).2) hXv
  · exact ⟨s, hs, hb⟩

/-- **Contacts are at corners.** Two simple loops with disjoint or nested insides, whose
boundaries meet in finitely many points, meet only at a corner of one of them. At a point
strictly within a side of each, the two sides lie on one straight line and share infinitely
many points, or the straight lines cross, and near the point all four combinations of inside
and outside occur, which neither disjoint nor nested insides allow. -/
theorem contact_vertex {P Q : List Point} (hP : SimpleLoop P) (hQ : SimpleLoop Q)
    (hc : (∀ X, loopInside P X → ¬ loopInside Q X) ∨ (∀ X, loopRegion P X → loopRegion Q X) ∨
      (∀ X, loopRegion Q X → loopRegion P X))
    {L : List Point} (hfin : ∀ Y, loopBoundary P Y → loopBoundary Q Y → Y ∈ L)
    {X : Point} (hXP : loopBoundary P X) (hXQ : loopBoundary Q X) : X ∈ P ∨ X ∈ Q := by
  refine Classical.byContradiction fun hn => ?_
  rw [not_or] at hn
  obtain ⟨u, hu, hbu⟩ := strictly_within hXP hn.1
  obtain ⟨v, hv, hbv⟩ := strictly_within hXQ hn.2
  obtain ⟨N, hu₁, hu₂⟩ := Postulate1 u.1 u.2 (hP.2.2.1 u hu)
  obtain ⟨M, hv₁, hv₂⟩ := Postulate1 v.1 v.2 (hQ.2.2.1 v hv)
  have hXN : OnLine X N := on_line_of_between_ends hbu hu₁ hu₂
  have hXM : OnLine X M := on_line_of_between_ends hbv hv₁ hv₂
  by_cases hMN : M = N
  · /- One straight line: the sides overlap. -/
    rw [hMN] at hv₁ hv₂
    obtain ⟨Y, hYu, hYv, hYL⟩ := common_point hu₁ hv₁ hv₂ hbu hbv L
    exact hYL (hfin Y ⟨u, hu, Or.inr (Or.inr hYu)⟩ ⟨v, hv, Or.inr (Or.inr hYv)⟩)
  /- Two straight lines crossing at X. -/
  have offN : ∀ {Y : Point}, OnLine Y M → Y ≠ X → ¬ OnLine Y N := fun hYM hYX hYN =>
    hMN (line_unique hYX hYM hXM hYN hXN)
  have offM : ∀ {Y : Point}, OnLine Y N → Y ≠ X → ¬ OnLine Y M := fun hYN hYX hYM =>
    hMN (line_unique hYX hYM hXM hYN hXN)
  have hv₁N := offN hv₁ (ne_of_between hbv)
  have hv₂N := offN hv₂ (ne_of_between (between_symm hbv))
  have hu₁M := offM hu₁ (ne_of_between hbu)
  have hu₂M := offM hu₂ (ne_of_between (between_symm hbu))
  have hoppN : ¬ SameSide v.1 v.2 N := pasch3 hbv hXN
  have hoppM : ¬ SameSide u.1 u.2 M := pasch3 hbu hXM
  obtain ⟨cP, hXcP, hbP, hinP⟩ := half_near hP hu hbu hu₁ hu₂
  obtain ⟨cQ, hXcQ, hbQ, hinQ⟩ := half_near hQ hv hbv hv₁ hv₂
  have q : ∀ {α β : Point}, OnLine α M → ¬ OnLine α N → OnLine β N → ¬ OnLine β M →
      ∃ Y, Sat cP Y ∧ Sat cQ Y ∧ SameSide Y α N ∧ SameSide Y β M := by
    intro α β hαM hαN hβN hβM
    obtain ⟨Y, hY, hYα, hYβ⟩ := quadrant hXN hXM hαM hαN hβN hβM (sat_append.mpr ⟨hXcP, hXcQ⟩)
    exact ⟨Y, (sat_append.mp hY).1, (sat_append.mp hY).2, hYα, hYβ⟩
  obtain ⟨Y₁₁, hP₁₁, hQ₁₁, hN₁₁, hM₁₁⟩ := q hv₁ hv₁N hu₁ hu₁M
  obtain ⟨Y₁₂, hP₁₂, hQ₁₂, hN₁₂, hM₁₂⟩ := q hv₁ hv₁N hu₂ hu₂M
  obtain ⟨Y₂₁, hP₂₁, hQ₂₁, hN₂₁, hM₂₁⟩ := q hv₂ hv₂N hu₁ hu₁M
  obtain ⟨Y₂₂, hP₂₂, hQ₂₂, hN₂₂, hM₂₂⟩ := q hv₂ hv₂N hu₂ hu₂M
  have same : ∀ {Y Y' α : Point} {K : Line}, SameSide Y α K → SameSide Y' α K →
      SameSide Y Y' K := fun h₁ h₂ => same_side_trans (same_side_symm h₁) (same_side_symm h₂)
  have opp : ∀ {Y Y' α α' : Point} {K : Line}, SameSide Y α K → SameSide Y' α' K →
      ¬ SameSide α α' K → ¬ SameSide Y Y' K := fun h₁ h₂ hn hs =>
    hn (same_side_trans (same_side_trans hs h₁) h₂)
  have off : ∀ {Y α : Point} {K : Line}, SameSide Y α K → ¬ OnLine Y K :=
    fun h => not_on_line_of_same_side h
  have pr : ∀ {Y Y' : Point}, Sat cP Y → Sat cP Y' → SameSide Y Y' N →
      (loopInside P Y ↔ loopInside P Y') := fun hY hY' hs =>
    (hinP _ _ hY hY' (off hs) (off (same_side_symm hs))).mpr hs
  have pn : ∀ {Y Y' : Point}, Sat cP Y → Sat cP Y' → ¬ OnLine Y N → ¬ OnLine Y' N →
      ¬ SameSide Y Y' N → (loopInside P Y ↔ ¬ loopInside P Y') := fun hY hY' h₁ h₂ hs =>
    iff_not_of_not_iff fun e => hs ((hinP _ _ hY hY' h₁ h₂).mp e)
  have qr : ∀ {Y Y' : Point}, Sat cQ Y → Sat cQ Y' → SameSide Y Y' M →
      (loopInside Q Y ↔ loopInside Q Y') := fun hY hY' hs =>
    (hinQ _ _ hY hY' (off hs) (off (same_side_symm hs))).mpr hs
  have qn : ∀ {Y Y' : Point}, Sat cQ Y → Sat cQ Y' → ¬ OnLine Y M → ¬ OnLine Y' M →
      ¬ SameSide Y Y' M → (loopInside Q Y ↔ ¬ loopInside Q Y') := fun hY hY' h₁ h₂ hs =>
    iff_not_of_not_iff fun e => hs ((hinQ _ _ hY hY' h₁ h₂).mp e)
  have hfour := four_quarters
    (pr hP₁₁ hP₁₂ (same hN₁₁ hN₁₂)) (pr hP₂₁ hP₂₂ (same hN₂₁ hN₂₂))
    (pn hP₁₁ hP₂₁ (off hN₁₁) (off hN₂₁) (opp hN₁₁ hN₂₁ hoppN))
    (qr hQ₁₁ hQ₂₁ (same hM₁₁ hM₂₁)) (qr hQ₁₂ hQ₂₂ (same hM₁₂ hM₂₂))
    (qn hQ₁₁ hQ₁₂ (off hM₁₁) (off hM₁₂) (opp hM₁₁ hM₁₂ hoppM))
  have bP : ∀ {Y α : Point}, Sat cP Y → SameSide Y α N → ¬ loopBoundary P Y :=
    fun hY h => hbP _ hY (off h)
  have bQ : ∀ {Y β : Point}, Sat cQ Y → SameSide Y β M → ¬ loopBoundary Q Y :=
    fun hY h => hbQ _ hY (off h)
  rcases hc with h | h | h
  · rcases hfour.1 with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> exact h _ hp hq
  · have hsub : ∀ {Y β : Point}, Sat cQ Y → SameSide Y β M → loopInside P Y →
        ¬ loopInside Q Y → False := fun hY hβ hp hq =>
      hq ((h _ (Or.inr hp)).resolve_left (bQ hY hβ))
    rcases hfour.2.1 with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact hsub hQ₁₁ hM₁₁ hp hq
    · exact hsub hQ₁₂ hM₁₂ hp hq
    · exact hsub hQ₂₁ hM₂₁ hp hq
    · exact hsub hQ₂₂ hM₂₂ hp hq
  · have hsup : ∀ {Y α : Point}, Sat cP Y → SameSide Y α N → ¬ loopInside P Y →
        loopInside Q Y → False := fun hY hα hp hq =>
      hp ((h _ (Or.inr hq)).resolve_left (bP hY hα))
    rcases hfour.2.2 with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact hsup hP₁₁ hN₁₁ hp hq
    · exact hsup hP₁₂ hN₁₂ hp hq
    · exact hsup hP₂₁ hN₂₁ hp hq
    · exact hsup hP₂₂ hN₂₂ hp hq

/-- **Compatibility survives a change of description** that keeps each contour's boundary and
region: insides are kept, and contacts stay at corners (`contact_vertex`), the finitely many
contacts of the old description bounding those of the new. -/
theorem compatible_transfer {P Q P' Q' : List Point} (hP' : SimpleLoop P')
    (hQ' : SimpleLoop Q')
    (hbP : ∀ X, loopBoundary P' X ↔ loopBoundary P X) (hgP : ∀ X, loopRegion P' X ↔ loopRegion P X)
    (hbQ : ∀ X, loopBoundary Q' X ↔ loopBoundary Q X) (hgQ : ∀ X, loopRegion Q' X ↔ loopRegion Q X)
    (h : CompatibleLoops P Q) : CompatibleLoops P' Q' := by
  have hiP : ∀ X, loopInside P' X ↔ loopInside P X := fun X => by
    rw [inside_iff_region, inside_iff_region, hgP, hbP]
  have hiQ : ∀ X, loopInside Q' X ↔ loopInside Q X := fun X => by
    rw [inside_iff_region, inside_iff_region, hgQ, hbQ]
  have hc : (∀ X, loopInside P' X → ¬ loopInside Q' X) ∨
      (∀ X, loopRegion P' X → loopRegion Q' X) ∨ (∀ X, loopRegion Q' X → loopRegion P' X) := by
    rcases h.2 with h₂ | h₂ | h₂
    · exact Or.inl fun X hp hq => h₂ X ((hiP X).mp hp) ((hiQ X).mp hq)
    · exact Or.inr (Or.inl fun X hp => (hgQ X).mpr (h₂ X ((hgP X).mp hp)))
    · exact Or.inr (Or.inr fun X hq => (hgP X).mpr (h₂ X ((hgQ X).mp hq)))
  refine ⟨fun X hXP hXQ => contact_vertex hP' hQ' hc (L := P ++ Q) ?_ hXP hXQ, hc⟩
  intro Y hYP hYQ
  rcases h.1 Y ((hbP Y).mp hYP) ((hbQ Y).mp hYQ) with e | e
  · exact List.mem_append_left _ e
  · exact List.mem_append_right _ e

/-! ## The region lies within a triangle about the corners

What follows does not use Postulate 5. It reduces `outline_bounded` to a statement about
finitely many points, that the corners lie within some triangle, which is where Postulate 5
must enter (brief 0013, section 8, "The arrangement and general division"): that is
`enclosing_triangle`, in `OutlineBound.lean`. -/

/-- A point of a straight line off finitely many other straight lines. -/
theorem line_point_avoiding (L : Line) (ls : List Line) (hls : ∀ M ∈ ls, M ≠ L) :
    ∃ Y, OnLine Y L ∧ ∀ M ∈ ls, ¬ OnLine Y M := by
  classical
  let meet (M : Line) : Option Point :=
    if h : ∃ P, OnLine P L ∧ OnLine P M then some (Classical.choose h) else none
  obtain ⟨Y, hYL, hY⟩ := exists_point_on_line L (ls.filterMap meet)
  refine ⟨Y, hYL, fun M hM hYM => hY (List.mem_filterMap.mpr ⟨M, hM, ?_⟩)⟩
  have h : ∃ P, OnLine P L ∧ OnLine P M := ⟨Y, hYL, hYM⟩
  have hP := Classical.choose_spec h
  have e : Classical.choose h = Y := Classical.byContradiction fun hne =>
    hls M hM (line_unique hne hP.2 hYM hP.1 hYL)
  simp only [meet, h, ↓reduceDIte, e]

/-- **A ray away from a straight line.** From a point on a straight line, or beyond it from
`R`, a ray through no given corner whose points are none of them on `R`'s side. From a point
on the line, aim at a point on the far side; from a point beyond it, aim straight away from a
point of the line. -/
theorem away_ray {R : Point} {L : Line} (hR : ¬ OnLine R L) {X : Point}
    (hX : ¬ SameSide X R L) (vs : List Point) (hXv : ∀ V ∈ vs, X ≠ V) :
    ∃ Q, GoodRay vs X Q ∧ ∀ P, OnRay P X Q → ¬ SameSide P R L := by
  let line (V : Point) : Line := Classical.choose (collinear_of_two X V)
  have hline (V : Point) : OnLine X (line V) ∧ OnLine V (line V) :=
    Classical.choose_spec (collinear_of_two X V)
  by_cases hXL : OnLine X L
  · obtain ⟨R', hR'R, -⟩ := exists_point_opposite_side hR []
    have hR'L : ¬ OnLine R' L := hR'R.1
    obtain ⟨A, B, C, hin, hcl⟩ := small_triangle [(R', L)] fun c hc => by
      rw [List.mem_singleton.mp hc]
      exact same_side_refl hR'L
    obtain ⟨Q, hQin, hQav⟩ := triangle_point_avoiding hin.1.symm.triangle.cab (vs.map line)
    have hQR' : SameSide Q R' L := hcl Q (Or.inl hQin) (R', L) (List.mem_singleton_self _)
    have hQL : ¬ OnLine Q L := not_on_line_of_same_side hQR'
    have hXQ : X ≠ Q := fun e => hQL (e ▸ hXL)
    obtain ⟨ℓ, hXℓ, hQℓ⟩ := Postulate1 X Q hXQ
    refine ⟨Q, ⟨hXQ, fun V hV ⟨M, hXM, hQM, hVM⟩ => ?_⟩, fun P hP hPR => ?_⟩
    · apply hQav (line V) (List.mem_map_of_mem hV)
      rw [line_unique (hXv V hV) (hline V).1 (hline V).2 hXM hVM]
      exact hQM
    · have hPs : SameSide P Q L := (Parity.onRay_iff_sameSide hXQ hXℓ hQℓ hXL hQL
        (hP.onLine hXℓ hQℓ) hP.2.1).mp hP
      exact hR'R.2.2 (same_side_trans hQR' (same_side_trans hPs hPR))
  · have hls : ∀ M ∈ vs.map line, M ≠ L := by
      intro M hM e
      obtain ⟨V, -, rfl⟩ := List.mem_map.mp hM
      exact hXL (e ▸ (hline V).1)
    obtain ⟨Y, hYL, hYav⟩ := line_point_avoiding L (vs.map line) hls
    have hYX : Y ≠ X := fun e => hXL (e ▸ hYL)
    obtain ⟨Q, hYXQ⟩ := produce hYX
    have hXQ : X ≠ Q := (ne_of_between (between_symm hYXQ)).symm
    refine ⟨Q, ⟨hXQ, fun V hV ⟨M, hXM, hQM, hVM⟩ => ?_⟩, fun P hP hPR => ?_⟩
    · apply hYav (line V) (List.mem_map_of_mem hV)
      rw [line_unique (hXv V hV) (hline V).1 (hline V).2 hXM hVM]
      exact on_line_of_between (between_symm hYXQ) hQM hXM
    · have hXP : SameSide X P L := pasch2 (hP.between hYXQ) hYL hXL
      exact hX (same_side_trans (same_side_symm hXP) hPR)

/-- **Inside a loop whose corners are on one side of a straight line** is on that side: from a
point elsewhere, a good ray away from the line crosses no side. -/
theorem inner_side {ps : List Point} (h : SimpleLoop ps) {R : Point} {L : Line}
    (hR : ¬ OnLine R L) (hV : ∀ V ∈ ps, SameSide V R L) {X : Point} (hi : loopInside ps X) :
    SameSide X R L := by
  refine Classical.byContradiction fun hXR => ?_
  obtain ⟨Q, hQ, hray⟩ := away_ray hR hXR ps fun V hV e => hi.1 (e ▸ vertex_boundary hV)
  have h0 : crossingCount ps X Q = 0 := LoopFacts.crossingCount_eq_zero fun t ht ⟨P, hP, hb⟩ =>
    hray P hP (Avoid.same_side_between hb (hV _ (LoopFacts.side_mem ht).1)
      (hV _ (LoopFacts.side_mem ht).2))
  have hodd := (inside_iff h hi.1 hQ).mp hi
  omega

/-- A point between two points inside a triangle is inside it. -/
theorem inside_between {U W X A B C : Point} (hU : InsideTriangle U A B C)
    (hW : InsideTriangle W A B C) (hb : Between U X W) : InsideTriangle X A B C :=
  ⟨⟨hU.1.1, fun L h₁ h₂ => Avoid.same_side_between hb (hU.1.2 L h₁ h₂) (hW.1.2 L h₁ h₂)⟩,
    ⟨hU.2.1.1, fun L h₁ h₂ => Avoid.same_side_between hb (hU.2.1.2 L h₁ h₂) (hW.2.1.2 L h₁ h₂)⟩,
    ⟨hU.2.2.1, fun L h₁ h₂ => Avoid.same_side_between hb (hU.2.2.2 L h₁ h₂) (hW.2.2.2 L h₁ h₂)⟩⟩

/-- **The region lies within any triangle that holds every corner.** A boundary point lies
between two corners, or is one; a point inside some contour is on the inner side of each of the
triangle's straight lines, since that contour's corners are (`inner_side`). Postulate 5 is not
used: it is needed only to find such a triangle for finitely many points. -/
theorem bounded_of_enclosure (F : Outline) {A B C : Point}
    (hin : ∀ ps ∈ F.loops, ∀ V ∈ ps, InsideTriangle V A B C) :
    ∀ X : Point, F.region X → InsideTriangle X A B C := by
  classical
  intro X hX
  rcases hX with ⟨ps, hps, s, hs, hXs⟩ | ⟨hXb, hodd⟩
  · have h₁ := hin ps hps _ (LoopFacts.side_mem hs).1
    have h₂ := hin ps hps _ (LoopFacts.side_mem hs).2
    rcases hXs with e | e | hb
    · exact e ▸ h₁
    · exact e ▸ h₂
    · exact inside_between h₁ h₂ hb
  · obtain ⟨ps, hps, hi⟩ : ∃ ps ∈ F.loops, loopInside ps X := by
      refine Classical.byContradiction fun hno => ?_
      have h0 : F.depth X = 0 := by
        unfold Outline.depth
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro ps hps hi
        exact hno ⟨ps, hps, by simpa using hi⟩
      rw [h0] at hodd
      exact absurd hodd (by decide)
    have h := F.simple ps hps
    obtain ⟨V₀, hV₀⟩ := exists_vertex h
    have hV₀in := hin ps hps V₀ hV₀
    obtain ⟨L₁, hB₁, hC₁⟩ := Postulate1 B C hV₀in.1.1
    obtain ⟨L₂, hC₂, hA₂⟩ := Postulate1 C A hV₀in.2.1.1
    obtain ⟨L₃, hA₃, hB₃⟩ := Postulate1 A B hV₀in.2.2.1
    have off : ∀ {P Q : Point} {L : Line}, SameSide P Q L → ¬ OnLine Q L :=
      fun h => not_on_line_of_same_side (same_side_symm h)
    exact ⟨SameSideOf.of_line hV₀in.1.1 hB₁ hC₁ (inner_side h (off (hV₀in.1.sameSide hB₁ hC₁))
        (fun V hV => (hin ps hps V hV).1.sameSide hB₁ hC₁) hi),
      SameSideOf.of_line hV₀in.2.1.1 hC₂ hA₂ (inner_side h
        (off (hV₀in.2.1.sameSide hC₂ hA₂)) (fun V hV => (hin ps hps V hV).2.1.sameSide hC₂ hA₂) hi),
      SameSideOf.of_line hV₀in.2.2.1 hA₃ hB₃ (inner_side h
        (off (hV₀in.2.2.sameSide hA₃ hB₃)) (fun V hV => (hin ps hps V hV).2.2.sameSide hA₃ hB₃)
        hi)⟩

end OutlineFacts

end Elements.Figures
