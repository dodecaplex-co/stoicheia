import Elements.Figure.Divisions.ExtractLists
import Elements.Figure.Arrangements.CoverFacts

/-!
# Book Zero: two simple loops that do not cross

Helper lemmas, in the namespace `Extract`, for `apart_has_outline`, in `Divisions.lean`
(brief 0013, section 8, "The arrangement and general division"; D10): the compatibility of
the contours in the fourth step of `Divisions/Extract.lean`. Nothing in Book Zero cites a
proposition of the *Elements*.

* **The first and the last crossing on a ray** (`first_hit`, `last_hit`). Of finitely many
  sides whose ends are off a ray's straight line, if the ray crosses one, some crossing point
  has no crossing point between it and the ray's start, and some has none beyond it.
* **Compatible from one side** (`compatible_of_status`). Two simple loops whose boundaries
  meet only at corners, each lying, off the other, wholly inside or wholly outside the other,
  are compatible. If neither lies inside the other, their insides are apart: from a point
  inside both, the first crossing along a good ray would be a point of one loop inside the
  other. If one lies inside the other, its closed region lies in the other's in the same way.
  Both cannot lie inside each other: beyond the last crossing along a ray from a point of one,
  nothing is inside either, yet that last crossing is a point of one loop inside the other.

No sector at a corner is examined.
-/

namespace Elements.Figures

namespace Extract

open Tacit Classical

/-! ## Order on a straight line -/

/-- If B is between A and C, and C between B and D, then C is between A and D. -/
theorem between_shift {A B C D : Point} (h₁ : Between A B C) (h₂ : Between B C D) :
    Between A C D :=
  between_symm (between_of_between_left (between_symm (between_of_between_right h₁ h₂))
    (between_symm h₂))

/-- A point between the start of a ray and a point of it is on the ray. -/
theorem onRay_of_between {X U Y Q : Point} (hXUY : Between X U Y) (hY : OnRay Y X Q) :
    OnRay U X Q := by
  obtain ⟨hXQ, -, ⟨M, hXM, hQM, hYM⟩, hn⟩ := hY
  refine ⟨hXQ, (ne_of_between hXUY).symm, ⟨M, hXM, hQM, on_line_of_between_ends hXUY hXM hYM⟩,
    fun hUXQ => hn (between_shift (between_symm hXUY) hUXQ)⟩

/-- A point beyond a point of a ray, from its start, is on the ray. -/
theorem onRay_of_beyond {X Z Y Q : Point} (hXZY : Between X Z Y) (hZ : OnRay Z X Q) :
    OnRay Y X Q := by
  obtain ⟨hXQ, -, ⟨M, hXM, hQM, hZM⟩, hn⟩ := hZ
  refine ⟨hXQ, (ne_of_between_ends hXZY).symm,
    ⟨M, hXM, hQM, on_line_of_between hXZY hXM hZM⟩, fun hYXQ => hn ?_⟩
  exact between_inner (between_symm hXZY) hYXQ

/-- **The nearest** of finitely many points to X: none of them lies between X and it. -/
theorem nearest (X : Point) :
    ∀ (Ys : List Point), Ys ≠ [] → ∃ Y0 ∈ Ys, ∀ Y ∈ Ys, ¬ Between X Y Y0
  | [], h => absurd rfl h
  | [Y], _ => ⟨Y, List.mem_singleton_self Y, fun Y' hY' hb => by
      rw [List.mem_singleton] at hY'
      subst hY'
      exact ne_of_between (between_symm hb) rfl⟩
  | Y :: Y' :: rest, _ => by
    obtain ⟨Y1, hY1, h1⟩ := nearest X (Y' :: rest) (List.cons_ne_nil _ _)
    by_cases hb : Between X Y Y1
    · refine ⟨Y, List.mem_cons_self, fun Z hZ hZY => ?_⟩
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact ne_of_between (between_symm hZY) rfl
      · exact h1 Z hZ (between_of_between_left hb hZY)
    · refine ⟨Y1, List.mem_cons_of_mem _ hY1, fun Z hZ => ?_⟩
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact hb
      · exact h1 Z hZ

/-- **The farthest** of finitely many points from X: none of them lies beyond it. -/
theorem farthest (X : Point) :
    ∀ (Ys : List Point), Ys ≠ [] → ∃ Y0 ∈ Ys, ∀ Y ∈ Ys, ¬ Between X Y0 Y
  | [], h => absurd rfl h
  | [Y], _ => ⟨Y, List.mem_singleton_self Y, fun Y' hY' hb => by
      rw [List.mem_singleton] at hY'
      subst hY'
      exact ne_of_between (between_symm hb) rfl⟩
  | Y :: Y' :: rest, _ => by
    obtain ⟨Y1, hY1, h1⟩ := farthest X (Y' :: rest) (List.cons_ne_nil _ _)
    by_cases hb : Between X Y1 Y
    · refine ⟨Y, List.mem_cons_self, fun Z hZ hYZ => ?_⟩
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact ne_of_between (between_symm hYZ) rfl
      · exact h1 Z hZ (between_of_between_right hb (between_inner hb hYZ))
    · refine ⟨Y1, List.mem_cons_of_mem _ hY1, fun Z hZ => ?_⟩
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact hb
      · exact h1 Z hZ

/-! ## Crossing points on a ray -/

/-- The point where a ray crosses a side, when it does. -/
noncomputable def crossPt (X Q : Point) (s : Point × Point) : Point :=
  if h : RayCrosses X Q s then Classical.choose h else X

/-- The crossing points of a ray with a list of sides. -/
noncomputable def crossPts (X Q : Point) (S : List (Point × Point)) : List Point :=
  (S.filter fun s => decide (RayCrosses X Q s)).map (crossPt X Q)

theorem crossPt_spec {X Q : Point} {s : Point × Point} (h : RayCrosses X Q s) :
    OnRay (crossPt X Q s) X Q ∧ Between s.1 (crossPt X Q s) s.2 := by
  unfold crossPt
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

theorem mem_crossPts {X Q : Point} {S : List (Point × Point)} {Y : Point}
    (hY : Y ∈ crossPts X Q S) : OnRay Y X Q ∧ ∃ s ∈ S, Between s.1 Y s.2 := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hY
  rw [List.mem_filter, decide_eq_true_eq] at hs
  obtain ⟨h1, h2⟩ := crossPt_spec hs.2
  exact ⟨h1, s, hs.1, h2⟩

theorem crossPts_mem {X Q : Point} {ℓ : Line} (hX : OnLine X ℓ) (hQ : OnLine Q ℓ)
    {S : List (Point × Point)} (hoff : ∀ s ∈ S, ¬ OnLine s.1 ℓ) {s : Point × Point}
    (hs : s ∈ S) {Y : Point} (hY : OnRay Y X Q) (hb : Between s.1 Y s.2) :
    Y ∈ crossPts X Q S := by
  have hc : RayCrosses X Q s := ⟨Y, hY, hb⟩
  obtain ⟨h1, h2⟩ := crossPt_spec hc
  have he : crossPt X Q s = Y :=
    OutlineFacts.cross_unique (hoff s hs) (h1.onLine hX hQ) (hY.onLine hX hQ) h2 hb
  rw [← he]
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hs, decide_eq_true hc⟩)

/-- **The first crossing.** If a ray crosses one of finitely many sides whose ends are off its
straight line, some crossing point has no point of any side strictly between it and the
start. -/
theorem first_hit {X Q : Point} {ℓ : Line} (hX : OnLine X ℓ) (hQ : OnLine Q ℓ)
    {S : List (Point × Point)} (hoff : ∀ s ∈ S, ¬ OnLine s.1 ℓ ∧ ¬ OnLine s.2 ℓ)
    (hc : ∃ s ∈ S, RayCrosses X Q s) :
    ∃ Y0 : Point, OnRay Y0 X Q ∧ (∃ s ∈ S, Between s.1 Y0 s.2) ∧
      ∀ U : Point, Between X U Y0 → ∀ s ∈ S, ¬ OnFiniteLine U s.1 s.2 := by
  obtain ⟨s, hs, Y, hY, hb⟩ := hc
  have hne : crossPts X Q S ≠ [] :=
    List.ne_nil_of_mem (crossPts_mem hX hQ (fun s hs => (hoff s hs).1) hs hY hb)
  obtain ⟨Y0, hY0, hnear⟩ := nearest X _ hne
  obtain ⟨hY0r, hY0s⟩ := mem_crossPts hY0
  refine ⟨Y0, hY0r, hY0s, fun U hU t ht hUt => ?_⟩
  have hUr := onRay_of_between hU hY0r
  have hUℓ : OnLine U ℓ := hUr.onLine hX hQ
  have hU1 : U ≠ t.1 := fun e => (hoff t ht).1 (e ▸ hUℓ)
  have hU2 : U ≠ t.2 := fun e => (hoff t ht).2 (e ▸ hUℓ)
  rcases hUt with e | e | hUt
  · exact hU1 e
  · exact hU2 e
  · exact hnear U (crossPts_mem hX hQ (fun s hs => (hoff s hs).1) ht hUr hUt) hU

/-- **The last crossing.** If a ray crosses one of finitely many sides whose ends are off its
straight line, some crossing point has no crossing point beyond it. -/
theorem last_hit {X Q : Point} {ℓ : Line} (hX : OnLine X ℓ) (hQ : OnLine Q ℓ)
    {S : List (Point × Point)} (hoff : ∀ s ∈ S, ¬ OnLine s.1 ℓ)
    (hc : ∃ s ∈ S, RayCrosses X Q s) :
    ∃ Z0 : Point, OnRay Z0 X Q ∧ (∃ s ∈ S, Between s.1 Z0 s.2) ∧
      ∀ s ∈ S, ∀ Y : Point, OnRay Y X Q → Between s.1 Y s.2 → ¬ Between X Z0 Y := by
  obtain ⟨s, hs, Y, hY, hb⟩ := hc
  have hne : crossPts X Q S ≠ [] := List.ne_nil_of_mem (crossPts_mem hX hQ hoff hs hY hb)
  obtain ⟨Z0, hZ0, hfar⟩ := farthest X _ hne
  obtain ⟨hZ0r, hZ0s⟩ := mem_crossPts hZ0
  exact ⟨Z0, hZ0r, hZ0s, fun t ht Y hY hb => hfar Y (crossPts_mem hX hQ hoff ht hY hb)⟩

/-- Beyond the last crossing, a ray from it crosses nothing. -/
theorem beyond_last {X Q Z0 Q' : Point} {S : List (Point × Point)}
    (hZ0 : OnRay Z0 X Q)
    (hlast : ∀ s ∈ S, ∀ Y : Point, OnRay Y X Q → Between s.1 Y s.2 → ¬ Between X Z0 Y)
    (hQ' : Between X Z0 Q') : ∀ s ∈ S, ¬ RayCrosses Z0 Q' s := by
  rintro s hs ⟨Y, hY, hb⟩
  have hXZY : Between X Z0 Y := hY.between hQ'
  exact hlast s hs Y (onRay_of_beyond hXZY hZ0) hb hXZY

/-! ## A ray through no corner -/

/-- From a point that is none of finitely many points, some straight line through it passes
through none of them, given some triangle to choose its direction in. -/
theorem line_avoiding {X : Point} {vs : List Point} (hX : X ∉ vs) {a b c : Point}
    (habc : Triangle a b c) :
    ∃ Q : Point, ∃ ℓ : Line, X ≠ Q ∧ OnLine X ℓ ∧ OnLine Q ℓ ∧ ∀ V ∈ vs, ¬ OnLine V ℓ := by
  obtain ⟨K, hXK⟩ := exists_line_through X
  obtain ⟨Q, -, hQ⟩ := triangle_point_avoiding habc (K :: vs.map fun V => Classical.choose (collinear_of_two X V))
  have hXQ : X ≠ Q := fun e => hQ K List.mem_cons_self (e ▸ hXK)
  obtain ⟨ℓ, hXℓ, hQℓ⟩ := Postulate1 X Q hXQ
  exact ⟨Q, ℓ, hXQ, hXℓ, hQℓ,
    CoverFacts.joins_off (fun L hL => hQ L (List.mem_cons_of_mem _ hL)) hX hXℓ hQℓ⟩

/-- A point off a loop's boundary is none of its corners. -/
theorem not_mem_of_off {ps : List Point} {X : Point} (hX : ¬ LoopBoundary ps X) : X ∉ ps := by
  intro hm
  obtain ⟨E, hE⟩ := outgoing_side hm
  exact hX ⟨(X, E), hE, Or.inl rfl⟩

/-- A point strictly within a side of a loop is on its boundary. -/
theorem boundary_of_side {ps : List Point} {s : Point × Point} (hs : s ∈ sides ps) {Y : Point}
    (hY : Between s.1 Y s.2) : LoopBoundary ps Y := ⟨s, hs, Or.inr (Or.inr hY)⟩

/-! ## Two loops -/

section TwoLoops

variable {A B : List Point}

/-- The ends of the sides of two loops are their corners. -/
theorem ends_off {ℓ : Line} (hoff : ∀ V ∈ A ++ B, ¬ OnLine V ℓ) :
    ∀ s ∈ sides A ++ sides B, ¬ OnLine s.1 ℓ ∧ ¬ OnLine s.2 ℓ := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact ⟨hoff _ (List.mem_append_left _ (LoopFacts.side_mem hs).1),
      hoff _ (List.mem_append_left _ (LoopFacts.side_mem hs).2)⟩
  · exact ⟨hoff _ (List.mem_append_right _ (LoopFacts.side_mem hs).1),
      hoff _ (List.mem_append_right _ (LoopFacts.side_mem hs).2)⟩

/-- A crossing point of a ray through no corner, on a side of A, is off B's boundary. -/
theorem hit_off {ℓ : Line} (hmeet : ∀ X, LoopBoundary A X → LoopBoundary B X → X ∈ A ∨ X ∈ B)
    (hoff : ∀ V ∈ A ++ B, ¬ OnLine V ℓ) {Y : Point} (hYℓ : OnLine Y ℓ)
    (hYA : LoopBoundary A Y) : ¬ LoopBoundary B Y := by
  intro hYB
  rcases hmeet Y hYA hYB with h | h
  · exact hoff Y (List.mem_append_left _ h) hYℓ
  · exact hoff Y (List.mem_append_right _ h) hYℓ

/-- **The first crossing from a point inside A**, off both boundaries, along a ray through no
corner: it is a point of A off B, with the same status for B as the start, or a point of B off
A, with the same status for A. -/
theorem first_crossing (hA : SimpleLoop A) (hB : SimpleLoop B)
    (hmeet : ∀ X, LoopBoundary A X → LoopBoundary B X → X ∈ A ∨ X ∈ B)
    {X : Point} (hXA : ¬ LoopBoundary A X) (hXB : ¬ LoopBoundary B X) (hin : LoopInside A X)
    {a b c : Point} (habc : Triangle a b c) :
    (∃ Y, LoopBoundary A Y ∧ ¬ LoopBoundary B Y ∧ (LoopInside B X ↔ LoopInside B Y)) ∨
      (∃ Y, LoopBoundary B Y ∧ ¬ LoopBoundary A Y ∧ (LoopInside A X ↔ LoopInside A Y)) := by
  have hXv : X ∉ A ++ B := by
    rw [List.mem_append]
    rintro (h | h)
    · exact not_mem_of_off hXA h
    · exact not_mem_of_off hXB h
  obtain ⟨Q, ℓ, hXQ, hXℓ, hQℓ, hoff⟩ := line_avoiding hXv habc
  have hgA : GoodRay A X Q :=
    OutlineFacts.good_of_line hXQ hXℓ hQℓ fun V hV => hoff V (List.mem_append_left _ hV)
  have hodd := (loop_inside_iff hA hXA hgA).mp hin
  have hcA : ∃ s ∈ sides A, RayCrosses X Q s := by
    refine Classical.byContradiction fun hno => ?_
    have h0 : crossingCount A X Q = 0 :=
      LoopFacts.crossingCount_eq_zero fun s hs hc => hno ⟨s, hs, hc⟩
    rw [h0] at hodd
    exact absurd hodd (by decide)
  obtain ⟨s, hs, hcs⟩ := hcA
  obtain ⟨Y0, hY0r, ⟨t, ht, hY0t⟩, hclear⟩ := first_hit hXℓ hQℓ (ends_off hoff)
    ⟨s, List.mem_append_left _ hs, hcs⟩
  have hY0ℓ : OnLine Y0 ℓ := hY0r.onLine hXℓ hQℓ
  have hXY0 : X ≠ Y0 := hY0r.2.1.symm
  /- The open finite straight line from X to the first crossing meets neither boundary. -/
  have hclearA : ∀ U, Between X U Y0 → ¬ LoopBoundary A U := fun U hU ⟨r, hr, hUr⟩ =>
    hclear U hU r (List.mem_append_left _ hr) hUr
  have hclearB : ∀ U, Between X U Y0 → ¬ LoopBoundary B U := fun U hU ⟨r, hr, hUr⟩ =>
    hclear U hU r (List.mem_append_right _ hr) hUr
  rcases List.mem_append.mp ht with ht | ht
  · have hY0A := boundary_of_side ht hY0t
    have hY0B := hit_off hmeet hoff hY0ℓ hY0A
    refine Or.inl ⟨Y0, hY0A, hY0B, ?_⟩
    exact CoverFacts.inside_of_segment hB hXY0 hXℓ hY0ℓ
      (fun V hV => hoff V (List.mem_append_right _ hV)) hXB hY0B hclearB
  · have hY0B := boundary_of_side ht hY0t
    have hY0A : ¬ LoopBoundary A Y0 := by
      intro hY0A
      exact hit_off hmeet hoff hY0ℓ hY0A hY0B
    refine Or.inr ⟨Y0, hY0B, hY0A, ?_⟩
    exact CoverFacts.inside_of_segment hA hXY0 hXℓ hY0ℓ
      (fun V hV => hoff V (List.mem_append_left _ hV)) hXA hY0A hclearA

/-- **Neither inside the other: insides apart.** -/
theorem insides_apart (hA : SimpleLoop A) (hB : SimpleLoop B)
    (hmeet : ∀ X, LoopBoundary A X → LoopBoundary B X → X ∈ A ∨ X ∈ B)
    (hsA : ∀ P, LoopBoundary A P → ¬ LoopBoundary B P → ¬ LoopInside B P)
    (hsB : ∀ P, LoopBoundary B P → ¬ LoopBoundary A P → ¬ LoopInside A P) :
    ∀ X, LoopInside A X → ¬ LoopInside B X := by
  intro X hXA hXB
  obtain ⟨a, -, b, -, c, -, habc⟩ := LoopFacts.simple_frame hA
  rcases first_crossing hA hB hmeet hXA.1 hXB.1 hXA habc with
    ⟨Y, hYA, hYB, hiff⟩ | ⟨Y, hYB, hYA, hiff⟩
  · exact hsA Y hYA hYB (hiff.mp hXB)
  · exact hsB Y hYB hYA (hiff.mp hXA)

/-- **One inside the other: closed regions nested.** -/
theorem region_nested (hA : SimpleLoop A) (hB : SimpleLoop B)
    (hmeet : ∀ X, LoopBoundary A X → LoopBoundary B X → X ∈ A ∨ X ∈ B)
    (hsA : ∀ P, LoopBoundary A P → ¬ LoopBoundary B P → LoopInside B P)
    (hsB : ∀ P, LoopBoundary B P → ¬ LoopBoundary A P → ¬ LoopInside A P) :
    ∀ X, LoopRegion A X → LoopRegion B X := by
  intro X hX
  by_cases hXB : LoopBoundary B X
  · exact Or.inl hXB
  rcases hX with hXA | hXA
  · exact Or.inr (hsA X hXA hXB)
  · obtain ⟨a, -, b, -, c, -, habc⟩ := LoopFacts.simple_frame hA
    rcases first_crossing hA hB hmeet hXA.1 hXB hXA habc with
      ⟨Y, hYA, hYB, hiff⟩ | ⟨Y, hYB, hYA, hiff⟩
    · exact Or.inr (hiff.mpr (hsA Y hYA hYB))
    · exact absurd (hiff.mp hXA) (hsB Y hYB hYA)

/-- **Not each inside the other.** Beyond the last crossing along a ray from a point of A
strictly within a side, nothing is inside either loop. -/
theorem not_both_inside (hA : SimpleLoop A) (hB : SimpleLoop B)
    (hmeet : ∀ X, LoopBoundary A X → LoopBoundary B X → X ∈ A ∨ X ∈ B)
    (hsA : ∀ P, LoopBoundary A P → ¬ LoopBoundary B P → LoopInside B P)
    (hsB : ∀ P, LoopBoundary B P → ¬ LoopBoundary A P → LoopInside A P) : False := by
  obtain ⟨a, -, b, -, c, -, habc⟩ := LoopFacts.simple_frame hA
  /- A point P strictly within a side of A, at no corner of either loop. -/
  obtain ⟨s, hs⟩ : ∃ s, s ∈ sides A := by
    obtain ⟨E, hE⟩ := outgoing_side (List.head_mem (List.ne_nil_of_length_pos (by
      have := hA.1
      omega)) : A.head (List.ne_nil_of_length_pos (by have := hA.1; omega)) ∈ A)
    exact ⟨_, hE⟩
  have hs12 := hA.2.2.1 s hs
  obtain ⟨M, h1, h2⟩ := Postulate1 s.1 s.2 hs12
  obtain ⟨P, -, hP, hPv⟩ := exists_point_between h1 h2 hs12 (A ++ B)
  have hPA := boundary_of_side hs hP
  have hPB : ¬ LoopBoundary B P := by
    intro hPB
    rcases hmeet P hPA hPB with h | h
    · exact hPv (List.mem_append_left _ h)
    · exact hPv (List.mem_append_right _ h)
  have hPin := hsA P hPA hPB
  /- A ray from P through no corner; it crosses B. -/
  obtain ⟨Q, ℓ, hPQ, hPℓ, hQℓ, hoff⟩ := line_avoiding hPv habc
  have hgB : GoodRay B P Q :=
    OutlineFacts.good_of_line hPQ hPℓ hQℓ fun V hV => hoff V (List.mem_append_right _ hV)
  have hodd := (loop_inside_iff hB hPB hgB).mp hPin
  have hcB : ∃ t ∈ sides B, RayCrosses P Q t := by
    refine Classical.byContradiction fun hno => ?_
    have h0 : crossingCount B P Q = 0 :=
      LoopFacts.crossingCount_eq_zero fun t ht hc => hno ⟨t, ht, hc⟩
    rw [h0] at hodd
    exact absurd hodd (by decide)
  obtain ⟨t, ht, hct⟩ := hcB
  obtain ⟨Z0, hZ0r, ⟨u, hu, hZ0u⟩, hlast⟩ := last_hit hPℓ hQℓ
    (fun r hr => (ends_off hoff r hr).1) ⟨t, List.mem_append_right _ ht, hct⟩
  have hZ0ℓ : OnLine Z0 ℓ := hZ0r.onLine hPℓ hQℓ
  obtain ⟨Q', hQ'⟩ := produce hZ0r.2.1.symm
  have hQ'ℓ : OnLine Q' ℓ := on_line_of_between hQ' hPℓ hZ0ℓ
  have hZQ' : Z0 ≠ Q' := (ne_of_between (between_symm hQ')).symm
  have hnone := beyond_last hZ0r hlast hQ'
  have hzero : ∀ {L : List Point}, (∀ r ∈ sides L, r ∈ sides A ++ sides B) →
      crossingCount L Z0 Q' = 0 := fun hsub =>
    LoopFacts.crossingCount_eq_zero fun r hr => hnone r (hsub r hr)
  rcases List.mem_append.mp hu with hu | hu
  · have hZA := boundary_of_side hu hZ0u
    have hZB := hit_off hmeet hoff hZ0ℓ hZA
    have hgB' : GoodRay B Z0 Q' :=
      OutlineFacts.good_of_line hZQ' hZ0ℓ hQ'ℓ fun V hV => hoff V (List.mem_append_right _ hV)
    have h := (loop_inside_iff hB hZB hgB').mp (hsA Z0 hZA hZB)
    rw [hzero fun r hr => List.mem_append_right _ hr] at h
    exact absurd h (by decide)
  · have hZB := boundary_of_side hu hZ0u
    have hZA : ¬ LoopBoundary A Z0 := fun hZA => hit_off hmeet hoff hZ0ℓ hZA hZB
    have hgA' : GoodRay A Z0 Q' :=
      OutlineFacts.good_of_line hZQ' hZ0ℓ hQ'ℓ fun V hV => hoff V (List.mem_append_left _ hV)
    have h := (loop_inside_iff hA hZA hgA').mp (hsB Z0 hZB hZA)
    rw [hzero fun r hr => List.mem_append_left _ hr] at h
    exact absurd h (by decide)

end TwoLoops

/-- **Compatible from one side.** Two simple loops whose boundaries meet only at corners, each
lying, off the other's boundary, wholly inside or wholly outside the other, are compatible. -/
theorem compatible_of_status {A B : List Point} (hA : SimpleLoop A) (hB : SimpleLoop B)
    (hmeet : ∀ X, LoopBoundary A X → LoopBoundary B X → X ∈ A ∨ X ∈ B)
    (sA : Prop) (hsA : ∀ P, LoopBoundary A P → ¬ LoopBoundary B P → (LoopInside B P ↔ sA))
    (sB : Prop) (hsB : ∀ P, LoopBoundary B P → ¬ LoopBoundary A P → (LoopInside A P ↔ sB)) :
    CompatibleLoops A B := by
  have hmeet' : ∀ X, LoopBoundary B X → LoopBoundary A X → X ∈ B ∨ X ∈ A :=
    fun X hB' hA' => (hmeet X hA' hB').symm
  refine ⟨hmeet, ?_⟩
  by_cases ha : sA <;> by_cases hb : sB
  · exact (not_both_inside hA hB hmeet (fun P h1 h2 => (hsA P h1 h2).mpr ha)
      (fun P h1 h2 => (hsB P h1 h2).mpr hb)).elim
  · exact Or.inr (Or.inl (region_nested hA hB hmeet (fun P h1 h2 => (hsA P h1 h2).mpr ha)
      (fun P h1 h2 h3 => hb ((hsB P h1 h2).mp h3))))
  · exact Or.inr (Or.inr (region_nested hB hA hmeet' (fun P h1 h2 => (hsB P h1 h2).mpr hb)
      (fun P h1 h2 h3 => ha ((hsA P h1 h2).mp h3))))
  · exact Or.inl (insides_apart hA hB hmeet (fun P h1 h2 h3 => ha ((hsA P h1 h2).mp h3))
      (fun P h1 h2 h3 => hb ((hsB P h1 h2).mp h3)))

end Extract

end Elements.Figures
