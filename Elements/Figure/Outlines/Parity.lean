import Elements.Figure.Outlines.LoopFacts

/-!
# Book Zero: two good rays give one parity

Helper lemmas, in the namespace `Parity`, for `crossing_parity_independent` (brief 0013,
section 8, D3) and `loop_normalise` (D4), in `Outlines.lean`. Nothing in Book Zero cites a
proposition of the *Elements*.

The route compares the two rays through the angle between them, rather than through a fan.
Let the rays from X run through Q and through R, not on one straight line, and call a point
*within the angle* when it is on R's side of the straight line XQ and on Q's side of the
straight line XR.

* **One side against the angle** (`side_parity`). A finite straight line whose ends are off
  both straight lines, and which does not pass through X, crosses the two rays together an
  odd number of times exactly when one of its ends is within the angle and the other is not.
  A point of the straight line XQ other than X is on the ray through Q exactly when it is on
  Q's side of XR (`onRay_iff_sameSide`); so it is a matter of where the finite straight line
  crosses the two straight lines, and in what order.
* **Round a closed outline** (`parity_of_angle`). Each corner is the first end of one side
  and the second end of one other, so the ends within the angle, counted over all the sides,
  come in pairs. Hence the crossings of the two rays together are even.
* **Rays on one straight line** (`parity_independent`). A third good ray off that straight
  line, found inside a frame of three corners (`third_ray`), compares with each. It is found
  by the avoidance construction that `good_ray_exists` uses too (`good_ray_avoiding`).
  `parity_independent` is the statement of `crossing_parity_independent`, proved here
  because the helpers that use it come before `Outlines.lean`, which states it.
* **A corner between its neighbours** (`remove_corner`, `straight_corner`). A loop that is not
  reduced has three consecutive corners on one straight line, the middle one between the
  others. Removing it keeps the loop simple, its boundary, and the crossing count of every
  good ray; a good ray of the shorter loop that runs through the removed corner compares with
  a third good ray, so the region is kept too.

Natural numbers count sides and corners only; they measure nothing.
-/

namespace Elements.Figures

open Tacit

namespace Parity

/-! ## Sides of a straight line -/

/-- Two points off a straight line are on one side of it exactly when they agree about a
third point off it. -/
theorem sameSide_iff_iff {A B R : Point} {L : Line} (hA : ¬ OnLine A L)
    (hB : ¬ OnLine B L) (hR : ¬ OnLine R L) :
    SameSide A B L ↔ (SameSide A R L ↔ SameSide B R L) := by
  constructor
  · intro hAB
    exact ⟨fun hAR => same_side_trans hAB hAR,
      fun hBR => same_side_trans (same_side_symm hAB) hBR⟩
  · intro he
    by_cases hAR : SameSide A R L
    · exact same_side_trans (same_side_symm hAR) (same_side_symm (he.mp hAR))
    · rcases same_side_or hA hR hB hAR with h | h
      · exact h
      · exact absurd (he.mpr (same_side_symm h)) hAR

/-- A point on one side with another is on one side with whatever the other is. -/
theorem sameSide_congr {Y A P : Point} {L : Line} (h : SameSide Y A L) :
    SameSide Y P L ↔ SameSide A P L :=
  ⟨fun hY => same_side_trans h hY, fun hA => same_side_trans (same_side_symm h) hA⟩

/-! ## Where a finite straight line meets a ray -/

/-- **A point of a ray's straight line.** Another straight line through X, with Q off it,
cuts the straight line XQ at X; a point of XQ other than X is on the ray through Q exactly
when it is on Q's side of that other straight line. -/
theorem onRay_iff_sameSide {X Q Y : Point} {ℓ m : Line} (hXQ : X ≠ Q) (hXℓ : OnLine X ℓ)
    (hQℓ : OnLine Q ℓ) (hXm : OnLine X m) (hQm : ¬ OnLine Q m) (hYℓ : OnLine Y ℓ)
    (hYX : Y ≠ X) : OnRay Y X Q ↔ SameSide Y Q m := by
  have hℓm : m ≠ ℓ := fun e => hQm (e ▸ hQℓ)
  have hYm : ¬ OnLine Y m := fun hYm => hℓm (line_unique hYX hYm hXm hYℓ hXℓ)
  constructor
  · rintro ⟨-, -, -, hn⟩
    refine Classical.byContradiction fun hs => hn ?_
    by_cases hYQ : Y = Q
    · subst hYQ
      exact absurd (same_side_refl hQm) hs
    · exact pasch4 hℓm hXm hXℓ hYℓ hQℓ hYQ hYX (Ne.symm hXQ) hs
  · intro hs
    exact ⟨hXQ, hYX, ⟨ℓ, hXℓ, hQℓ, hYℓ⟩, fun hb => pasch3 hb hXm hs⟩

/-- A finite straight line with one end off the ray's straight line, crossing it at Y,
crosses the ray exactly when Y is on the ray: it meets that straight line only there. -/
theorem crosses_at {X Q A B Y : Point} {ℓ : Line} (hXℓ : OnLine X ℓ) (hQℓ : OnLine Q ℓ)
    (hAℓ : ¬ OnLine A ℓ) (hY : Between A Y B) (hYℓ : OnLine Y ℓ) :
    RayCrosses X Q (A, B) ↔ OnRay Y X Q := by
  constructor
  · rintro ⟨Z, hZ, hAZB⟩
    have hAZB' : Between A Z B := hAZB
    have hZℓ : OnLine Z ℓ := hZ.onLine hXℓ hQℓ
    obtain ⟨N, hAN, hBN⟩ := Postulate1 A B (ne_of_between_ends hY)
    have hYN : OnLine Y N := on_line_of_between_ends hY hAN hBN
    have hZN : OnLine Z N := on_line_of_between_ends hAZB' hAN hBN
    by_cases hZY : Z = Y
    · exact hZY ▸ hZ
    · exact absurd (line_unique hZY hZN hYN hZℓ hYℓ ▸ hAN) hAℓ
  · intro h
    exact ⟨Y, h, hY⟩

/-- A ray does not cross a finite straight line whose ends are on one side of the ray's
straight line. -/
theorem not_crosses_of_sameSide {X Q A B : Point} {ℓ : Line} (hXℓ : OnLine X ℓ)
    (hQℓ : OnLine Q ℓ) (h : SameSide A B ℓ) : ¬ RayCrosses X Q (A, B) := by
  rintro ⟨Z, hZ, hAZB⟩
  exact pasch3 hAZB (hZ.onLine hXℓ hQℓ) h

/-- Two points strictly within a finite straight line, read from one end, come in some
order. -/
theorem between_order {A B Y Z : Point} (hY : Between A Y B) (hZ : Between A Z B)
    (hYZ : Y ≠ Z) : Between A Y Z ∨ Between A Z Y := by
  obtain ⟨N, hAN, hBN⟩ := Postulate1 A B (ne_of_between_ends hY)
  rcases between_cases (ne_of_between hY) hYZ (ne_of_between hZ) hAN
      (on_line_of_between_ends hY hAN hBN) (on_line_of_between_ends hZ hAN hBN) with
    h | h | h
  · exact Or.inl h
  · exact absurd h ((OnRay.of_between hY).not_between (OnRay.of_between hZ))
  · exact Or.inr h

/-! ## One finite straight line against an angle

Throughout, the straight line `ℓ` joins X to Q and `m` joins X to R, with R off `ℓ` and Q
off `m`; the finite straight line AB has its ends off both and does not pass through X. -/

section Angle

variable {X Q R A B : Point} {ℓ m : Line}

/-- **Across one straight line only.** If AB crosses the straight line XQ but not XR, it
crosses the ray through Q exactly when A is on Q's side of XR, and never the ray through R. -/
theorem one_line_crossed (hXQ : X ≠ Q) (hXℓ : OnLine X ℓ) (hQℓ : OnLine Q ℓ) (hXm : OnLine X m)
    (hRm : OnLine R m) (hQm : ¬ OnLine Q m) (hAℓ : ¬ OnLine A ℓ)
    (hBℓ : ¬ OnLine B ℓ) (hX : ¬ Between A X B) (hℓ : ¬ SameSide A B ℓ)
    (hm : SameSide A B m) :
    (RayCrosses X Q (A, B) ↔ SameSide A Q m) ∧ ¬ RayCrosses X R (A, B) := by
  obtain ⟨Y, hYℓ, hY⟩ := OppositeSides.exists_between ⟨hAℓ, hBℓ, hℓ⟩
  have hYX : Y ≠ X := fun e => hX (e ▸ hY)
  refine ⟨?_, not_crosses_of_sameSide hXm hRm hm⟩
  rw [crosses_at hXℓ hQℓ hAℓ hY hYℓ, onRay_iff_sameSide hXQ hXℓ hQℓ hXm hQm hYℓ hYX]
  exact sameSide_congr (same_side_symm (pasch1 hY hm))

/-- **Across both straight lines, XQ first.** If AB crosses the straight line XQ at Y and
then XR at Z, it crosses the ray through Q exactly when A is on Q's side of XR, and the ray
through R exactly when B is on R's side of XQ. -/
theorem both_lines_crossed (hXQ : X ≠ Q) (hXR : X ≠ R) (hXℓ : OnLine X ℓ)
    (hQℓ : OnLine Q ℓ) (hXm : OnLine X m) (hRm : OnLine R m) (hRℓ : ¬ OnLine R ℓ)
    (hQm : ¬ OnLine Q m) (hAℓ : ¬ OnLine A ℓ) (hAm : ¬ OnLine A m) (hX : ¬ Between A X B)
    {Y Z : Point} (hYℓ : OnLine Y ℓ) (hY : Between A Y B) (hZm : OnLine Z m)
    (hZ : Between A Z B) (hYZ : Between A Y Z) :
    (RayCrosses X Q (A, B) ↔ SameSide A Q m) ∧ (RayCrosses X R (A, B) ↔ SameSide B R ℓ) := by
  have hYX : Y ≠ X := fun e => hX (e ▸ hY)
  have hZX : Z ≠ X := fun e => hX (e ▸ hZ)
  have hYm : ¬ OnLine Y m := fun h =>
    hRℓ (line_unique hYX h hXm hYℓ hXℓ ▸ hRm)
  have hZℓ : ¬ OnLine Z ℓ := fun h =>
    hQm (line_unique hZX h hXℓ hZm hXm ▸ hQℓ)
  constructor
  · rw [crosses_at hXℓ hQℓ hAℓ hY hYℓ, onRay_iff_sameSide hXQ hXℓ hQℓ hXm hQm hYℓ hYX]
    exact sameSide_congr (pasch2 (between_symm hYZ) hZm hYm)
  · rw [crosses_at hXm hRm hAm hZ hZm, onRay_iff_sameSide hXR hXm hRm hXℓ hRℓ hZm hZX]
    exact sameSide_congr (pasch2 (between_inner hYZ hZ) hYℓ hZℓ)

/-- **One side against the angle.** The finite straight line AB crosses the rays through Q
and through R together an odd number of times exactly when one of A and B is within the
angle QXR and the other is not. -/
theorem side_parity (hXQ : X ≠ Q) (hXR : X ≠ R) (hXℓ : OnLine X ℓ) (hQℓ : OnLine Q ℓ)
    (hXm : OnLine X m) (hRm : OnLine R m) (hRℓ : ¬ OnLine R ℓ) (hQm : ¬ OnLine Q m)
    (hAℓ : ¬ OnLine A ℓ) (hBℓ : ¬ OnLine B ℓ) (hAm : ¬ OnLine A m) (hBm : ¬ OnLine B m)
    (hX : ¬ Between A X B) :
    (RayCrosses X Q (A, B) ↔ RayCrosses X R (A, B)) ↔
      ((SameSide A R ℓ ∧ SameSide A Q m) ↔ (SameSide B R ℓ ∧ SameSide B Q m)) := by
  have eℓ := sameSide_iff_iff hAℓ hBℓ hRℓ (L := ℓ)
  have em := sameSide_iff_iff hAm hBm hQm (L := m)
  by_cases hℓ : SameSide A B ℓ <;> by_cases hm : SameSide A B m
  · /- Neither straight line is crossed, and the ends agree about both. -/
    have nQ := not_crosses_of_sameSide hXℓ hQℓ hℓ
    have nR := not_crosses_of_sameSide hXm hRm hm
    have e₁ := eℓ.mp hℓ
    have e₂ := em.mp hm
    grind
  · /- Only XR is crossed. -/
    obtain ⟨hR', nQ⟩ := one_line_crossed hXR hXm hRm hXℓ hQℓ hRℓ hAm hBm hX hm hℓ
    have e₁ := eℓ.mp hℓ
    have e₂ : ¬ (SameSide A Q m ↔ SameSide B Q m) := fun e => hm (em.mpr e)
    grind
  · /- Only XQ is crossed. -/
    obtain ⟨hQ', nR⟩ := one_line_crossed hXQ hXℓ hQℓ hXm hRm hQm hAℓ hBℓ hX hℓ hm
    have e₁ : ¬ (SameSide A R ℓ ↔ SameSide B R ℓ) := fun e => hℓ (eℓ.mpr e)
    have e₂ := em.mp hm
    grind
  · /- Both are crossed, at different points, since AB misses X. -/
    have e₁ : ¬ (SameSide A R ℓ ↔ SameSide B R ℓ) := fun e => hℓ (eℓ.mpr e)
    have e₂ : ¬ (SameSide A Q m ↔ SameSide B Q m) := fun e => hm (em.mpr e)
    obtain ⟨Y, hYℓ, hY⟩ := OppositeSides.exists_between ⟨hAℓ, hBℓ, hℓ⟩
    obtain ⟨Z, hZm, hZ⟩ := OppositeSides.exists_between ⟨hAm, hBm, hm⟩
    have hYZ : Y ≠ Z := by
      intro e
      subst e
      have hYX : Y ≠ X := fun e => hX (e ▸ hY)
      exact hRℓ (line_unique hYX hZm hXm hYℓ hXℓ ▸ hRm)
    rcases between_order hY hZ hYZ with h | h
    · obtain ⟨hQ', hR'⟩ := both_lines_crossed hXQ hXR hXℓ hQℓ hXm hRm hRℓ hQm hAℓ hAm hX
        hYℓ hY hZm hZ h
      grind
    · obtain ⟨hR', hQ'⟩ := both_lines_crossed hXR hXQ hXm hRm hXℓ hQℓ hQm hRℓ hAm hAℓ hX
        hZm hZ hYℓ hY h
      grind

end Angle

/-! ## Counting round a closed outline -/

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

/-- The second ends of a chain's segments are its points after the first. -/
theorem segments_map_snd (a : Point) (l : List Point) :
    (segments (a :: l)).map Prod.snd = l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    have he : segments (a :: b :: l) = (a, b) :: segments (b :: l) := rfl
    rw [he, List.map_cons, ih]

/-- The second ends of the sides are the corners, in another order. -/
theorem sides_map_snd_perm (ps : List Point) : ((sides ps).map Prod.snd).Perm ps := by
  cases ps with
  | nil => exact List.Perm.refl _
  | cons c cs =>
    have he : (sides (c :: cs)).map Prod.snd = cs ++ [c] := segments_map_snd c (cs ++ [c])
    rw [he]
    exact List.perm_append_comm

/-- No two sides of a list of distinct corners end at one corner. -/
theorem sides_pairwise_snd {ps : List Point} (h : ps.Nodup) :
    (sides ps).Pairwise (fun s t => s.2 ≠ t.2) := by
  have hm : ((sides ps).map Prod.snd).Nodup := (sides_map_snd_perm ps).nodup_iff.mpr h
  exact List.pairwise_map.mp hm

/-- Two sides of a list of distinct corners that end at one corner are one side. -/
theorem sides_snd_inj {ps : List Point} (h : ps.Nodup) {s t : Point × Point}
    (hs : s ∈ sides ps) (ht : t ∈ sides ps) (he : s.2 = t.2) : s = t := by
  rcases LoopFacts.pairwise_mem (sides_pairwise_snd h) hs ht with e | e | e
  · exact e
  · exact False.elim (e he)
  · exact False.elim (e he.symm)

/-- **Ends counted over the sides come in pairs.** Each corner is the first end of one side
and the second end of one other. -/
theorem ends_count (ps : List Point) (w : Point → Bool) :
    (sides ps).countP (fun s => w s.1) + (sides ps).countP (fun s => w s.2) =
      2 * ps.countP w := by
  have h₁ : (sides ps).countP (fun s => w s.1) = ps.countP w := by
    have hc := List.countP_map (p := w) (f := Prod.fst) (l := sides ps)
    rw [LoopFacts.sides_map_fst] at hc
    exact hc.symm
  have h₂ : (sides ps).countP (fun s => w s.2) = ps.countP w := by
    have hc := List.countP_map (p := w) (f := Prod.snd) (l := sides ps)
    rw [(sides_map_snd_perm ps).countP_eq] at hc
    exact hc.symm
  omega

/-! ## Two good rays -/

/-- **Two good rays not on one straight line** give the same parity: each side crosses them
together oddly exactly when its ends disagree about the angle between them, and those ends
pair off round the outline. -/
theorem parity_of_angle {ps : List Point} {X Q R : Point} (hX : ¬ LoopBoundary ps X)
    (hQ : GoodRay ps X Q) (hR : GoodRay ps X R) (hXQR : Triangle X Q R) :
    crossingCount ps X Q % 2 = crossingCount ps X R % 2 := by
  classical
  obtain ⟨hXQ, hQV⟩ := hQ
  obtain ⟨hXR, hRV⟩ := hR
  obtain ⟨ℓ, hXℓ, hQℓ⟩ := Postulate1 X Q hXQ
  obtain ⟨m, hXm, hRm⟩ := Postulate1 X R hXR
  have hRℓ : ¬ OnLine R ℓ := fun h => hXQR ⟨ℓ, hXℓ, hQℓ, h⟩
  have hQm : ¬ OnLine Q m := fun h => hXQR ⟨m, hXm, h, hRm⟩
  have offℓ : ∀ V ∈ ps, ¬ OnLine V ℓ := fun V hV h => hQV V hV ⟨ℓ, hXℓ, hQℓ, h⟩
  have offm : ∀ V ∈ ps, ¬ OnLine V m := fun V hV h => hRV V hV ⟨m, hXm, hRm, h⟩
  let w : Point → Bool := fun V => decide (SameSide V R ℓ ∧ SameSide V Q m)
  have key : ∀ s ∈ sides ps,
      (decide (RayCrosses X Q s) = decide (RayCrosses X R s) ↔ w s.1 = w s.2) := by
    intro s hs
    have h₁ := (LoopFacts.side_mem hs).1
    have h₂ := (LoopFacts.side_mem hs).2
    have hXs : ¬ Between s.1 X s.2 := fun h => hX ⟨s, hs, Or.inr (Or.inr h)⟩
    simp only [w, decide_eq_decide]
    exact side_parity hXQ hXR hXℓ hQℓ hXm hRm hRℓ hQm (offℓ _ h₁) (offℓ _ h₂)
      (offm _ h₁) (offm _ h₂) hXs
  have hc := countP_parity (sides ps) _ _ (fun s => w s.1) (fun s => w s.2) key
  rw [ends_count ps w] at hc
  unfold crossingCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  omega

/-- **A good ray off finitely many straight lines.** From a point that is no corner, a ray
through a point inside a frame of three corners (`LoopFacts.simple_frame`), away from the
straight lines joining the point to the corners and from the given straight lines. -/
theorem good_ray_avoiding {ps : List Point} (h : SimpleLoop ps) {X : Point} (hX : X ∉ ps)
    (ls : List Line) : ∃ Q : Point, GoodRay ps X Q ∧ Avoid ls Q := by
  let line (V : Point) : Line := Classical.choose (collinear_of_two X V)
  have hline (V : Point) : OnLine X (line V) ∧ OnLine V (line V) :=
    Classical.choose_spec (collinear_of_two X V)
  obtain ⟨A, hA, B, -, C, -, hABC⟩ := LoopFacts.simple_frame h
  obtain ⟨Q, -, hQ⟩ := triangle_point_avoiding hABC (ls ++ ps.map line)
  have hQl {V : Point} (hV : V ∈ ps) : ¬ OnLine Q (line V) :=
    hQ (line V) (List.mem_append_right _ (List.mem_map_of_mem hV))
  refine ⟨Q, ⟨fun hXQ => hQl hA (hXQ ▸ (hline A).1), fun V hV hcol => ?_⟩,
    fun L hL => hQ L (List.mem_append_left _ hL)⟩
  obtain ⟨M, hXM, hQM, hVM⟩ := hcol
  have hVX : V ≠ X := fun e => hX (e ▸ hV)
  have he : line V = M := line_unique hVX.symm (hline V).1 (hline V).2 hXM hVM
  exact hQl hV (he ▸ hQM)

/-- **A third good ray**, off the straight line of a given one (`good_ray_avoiding`). -/
theorem third_ray {ps : List Point} (h : SimpleLoop ps) {X Q : Point} (hQ : GoodRay ps X Q) :
    ∃ P : Point, GoodRay ps X P ∧ Triangle X Q P := by
  obtain ⟨ℓ, hXℓ, hQℓ⟩ := Postulate1 X Q hQ.1
  have hX : X ∉ ps := fun hm => hQ.2 X hm ⟨ℓ, hXℓ, hQℓ, hXℓ⟩
  obtain ⟨P, hP, hPa⟩ := good_ray_avoiding h hX [ℓ]
  refine ⟨P, hP, ?_⟩
  rintro ⟨M, hXM, hQM, hPM⟩
  exact hPa ℓ List.mem_cons_self (line_unique hQ.1 hXM hQM hXℓ hQℓ ▸ hPM)

/-- **Two good rays give the same parity.** Rays not on one straight line compare through
the angle between them; rays on one straight line each compare with a third good ray off
it. This is the statement of `crossing_parity_independent`, proved here because
`remove_corner` below and `OutlineFacts.lean` use it, and come before `Outlines.lean`, which
states it. -/
theorem parity_independent {ps : List Point} (h : SimpleLoop ps) {X Q R : Point}
    (hX : ¬ LoopBoundary ps X) (hQ : GoodRay ps X Q) (hR : GoodRay ps X R) :
    crossingCount ps X Q % 2 = crossingCount ps X R % 2 := by
  by_cases hXQR : Collinear X Q R
  · obtain ⟨P, hP, hXQP⟩ := third_ray h hQ
    have hXPR : Triangle X P R := by
      rintro ⟨M, hXM, hPM, hRM⟩
      obtain ⟨L, hXL, hQL, hRL⟩ := hXQR
      have he : L = M := line_unique hR.1 hXL hRL hXM hRM
      exact hXQP ⟨L, hXL, hQL, he ▸ hPM⟩
    exact (parity_of_angle hX hQ hP hXQP).trans (parity_of_angle hX hP hR hXPR)
  · exact parity_of_angle hX hQ hR hXQR

/-! ## A corner between its neighbours

For `loop_normalise`. A corner is removed only when it lies between its neighbours, so the two
sides at it make one finite straight line. Read from the corner before it, the outline is
`a :: b :: c :: rest`, and without b it is `a :: c :: rest`: the side ac replaces ab and bc,
and every other side stays. -/

/-- With b between a and c, the finite straight line ac is made of ab and bc. -/
theorem onFiniteLine_split {a b c X : Point} (habc : Between a b c) :
    OnFiniteLine X a c ↔ OnFiniteLine X a b ∨ OnFiniteLine X b c := by
  constructor
  · rintro (e | e | hX)
    · exact Or.inl (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · by_cases hXb : X = b
      · exact Or.inl (Or.inr (Or.inl hXb))
      · rcases between_order hX habc hXb with h | h
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inr (between_inner h hX)))
  · rintro ((e | e | hX) | (e | e | hX))
    · exact Or.inl e
    · exact Or.inr (Or.inr (e ▸ habc))
    · exact Or.inr (Or.inr (between_of_between_left habc hX))
    · exact Or.inr (Or.inr (e ▸ habc))
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (between_symm
        (between_of_between_left (between_symm habc) (between_symm hX))))

section Remove

variable {a b c : Point} {rest : List Point}

/-- The sides of `a :: b :: c :: rest`: ab, bc, and the chain from c round to a. -/
theorem sides_four :
    sides (a :: b :: c :: rest) = (a, b) :: (b, c) :: segments (c :: rest ++ [a]) := rfl

/-- The sides of `a :: c :: rest`: ac, and the same chain from c round to a. -/
theorem sides_three : sides (a :: c :: rest) = (a, c) :: segments (c :: rest ++ [a]) := rfl

/-- Removing b leaves the boundary as it was. -/
theorem remove_boundary (habc : Between a b c) (X : Point) :
    LoopBoundary (a :: c :: rest) X ↔ LoopBoundary (a :: b :: c :: rest) X := by
  unfold LoopBoundary
  rw [sides_three, sides_four]
  simp only [List.mem_cons, exists_eq_or_imp]
  rw [onFiniteLine_split habc, or_assoc]

/-- Removing b leaves a simple loop, when three corners or more remain: the side ac meets
another side only where ab or bc did, and never at b, which is on no other side. -/
theorem remove_simple (h : SimpleLoop (a :: b :: c :: rest)) (hrest : rest ≠ [])
    (habc : Between a b c) : SimpleLoop (a :: c :: rest) := by
  obtain ⟨-, hnd, hne, hpw⟩ := h
  have hb : b ∉ c :: rest ++ [a] := by
    intro hm
    rw [List.nodup_cons, List.nodup_cons] at hnd
    rcases List.mem_append.mp hm with hm | hm
    · exact hnd.2.1 hm
    · exact hnd.1 (by rw [List.mem_singleton.mp hm]; exact List.mem_cons_self)
  rw [sides_four] at hne hpw
  rw [List.pairwise_cons, List.pairwise_cons] at hpw
  obtain ⟨hab, ⟨hbc, hT⟩⟩ := hpw
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases rest with
    | nil => exact absurd rfl hrest
    | cons d rest => simp
  · exact hnd.sublist (List.Sublist.cons_cons a ((List.Sublist.refl _).cons b))
  · rw [sides_three]
    intro s hs
    rcases List.mem_cons.mp hs with e | hs
    · rw [e]
      exact ne_of_between_ends habc
    · exact hne s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
  · rw [sides_three, List.pairwise_cons]
    refine ⟨fun t ht X hXac hXt => ?_, hT⟩
    have hends := segment_corners ht
    have notb (e : X = b) (e' : X = t.1 ∨ X = t.2) : False := by
      rcases e' with e' | e'
      · exact hb (by rw [← e, e']; exact hends.1)
      · exact hb (by rw [← e, e']; exact hends.2)
    rcases (onFiniteLine_split habc).mp hXac with hX | hX
    · obtain ⟨h₁, h₂⟩ := hab t (List.mem_cons_of_mem _ ht) X hX hXt
      refine ⟨?_, h₂⟩
      rcases h₁ with e | e
      · exact Or.inl e
      · exact absurd (notb e h₂) id
    · obtain ⟨h₁, h₂⟩ := hbc t ht X hX hXt
      refine ⟨?_, h₂⟩
      rcases h₁ with e | e
      · exact absurd (notb e h₂) id
      · exact Or.inr e

/-- A good ray crosses ac exactly when it crosses ab or bc, and never both: its straight
line misses a, b and c, and meets the straight line ac once. So removing b leaves the
crossing count of a good ray as it was. -/
theorem remove_count (habc : Between a b c) {X Q : Point}
    (hQ : GoodRay (a :: b :: c :: rest) X Q) :
    crossingCount (a :: c :: rest) X Q = crossingCount (a :: b :: c :: rest) X Q := by
  classical
  obtain ⟨hXQ, hV⟩ := hQ
  obtain ⟨ℓ, hXℓ, hQℓ⟩ := Postulate1 X Q hXQ
  have ha : ¬ OnLine a ℓ := fun h => hV a (by simp) ⟨ℓ, hXℓ, hQℓ, h⟩
  have hb : ¬ OnLine b ℓ := fun h => hV b (by simp) ⟨ℓ, hXℓ, hQℓ, h⟩
  have hc : ¬ OnLine c ℓ := fun h => hV c (by simp) ⟨ℓ, hXℓ, hQℓ, h⟩
  obtain ⟨N, haN, hcN⟩ := Postulate1 a c (ne_of_between_ends habc)
  have hiff : RayCrosses X Q (a, c) ↔ RayCrosses X Q (a, b) ∨ RayCrosses X Q (b, c) := by
    constructor
    · rintro ⟨Y, hY, hYac⟩
      have hYℓ := hY.onLine hXℓ hQℓ
      rcases (onFiniteLine_split habc).mp (Or.inr (Or.inr hYac)) with
        (e | e | h) | (e | e | h)
      · exact absurd (e ▸ hYℓ) ha
      · exact absurd (e ▸ hYℓ) hb
      · exact Or.inl ⟨Y, hY, h⟩
      · exact absurd (e ▸ hYℓ) hb
      · exact absurd (e ▸ hYℓ) hc
      · exact Or.inr ⟨Y, hY, h⟩
    · rintro (⟨Y, hY, hYab⟩ | ⟨Y, hY, hYbc⟩)
      · exact ⟨Y, hY, between_of_between_left habc hYab⟩
      · exact ⟨Y, hY, between_symm
          (between_of_between_left (between_symm habc) (between_symm hYbc))⟩
  have hex : ¬ (RayCrosses X Q (a, b) ∧ RayCrosses X Q (b, c)) := by
    rintro ⟨⟨Y, hY, hYab⟩, ⟨Z, hZ, hZbc⟩⟩
    have hYab' : Between a Y b := hYab
    have hZbc' : Between b Z c := hZbc
    have hYN : OnLine Y N :=
      on_line_of_between_ends (between_of_between_left habc hYab') haN hcN
    have hZN : OnLine Z N := on_line_of_between_ends (between_symm
      (between_of_between_left (between_symm habc) (between_symm hZbc'))) haN hcN
    by_cases hYZ : Y = Z
    · rw [← hYZ] at hZbc'
      exact not_between_of_between (between_inner hYab' habc) hZbc'
    · exact ha (line_unique hYZ (hY.onLine hXℓ hQℓ) (hZ.onLine hXℓ hQℓ) hYN hZN ▸ haN)
  unfold crossingCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, sides_three, sides_four]
  simp only [List.countP_cons]
  by_cases h₁ : RayCrosses X Q (a, b) <;> by_cases h₂ : RayCrosses X Q (b, c)
  · exact absurd ⟨h₁, h₂⟩ hex
  · have h₃ : RayCrosses X Q (a, c) := hiff.mpr (Or.inl h₁)
    simp [h₁, h₂, h₃]
  · have h₃ : RayCrosses X Q (a, c) := hiff.mpr (Or.inr h₂)
    simp [h₁, h₂, h₃]
  · have h₃ : ¬ RayCrosses X Q (a, c) := fun h => (hiff.mp h).elim h₁ h₂
    simp [h₁, h₂, h₃]

/-- **Removing a corner between its neighbours** leaves a simple loop with the same boundary
and the same region. A good ray of the new outline that runs through b compares with a third
good ray, off b's straight line from X, which is good for both. -/
theorem remove_corner (h : SimpleLoop (a :: b :: c :: rest)) (hrest : rest ≠ [])
    (habc : Between a b c) :
    SimpleLoop (a :: c :: rest) ∧
      (∀ X : Point, LoopBoundary (a :: c :: rest) X ↔ LoopBoundary (a :: b :: c :: rest) X) ∧
      (∀ X : Point, LoopRegion (a :: c :: rest) X ↔ LoopRegion (a :: b :: c :: rest) X) := by
  have hs := remove_simple h hrest habc
  have hbd : ∀ X, LoopBoundary (a :: c :: rest) X ↔ LoopBoundary (a :: b :: c :: rest) X :=
    remove_boundary habc
  have hmem : ∀ V ∈ a :: b :: c :: rest, V = b ∨ V ∈ a :: c :: rest := by
    intro V hV
    simp only [List.mem_cons] at hV ⊢
    rcases hV with e | e | e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inl e
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr e))
  have hsub : ∀ V ∈ a :: c :: rest, V ∈ a :: b :: c :: rest := by
    intro V hV
    simp only [List.mem_cons] at hV ⊢
    rcases hV with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr e))
  refine ⟨hs, hbd, fun X => ?_⟩
  unfold LoopRegion LoopInside
  rw [hbd]
  by_cases hXb : LoopBoundary (a :: b :: c :: rest) X
  · exact ⟨fun _ => Or.inl hXb, fun _ => Or.inl hXb⟩
  have hXbq : ¬ LoopBoundary (a :: c :: rest) X := fun h' => hXb ((hbd X).mp h')
  constructor
  · rintro (hb' | ⟨-, Q, hQ, hodd⟩)
    · exact Or.inl hb'
    refine Or.inr ⟨hXb, ?_⟩
    by_cases hQb : Collinear X Q b
    · obtain ⟨P, hP, hXQP⟩ := third_ray hs hQ
      have hXb' : X ≠ b := fun e => hXb ⟨(a, b), by rw [sides_four]; exact List.mem_cons_self,
        Or.inr (Or.inl e)⟩
      have hPps : GoodRay (a :: b :: c :: rest) X P := by
        refine ⟨hP.1, fun V hV hcol => ?_⟩
        rcases hmem V hV with e | hV'
        · rw [e] at hcol
          obtain ⟨L, hXL, hQL, hbL⟩ := hQb
          obtain ⟨M, hXM, hPM, hbM⟩ := hcol
          exact hXQP ⟨L, hXL, hQL, line_unique hXb' hXM hbM hXL hbL ▸ hPM⟩
        · exact hP.2 V hV' hcol
      refine ⟨P, hPps, ?_⟩
      rw [← remove_count habc hPps, ← parity_independent hs hXbq hQ hP]
      exact hodd
    · have hQps : GoodRay (a :: b :: c :: rest) X Q := by
        refine ⟨hQ.1, fun V hV hcol => ?_⟩
        rcases hmem V hV with e | hV'
        · exact hQb (e ▸ hcol)
        · exact hQ.2 V hV' hcol
      refine ⟨Q, hQps, ?_⟩
      rw [← remove_count habc hQps]
      exact hodd
  · rintro (hb' | ⟨-, Q, hQ, hodd⟩)
    · exact Or.inl hb'
    refine Or.inr ⟨hXb, Q, ⟨hQ.1, fun V hV => hQ.2 V (hsub V hV)⟩, ?_⟩
    rw [remove_count habc hQ]
    exact hodd

end Remove

/-! ## Finding a corner between its neighbours -/

/-- The consecutive triples of a closed outline are made of its sides. -/
theorem triple_sides {ps : List Point} {t : Point × Point × Point}
    (ht : t ∈ triples (ps ++ ps.take 2)) :
    (t.1, t.2.1) ∈ sides ps ∧ (t.2.1, t.2.2) ∈ sides ps := by
  have hsub : ∀ s ∈ segments (ps ++ ps.take 2), s ∈ sides ps := by
    intro s hs
    rcases ps with _ | ⟨p, _ | ⟨q, rest⟩⟩
    · simp [segments] at hs
    · exact hs
    · have he : segments (p :: q :: rest ++ (p :: q :: rest).take 2) =
          sides (p :: q :: rest) ++ [(p, q)] := by
        show segments ((p :: q :: rest) ++ p :: [q]) =
          segments ((p :: q :: rest) ++ [p]) ++ segments [p, q]
        exact segments_join _ _ _
      rw [he] at hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hs
      · rw [List.mem_singleton.mp hs]
        exact List.mem_cons_self
  obtain ⟨h₁, h₂⟩ := LoopFacts.triples_segments _ t ht
  exact ⟨hsub _ h₁, hsub _ h₂⟩

/-- Two different sides of a simple loop meet only at ends of both. -/
theorem side_meet {ps : List Point} (h : SimpleLoop ps) {s t : Point × Point}
    (hs : s ∈ sides ps) (ht : t ∈ sides ps) (hst : s ≠ t) (X : Point) :
    OnFiniteLine X s.1 s.2 → OnFiniteLine X t.1 t.2 →
      (X = s.1 ∨ X = s.2) ∧ (X = t.1 ∨ X = t.2) := by
  rcases LoopFacts.pairwise_mem h.2.2.2 hs ht with e | e | e
  · exact absurd e hst
  · exact e X
  · intro h₁ h₂
    exact (e X h₂ h₁).symm

/-- Read from x, a closed outline of distinct corners with sides xy and yz begins x, y, z. -/
theorem rotate_to {ps : List Point} (hnd : ps.Nodup) (hlen : 3 ≤ ps.length) {x y z : Point}
    (hxy : (x, y) ∈ sides ps) (hyz : (y, z) ∈ sides ps) :
    ∃ us vs rest : List Point, ps = us ++ vs ∧ vs ++ us = x :: y :: z :: rest := by
  obtain ⟨us, ws, rfl⟩ := List.append_of_mem (LoopFacts.side_mem hxy).1
  have hperm := LoopFacts.sides_rotate_perm us (x :: ws)
  have hxy' := hperm.mem_iff.mp hxy
  have hyz' := hperm.mem_iff.mp hyz
  have hnd' : (x :: ws ++ us).Nodup := List.perm_append_comm.nodup_iff.mp hnd
  have hlen' : 3 ≤ (x :: ws ++ us).length := by
    simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  rw [List.cons_append] at hxy' hyz' hnd' hlen'
  obtain ⟨r, hr⟩ : ∃ r, ws ++ us = r := ⟨_, rfl⟩
  rw [hr] at hxy' hyz' hnd' hlen'
  rcases r with _ | ⟨w, _ | ⟨w', rest⟩⟩
  · simp at hlen'
  · simp at hlen'
  have h₁ : (x, w) ∈ sides (x :: w :: w' :: rest) := by simp [sides, segments]
  have h₂ : (w, w') ∈ sides (x :: w :: w' :: rest) := by simp [sides, segments]
  have e₁ : (x, y) = (x, w) := LoopFacts.sides_fst_inj hnd' hxy' h₁ rfl
  rw [Prod.mk.injEq] at e₁
  rw [e₁.2] at hyz'
  have e₂ : (w, z) = (w, w') := LoopFacts.sides_fst_inj hnd' hyz' h₂ rfl
  rw [Prod.mk.injEq] at e₂
  refine ⟨us, x :: ws, rest, rfl, ?_⟩
  rw [List.cons_append, hr, e₁.2, e₂.2]

/-- **A corner between its neighbours.** A simple loop that is not reduced has three
consecutive corners on one straight line; the middle one is between the others, since two
neighbouring sides meet only at their common end. Read from the first of them, the outline
has a fourth corner, for three corners of a simple loop make a triangle. -/
theorem straight_corner {ps : List Point} (h : SimpleLoop ps) (hr : ¬ ReducedLoop ps) :
    ∃ us vs : List Point, ∃ a b c : Point, ∃ rest : List Point,
      ps = us ++ vs ∧ vs ++ us = a :: b :: c :: rest ∧ rest ≠ [] ∧ Between a b c := by
  obtain ⟨t, ht, hcol⟩ : ∃ t ∈ triples (ps ++ ps.take 2), Collinear t.1 t.2.1 t.2.2 :=
    Classical.byContradiction fun hno => hr fun t ht hc => hno ⟨t, ht, hc⟩
  obtain ⟨h₁, h₂⟩ := triple_sides ht
  have hne₁ := h.2.2.1 _ h₁
  have hne₂ := h.2.2.1 _ h₂
  have hst : (t.1, t.2.1) ≠ (t.2.1, t.2.2) := fun e => hne₁ (Prod.mk.inj e).1
  have hb := LoopFacts.straight_of_collinear (side_meet h h₁ h₂ hst) hne₁ hne₂ hcol
  obtain ⟨us, vs, rest, rfl, hrot⟩ := rotate_to h.2.1 h.1 h₁ h₂
  refine ⟨us, vs, t.1, t.2.1, t.2.2, rest, rfl, hrot, ?_, hb⟩
  rintro rfl
  obtain ⟨A, hA, B, hB, C, hC, hABC⟩ := LoopFacts.simple_frame h
  obtain ⟨L, hx, hy, hz⟩ := hcol
  have hon : ∀ V ∈ us ++ vs, OnLine V L := by
    intro V hV
    have hV' : V ∈ vs ++ us := List.perm_append_comm.mem_iff.mp hV
    rw [hrot] at hV'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hV'
    rcases hV' with e | e | e <;> rw [e]
    · exact hx
    · exact hy
    · exact hz
  exact hABC ⟨L, hon A hA, hon B hB, hon C hC⟩

end Parity

end Elements.Figures
