import Elements.Figure.Divisions.ExtractRay

/-!
# Book Zero: the sides of triangles that lie apart, cut at their corners

Helper lemmas, in the namespace `Extract`, for `apart_has_outline`, in `Divisions.lean`
(brief 0013, section 8, "The arrangement and general division"; D10): the first step of
`Divisions/Extract.lean`. Nothing in Book Zero cites a proposition of the *Elements*.

Take triangles that lie apart (`Apart`). Their corners cut their sides into **elementary
finite straight lines** (`Elem`): a finite straight line between two corners, along a side of
one of the triangles, with no corner strictly between its ends.

* **No point of a side is inside a triangle** (`int_not_on_side`): near such a point both
  triangles would have inner points in common.
* **Sides never cross** (`no_cross`): two sides that cross at a point strictly within both
  would carry inner points of both triangles near it.
* **Two elementary lines meet only at common ends** (`elem_meet`); two that share a point
  strictly within both are the same (`elem_overlap`).
* **At most two triangles along one** (`mult_le_two`): two triangles against one elementary
  line lie on opposite sides of it, and of three, two would be on one side.
* **A side is cut into elementary lines** (`side_elem`), and **a corner of the figure is an
  end of exactly two elementary lines along the sides of any triangle through it**
  (`two_at`): one in each direction along each side through it.
-/

namespace Elements.Figures

namespace Extract

open Tacit Classical

/-! ## Order on a finite straight line -/

/-- A point between two points of a finite straight line is strictly within it. -/
theorem between_within {a b P Q X : Point} (hP : OnFiniteLine P a b) (hQ : OnFiniteLine Q a b)
    (hX : Between P X Q) : Between a X b := by
  rcases hP with rfl | rfl | hP <;> rcases hQ with rfl | rfl | hQ
  · exact absurd rfl (ne_of_between_ends hX)
  · exact hX
  · exact between_of_between_left hQ hX
  · exact between_symm hX
  · exact absurd rfl (ne_of_between_ends hX)
  · exact between_symm (between_of_between_left (between_symm hQ) hX)
  · exact between_of_between_left hP (between_symm hX)
  · exact between_symm (between_of_between_left (between_symm hP) (between_symm hX))
  · rcases Parity.between_order hP hQ (ne_of_between_ends hX) with h | h
    · exact between_of_between_left hQ (between_shift (between_cut h hX) hX)
    · exact between_of_between_left hP
        (between_shift (between_cut h (between_symm hX)) (between_symm hX))

/-- A point of a finite straight line between two points of another lies on the other. -/
theorem onFinite_within {a b P Q X : Point} (hP : OnFiniteLine P a b) (hQ : OnFiniteLine Q a b)
    (hX : OnFiniteLine X P Q) : OnFiniteLine X a b := by
  rcases hX with rfl | rfl | hX
  · exact hP
  · exact hQ
  · exact Or.inr (Or.inr (between_within hP hQ hX))

/-- Two points of a finite straight line, other than its end V, are not on opposite sides of
V. -/
theorem not_between_end {V D W W' : Point} (hW : OnFiniteLine W V D) (hW' : OnFiniteLine W' V D)
    (hWV : W ≠ V) (hW'V : W' ≠ V) : ¬ Between W V W' := by
  intro hb
  rcases hW with e | rfl | hW
  · exact hWV e
  · rcases hW' with e | rfl | hW'
    · exact hW'V e
    · exact ne_of_between_ends hb rfl
    · exact not_between_of_between hW' (between_symm hb)
  · rcases hW' with e | rfl | hW'
    · exact hW'V e
    · exact not_between_of_between hW hb
    · exact (OnRay.of_between hW).not_between (OnRay.of_between hW') hb

/-- Points on either side of an inner point of a finite straight line, towards its two ends,
are on opposite sides of it. -/
theorem opposite_ends {a b Y P Q : Point} (hY : Between a Y b) (hP : OnFiniteLine P Y a)
    (hPY : P ≠ Y) (hQ : OnFiniteLine Q Y b) (hQY : Q ≠ Y) : Between P Y Q := by
  rcases hP with e | rfl | hP
  · exact absurd e hPY
  · rcases hQ with e | rfl | hQ
    · exact absurd e hQY
    · exact hY
    · exact between_cut hY hQ
  · rcases hQ with e | rfl | hQ
    · exact absurd e hQY
    · exact between_symm (between_cut (between_symm hY) hP)
    · exact between_inner (between_symm hP) (between_cut hY hQ)

/-- A point of both halves of a finite straight line, cut at an inner point, is that point. -/
theorem halves_meet {u V v W : Point} (h : Between u V v) (h₁ : OnFiniteLine W V u)
    (h₂ : OnFiniteLine W V v) : W = V := by
  refine Classical.byContradiction fun hWV => ?_
  exact ne_of_between_ends (opposite_ends h h₁ hWV h₂ hWV) rfl

/-! ## Triangles -/

/-- The sides of a triangle given by its corners. -/
def triSides (t : Point × Point × Point) : List (Point × Point) := sides [t.1, t.2.1, t.2.2]

theorem mem_triSides {t : Point × Point × Point} {s : Point × Point} :
    s ∈ triSides t ↔ s = (t.1, t.2.1) ∨ s = (t.2.1, t.2.2) ∨ s = (t.2.2, t.1) := by
  simp [triSides, sides, segments]

/-- X lies on the finite straight line s. -/
def OnSeg (X : Point) (s : Point × Point) : Prop := OnFiniteLine X s.1 s.2

/-- Both ends of e lie on the finite straight line s, so e lies along it. -/
def Within (e s : Point × Point) : Prop := OnSeg e.1 s ∧ OnSeg e.2 s

/-- e lies along a side of the triangle t. -/
def InSide (e : Point × Point) (t : Point × Point × Point) : Prop :=
  ∃ s ∈ triSides t, Within e s

theorem within_of_same {e e' s : Point × Point} (h : Same e e') : Within e s ↔ Within e' s := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact and_comm

theorem inSide_of_same {e e' : Point × Point} (h : Same e e') (t : Point × Point × Point) :
    InSide e t ↔ InSide e' t := by
  unfold InSide
  constructor
  · rintro ⟨s, hs, hw⟩
    exact ⟨s, hs, (within_of_same h).mp hw⟩
  · rintro ⟨s, hs, hw⟩
    exact ⟨s, hs, (within_of_same h).mpr hw⟩

/-- A point of a side is within or on the triangle. -/
theorem closed_of_onSeg {t : Point × Point × Point} {s : Point × Point} (hs : s ∈ triSides t)
    {X : Point} (hX : OnSeg X s) : OnOrInsideTriangle X t.1 t.2.1 t.2.2 := by
  unfold OnOrInsideTriangle
  rcases mem_triSides.mp hs with rfl | rfl | rfl <;> rcases hX with e | e | hX
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
  · exact Or.inr (Or.inl hX)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))
  · exact Or.inr (Or.inr (Or.inl hX))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hX)))

/-- A triangle read from another corner. -/
structure Rot (t : Point × Point × Point) (u v w : Point) : Prop where
  tri : Triangle u v w
  inside : ∀ X, InsideTriangle X t.1 t.2.1 t.2.2 ↔ InsideTriangle X u v w
  sides : ∀ s, s ∈ triSides t ↔ (s = (u, v) ∨ s = (v, w) ∨ s = (w, u))

theorem inside_rotate {X a b c : Point} : InsideTriangle X a b c ↔ InsideTriangle X b c a := by
  unfold InsideTriangle
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h3, h1⟩, fun ⟨h2, h3, h1⟩ => ⟨h1, h2, h3⟩⟩

theorem rot_self {t : Point × Point × Point} (h : Triangle t.1 t.2.1 t.2.2) :
    Rot t t.1 t.2.1 t.2.2 :=
  ⟨h, fun _ => Iff.rfl, fun _ => mem_triSides⟩

theorem rot_next {t : Point × Point × Point} (h : Triangle t.1 t.2.1 t.2.2) :
    Rot t t.2.1 t.2.2 t.1 :=
  ⟨h.bca, fun _ => inside_rotate, fun s => by
    rw [mem_triSides]
    exact ⟨fun h' => by rcases h' with h' | h' | h' <;> simp [h'],
      fun h' => by rcases h' with h' | h' | h' <;> simp [h']⟩⟩

theorem rot_last {t : Point × Point × Point} (h : Triangle t.1 t.2.1 t.2.2) :
    Rot t t.2.2 t.1 t.2.1 :=
  ⟨h.cab, fun _ => inside_rotate.trans inside_rotate, fun s => by
    rw [mem_triSides]
    exact ⟨fun h' => by rcases h' with h' | h' | h' <;> simp [h'],
      fun h' => by rcases h' with h' | h' | h' <;> simp [h']⟩⟩

/-- Read a triangle from the first end of any of its sides. -/
theorem rot_side {t : Point × Point × Point} (h : Triangle t.1 t.2.1 t.2.2) {s : Point × Point}
    (hs : s ∈ triSides t) : ∃ u v w, s = (u, v) ∧ Rot t u v w := by
  rcases mem_triSides.mp hs with rfl | rfl | rfl
  · exact ⟨_, _, _, rfl, rot_self h⟩
  · exact ⟨_, _, _, rfl, rot_next h⟩
  · exact ⟨_, _, _, rfl, rot_last h⟩

theorem Rot.inSide {t : Point × Point × Point} {u v w : Point} (hr : Rot t u v w)
    (e : Point × Point) :
    InSide e t ↔ (Within e (u, v) ∨ Within e (v, w) ∨ Within e (w, u)) := by
  unfold InSide
  constructor
  · rintro ⟨s, hs, hw⟩
    rcases (hr.sides s).mp hs with rfl | rfl | rfl
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr hw)
  · rintro (hw | hw | hw)
    · exact ⟨_, (hr.sides _).mpr (Or.inl rfl), hw⟩
    · exact ⟨_, (hr.sides _).mpr (Or.inr (Or.inl rfl)), hw⟩
    · exact ⟨_, (hr.sides _).mpr (Or.inr (Or.inr rfl)), hw⟩

/-- The three conditions for being inside a triangle, each about one straight line. -/
theorem inside_conds {u v w X : Point} (h : Triangle u v w) (hX : InsideTriangle X u v w) :
    ∃ hs : List (Point × Line), (∀ p ∈ hs, SameSide X p.1 p.2) ∧
      ∀ Y, (∀ p ∈ hs, SameSide Y p.1 p.2) → InsideTriangle Y u v w := by
  obtain ⟨L, hvL, hwL⟩ := Postulate1 v w h.ne₂₃
  obtain ⟨M, hwM, huM⟩ := Postulate1 w u h.ne₁₃.symm
  obtain ⟨N, huN, hvN⟩ := Postulate1 u v h.ne₁₂
  refine ⟨[(u, L), (v, M), (w, N)], ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hX.1.sameSide hvL hwL
    · exact hX.2.1.sameSide hwM huM
    · exact hX.2.2.sameSide huN hvN
  · intro Y hY
    exact ⟨SameSideOf.of_line h.ne₂₃ hvL hwL (hY (u, L) (by simp)),
      SameSideOf.of_line h.ne₁₃.symm hwM huM (hY (v, M) (by simp)),
      SameSideOf.of_line h.ne₁₂ huN hvN (hY (w, N) (by simp))⟩

/-- A point inside a triangle is on none of its sides. -/
theorem inside_off_side {u v w X : Point} (hX : InsideTriangle X u v w) :
    ¬ OnFiniteLine X u v ∧ ¬ OnFiniteLine X v w ∧ ¬ OnFiniteLine X w u := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨N, huN, hvN⟩ := Postulate1 u v hX.2.2.1
    exact not_on_line_of_same_side (hX.2.2.sameSide huN hvN)
      (LoopFacts.onFiniteLine_onLine h huN hvN)
  · obtain ⟨L, hvL, hwL⟩ := Postulate1 v w hX.1.1
    exact not_on_line_of_same_side (hX.1.sameSide hvL hwL)
      (LoopFacts.onFiniteLine_onLine h hvL hwL)
  · obtain ⟨M, hwM, huM⟩ := Postulate1 w u hX.2.1.1
    exact not_on_line_of_same_side (hX.2.1.sameSide hwM huM)
      (LoopFacts.onFiniteLine_onLine h hwM huM)

/-- A point between an inner point of the side uv and the corner w is inside uvw. -/
theorem inside_toward {u v w M Z : Point} (h : Triangle u v w) (hM : Between u M v)
    (hZ : Between M Z w) : InsideTriangle Z u v w :=
  inside_rotate.mpr (inside_rotate.mpr (inside_triangle_of_between h.cab hM (between_symm hZ)))

/-- A point strictly within the side uv is on u's side of vw, and on v's side of wu. -/
theorem side_conds {u v w M : Point} (h : Triangle u v w) (hM : Between u M v) :
    ∃ hs : List (Point × Line), (∀ p ∈ hs, SameSide M p.1 p.2) ∧
      ∀ Y, (∀ p ∈ hs, SameSide Y p.1 p.2) → ∀ N : Line, OnLine u N → OnLine v N →
        SameSide Y w N → InsideTriangle Y u v w := by
  obtain ⟨L, hvL, hwL⟩ := Postulate1 v w h.ne₂₃
  obtain ⟨M', hwM, huM⟩ := Postulate1 w u h.ne₁₃.symm
  refine ⟨[(u, L), (v, M')], ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact same_side_between_on (between_symm hM) hvL (h.bca.off_line hvL hwL)
    · exact same_side_between_on hM huM (h.cab.off_line hwM huM)
  · intro Y hY N huN hvN hYw
    exact ⟨SameSideOf.of_line h.ne₂₃ hvL hwL (hY (u, L) (by simp)),
      SameSideOf.of_line h.ne₁₃.symm hwM huM (hY (v, M') (by simp)),
      SameSideOf.of_line h.ne₁₂ huN hvN hYw⟩

/-! ## Triangles that lie apart -/

section Apart

variable (R : Apart)

/-- Two different triangles of the division have no inner point in common. -/
theorem apart_ne {t t' : Point × Point × Point} (ht : t ∈ R.pieces) (ht' : t' ∈ R.pieces)
    (hne : t ≠ t') {Y : Point} (hY : InsideTriangle Y t.1 t.2.1 t.2.2) :
    ¬ InsideTriangle Y t'.1 t'.2.1 t'.2.2 := by
  rcases LoopFacts.pairwise_mem R.apart ht ht' with e | h | h
  · exact absurd e hne
  · exact h Y hY
  · exact fun h' => h Y h' hY

/-- No triangle is listed twice. -/
theorem pieces_nodup : R.pieces.Nodup := by
  refine R.apart.imp_of_mem fun hs _ h e => ?_
  subst e
  obtain ⟨Y, hY⟩ := inside_exists (R.triangle _ hs)
  exact h Y hY hY

/-- **No point of a side is inside a triangle.** -/
theorem int_not_on_side {t t' : Point × Point × Point} (ht : t ∈ R.pieces)
    (ht' : t' ∈ R.pieces) {X : Point} (hX : InsideTriangle X t.1 t.2.1 t.2.2)
    {s : Point × Point} (hs : s ∈ triSides t') (hXs : OnSeg X s) : False := by
  by_cases he : t = t'
  · subst he
    rcases mem_triSides.mp hs with rfl | rfl | rfl
    · exact (inside_off_side hX).1 hXs
    · exact (inside_off_side hX).2.1 hXs
    · exact (inside_off_side hX).2.2 hXs
  obtain ⟨u, v, w, rfl, hr⟩ := rot_side (R.triangle t' ht') hs
  have h := hr.tri
  obtain ⟨hs0, hs1, hs2⟩ := inside_conds (R.triangle t ht) hX
  /- A point strictly within uv, inside t. -/
  obtain ⟨X', hX'uv, hX'⟩ : ∃ X', Between u X' v ∧ InsideTriangle X' t.1 t.2.1 t.2.2 := by
    rcases (hXs : OnFiniteLine X u v) with e | e | hb
    · subst e
      obtain ⟨X', hb, hc⟩ := shorten_off_lines h.ne₁₂ hs0 hs1
      exact ⟨X', hb, hs2 X' hc⟩
    · subst e
      obtain ⟨X', hb, hc⟩ := shorten_off_lines h.ne₁₂.symm hs0 hs1
      exact ⟨X', between_symm hb, hs2 X' hc⟩
    · exact ⟨X, hb, hX⟩
  /- Towards w from it, a point inside both triangles. -/
  obtain ⟨hs0', hs1', hs2'⟩ := inside_conds (R.triangle t ht) hX'
  have hX'w : X' ≠ w := by
    rintro rfl
    obtain ⟨N, huN, hvN⟩ := Postulate1 u v h.ne₁₂
    exact h ⟨N, huN, hvN, on_line_of_between_ends hX'uv huN hvN⟩
  obtain ⟨Z, hZ, hZc⟩ := shorten_off_lines hX'w hs0' hs1'
  exact apart_ne R ht ht' he (hs2' Z hZc) ((hr.inside Z).mpr (inside_toward h hX'uv hZ))

/-- **Sides never cross.** -/
theorem no_cross {t t' : Point × Point × Point} (ht : t ∈ R.pieces) (ht' : t' ∈ R.pieces)
    {s s' : Point × Point} (hs : s ∈ triSides t) (hs' : s' ∈ triSides t') {X : Point}
    (hX : Between s.1 X s.2) (hX' : Between s'.1 X s'.2) {ℓ : Line} (h1 : OnLine s.1 ℓ)
    (h2 : OnLine s.2 ℓ) (hoff : ¬ (OnLine s'.1 ℓ ∧ OnLine s'.2 ℓ)) : False := by
  obtain ⟨u, v, w, rfl, hr⟩ := rot_side (R.triangle t ht) hs
  have h := hr.tri
  have hXℓ : OnLine X ℓ := on_line_of_between_ends hX h1 h2
  /- Both ends of s' are off ℓ, on opposite sides. -/
  have hoff' : ¬ OnLine s'.1 ℓ ∧ ¬ OnLine s'.2 ℓ := by
    obtain ⟨M, hM1, hM2⟩ := Postulate1 s'.1 s'.2 (ne_of_between_ends hX')
    have hXM := on_line_of_between_ends hX' hM1 hM2
    refine ⟨fun h' => hoff ⟨h', ?_⟩, fun h' => hoff ⟨?_, h'⟩⟩
    · have e := line_unique (ne_of_between hX').symm hXℓ h' hXM hM1
      exact e ▸ hM2
    · have e := line_unique (ne_of_between (between_symm hX')).symm hXℓ h' hXM hM2
      exact e ▸ hM1
  have hw : ¬ OnLine w ℓ := h.off_line h1 h2
  obtain ⟨e, he, hew⟩ : ∃ e, (e = s'.1 ∨ e = s'.2) ∧ SameSide e w ℓ := by
    rcases same_side_or hoff'.1 hoff'.2 hw (pasch3 hX' hXℓ) with h' | h'
    · exact ⟨_, Or.inl rfl, h'⟩
    · exact ⟨_, Or.inr rfl, h'⟩
  have hXe : X ≠ e := fun hXe => not_on_line_of_same_side hew (hXe ▸ hXℓ)
  obtain ⟨hc, hc0, hc1⟩ := side_conds h hX
  obtain ⟨Z, hZ, hZc⟩ := shorten_off_lines hXe hc hc0
  have hZw : SameSide Z w ℓ :=
    same_side_trans (same_side_symm (same_side_between_on hZ hXℓ
      (not_on_line_of_same_side hew))) hew
  have hZin := hc1 Z hZc ℓ h1 h2 hZw
  have hZs' : OnSeg Z s' := by
    refine Or.inr (Or.inr (between_within (Or.inr (Or.inr hX')) ?_ hZ))
    rcases he with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  exact int_not_on_side R ht ht' ((hr.inside Z).mpr hZin) hs' hZs'

/-! ## Corners and elementary lines -/

/-- All the corners of all the triangles. -/
def verts : List Point := R.pieces.flatMap fun t => [t.1, t.2.1, t.2.2]

theorem corner_mem {t : Point × Point × Point} (ht : t ∈ R.pieces) {V : Point}
    (hV : V = t.1 ∨ V = t.2.1 ∨ V = t.2.2) : V ∈ verts R := by
  unfold verts
  rw [List.mem_flatMap]
  refine ⟨t, ht, ?_⟩
  rcases hV with rfl | rfl | rfl <;> simp

theorem side_ends_mem {t : Point × Point × Point} (ht : t ∈ R.pieces) {s : Point × Point}
    (hs : s ∈ triSides t) : s.1 ∈ verts R ∧ s.2 ∈ verts R := by
  rcases mem_triSides.mp hs with rfl | rfl | rfl
  · exact ⟨corner_mem R ht (Or.inl rfl), corner_mem R ht (Or.inr (Or.inl rfl))⟩
  · exact ⟨corner_mem R ht (Or.inr (Or.inl rfl)), corner_mem R ht (Or.inr (Or.inr rfl))⟩
  · exact ⟨corner_mem R ht (Or.inr (Or.inr rfl)), corner_mem R ht (Or.inl rfl)⟩

/-- **An elementary finite straight line**: between two different corners, along a side of
one of the triangles, with no corner strictly between its ends. -/
def Elem (P Q : Point) : Prop :=
  P ≠ Q ∧ P ∈ verts R ∧ Q ∈ verts R ∧ (∃ t ∈ R.pieces, InSide (P, Q) t) ∧
    ∀ V ∈ verts R, ¬ Between P V Q

theorem elem_symm {P Q : Point} (h : Elem R P Q) : Elem R Q P := by
  obtain ⟨hPQ, hP, hQ, ⟨t, ht, hin⟩, hb⟩ := h
  refine ⟨hPQ.symm, hQ, hP, ⟨t, ht, (inSide_of_same (Or.inr rfl) t).mp hin⟩,
    fun V hV hVb => hb V hV (between_symm hVb)⟩

theorem elem_of_same {e e' : Point × Point} (h : Same e e') (he : Elem R e.1 e.2) :
    Elem R e'.1 e'.2 := by
  rcases h with rfl | rfl
  · exact he
  · exact elem_symm R he

/-- The number of triangles with a side along e. -/
noncomputable def mult (e : Point × Point) : Nat := R.pieces.countP fun t => decide (InSide e t)

theorem mult_of_same {e e' : Point × Point} (h : Same e e') : mult R e = mult R e' := by
  unfold mult
  exact List.countP_congr fun t _ => by simp only [decide_eq_true_eq, inSide_of_same h t]

theorem mult_pos {P Q : Point} (h : Elem R P Q) : 0 < mult R (P, Q) := by
  obtain ⟨-, -, -, ⟨t, ht, hin⟩, -⟩ := h
  exact List.countP_pos_iff.mpr ⟨t, ht, decide_eq_true hin⟩

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

/-- **Elementary lines that share an inner point are the same.** -/
theorem elem_overlap {P Q P' Q' X : Point} (he : Elem R P Q) (he' : Elem R P' Q')
    (hX : Between P X Q) (hX' : Between P' X Q') : Same (P, Q) (P', Q') := by
  obtain ⟨hPQ, hP, hQ, ⟨t, ht, s, hs, hPs, hQs⟩, hb⟩ := he
  obtain ⟨hPQ', hP', hQ', ⟨t', ht', s', hs', hPs', hQs'⟩, hb'⟩ := he'
  obtain ⟨ℓ, hPℓ, hQℓ⟩ := Postulate1 P Q hPQ
  by_cases hcol : OnLine P' ℓ ∧ OnLine Q' ℓ
  · /- On one straight line: each end of either is an end of the other. -/
    have hXℓ := on_line_of_between_ends hX hPℓ hQℓ
    have key : ∀ {A B : Point}, A ∈ verts R → OnLine A ℓ → Between A X B →
        (∀ V ∈ verts R, ¬ Between A V B) → A = P ∨ A = Q := by
      intro A B hA hAℓ hAXB hAB
      refine Classical.byContradiction fun hne => ?_
      simp only [not_or] at hne
      rcases between_cases hPQ (Ne.symm hne.2) (Ne.symm hne.1) hPℓ hQℓ hAℓ with h | h | h
      · exact hAB Q hQ (between_of_between_left hAXB (between_symm (between_inner hX h)))
      · exact hAB P hP (between_of_between_left hAXB
          (between_symm (between_inner (between_symm hX) h)))
      · exact hb A hA h
    rcases key hP' hcol.1 hX' hb' with e1 | e1 <;>
      rcases key hQ' hcol.2 (between_symm hX') (fun V hV h => hb' V hV (between_symm h)) with
        e2 | e2
    · exact absurd (e1.trans e2.symm) hPQ'
    · rw [e1, e2]
      exact Or.inl rfl
    · rw [e1, e2]
      exact Or.inr rfl
    · exact absurd (e1.trans e2.symm) hPQ'
  · /- Not on one straight line: two sides would cross. -/
    have hXs := between_within hPs hQs hX
    have hXs' := between_within hPs' hQs' hX'
    have hs12 : s.1 ≠ s.2 := ne_of_between_ends hXs
    obtain ⟨m, hm1, hm2⟩ := Postulate1 s.1 s.2 hs12
    have hm : m = ℓ := line_unique hPQ (LoopFacts.onFiniteLine_onLine hPs hm1 hm2)
      (LoopFacts.onFiniteLine_onLine hQs hm1 hm2) hPℓ hQℓ
    subst hm
    refine (no_cross R ht ht' hs hs' hXs hXs' hm1 hm2 fun h' => hcol ⟨?_, ?_⟩).elim
    · exact LoopFacts.onFiniteLine_onLine hPs' h'.1 h'.2
    · exact LoopFacts.onFiniteLine_onLine hQs' h'.1 h'.2

/-- **Two elementary lines meet only at common ends.** -/
theorem elem_meet {e e' : Point × Point} (he : Elem R e.1 e.2) (he' : Elem R e'.1 e'.2)
    (hne : ¬ Same e e') {X : Point} (hX : OnFiniteLine X e.1 e.2)
    (hX' : OnFiniteLine X e'.1 e'.2) : (X = e.1 ∨ X = e.2) ∧ (X = e'.1 ∨ X = e'.2) := by
  have hv : X ∈ verts R → (X = e'.1 ∨ X = e'.2) := fun hXv => by
    rcases hX' with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (he'.2.2.2.2 X hXv)
  rcases hX with h | h | h
  · exact ⟨Or.inl h, hv (h ▸ he.2.1)⟩
  · exact ⟨Or.inr h, hv (h ▸ he.2.2.1)⟩
  · rcases hX' with h' | h' | h'
    · exact absurd h (he.2.2.2.2 X (h' ▸ he'.2.1))
    · exact absurd h (he.2.2.2.2 X (h' ▸ he'.2.2.1))
    · exact absurd (elem_overlap R he he' h h') hne

theorem Rot.next {t : Point × Point × Point} {u v w : Point} (hr : Rot t u v w) :
    Rot t v w u := by
  refine ⟨hr.tri.bca, fun X => (hr.inside X).trans inside_rotate, fun s => ?_⟩
  rw [hr.sides s]
  exact ⟨fun h' => by rcases h' with h' | h' | h' <;> simp [h'],
    fun h' => by rcases h' with h' | h' | h' <;> simp [h']⟩

/-- A triangle along an elementary line, read from that side: its third corner is off the
straight line. -/
theorem third_off {t : Point × Point × Point} (ht : t ∈ R.pieces) {P Q : Point} (hPQ : P ≠ Q)
    (hin : InSide (P, Q) t) {ℓ : Line} (hP : OnLine P ℓ) (hQ : OnLine Q ℓ) :
    ∃ u v w, Rot t u v w ∧ Within (P, Q) (u, v) ∧ OnLine u ℓ ∧ OnLine v ℓ ∧ ¬ OnLine w ℓ := by
  obtain ⟨s, hs, hw⟩ := hin
  obtain ⟨u, v, w, rfl, hr⟩ := rot_side (R.triangle t ht) hs
  obtain ⟨N, huN, hvN⟩ := Postulate1 u v hr.tri.ne₁₂
  have he : N = ℓ := line_unique hPQ (LoopFacts.onFiniteLine_onLine hw.1 huN hvN)
    (LoopFacts.onFiniteLine_onLine hw.2 huN hvN) hP hQ
  subst he
  exact ⟨u, v, w, hr, hw, huN, hvN, hr.tri.off_line huN hvN⟩

/-- Two different triangles along one elementary line are not on the same side of it. -/
theorem same_side_false {t₁ t₂ : Point × Point × Point} (h₁ : t₁ ∈ R.pieces)
    (h₂ : t₂ ∈ R.pieces) (hne : t₁ ≠ t₂) {P Q : Point} (hPQ : P ≠ Q) {ℓ : Line}
    {u₁ v₁ w₁ u₂ v₂ w₂ : Point} (hr₁ : Rot t₁ u₁ v₁ w₁) (hr₂ : Rot t₂ u₂ v₂ w₂)
    (hw₁ : Within (P, Q) (u₁, v₁)) (hw₂ : Within (P, Q) (u₂, v₂)) (hP : OnLine P ℓ)
    (hQ : OnLine Q ℓ) (hu₂ : OnLine u₂ ℓ) (hv₂ : OnLine v₂ ℓ) (hw1off : ¬ OnLine w₁ ℓ)
    (hs : SameSide w₁ w₂ ℓ) : False := by
  obtain ⟨M, hMℓ, hM, -⟩ := exists_point_between hP hQ hPQ []
  have hM₁ := between_within hw₁.1 hw₁.2 hM
  have hM₂ := between_within hw₂.1 hw₂.2 hM
  obtain ⟨hc, hc0, hc1⟩ := side_conds hr₂.tri hM₂
  have hMw : M ≠ w₁ := fun e => hw1off (e ▸ hMℓ)
  obtain ⟨Z, hZ, hZc⟩ := shorten_off_lines hMw hc hc0
  have hZw₁ : SameSide Z w₁ ℓ := same_side_between_on hZ hMℓ hw1off
  have hZw₂ : SameSide Z w₂ ℓ := same_side_trans (same_side_symm hZw₁) hs
  exact apart_ne R h₁ h₂ hne ((hr₁.inside Z).mpr (inside_toward hr₁.tri hM₁ hZ))
    ((hr₂.inside Z).mpr (hc1 Z hZc ℓ hu₂ hv₂ hZw₂))

/-- **At most two triangles along an elementary line.** -/
theorem mult_le_two {P Q : Point} (hPQ : P ≠ Q) : mult R (P, Q) ≤ 2 := by
  refine Classical.byContradiction fun hgt => ?_
  have h3 : 3 ≤ (R.pieces.filter fun t => decide (InSide (P, Q) t)).length := by
    unfold mult at hgt
    rw [List.countP_eq_length_filter] at hgt
    omega
  have hnd : (R.pieces.filter fun t => decide (InSide (P, Q) t)).Nodup :=
    List.Pairwise.filter _ (pieces_nodup R)
  have hmem : ∀ t ∈ (R.pieces.filter fun t => decide (InSide (P, Q) t)),
      t ∈ R.pieces ∧ InSide (P, Q) t := fun t ht => by
    rw [List.mem_filter, decide_eq_true_eq] at ht
    exact ht
  generalize (R.pieces.filter fun t => decide (InSide (P, Q) t)) = F at h3 hnd hmem
  match F, h3, hnd, hmem with
  | t₁ :: t₂ :: t₃ :: rest, _, hnd, hmem =>
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨ℓ, hPℓ, hQℓ⟩ := Postulate1 P Q hPQ
    obtain ⟨ht₁, hi₁⟩ := hmem t₁ (by simp)
    obtain ⟨ht₂, hi₂⟩ := hmem t₂ (by simp)
    obtain ⟨ht₃, hi₃⟩ := hmem t₃ (by simp)
    obtain ⟨u₁, v₁, w₁, hr₁, hw₁, hu₁, hv₁, ho₁⟩ := third_off R ht₁ hPQ hi₁ hPℓ hQℓ
    obtain ⟨u₂, v₂, w₂, hr₂, hw₂, hu₂, hv₂, ho₂⟩ := third_off R ht₂ hPQ hi₂ hPℓ hQℓ
    obtain ⟨u₃, v₃, w₃, hr₃, hw₃, hu₃, hv₃, ho₃⟩ := third_off R ht₃ hPQ hi₃ hPℓ hQℓ
    have h12 : ¬ SameSide w₁ w₂ ℓ := fun h' =>
      same_side_false R ht₁ ht₂ hnd.1.1 hPQ hr₁ hr₂ hw₁ hw₂ hPℓ hQℓ hu₂ hv₂ ho₁ h'
    rcases same_side_or ho₁ ho₂ ho₃ h12 with h' | h'
    · exact same_side_false R ht₁ ht₃ hnd.1.2.1 hPQ hr₁ hr₃ hw₁ hw₃ hPℓ hQℓ hu₃ hv₃ ho₁ h'
    · exact same_side_false R ht₂ ht₃ hnd.2.1.1 hPQ hr₂ hr₃ hw₂ hw₃ hPℓ hQℓ hu₃ hv₃ ho₂ h'

/-! ## Cutting the sides at the corners -/

/-- **The nearest of finitely many points, from V towards D**, D being one of them. It is the
only one of them on the finite straight line VD, other than V, with none of them between V and
it. -/
theorem dir (vs : List Point) {V D : Point} (hVD : V ≠ D) (hD : D ∈ vs) :
    ∃ W, W ≠ V ∧ OnFiniteLine W V D ∧ W ∈ vs ∧ (∀ U ∈ vs, ¬ Between V U W) ∧
      ∀ W', W' ≠ V → OnFiniteLine W' V D → W' ∈ vs → (∀ U ∈ vs, ¬ Between V U W') →
        W' = W := by
  have hDY : D ∈ vs.filter fun U => decide (U ≠ V ∧ OnFiniteLine U V D) :=
    List.mem_filter.mpr ⟨hD, decide_eq_true ⟨hVD.symm, Or.inr (Or.inl rfl)⟩⟩
  obtain ⟨W, hW, hnear⟩ := nearest V _ (List.ne_nil_of_mem hDY)
  obtain ⟨hWvs, hWc⟩ := List.mem_filter.mp hW
  rw [decide_eq_true_eq] at hWc
  have hclear : ∀ U ∈ vs, ¬ Between V U W := by
    intro U hU hb
    refine hnear U (List.mem_filter.mpr ⟨hU, decide_eq_true ⟨(ne_of_between hb).symm, ?_⟩⟩) hb
    exact onFinite_within (Or.inl rfl) hWc.2 (Or.inr (Or.inr hb))
  refine ⟨W, hWc.1, hWc.2, hWvs, hclear, fun W' hW'V hW'D hW'vs hW'c => ?_⟩
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨L, hVL, hDL⟩ := Postulate1 V D hVD
  rcases LoopFacts.order_from hVL (LoopFacts.onFiniteLine_onLine hW'D hVL hDL)
      (LoopFacts.onFiniteLine_onLine hWc.2 hVL hDL) hW'V.symm hWc.1.symm hne
      (not_between_end hW'D hWc.2 hW'V hWc.1) with h | h
  · exact hclear W' hW'vs h
  · exact hW'c W hWvs h

/-- **A side is cut into elementary lines**: a point strictly within a side, at no corner, is
strictly within an elementary line along that side. -/
theorem side_elem {t : Point × Point × Point} (ht : t ∈ R.pieces) {s : Point × Point}
    (hs : s ∈ triSides t) {Y : Point} (hY : Between s.1 Y s.2) (hYv : Y ∉ verts R) :
    ∃ P Q, Elem R P Q ∧ Within (P, Q) s ∧ Between P Y Q := by
  obtain ⟨h1, h2⟩ := side_ends_mem R ht hs
  obtain ⟨P, hPY, hPs, hPv, hPc, -⟩ := dir (verts R) (ne_of_between hY).symm h1
  obtain ⟨Q, hQY, hQs, hQv, hQc, -⟩ := dir (verts R) (ne_of_between (between_symm hY)).symm h2
  have hPYQ := opposite_ends hY hPs hPY hQs hQY
  have hYs : OnFiniteLine Y s.1 s.2 := Or.inr (Or.inr hY)
  have hPw : OnSeg P s := onFinite_within hYs (Or.inl rfl) (LoopFacts.onFiniteLine_comm.mp
    (LoopFacts.onFiniteLine_comm.mpr hPs))
  have hQw : OnSeg Q s := onFinite_within hYs (Or.inr (Or.inl rfl)) hQs
  refine ⟨P, Q, ⟨ne_of_between_ends hPYQ, hPv, hQv, ⟨t, ht, s, hs, hPw, hQw⟩, ?_⟩,
    ⟨hPw, hQw⟩, hPYQ⟩
  intro V hV hb
  have hVY : V ≠ Y := fun e => hYv (e ▸ hV)
  rcases Parity.between_order hb hPYQ hVY with h | h
  · exact hPc V hV (between_symm h)
  · exact hQc V hV (between_inner h hb)

/-- The corner u of the triangle uvw, or a point strictly within its side uv, is not on its
side vw. -/
theorem off_other_sides {u v w V : Point} (h : Triangle u v w) (hV : V = u ∨ Between u V v) :
    ¬ OnFiniteLine V v w := by
  obtain ⟨L, hvL, hwL⟩ := Postulate1 v w h.ne₂₃
  intro hVL
  have hVL' := LoopFacts.onFiniteLine_onLine hVL hvL hwL
  rcases hV with rfl | hV
  · exact h.bca.off_line hvL hwL hVL'
  · exact not_on_line_of_same_side
      (same_side_between_on (between_symm hV) hvL (h.bca.off_line hvL hwL)) hVL'

/-- At a corner u of a triangle, exactly two elementary lines run along its sides. -/
theorem corner_two {t : Point × Point × Point} (ht : t ∈ R.pieces) {u v w : Point}
    (hr : Rot t u v w) :
    ∃ W₁ W₂, W₁ ≠ W₂ ∧ ∀ W, (Elem R u W ∧ InSide (u, W) t) ↔ (W = W₁ ∨ W = W₂) := by
  have h := hr.tri
  have huv := side_ends_mem R ht ((hr.sides (u, v)).mpr (Or.inl rfl))
  have hvw := side_ends_mem R ht ((hr.sides (v, w)).mpr (Or.inr (Or.inl rfl)))
  obtain ⟨W₁, h1V, h1D, h1v, h1c, h1u⟩ := dir (verts R) h.ne₁₂ huv.2
  obtain ⟨W₂, h2V, h2D, h2v, h2c, h2u⟩ := dir (verts R) h.ne₁₃ hvw.2
  refine ⟨W₁, W₂, fun e => ?_, fun W => ⟨fun ⟨he, hin⟩ => ?_, fun hW => ?_⟩⟩
  · obtain ⟨L, huL, hvL⟩ := Postulate1 u v h.ne₁₂
    obtain ⟨M, huM, hwM⟩ := Postulate1 u w h.ne₁₃
    have h1L := LoopFacts.onFiniteLine_onLine h1D huL hvL
    have h2M := LoopFacts.onFiniteLine_onLine h2D huM hwM
    have hLM : L = M := line_unique h1V.symm huL h1L huM (e ▸ h2M)
    exact h ⟨L, huL, hvL, hLM ▸ hwM⟩
  · rcases (hr.inSide _).mp hin with hw | hw | hw
    · exact Or.inl (h1u W he.1.symm hw.2 he.2.2.1 he.2.2.2.2)
    · exact absurd hw.1 (off_other_sides h (Or.inl rfl))
    · exact Or.inr (h2u W he.1.symm (LoopFacts.onFiniteLine_comm.mp hw.2) he.2.2.1
        he.2.2.2.2)
  · have hin : InSide (u, W) t := by
      rcases hW with rfl | rfl
      · exact (hr.inSide _).mpr (Or.inl ⟨Or.inl rfl, h1D⟩)
      · exact (hr.inSide _).mpr (Or.inr (Or.inr ⟨Or.inr (Or.inl rfl),
          LoopFacts.onFiniteLine_comm.mp h2D⟩))
    rcases hW with rfl | rfl
    · exact ⟨⟨h1V.symm, huv.1, h1v, ⟨t, ht, hin⟩, h1c⟩, hin⟩
    · exact ⟨⟨h2V.symm, huv.1, h2v, ⟨t, ht, hin⟩, h2c⟩, hin⟩

/-- At a corner of the figure strictly within the side uv of a triangle, exactly two elementary
lines run along its sides. -/
theorem inner_two {t : Point × Point × Point} (ht : t ∈ R.pieces) {u v w V : Point}
    (hr : Rot t u v w) (hV : Between u V v) (hVv : V ∈ verts R) :
    ∃ W₁ W₂, W₁ ≠ W₂ ∧ ∀ W, (Elem R V W ∧ InSide (V, W) t) ↔ (W = W₁ ∨ W = W₂) := by
  have h := hr.tri
  have huv := side_ends_mem R ht ((hr.sides (u, v)).mpr (Or.inl rfl))
  obtain ⟨W₁, h1V, h1D, h1v, h1c, h1u⟩ := dir (verts R) (ne_of_between hV).symm huv.1
  obtain ⟨W₂, h2V, h2D, h2v, h2c, h2u⟩ := dir (verts R) (ne_of_between (between_symm hV)).symm
    huv.2
  have hVs : OnFiniteLine V u v := Or.inr (Or.inr hV)
  refine ⟨W₁, W₂, fun e => h1V (halves_meet hV h1D (e ▸ h2D)), fun W =>
    ⟨fun ⟨he, hin⟩ => ?_, fun hW => ?_⟩⟩
  · rcases (hr.inSide _).mp hin with hw | hw | hw
    · rcases (Parity.onFiniteLine_split hV).mp hw.2 with hW | hW
      · exact Or.inl (h1u W he.1.symm (LoopFacts.onFiniteLine_comm.mp hW) he.2.2.1
          he.2.2.2.2)
      · exact Or.inr (h2u W he.1.symm hW he.2.2.1 he.2.2.2.2)
    · exact absurd hw.1 (off_other_sides h (Or.inr hV))
    · exact absurd (LoopFacts.onFiniteLine_comm.mp hw.1)
        (off_other_sides h.bac (Or.inr (between_symm hV)))
  · have hin : InSide (V, W) t := by
      refine (hr.inSide _).mpr (Or.inl ⟨hVs, ?_⟩)
      rcases hW with rfl | rfl
      · exact onFinite_within hVs (Or.inl rfl) h1D
      · exact onFinite_within hVs (Or.inr (Or.inl rfl)) h2D
    rcases hW with rfl | rfl
    · exact ⟨⟨h1V.symm, hVv, h1v, ⟨t, ht, hin⟩, h1c⟩, hin⟩
    · exact ⟨⟨h2V.symm, hVv, h2v, ⟨t, ht, hin⟩, h2c⟩, hin⟩

/-- **At a corner of the figure on a triangle's boundary, exactly two elementary lines run along
the triangle's sides.** -/
theorem two_at {V : Point} (hV : V ∈ verts R) {t : Point × Point × Point} (ht : t ∈ R.pieces)
    {s : Point × Point} (hs : s ∈ triSides t) (hVs : OnSeg V s) :
    ∃ W₁ W₂, W₁ ≠ W₂ ∧ ∀ W, (Elem R V W ∧ InSide (V, W) t) ↔ (W = W₁ ∨ W = W₂) := by
  obtain ⟨u, v, w, rfl, hr⟩ := rot_side (R.triangle t ht) hs
  rcases (hVs : OnFiniteLine V u v) with rfl | rfl | hb
  · exact corner_two R ht hr
  · exact corner_two R ht hr.next
  · exact inner_two R ht hr hb hV

end Apart

end Extract

end Elements.Figures
