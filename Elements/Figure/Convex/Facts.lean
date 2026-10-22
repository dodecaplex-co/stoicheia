import Elements.Foundations.Figures
import Elements.Figure.Basics
import Elements.Figure.Rectilineal

/-!
# Book Zero: sides, half-planes and diagonals of a convex outline

The facts that the convex steps of brief 0013's route share (section 8, rows A2 and B3 to
B6 of its ledger), for figures given by their outlines (`Foundations/Figures.lean`):

* **Chains and outlines.** The segments of a chain and the sides of an outline, read from
  another corner, the other way round, or joined at a common corner.
* **Half-planes.** A closed triangle is exactly the common part of the closed half-planes of
  its sides towards the opposite corners (`triangle_halfplanes`, from which
  `closed_triangle_sides` follows). A point inside a triangle lies between a corner and a
  point of the opposite side (`inside_between`, `inside_through`), by the crossbar.
* **Convex outlines.** The straight line of each side supports the outline: no corner lies
  within or on a triangle of three other corners (`corner_not_in_triangle`). So the diagonal
  AC separates B from the later corners (`ear_opposite`), and removing B leaves a convex
  outline while three corners remain (`cut_convex`). Ears removed one after another give
  the crossing diagonals by which fans from neighbouring corners are compared
  (`ConvexOutline.fan_cross`, `diagonals_cross`).

The half-plane and fan arguments build on the probe of 19 October (brief 0013, section 8).
Nothing in Book Zero cites a proposition of the *Elements*.
-/

namespace Elements.Figures

open Tacit

/-- Joining two chains at a common corner joins their lists of segments. -/
theorem segments_join (as bs : List Point) (b : Point) :
    segments (as ++ b :: bs) = segments (as ++ [b]) ++ segments (b :: bs) := by
  induction as with
  | nil => simp [segments]
  | cons a as ih =>
    cases as with
    | nil => simp [segments]
    | cons d ds => simpa [segments] using congrArg (List.cons (a, d)) ih

/-- Reversing a chain reverses its segments and exchanges their ends. -/
theorem segments_reverse (cs : List Point) :
    segments cs.reverse = (segments cs).reverse.map Prod.swap := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds =>
      simp only [List.reverse_cons, segments, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil]
      rw [List.append_assoc]
      simp only [List.cons_append, List.nil_append]
      rw [segments_join]
      simpa [segments] using congrArg (fun ss => ss ++ [(d, c)]) ih

/-- Reading a closed outline from its next corner preserves its sides. -/
theorem mem_sides_rotate (c : Point) (cs : List Point) (s : Point × Point) :
    s ∈ sides (cs ++ [c]) ↔ s ∈ sides (c :: cs) := by
  cases cs with
  | nil => rfl
  | cons d ds =>
    simp only [sides, List.cons_append, List.append_assoc, List.nil_append]
    change s ∈ segments ((d :: ds) ++ c :: [d]) ↔
      s ∈ (c, d) :: segments ((d :: ds) ++ [c])
    rw [segments_join]
    simp only [segments, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact or_comm

/-- Convexity depends on the cyclic order, not the starting corner. -/
theorem convexOutline_rotate_iff (A : Point) (ps : List Point) :
    ConvexOutline (ps ++ [A]) ↔ ConvexOutline (A :: ps) := by
  have hm (P : Point) : P ∈ ps ++ [A] ↔ P ∈ A :: ps := by simp [or_comm]
  have hn : (ps ++ [A]).Nodup ↔ (A :: ps).Nodup := by
    simp [List.nodup_append, List.nodup_cons, and_comm]
    grind
  unfold ConvexOutline
  simp only [List.length_append, List.length_cons]
  constructor <;> rintro ⟨hl, hd, hs⟩
  · exact ⟨hl, hn.mp hd, fun s h P hP Q hQ =>
      hs s ((mem_sides_rotate A ps s).mpr h) P ((hm P).mpr hP) Q ((hm Q).mpr hQ)⟩
  · exact ⟨hl, hn.mpr hd, fun s h P hP Q hQ =>
      hs s ((mem_sides_rotate A ps s).mp h) P ((hm P).mp hP) Q ((hm Q).mp hQ)⟩

/-- Reversing an outline exchanges the ends of each side. -/
theorem mem_sides_reverse (cs : List Point) (s : Point × Point) :
    s ∈ sides cs.reverse ↔ s.swap ∈ sides cs := by
  cases cs with
  | nil => simp [sides]
  | cons c cs =>
    rw [List.reverse_cons, mem_sides_rotate]
    have he : c :: cs.reverse ++ [c] = (c :: cs ++ [c]).reverse := by simp
    simp only [sides]
    rw [he, segments_reverse]
    simp only [List.mem_map, List.mem_reverse]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hs
      exact ⟨s.swap, hs, Prod.swap_swap s⟩

/-- Both ends of a segment belong to its chain. -/
theorem segment_corners {cs : List Point} {s : Point × Point} (hs : s ∈ segments cs) :
    s.1 ∈ cs ∧ s.2 ∈ cs := by
  induction cs with
  | nil => simp [segments] at hs
  | cons a cs ih =>
    cases cs with
    | nil => simp [segments] at hs
    | cons b bs =>
      rcases List.mem_cons.mp hs with rfl | hs
      · simp
      · exact ⟨List.mem_cons_of_mem a (ih hs).1, List.mem_cons_of_mem a (ih hs).2⟩

/-- Extending a chain preserves its existing segments. -/
theorem segment_mem_append {cs : List Point} {s : Point × Point}
    (hs : s ∈ segments cs) (ds : List Point) : s ∈ segments (cs ++ ds) := by
  induction cs with
  | nil => simp [segments] at hs
  | cons a cs ih =>
    cases cs with
    | nil => simp [segments] at hs
    | cons b bs =>
      rcases List.mem_cons.mp hs with rfl | hs
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hs)

/-- A segment of the corners following the first is a side of the outline. -/
theorem fan_base_side {c : Point} {cs : List Point} {s : Point × Point}
    (hs : s ∈ segments cs) : s ∈ sides (c :: cs) := by
  cases cs with
  | nil => simp [segments] at hs
  | cons d ds => exact List.mem_cons_of_mem _ (segment_mem_append hs [c])

/-- A finite straight line between points of a closed half-plane stays in it. -/
theorem half_between {X Y Z R : Point} {L : Line}
    (hX : Half X R L) (hZ : Half Z R L) (h : Between X Y Z) : Half Y R L := by
  by_cases hY : OnLine Y L
  · exact Or.inl hY
  apply Or.inr
  rcases hX with hX | hX <;> rcases hZ with hZ | hZ
  · exact False.elim (hY (on_line_of_between_ends h hX hZ))
  · exact same_side_trans (same_side_symm (pasch2 h hX hY)) hZ
  · exact same_side_trans (same_side_symm (pasch2 (between_symm h) hZ hY)) hX
  · exact same_side_trans (pasch1 h
      (same_side_trans (same_side_symm hX) (same_side_symm hZ))) hX

/-- A closed triangle can be named from its next corner. -/
theorem closed_rotate {X A B C : Point} (h : OnOrInsideTriangle X A B C) :
    OnOrInsideTriangle X B C A := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl ⟨h.2.1, h.2.2, h.1⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

/-- A closed triangle is within the inward closed side of each of its sides. -/
theorem closed_half {X A B C : Point} {L : Line}
    (hABC : Triangle A B C) (hA : OnLine A L) (hB : OnLine B L)
    (h : OnOrInsideTriangle X A B C) : Half X C L := by
  have hC : Half C C L := Or.inr (same_side_refl (hABC.off_line hA hB))
  rcases h with h | h | h | h | rfl | rfl | rfl
  · exact Or.inr (h.2.2.sameSide hA hB)
  · exact Or.inl (on_line_of_between_ends h hA hB)
  · exact half_between (Or.inl hB) hC h
  · exact half_between hC (Or.inl hA) h
  · exact Or.inl hA
  · exact Or.inl hB
  · exact hC

/-- On one side-line, the other two closed half-planes cut out the finite side. -/
theorem side_interval {X A B C : Point} {L M N : Line}
    (hABC : Triangle A B C) (hAL : OnLine A L) (hBL : OnLine B L)
    (hBM : OnLine B M) (hCM : OnLine C M)
    (hCN : OnLine C N) (hAN : OnLine A N)
    (hXL : OnLine X L) (hM : Half X A M) (hN : Half X B N) :
    OnFiniteLine X A B := by
  by_cases hXA : X = A
  · exact Or.inl hXA
  by_cases hXB : X = B
  · exact Or.inr (Or.inl hXB)
  have hXM : ¬ OnLine X M := fun h => hABC.bca.off_line hBM hCM
    ((line_unique hXB hXL hBL h hBM) ▸ hAL)
  have hXN : ¬ OnLine X N := fun h => hABC.cab.off_line hCN hAN
    ((line_unique hXA hXL hAL h hAN) ▸ hBL)
  have hsM := hM.resolve_left hXM
  have hsN := hN.resolve_left hXN
  rcases between_cases (Ne.symm hXA) hXB hABC.ne₁₂ hAL hXL hBL with h | h | h
  · exact Or.inr (Or.inr h)
  · exact False.elim (pasch3 h hAN hsN)
  · exact False.elim (pasch3 h hBM (same_side_symm hsM))

/-- A closed triangle is exactly the intersection of its three inward half-planes. -/
theorem triangle_halfplanes {X A B C : Point} {L M N : Line}
    (hABC : Triangle A B C) (hAL : OnLine A L) (hBL : OnLine B L)
    (hBM : OnLine B M) (hCM : OnLine C M)
    (hCN : OnLine C N) (hAN : OnLine A N) :
    OnOrInsideTriangle X A B C ↔ Half X C L ∧ Half X A M ∧ Half X B N := by
  constructor
  · intro h
    exact ⟨closed_half hABC hAL hBL h,
      closed_half hABC.bca hBM hCM (closed_rotate h),
      closed_half hABC.cab hCN hAN (closed_rotate (closed_rotate h))⟩
  · rintro ⟨hL, hM, hN⟩
    by_cases hXL : OnLine X L
    · rcases side_interval hABC hAL hBL hBM hCM hCN hAN hXL hM hN with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inl h)
    by_cases hXM : OnLine X M
    · rcases side_interval hABC.bca hBM hCM hCN hAN hAL hBL hXM hN hL with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      · exact Or.inr (Or.inr (Or.inl h))
    by_cases hXN : OnLine X N
    · rcases side_interval hABC.cab hCN hAN hAL hBL hBM hCM hXN hL hM with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    exact Or.inl ⟨SameSideOf.of_line hABC.ne₂₃ hBM hCM (hM.resolve_left hXM),
      SameSideOf.of_line hABC.ne₁₃.symm hCN hAN (hN.resolve_left hXN),
      SameSideOf.of_line hABC.ne₁₂ hAL hBL (hL.resolve_left hXL)⟩

/-- A point inside a triangle lies between a corner and a point of the opposite side. -/
theorem inside_between {X A B C : Point} (h : InsideTriangle X A B C) :
    ∃ Y : Point, Between B Y C ∧ Between A X Y := by
  obtain ⟨Y, hBYC, hY⟩ := crossbar h.2.2 h.2.1.swap
  have hAX : A ≠ X := h.2.2.triangle.ne₁₃
  obtain ⟨M, hBM, hCM⟩ := Postulate1 B C h.1.1
  have hYM := on_line_of_between_ends hBYC hBM hCM
  have hXY : X ≠ Y := fun e =>
    not_on_line_of_same_side (h.1.sameSide hBM hCM) (e.symm ▸ hYM)
  obtain ⟨N, hAN, hXN, hYN⟩ := hY.2.2.1
  refine ⟨Y, hBYC, ?_⟩
  rcases between_cases hAX hXY hY.2.1.symm hAN hXN hYN with hb | hb | hb
  · exact hb
  · exact False.elim (hY.2.2.2 (between_symm hb))
  · exact False.elim (pasch3 hb hYM (same_side_symm (h.1.sameSide hBM hCM)))

/-- The straight line from a corner through a point inside a triangle meets the opposite
side: from B through D, it meets AC between A and C. I.21 draws the same line;
here it follows from the crossbar, with no proposition cited. -/
theorem inside_through {A B C D : Point} (hD : InsideTriangle D A B C) :
    ∃ E : Point, Between B D E ∧ Between A E C := by
  obtain ⟨E, hCEA, hBDE⟩ :=
    inside_between (show InsideTriangle D B C A from ⟨hD.2.1, hD.2.2, hD.1⟩)
  exact ⟨E, hBDE, between_symm hCEA⟩

/-- A closed triangle whose corners lie in a closed half-plane stays in it. -/
theorem closed_in_half {X A B C R : Point} {L : Line}
    (hA : Half A R L) (hB : Half B R L) (hC : Half C R L)
    (h : OnOrInsideTriangle X A B C) : Half X R L := by
  rcases h with h | h | h | h | rfl | rfl | rfl
  · obtain ⟨Y, hBYC, hAXY⟩ := inside_between h
    exact half_between hA (half_between hB hC hBYC) hAXY
  · exact half_between hA hB h
  · exact half_between hB hC h
  · exact half_between hC hA h
  · exact hA
  · exact hB
  · exact hC

/-- If a segment in a closed half-plane meets its boundary internally,
both ends are on that boundary. -/
theorem half_between_on_line {A X B R : Point} {L : Line}
    (hA : Half A R L) (hB : Half B R L) (h : Between A X B) (hX : OnLine X L) :
    OnLine A L ∧ OnLine B L := by
  rcases hA with hA | hA
  · exact ⟨hA, on_line_of_between h hA hX⟩
  rcases hB with hB | hB
  · exact ⟨on_line_of_between (between_symm h) hB hX, hB⟩
  · exact False.elim (pasch3 h hX (same_side_trans (same_side_symm hA)
      (same_side_symm hB)))

/-- A closed triangle in a half-plane cannot touch its boundary except at a corner
if no two of its corners are on the boundary. -/
theorem closed_support_corner {X A B C R : Point} {L : Line}
    (hA : Half A R L) (hB : Half B R L) (hC : Half C R L)
    (hAB : ¬ (OnLine A L ∧ OnLine B L))
    (hBC : ¬ (OnLine B L ∧ OnLine C L))
    (hCA : ¬ (OnLine C L ∧ OnLine A L))
    (hX : OnLine X L) (h : OnOrInsideTriangle X A B C) :
    X = A ∨ X = B ∨ X = C := by
  rcases h with h | h | h | h | h | h | h
  · obtain ⟨Y, hBYC, hAXY⟩ := inside_between h
    have hY := (half_between_on_line hA (half_between hB hC hBYC) hAXY hX).2
    exact False.elim (hBC (half_between_on_line hB hC hBYC hY))
  · exact False.elim (hAB (half_between_on_line hA hB h hX))
  · exact False.elim (hBC (half_between_on_line hB hC h hX))
  · exact False.elim (hCA (half_between_on_line hC hA h hX))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- A chain continued to a final corner has an outgoing segment at every earlier corner. -/
theorem outgoing_segment {cs : List Point} {D : Point} (hD : D ∈ cs) (a : Point) :
    ∃ E : Point, (D, E) ∈ segments (cs ++ [a]) := by
  induction cs with
  | nil => simp at hD
  | cons c cs ih =>
    rcases List.mem_cons.mp hD with rfl | hD
    · cases cs with
      | nil => exact ⟨a, by simp [segments]⟩
      | cons b bs => exact ⟨b, by simp [segments]⟩
    · obtain ⟨E, hE⟩ := ih hD
      cases cs with
      | nil => simp at hD
      | cons b bs => exact ⟨E, List.mem_cons_of_mem _ hE⟩

/-- Every corner of a nonempty outline starts one of its sides. -/
theorem outgoing_side {cs : List Point} {D : Point} (hD : D ∈ cs) :
    ∃ E : Point, (D, E) ∈ sides cs := by
  cases cs with
  | nil => simp at hD
  | cons c cs => exact outgoing_segment hD c

/-- A corner of a convex outline is on the inward closed side of every side. -/
theorem corner_half {cs : List Point} (h : ConvexOutline cs)
    {A B P Q : Point} {L : Line} (hs : (A, B) ∈ sides cs)
    (hP : P ∈ cs) (hPA : P ≠ A) (hPB : P ≠ B) (hQ : Q ∈ cs)
    (hAL : OnLine A L) (hBL : OnLine B L) : Half Q P L := by
  by_cases hQA : Q = A
  · exact Or.inl (hQA ▸ hAL)
  by_cases hQB : Q = B
  · exact Or.inl (hQB ▸ hBL)
  exact Or.inr ((h.2.2 (A, B) hs Q hQ P hP hQA hQB hPA hPB).sameSide hAL hBL)

/-- A corner cannot be within or on a triangle made from three other corners.
Its outgoing side is a supporting line, with at most one of those corners on it. -/
theorem corner_not_in_triangle {cs : List Point} (h : ConvexOutline cs)
    {D A B C : Point} (hD : D ∈ cs) (hA : A ∈ cs) (hB : B ∈ cs) (hC : C ∈ cs)
    (hDA : D ≠ A) (hDB : D ≠ B) (hDC : D ≠ C) (hABC : Triangle A B C) :
    ¬ OnOrInsideTriangle D A B C := by
  obtain ⟨E, hs⟩ := outgoing_side hD
  have hp : ∃ P : Point, P ∈ cs ∧ P ≠ D ∧ P ≠ E := by
    by_cases hAE : A = E
    · exact ⟨B, hB, hDB.symm, fun e => hABC.ne₁₂ (hAE.trans e.symm)⟩
    · exact ⟨A, hA, hDA.symm, hAE⟩
  obtain ⟨P, hP, hPD, hPE⟩ := hp
  have hss := h.2.2 (D, E) hs P hP P hP hPD hPE hPD hPE
  obtain ⟨L, hDL, hEL⟩ := Postulate1 D E hss.1
  have hon : ∀ Q ∈ cs, Q ≠ D → OnLine Q L → Q = E := by
    intro Q hQ hQD hQL
    by_cases hQE : Q = E
    · exact hQE
    · exact False.elim (not_on_line_of_same_side
        ((h.2.2 (D, E) hs Q hQ P hP hQD hQE hPD hPE).sameSide hDL hEL) hQL)
  have ha := corner_half h hs hP hPD hPE hA hDL hEL
  have hb := corner_half h hs hP hPD hPE hB hDL hEL
  have hc := corner_half h hs hP hPD hPE hC hDL hEL
  intro hi
  have he := closed_support_corner ha hb hc
    (fun hh => hABC.ne₁₂ ((hon A hA hDA.symm hh.1).trans (hon B hB hDB.symm hh.2).symm))
    (fun hh => hABC.ne₂₃ ((hon B hB hDB.symm hh.1).trans (hon C hC hDC.symm hh.2).symm))
    (fun hh => hABC.ne₁₃ ((hon A hA hDA.symm hh.2).trans (hon C hC hDC.symm hh.1).symm))
    hDL hi
  exact he.elim hDA (fun he => he.elim hDB hDC)

/-- The straight line through two distinct corners gives the same closed side
as the phrase using those two corners. -/
theorem closedSide_iff_half {X P A B : Point} {L : Line}
    (hAB : A ≠ B) (hAL : OnLine A L) (hBL : OnLine B L) :
    ClosedSide X P A B ↔ Half X P L := by
  constructor
  · rintro (⟨M, hAM, hBM, hXM⟩ | h)
    · exact Or.inl (line_unique hAB hAM hBM hAL hBL ▸ hXM)
    · exact Or.inr (h.sameSide hAL hBL)
  · rintro (h | h)
    · exact Or.inl ⟨L, hAL, hBL, h⟩
    · exact Or.inr (SameSideOf.of_line hAB hAL hBL h)

/-- Some corner of a convex outline is neither end of a given side. -/
theorem convex_third {cs : List Point} (h : ConvexOutline cs) (s : Point × Point) :
    ∃ G ∈ cs, G ≠ s.1 ∧ G ≠ s.2 := by
  match cs, h with
  | a :: b :: c :: rest, h =>
    have hn := h.2.1
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    by_cases ha : a ≠ s.1 ∧ a ≠ s.2
    · exact ⟨a, List.mem_cons_self, ha⟩
    by_cases hb : b ≠ s.1 ∧ b ≠ s.2
    · exact ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, hb⟩
    refine ⟨c, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_, ?_⟩
    · intro hc
      apply ha
      refine ⟨fun e => hn.1.2.1 (e.trans hc.symm), fun e => ?_⟩
      apply hb
      refine ⟨fun e' => hn.2.1.1 (e'.trans hc.symm), fun e' => hn.1.1 (e.trans e'.symm)⟩
    · intro hc
      apply ha
      refine ⟨fun e => ?_, fun e => hn.1.2.1 (e.trans hc.symm)⟩
      apply hb
      exact ⟨fun e' => hn.1.1 (e.trans e'.symm), fun e' => hn.2.1.1 (e'.trans hc.symm)⟩
  | [], h => have := h.1; simp at this
  | [_], h => have := h.1; simp at this
  | [_, _], h => have := h.1; simp at this

/-- The ends of a side of a convex outline differ. -/
theorem convex_side_ne {cs : List Point} (h : ConvexOutline cs) {s : Point × Point}
    (hs : s ∈ sides cs) : s.1 ≠ s.2 := by
  obtain ⟨P, hP, h₁, h₂⟩ := convex_third h s
  exact (h.2.2 s hs P hP P hP h₁ h₂ h₁ h₂).1

/-- The closed region of a convex outline holds every point between two of its points. -/
theorem convex_region_between {cs : List Point} (h : ConvexOutline cs) {U X W : Point}
    (hU : ConvexRegion cs U) (hW : ConvexRegion cs W) (hb : Between U X W) :
    ConvexRegion cs X := by
  intro s hs P hP hP₁ hP₂
  have hne := convex_side_ne h hs
  obtain ⟨L, h₁, h₂⟩ := Postulate1 s.1 s.2 hne
  exact (closedSide_iff_half hne h₁ h₂).mpr (half_between
    ((closedSide_iff_half hne h₁ h₂).mp (hU s hs P hP hP₁ hP₂))
    ((closedSide_iff_half hne h₁ h₂).mp (hW s hs P hP hP₁ hP₂)) hb)

/-- The diagonal AC separates B from every later corner of the convex outline. -/
theorem ear_opposite {A B C D : Point} {ds : List Point}
    (h : ConvexOutline (A :: B :: C :: ds)) (hD : D ∈ ds) :
    OppositeSidesOf B D A C := by
  have hn := h.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at hn
  have hDA : D ≠ A := fun e => hn.1.2.2 (e ▸ hD)
  have hDB : D ≠ B := fun e => hn.2.1.2 (e ▸ hD)
  have hDC : D ≠ C := fun e => hn.2.2.1 (e ▸ hD)
  have hAB := h.2.2 (A, B) (by simp [sides, segments])
    C (by simp) D (by simp [hD]) (Ne.symm hn.1.2.1) (Ne.symm hn.2.1.1) hDA hDB
  have hBC := h.2.2 (B, C) (by simp [sides, segments])
    A (by simp) D (by simp [hD]) hn.1.1 hn.1.2.1 hDB hDC
  have hABC : Triangle A B C := hAB.triangle
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hABC.ne₁₂
  obtain ⟨M, hBM, hCM⟩ := Postulate1 B C hABC.ne₂₃
  obtain ⟨N, hCN, hAN⟩ := Postulate1 C A hABC.ne₁₃.symm
  have hout := corner_not_in_triangle h (by simp [hD]) (by simp) (by simp) (by simp)
    hDA hDB hDC hABC
  have hDL : Half D C L := Or.inr (hAB.symm.sameSide hAL hBL)
  have hDM : Half D A M := Or.inr (hBC.symm.sameSide hBM hCM)
  have hDN : ¬ OnLine D N := fun hd => hout
    ((triangle_halfplanes hABC hAL hBL hBM hCM hCN hAN).mpr ⟨hDL, hDM, Or.inl hd⟩)
  have hBD : ¬ SameSide B D N := fun hd => hout
    ((triangle_halfplanes hABC hAL hBL hBM hCM hCN hAN).mpr
      ⟨hDL, hDM, Or.inr (same_side_symm hd)⟩)
  exact OppositeSidesOf.of_line hABC.ne₁₃ hAN hCN
    ⟨hABC.acb.off_line hAN hCN, hDN, hBD⟩

/-- Cutting off the triangle at the second corner leaves a convex outline,
provided at least three corners remain. -/
theorem cut_convex {A B C : Point} {ds : List Point}
    (h : ConvexOutline (A :: B :: C :: ds)) (hds : ds ≠ []) :
    ConvexOutline (A :: C :: ds) := by
  have hn := List.nodup_cons.mp h.2.1
  have ht := List.nodup_cons.mp hn.2
  refine ⟨?_, List.nodup_cons.mpr ⟨?_, ht.2⟩, ?_⟩
  · cases ds with
    | nil => exact False.elim (hds rfl)
    | cons d ds => simp
  · intro ha
    exact hn.1 (List.mem_cons_of_mem B ha)
  · intro s hs P hP Q hQ hP₁ hP₂ hQ₁ hQ₂
    change s ∈ (A, C) :: segments (C :: ds ++ [A]) at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · have hp : P ∈ ds := by simpa [hP₁, hP₂] using hP
      have hq : Q ∈ ds := by simpa [hQ₁, hQ₂] using hQ
      exact (ear_opposite h hp).sameSideOf (ear_opposite h hq)
    · have hs' : s ∈ sides (A :: B :: C :: ds) :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs)
      have incl : ∀ R ∈ A :: C :: ds, R ∈ A :: B :: C :: ds := by
        intro R hR
        rcases List.mem_cons.mp hR with rfl | hR
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
      exact h.2.2 s hs' P (incl P hP) Q (incl Q hQ) hP₁ hP₂ hQ₁ hQ₂

/-- Every closed triangle formed from corners lies in the outline's region. -/
theorem triangle_in_region {cs : List Point} (h : ConvexOutline cs)
    {X A B C : Point} (hA : A ∈ cs) (hB : B ∈ cs) (hC : C ∈ cs)
    (hX : OnOrInsideTriangle X A B C) : ConvexRegion cs X := by
  intro s hs P hP hP₁ hP₂
  have hss := h.2.2 s hs P hP P hP hP₁ hP₂ hP₁ hP₂
  obtain ⟨L, h₁, h₂⟩ := Postulate1 s.1 s.2 hss.1
  exact (closedSide_iff_half hss.1 h₁ h₂).mpr (closed_in_half
    (corner_half h hs hP hP₁ hP₂ hA h₁ h₂)
    (corner_half h hs hP hP₁ hP₂ hB h₁ h₂)
    (corner_half h hs hP hP₁ hP₂ hC h₁ h₂) hX)

/-- Removing the third corner preserves convexity when there is a fourth corner. -/
theorem ConvexOutline.erase_third {A B C D : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: C :: D :: ps)) :
    ConvexOutline (A :: B :: D :: ps) := by
  have hr := (convexOutline_rotate_iff A (B :: C :: D :: ps)).mpr h
  have he := cut_convex hr (by simp)
  exact (convexOutline_rotate_iff A (B :: D :: ps)).mp he

/-- The first two corners and each later side have crossing diagonals. Removing
successive ears reduces each side to the case of four successive corners. -/
theorem ConvexOutline.fan_cross {A B C : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: C :: ps)) :
    ∀ s ∈ segments (C :: ps),
      OppositeSidesOf A s.1 B s.2 ∧ OppositeSidesOf B s.2 A s.1 := by
  induction ps generalizing C with
  | nil => intro s hs; cases hs
  | cons D ps ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · have hr := (convexOutline_rotate_iff A (B :: C :: D :: ps)).mpr h
      exact ⟨(ear_opposite hr (by simp)).symm, ear_opposite h (by simp)⟩
    · exact ih h.erase_third s hs

/-- Two separating diagonals meet inside both finite segments. -/
theorem diagonals_cross {A B C D : Point}
    (hAC : OppositeSidesOf A C B D) (hBD : OppositeSidesOf B D A C) :
    ∃ X : Point, Between A X C ∧ Between B X D := by
  obtain ⟨L, hB, hD⟩ := Postulate1 B D hAC.1
  obtain ⟨M, hA, hC⟩ := Postulate1 A C hBD.1
  have hac := hAC.oppositeSides hB hD
  have hbd := hBD.oppositeSides hA hC
  obtain ⟨X, hXL, hAXC⟩ := hac.exists_between
  have hXM := on_line_of_between_ends hAXC hA hC
  have hML : M ≠ L := fun e => hac.1 (e ▸ hA)
  have hBXD : Between B X D := pasch4 hML hXM hXL hB hD hAC.1
    (fun e => hbd.1 (e.symm ▸ hXM))
    (fun e => hbd.2.1 (e.symm ▸ hXM)) hbd.2.2
  exact ⟨X, hAXC, hBXD⟩

end Elements.Figures
