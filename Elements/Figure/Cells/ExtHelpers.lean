import Elements.Figure.Convex.Facts
import Elements.Figure.Convex.Cover
import Elements.Figure.Convex.Area
import Elements.Figure.Convex.Closed
import Elements.Figure.Convex.Avoid

/-!
Supporting sides and extreme points for convex cells. With thanks to David Hilbert,
whose theory of content guides this route. The supporting steps use closed-triangle
characterisation, fan coverage, finite avoidance, outline symmetries and fan invariance.
-/

namespace Elements.Figures.Extreme

open Tacit

/-- A chain that ends with V and then A has VA among its segments: for an outline A, B, …, V it is
the closing side. -/
theorem closing_segment (A V : Point) (ps : List Point) :
    (V, A) ∈ segments (ps ++ [V, A]) := by
  induction ps with
  | nil => simp [segments]
  | cons B ps ih =>
    cases ps with
    | nil => simp [segments]
    | cons C ps => exact List.mem_cons_of_mem _ ih

/-- Every corner lies in the closed region specified by the supporting sides. -/
theorem corner_region {ps : List Point} (h : ConvexOutline ps)
    {X : Point} (hX : X ∈ ps) : ConvexRegion ps X := by
  intro s hs P hP hP₁ hP₂
  by_cases h₁ : X = s.1
  · obtain ⟨L, hA, hB⟩ := collinear_of_two s.1 s.2
    exact Or.inl ⟨L, hA, hB, h₁ ▸ hA⟩
  by_cases h₂ : X = s.2
  · obtain ⟨L, hA, hB⟩ := collinear_of_two s.1 s.2
    exact Or.inl ⟨L, hA, hB, h₂ ▸ hB⟩
  exact Or.inr (h.2.2 s hs X hX P hP h₁ h₂ hP₁ hP₂)

/-- Moving a prefix to the end preserves convexity. -/
theorem convex_rotate_prefix (us vs : List Point) (h : ConvexOutline (us ++ vs)) :
    ConvexOutline (vs ++ us) := by
  induction us generalizing vs with
  | nil => simpa using h
  | cons A us ih =>
    have hr := ConvexOutline.rotate h
    have hi := ih (vs ++ [A]) (by simpa [List.append_assoc] using hr)
    simpa [List.append_assoc] using hi

/-- Moving a prefix to the end preserves the closed region. -/
theorem region_rotate_prefix (us vs : List Point) (X : Point) :
    ConvexRegion (vs ++ us) X ↔ ConvexRegion (us ++ vs) X := by
  induction us generalizing vs with
  | nil => simp
  | cons A us ih =>
    have hi : ConvexRegion ((vs ++ A :: us)) X ↔
        ConvexRegion ((us ++ vs) ++ [A]) X := by
      simpa [List.append_assoc] using ih (vs ++ [A])
    exact hi.trans (convexRegion_rotate A (us ++ vs) X)

/-- Moving a prefix to the end preserves the fan sum. -/
theorem fanSum_rotate_prefix (us vs : List Point) (h : ConvexOutline (us ++ vs)) :
    fanSum (vs ++ us) = fanSum (us ++ vs) := by
  induction us generalizing vs with
  | nil => simp
  | cons A us ih =>
    have hr := ConvexOutline.rotate h
    have hi := ih (vs ++ [A]) (by simpa [List.append_assoc] using hr)
    have he : fanSum (vs ++ A :: us) = fanSum ((us ++ vs) ++ [A]) := by
      simpa [List.append_assoc] using hi
    exact he.trans (fanSum_rotate h)

/-- The three corners of a fan triangle occur in the outline. -/
theorem fan_mem {ps : List Point} {t : Point × Point × Point} (ht : t ∈ fan ps) :
    t.1 ∈ ps ∧ t.2.1 ∈ ps ∧ t.2.2 ∈ ps := by
  cases ps with
  | nil => simp [fan] at ht
  | cons A ps =>
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    obtain ⟨h₁, h₂⟩ := segment_corners hs
    exact ⟨by simp, List.mem_cons_of_mem _ h₁, List.mem_cons_of_mem _ h₂⟩

/-- A non-corner point of the region lies strictly between two region points. -/
theorem noncorner_segment {ps : List Point} (h : ConvexOutline ps) {X : Point}
    (hX : ConvexRegion ps X) (hn : X ∉ ps) :
    ∃ A B : Point, ConvexRegion ps A ∧ ConvexRegion ps B ∧ Between A X B := by
  obtain ⟨⟨A, B, C⟩, ht, hT⟩ := (fan_covers h X).mpr hX
  obtain ⟨hA, hB, hC⟩ := fan_mem ht
  rcases hT with hi | hab | hbc | hca | rfl | rfl | rfl
  · obtain ⟨E, hBE, hAE⟩ := inside_through hi
    exact ⟨B, E, corner_region h hB,
      triangle_in_region h hA hB hC
        (Or.inr (Or.inr (Or.inr (Or.inl (between_symm hAE))))), hBE⟩
  · exact ⟨A, B, corner_region h hA, corner_region h hB, hab⟩
  · exact ⟨B, C, corner_region h hB, corner_region h hC, hbc⟩
  · exact ⟨C, A, corner_region h hC, corner_region h hA, hca⟩
  · exact False.elim (hn hA)
  · exact False.elim (hn hB)
  · exact False.elim (hn hC)

/-- A triangle's three corners form a convex outline. -/
theorem triangle_outline {A B C : Point} (h : Triangle A B C) :
    ConvexOutline [A, B, C] := by
  refine ⟨by simp, ?_, ?_⟩
  · simp [List.nodup_cons, h.ne₁₂, h.ne₁₃, h.ne₂₃]
  · intro s hs P hP Q hQ hP₁ hP₂ hQ₁ hQ₂
    have self {D E F : Point} (ht : Triangle D E F) : SameSideOf F F D E := by
      exact ⟨ht.ne₁₂, fun L hD hE => same_side_refl (ht.off_line hD hE)⟩
    simp only [sides, List.cons_append, List.nil_append, segments, List.mem_cons,
      List.not_mem_nil] at hs
    rcases hs with hs | hs | hs | hs <;> try contradiction
    all_goals subst s
    · have hp : P = C := by simpa [hP₁, hP₂] using hP
      have hq : Q = C := by simpa [hQ₁, hQ₂] using hQ
      subst P; subst Q
      exact self h
    · have hp : P = A := by simpa [hP₁, hP₂] using hP
      have hq : Q = A := by simpa [hQ₁, hQ₂] using hQ
      subst P; subst Q
      exact self h.bca
    · have hp : P = B := by simpa [hP₁, hP₂] using hP
      have hq : Q = B := by simpa [hQ₁, hQ₂] using hQ
      subst P; subst Q
      exact self h.cab

/-- The first corner cannot lie strictly between two region points. -/
theorem head_not_between {A B V : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: (ps ++ [V])))
    {U W : Point} (hU : ConvexRegion (A :: B :: (ps ++ [V])) U)
    (hW : ConvexRegion (A :: B :: (ps ++ [V])) W) : ¬ Between U A W := by
  have hn := h.2.1
  simp only [List.nodup_cons] at hn
  have hAB : A ≠ B := fun e => hn.1 (by simp [e])
  have hAV : A ≠ V := fun e => hn.1 (by simp [e])
  have hBV : B ≠ V := fun e => hn.2.1 (by simp [e])
  have hs : (A, B) ∈ sides (A :: B :: (ps ++ [V])) := by simp [sides, segments]
  have ht : (V, A) ∈ sides (A :: B :: (ps ++ [V])) := by
    simpa [sides, List.append_assoc] using closing_segment A V (A :: B :: ps)
  have hVm : V ∈ A :: B :: (ps ++ [V]) := by simp
  have hBm : B ∈ A :: B :: (ps ++ [V]) := by simp
  have hT := (h.2.2 (A, B) hs V hVm V hVm hAV.symm hBV.symm
    hAV.symm hBV.symm).triangle
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  obtain ⟨M, hVM, hAM⟩ := Postulate1 V A hAV.symm
  intro hb
  have hUL := (half_between_on_line
    ((closedSide_iff_half hAB hAL hBL).mp (hU (A, B) hs V hVm hAV.symm hBV.symm))
    ((closedSide_iff_half hAB hAL hBL).mp (hW (A, B) hs V hVm hAV.symm hBV.symm)) hb hAL).1
  have hUM := (half_between_on_line
    ((closedSide_iff_half hAV.symm hVM hAM).mp (hU (V, A) ht B hBm hBV hAB.symm))
    ((closedSide_iff_half hAV.symm hVM hAM).mp (hW (V, A) ht B hBm hBV hAB.symm)) hb hAM).1
  have he : M = L := line_unique (ne_of_between hb) hUM hAM hUL hAL
  exact hT.off_line hAL hBL (he ▸ hVM)

/-- A nonempty list can be read as an initial list followed by its last member: Lean's
`List.eq_nil_or_concat`, for a list known to be nonempty, with `concat` read as appending. -/
theorem split_last {α : Type} (ps : List α) (h : ps ≠ []) :
    ∃ us V, ps = us ++ [V] := by
  rcases List.eq_nil_or_concat ps with he | ⟨us, V, he⟩
  · exact False.elim (h he)
  · exact ⟨us, V, by simpa using he⟩

/-- No corner lies strictly between two points of the region. -/
theorem corner_not_between {ps : List Point} (h : ConvexOutline ps) {X : Point}
    (hX : X ∈ ps) {U V : Point} (hU : ConvexRegion ps U) (hV : ConvexRegion ps V) :
    ¬ Between U X V := by
  obtain ⟨us, vs, rfl⟩ := List.mem_iff_append.mp hX
  have hr := convex_rotate_prefix us (X :: vs) h
  have hUr := (region_rotate_prefix us (X :: vs) U).mpr hU
  have hVr := (region_rotate_prefix us (X :: vs) V).mpr hV
  change ConvexOutline (X :: (vs ++ us)) at hr
  change ConvexRegion (X :: (vs ++ us)) U at hUr
  change ConvexRegion (X :: (vs ++ us)) V at hVr
  generalize he : vs ++ us = ws at hr hUr hVr
  cases ws with
  | nil => have := hr.1; simp at this
  | cons B ws =>
    obtain ⟨rs, Z, rfl⟩ := split_last ws (by intro he; subst ws; have := hr.1; simp at this)
    exact head_not_between hr hUr hVr

/-- From a closed half-plane towards its open half-plane, every intermediate point
is in the open half-plane. -/
theorem between_half_open {X Y Z R : Point} {L : Line}
    (hX : OnLine X L ∨ SameSide X R L) (hY : SameSide Y R L)
    (hb : Between X Z Y) : SameSide Z R L := by
  rcases hX with hX | hX
  · have hZ : ¬ OnLine Z L := fun hz =>
      not_on_line_of_same_side hY (on_line_of_between hb hX hz)
    exact same_side_trans (same_side_symm (pasch2 hb hX hZ)) hY
  · have hXY := same_side_trans (same_side_symm hX) (same_side_symm hY)
    exact same_side_trans (pasch1 hb hXY) hX

/-- A point between a closed triangle point and an interior point is interior. -/
theorem between_triangle_open {A B C X Y Z : Point} (h : Triangle A B C)
    (hX : OnOrInsideTriangle X A B C) (hY : InsideTriangle Y A B C)
    (hb : Between X Z Y) : InsideTriangle Z A B C := by
  have hc := (closed_triangle_sides h).mp hX
  have step {U V R : Point} (hUV : U ≠ V)
      (hXR : ClosedSide X R U V) (hYR : SameSideOf Y R U V) :
      SameSideOf Z R U V := by
    obtain ⟨L, hU, hV⟩ := Postulate1 U V hUV
    exact SameSideOf.of_line hUV hU hV (between_half_open
      ((closedSide_iff_half hUV hU hV).mp hXR) (hYR.sameSide hU hV) hb)
  exact ⟨step h.ne₂₃ hc.1 hY.1, step h.ne₁₃.symm hc.2.1 hY.2.1,
    step h.ne₁₂ hc.2.2 hY.2.2⟩

/-- Given a point within or on a triangle and off a straight line, another point
within or on the triangle avoids a prescribed finite list of lines and remains
on the same side of the first line as the given point. -/
theorem triangle_local_avoiding {A B C X : Point} {L : Line}
    (h : Triangle A B C) (hX : OnOrInsideTriangle X A B C)
    (hXL : ¬ OnLine X L) (ls : List Line) :
    ∃ Y, OnOrInsideTriangle Y A B C ∧ Avoid ls Y ∧ SameSide Y X L := by
  obtain ⟨I, hI, _⟩ := triangle_point_avoiding h []
  have hz : ∃ Z, InsideTriangle Z A B C ∧ SameSide Z X L := by
    by_cases he : X = I
    · exact ⟨X, he ▸ hI, same_side_refl hXL⟩
    · obtain ⟨Z, hb, hs⟩ := shorten_off_line he hXL
      exact ⟨Z, between_triangle_open h hX hI hb, hs⟩
  obtain ⟨Z, hZ, hZL⟩ := hz
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C h.ne₂₃
  obtain ⟨CA, hC', hA⟩ := Postulate1 C A h.ne₁₃.symm
  obtain ⟨AB, hA', hB'⟩ := Postulate1 A B h.ne₁₂
  let hs : List (Point × Line) := [(A, BC), (B, CA), (C, AB), (X, L)]
  have hzs : ∀ s ∈ hs, SameSide Z s.1 s.2 := by
    intro s hsm
    simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hsm
    rcases hsm with rfl | rfl | rfl | rfl
    · exact hZ.1.sameSide hB hC
    · exact hZ.2.1.sameSide hC' hA
    · exact hZ.2.2.sameSide hA' hB'
    · exact hZL
  obtain ⟨D, E, F, hDEF, hsmall⟩ := small_triangle hs hzs
  obtain ⟨Y, hY, hYa⟩ := triangle_point_avoiding hDEF.1.symm.triangle.cab ls
  have hy := hsmall Y (Or.inl hY)
  refine ⟨Y, Or.inl ?_, hYa, hy (X, L) (by simp [hs])⟩
  exact ⟨SameSideOf.of_line h.ne₂₃ hB hC (hy (A, BC) (by simp [hs])),
    SameSideOf.of_line h.ne₁₃.symm hC' hA (hy (B, CA) (by simp [hs])),
    SameSideOf.of_line h.ne₁₂ hA' hB' (hy (C, AB) (by simp [hs]))⟩

/-- Inclusion away from finitely many lines implies inclusion of the closed regions. -/
theorem region_inclusion {ps qs : List Point} (hp : ConvexOutline ps)
    (ls : List Line)
    (hin : ∀ Y, Avoid ls Y → ConvexRegion ps Y → ConvexRegion qs Y) :
    ∀ X, ConvexRegion ps X → ConvexRegion qs X := by
  intro X hX s hs R hR hR₁ hR₂
  apply Classical.byContradiction
  intro hn
  have hne : s.1 ≠ s.2 := by
    intro he
    obtain ⟨M, hM, hMX⟩ := collinear_of_two s.1 X
    exact hn (Or.inl ⟨M, hM, he ▸ hM, hMX⟩)
  obtain ⟨L, hA, hB⟩ := Postulate1 s.1 s.2 hne
  have hXL : ¬ OnLine X L := fun hx => hn (Or.inl ⟨L, hA, hB, hx⟩)
  have hXR : ¬ SameSide X R L := fun hx => hn
    (Or.inr (SameSideOf.of_line hne hA hB hx))
  obtain ⟨t, ht, hXt⟩ := (fan_covers hp X).mpr hX
  obtain ⟨Y, hYt, hYa, hYX⟩ := triangle_local_avoiding (fan_triangle hp t ht) hXt hXL ls
  obtain ⟨htA, htB, htC⟩ := fan_mem ht
  have hYq := hin Y hYa (triangle_in_region hp htA htB htC hYt)
  rcases (closedSide_iff_half hne hA hB).mp (hYq s hs R hR hR₁ hR₂) with hy | hy
  · exact not_on_line_of_same_side hYX hy
  · exact hXR (same_side_trans hYX hy)

/-- A supporting line from the first corner to another corner reaches one of its
two neighbours. The two incident supporting sides exclude every interior ray. -/
theorem support_neighbours {A B V X : Point} {ps : List Point}
    (h : ConvexOutline (A :: B :: (ps ++ [V])))
    (hX : X ∈ A :: B :: (ps ++ [V])) (hXA : X ≠ A)
    (hs : B ≠ X → V ≠ X → SameSideOf B V A X) : X = B ∨ X = V := by
  by_cases hXB : X = B
  · exact Or.inl hXB
  by_cases hXV : X = V
  · exact Or.inr hXV
  have hn := h.2.1
  simp only [List.nodup_cons] at hn
  have hAB : A ≠ B := fun e => hn.1 (by simp [e])
  have hAV : A ≠ V := fun e => hn.1 (by simp [e])
  have hBV : B ≠ V := fun e => hn.2.1 (by simp [e])
  have hBm : B ∈ A :: B :: (ps ++ [V]) := by simp
  have hVm : V ∈ A :: B :: (ps ++ [V]) := by simp
  have hfirst : (A, B) ∈ sides (A :: B :: (ps ++ [V])) := by simp [sides, segments]
  have hlast : (V, A) ∈ sides (A :: B :: (ps ++ [V])) := by
    simpa [sides, List.append_assoc] using closing_segment A V (A :: B :: ps)
  have hXVside := h.2.2 (A, B) hfirst X hX V hVm hXA hXB hAV.symm hBV.symm
  have hBXside := h.2.2 (V, A) hlast B hBm X hX hBV hAB.symm hXV hXA
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  obtain ⟨M, hAM, hXM⟩ := Postulate1 A X hXA.symm
  obtain ⟨N, hAN, hVN⟩ := Postulate1 A V hAV
  exact False.elim (triple_incidence1 hAL hAM hAN hBL hXM hVN
    (hXVside.sameSide hAL hBL) (hBXside.sameSide hVN hAN)
    ((hs (Ne.symm hXB) (Ne.symm hXV)).sameSide hAM hXM))

/-- Once an initial directed edge is fixed, the unvisited corners of two convex
outlines with the same remaining corners occur in the same order. -/
theorem tails_unique (ps : List Point) : ∀ (qs us : List Point) (A B : Point),
    ConvexOutline (A :: B :: (ps ++ us)) →
    ConvexOutline (A :: B :: (qs ++ us)) →
    (∀ X, X ∈ ps ↔ X ∈ qs) → ps = qs := by
  induction ps with
  | nil =>
    intro qs us A B hp hq hm
    cases qs with
    | nil => rfl
    | cons C qs => exact False.elim (List.not_mem_nil ((hm C).mpr (by simp)))
  | cons C ps ih =>
    intro qs us A B hp hq hm
    cases qs with
    | nil => exact False.elim (List.not_mem_nil ((hm C).mp (by simp)))
    | cons D qs =>
      have hpr := ConvexOutline.rotate hp
      have hqr := ConvexOutline.rotate hq
      have hndp := hp.2.1
      have hndq := hq.2.1
      simp only [List.cons_append, List.nodup_cons] at hndp hndq
      have hCA : C ≠ A := fun e => hndp.1 (by simp [e])
      have hCB : C ≠ B := fun e => hndp.2.1 (by simp [e])
      have hAB : A ≠ B := fun e => hndp.1 (by simp [e])
      have hDB : D ≠ B := fun e => hndq.2.1 (by simp [e])
      have hCm : C ∈ B :: D :: ((qs ++ us) ++ [A]) := by
        have hc := (hm C).mp (by simp)
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · simp
        · simp [hc]
      have he : C = D ∨ C = A := support_neighbours
        (by simpa [List.append_assoc] using hqr) hCm hCB (by
          intro hDC hAC
          have hDm : D ∈ B :: C :: ((ps ++ us) ++ [A]) := by
            have hd := (hm D).mpr (by simp)
            simp only [List.mem_cons] at hd
            rcases hd with rfl | hd
            · simp
            · simp [hd]
          exact hpr.2.2 (B, C) (by simp [sides, segments]) D hDm A (by simp)
            hDB hDC hAB hAC)
      have hCD := he.resolve_right hCA
      subst D
      have hm' : ∀ X, X ∈ ps ↔ X ∈ qs := by
        intro X
        constructor
        · intro hx
          rcases List.mem_cons.mp ((hm X).mp (List.mem_cons_of_mem C hx)) with he | hy
          · exact False.elim (hndp.2.2.1 (by simp [← he, hx]))
          · exact hy
        · intro hy
          rcases List.mem_cons.mp ((hm X).mpr (List.mem_cons_of_mem C hy)) with he | hx
          · exact False.elim (hndq.2.2.1 (by simp [← he, hy]))
          · exact hx
      exact congrArg (List.cons C) (ih qs (us ++ [A]) B C
        (by simpa [List.append_assoc] using hpr)
        (by simpa [List.append_assoc] using hqr) hm')

/-- Equal corner sets and the same first directed edge determine the whole outline. -/
theorem first_edge_unique {A B : Point} {ps qs : List Point}
    (hp : ConvexOutline (A :: B :: ps)) (hq : ConvexOutline (A :: B :: qs))
    (hm : ∀ X, X ∈ A :: B :: ps ↔ X ∈ A :: B :: qs) : ps = qs := by
  apply tails_unique ps qs [] A B (by simpa using hp) (by simpa using hq)
  intro X
  have hnP := hp.2.1
  have hnQ := hq.2.1
  simp only [List.nodup_cons] at hnP hnQ
  by_cases hXA : X = A
  · subst X
    have hAp : A ∉ ps := fun hm => hnP.1 (List.mem_cons_of_mem B hm)
    have hAq : A ∉ qs := fun hm => hnQ.1 (List.mem_cons_of_mem B hm)
    simp [hAp, hAq]
  by_cases hXB : X = B
  · subst X
    simp [hnP.2.1, hnQ.2.1]
  simpa [hXA, hXB] using hm X

/-- With the first corner fixed, equal corner sets determine the outline in one
of the two directions. -/
theorem head_order_unique {A B : Point} {ps qs : List Point}
    (hp : ConvexOutline (A :: B :: ps)) (hq : ConvexOutline (A :: qs))
    (hm : ∀ X, X ∈ A :: B :: ps ↔ X ∈ A :: qs) :
    A :: B :: ps = A :: qs ∨ A :: B :: ps = A :: qs.reverse := by
  cases qs with
  | nil => have := hq.1; simp at this
  | cons D qs =>
    obtain ⟨rs, V, rfl⟩ := split_last qs (by intro he; subst qs; have := hq.1; simp at this)
    have hndp := hp.2.1
    have hndq := hq.2.1
    simp only [List.nodup_cons] at hndp hndq
    have hBA : B ≠ A := fun he => hndp.1 (by simp [he])
    have hDA : D ≠ A := fun he => hndq.1 (by simp [he])
    have hVA : V ≠ A := fun he => hndq.1 (by simp [he])
    have hBm := (hm B).mp (by simp)
    have hn : B = D ∨ B = V := support_neighbours hq hBm hBA (by
      intro hDB hVB
      exact hp.2.2 (A, B) (by simp [sides, segments])
        D ((hm D).mpr (by simp)) V ((hm V).mpr (by simp)) hDA hDB hVA hVB)
    rcases hn with rfl | rfl
    · have he := first_edge_unique hp hq hm
      exact Or.inl (by rw [he])
    · have hr : ConvexOutline (A :: (D :: (rs ++ [B])).reverse) := by
        have hh := convex_rotate_prefix (D :: (rs ++ [B])).reverse [A] (by simpa using hq.reverse)
        simpa using hh
      have hm' : ∀ X, X ∈ A :: B :: ps ↔ X ∈ A :: B :: (rs.reverse ++ [D]) := by
        intro X
        have ht : X ∈ A :: (D :: (rs ++ [B])).reverse ↔ X ∈ A :: D :: (rs ++ [B]) := by
          simp only [List.mem_cons, List.mem_reverse]
        simpa using (hm X).trans ht.symm
      have he := first_edge_unique hp (by simpa using hr) hm'
      exact Or.inr (by simp [he])

end Elements.Figures.Extreme
