import Staging.Figures.CoverFacts

/-!
# Staging: the outline of the checked fan of I.45

Helper lemmas for `Prop45.fan_boundary` in `BookI.lean` (brief 0013, section 8, the
"E2 bridge" of the lemma ledger). No proposition of the Elements is cited here; through
`Outline.lean` this file imports I.23, which only `outline_bounded` uses. `Fitted.fan`, which
cites I.13, is applied only in `BookI.lean`, and these lemmas take what it proves as a
hypothesis.

The fan's triangles O A₁ A₂, O A₂ A₃, …, O Aₙ₋₁ Aₙ are laid round O one at a time.

* **Fitted triangles meet only along their glued sides** (`fitted_meet`). Each triangle of a
  fitted list meets every earlier one only on the finite straight line of its own first two
  corners, the side it was glued across; for a fan triangle O Aᵢ Aᵢ₊₁ that is O Aᵢ.
* **Gluing a triangle onto an outline** (`glue`). Let the outline run from O round to Z and
  close along ZO, and let the triangle O Z W meet its region only on the finite straight line
  OZ. Replacing the side ZO by ZW and WO keeps the outline simple, and its region gains the
  closed triangle and nothing else. A good ray crosses the old outline and the triangle
  together as often as the new outline, with ZO counted twice more; a point of the region and
  of the triangle at once would be on OZ. A point strictly within OZ is joined,
  along a finite straight line through no corner, to a point inside the triangle
  (`CoverFacts.inside_of_segment`).
* **The whole fan** (`fan_chain`, `fan_loop`). From the triangle O A₁ A₂ (`triangle_region`),
  glue the rest in order. No case divides on the size of the angle at O: a straight or
  reflex corner there is a corner of the outline like any other.

Natural numbers count sides and crossings; they measure nothing.
-/

namespace Elements.Figures

open Tacit

namespace FanBoundary

/-! ## Triangles -/

/-- A corner of a triangle is not on the opposite side. -/
theorem not_on_side {A B C : Point} (h : Triangle A B C) : ¬ OnFiniteLine C A B := by
  intro hC
  obtain ⟨L, hA, hB⟩ := Postulate1 A B h.ne₁₂
  exact h ⟨L, hA, hB, LoopFacts.onFiniteLine_onLine hC hA hB⟩

/-- Two sides of a triangle from one corner meet only at that corner. -/
theorem sides_meet {O Z W X : Point} (h : Triangle O Z W) (hZ : OnFiniteLine X O Z)
    (hW : OnFiniteLine X O W) : X = O := by
  refine Classical.byContradiction fun hXO => ?_
  obtain ⟨L, hOL, hZL⟩ := Postulate1 O Z h.ne₁₂
  obtain ⟨M, hOM, hWM⟩ := Postulate1 O W h.ne₁₃
  have he : L = M := line_unique hXO (LoopFacts.onFiniteLine_onLine hZ hOL hZL) hOL
    (LoopFacts.onFiniteLine_onLine hW hOM hWM) hOM
  exact h ⟨L, hOL, hZL, he ▸ hWM⟩

/-- A point inside a triangle is on none of its sides. -/
theorem inside_off_sides {O Z W Y : Point} (h : Triangle O Z W)
    (hY : InsideTriangle Y O Z W) :
    ¬ OnFiniteLine Y O Z ∧ ¬ OnFiniteLine Y Z W ∧ ¬ OnFiniteLine Y W O := by
  obtain ⟨L, hOL, hZL⟩ := Postulate1 O Z h.ne₁₂
  obtain ⟨M, hZM, hWM⟩ := Postulate1 Z W h.ne₂₃
  obtain ⟨N, hWN, hON⟩ := Postulate1 W O h.ne₁₃.symm
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · exact not_on_line_of_same_side (hY.2.2.sameSide hOL hZL)
      (LoopFacts.onFiniteLine_onLine e hOL hZL)
  · exact not_on_line_of_same_side (hY.1.sameSide hZM hWM)
      (LoopFacts.onFiniteLine_onLine e hZM hWM)
  · exact not_on_line_of_same_side (hY.2.1.sameSide hWN hON)
      (LoopFacts.onFiniteLine_onLine e hWN hON)

/-- The sides of a triangle are within or on it. -/
theorem side_closed {O Z W X : Point}
    (h : OnFiniteLine X O Z ∨ OnFiniteLine X Z W ∨ OnFiniteLine X W O) :
    OnOrInsideTriangle X O Z W := by
  unfold OnOrInsideTriangle
  rcases h with (e | e | h) | (e | e | h) | (e | e | h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-! ## Fitted triangles -/

/-- **Fitted triangles meet only along their glued sides.** In a fitted list, a point within
or on a later triangle and within or on an earlier one lies on the finite straight line of
the later triangle's first two corners: the side across which it was glued, which is how
`Fitted.glue` names it. -/
theorem fitted_meet {l : List (Point × Point × Point)} (h : Fitted l) :
    l.Pairwise (fun s t => ∀ Y : Point, OnOrInsideTriangle Y t.1 t.2.1 t.2.2 →
      OnOrInsideTriangle Y s.1 s.2.1 s.2.2 → OnFiniteLine Y t.1 t.2.1) := by
  induction h with
  | single _ => exact List.pairwise_singleton _ _
  | glue _ _ _ _ hmeet ih =>
    rw [List.pairwise_append]
    refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
    intro s hs t ht Y hYt hYs
    rw [List.mem_singleton] at ht
    subst ht
    exact hmeet Y hYt s hs hYs

/-! ## Gluing a triangle onto an outline

The outline is read from O round to its last corner Z, `O :: (ws ++ [Z])`, closing along ZO.
The triangle O Z W is glued across ZO, and the new outline `O :: (ws ++ [Z, W])` runs from
Z to W and closes along WO. -/

/-- The sides of the outline from O round to Z: the chain from O to Z, and ZO. -/
theorem sides_close (O Z : Point) (ws : List Point) :
    sides (O :: (ws ++ [Z])) = segments (O :: (ws ++ [Z])) ++ [(Z, O)] := by
  have e := segments_join (O :: ws) [O] Z
  simp only [List.cons_append] at e
  simpa [sides, segments] using e

/-- The sides of the outline continued from Z to W: the same chain, ZW and WO. -/
theorem sides_glue (O Z W : Point) (ws : List Point) :
    sides (O :: (ws ++ [Z, W])) = segments (O :: (ws ++ [Z])) ++ [(Z, W), (W, O)] := by
  have e := segments_join (O :: ws) [W, O] Z
  simp only [List.cons_append] at e
  simpa [sides, segments] using e

/-- The boundary of the outline from O round to Z: the chain, or the closing side ZO. -/
theorem boundary_close (O Z : Point) (ws : List Point) (X : Point) :
    loopBoundary (O :: (ws ++ [Z])) X ↔
      (∃ s ∈ segments (O :: (ws ++ [Z])), OnFiniteLine X s.1 s.2) ∨ OnFiniteLine X Z O := by
  unfold loopBoundary
  rw [sides_close]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_and_right,
    exists_or, exists_eq_left]

/-- The boundary of the outline continued to W: the chain, ZW or WO. -/
theorem boundary_glue (O Z W : Point) (ws : List Point) (X : Point) :
    loopBoundary (O :: (ws ++ [Z, W])) X ↔
      (∃ s ∈ segments (O :: (ws ++ [Z])), OnFiniteLine X s.1 s.2) ∨
        OnFiniteLine X Z W ∨ OnFiniteLine X W O := by
  unfold loopBoundary
  rw [sides_glue]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_and_right,
    exists_or, exists_eq_left]

/-- **The count across the glued triangle.** A ray crosses the new outline and ZO as often as
the old outline and ZW and WO; the triangle's own count adds ZO once more. So the new count
has the parity of the old count and the triangle's together. -/
theorem count_glue (O Z W : Point) (ws : List Point) (X Q : Point) :
    crossingCount (O :: (ws ++ [Z, W])) X Q % 2 =
      (crossingCount (O :: (ws ++ [Z])) X Q + crossingCount [O, Z, W] X Q) % 2 := by
  classical
  have hsym : RayCrosses X Q (O, Z) ↔ RayCrosses X Q (Z, O) :=
    ⟨fun ⟨Y, hY, hb⟩ => ⟨Y, hY, between_symm hb⟩,
      fun ⟨Y, hY, hb⟩ => ⟨Y, hY, between_symm hb⟩⟩
  have e : sides [O, Z, W] = [(O, Z), (Z, W), (W, O)] := rfl
  unfold crossingCount
  rw [sides_glue, sides_close, e, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  simp only [List.countP_append, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  by_cases h₁ : RayCrosses X Q (Z, O) <;> by_cases h₂ : RayCrosses X Q (Z, W) <;>
    by_cases h₃ : RayCrosses X Q (W, O) <;> simp [h₁, h₂, h₃, hsym] <;> omega

/-- **Gluing a triangle onto an outline.** Let the simple outline run from O round to Z, and
let the triangle O Z W meet its region only on the finite straight line OZ. Then the outline
continued from Z to W, and closed along WO, is simple, and its region is the old region
together with the closed triangle. -/
theorem glue {O Z W : Point} {ws : List Point} (h : SimpleLoop (O :: (ws ++ [Z])))
    (hT : Triangle O Z W)
    (hmeet : ∀ X : Point, loopRegion (O :: (ws ++ [Z])) X → OnOrInsideTriangle X O Z W →
      OnFiniteLine X O Z) :
    SimpleLoop (O :: (ws ++ [Z, W])) ∧
      ∀ X : Point, loopRegion (O :: (ws ++ [Z, W])) X ↔
        loopRegion (O :: (ws ++ [Z])) X ∨ OnOrInsideTriangle X O Z W := by
  have hold := h
  obtain ⟨hlen, hnd, hne, hpw⟩ := h
  have hbo := boundary_close O Z ws
  have hbn := boundary_glue O Z W ws
  have hso := sides_close O Z ws
  have hsn := sides_glue O Z W ws
  /- The new corner W is not an old one: on the old boundary, it would be on OZ. -/
  have hWnot : W ∉ O :: (ws ++ [Z]) := by
    intro hW
    obtain ⟨E, hE⟩ := outgoing_side hW
    exact not_on_side hT (hmeet W (Or.inl ⟨(W, E), hE, Or.inl rfl⟩)
      (side_closed (Or.inr (Or.inl (Or.inr (Or.inl rfl))))))
  have hsub : ∀ V ∈ O :: (ws ++ [Z]), V ∈ O :: (ws ++ [Z, W]) := by
    intro V hV
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hV ⊢
    rcases hV with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
  have htsub : ∀ V ∈ [O, Z, W], V ∈ O :: (ws ++ [Z, W]) := by
    intro V hV
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hV ⊢
    rcases hV with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr e))
  /- The old sides of the chain meet the new sides ZW and WO only at Z and at O, where the
  closing side ZO met them. -/
  have hchain : ∀ a ∈ segments (O :: (ws ++ [Z])), ∀ X : Point,
      OnFiniteLine X a.1 a.2 → OnFiniteLine X Z O → (X = a.1 ∨ X = a.2) := by
    intro a ha X hXa hXZO
    rw [hso] at hpw
    exact ((List.pairwise_append.mp hpw).2.2 a ha (Z, O) List.mem_cons_self X hXa hXZO).1
  have hnew : SimpleLoop (O :: (ws ++ [Z, W])) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢
      omega
    · have hc : (W :: O :: (ws ++ [Z])).Nodup := List.nodup_cons.mpr ⟨hWnot, hnd⟩
      have hp := (List.perm_append_comm (l₁ := O :: (ws ++ [Z])) (l₂ := [W])).nodup_iff.mpr hc
      simpa using hp
    · rw [hsn]
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hne s (by rw [hso]; exact List.mem_append_left _ hs)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact hT.ne₂₃
        · exact hT.ne₁₃.symm
    · rw [hsn, List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [hso] at hpw
        exact (List.pairwise_append.mp hpw).1
      · refine List.pairwise_pair.mpr fun X hXZW hXWO => ?_
        have e : X = W := sides_meet hT.cba (LoopFacts.onFiniteLine_comm.mp hXZW) hXWO
        exact ⟨Or.inr e, Or.inl e⟩
      · intro a ha b hb X hXa hXb
        have hXo : loopRegion (O :: (ws ++ [Z])) X :=
          Or.inl ((hbo X).mpr (Or.inl ⟨a, ha, hXa⟩))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · /- On ZW and on the old boundary: on OZ, hence at Z. -/
          have hXZO := LoopFacts.onFiniteLine_comm.mp
            (hmeet X hXo (side_closed (Or.inr (Or.inl hXb))))
          exact ⟨hchain a ha X hXa hXZO, Or.inl (sides_meet hT.bac hXZO hXb)⟩
        · /- On WO and on OZ: at O. -/
          have hXOZ := hmeet X hXo (side_closed (Or.inr (Or.inr hXb)))
          have e : X = O := sides_meet hT hXOZ (LoopFacts.onFiniteLine_comm.mp hXb)
          exact ⟨hchain a ha X hXa (LoopFacts.onFiniteLine_comm.mp hXOZ), Or.inr e⟩
  /- A point inside the triangle is on neither boundary. -/
  have hoffT : ∀ U : Point, InsideTriangle U O Z W →
      ¬ loopBoundary (O :: (ws ++ [Z, W])) U ∧ ¬ loopBoundary (O :: (ws ++ [Z])) U := by
    intro U hU
    obtain ⟨h₁, h₂, h₃⟩ := inside_off_sides hT hU
    have hUo : ¬ loopBoundary (O :: (ws ++ [Z])) U := fun hb =>
      h₁ (hmeet U (Or.inl hb) (Or.inl hU))
    refine ⟨fun hb => ?_, hUo⟩
    rcases (hbn U).mp hb with hs | hU' | hU'
    · exact hUo ((hbo U).mpr (Or.inl hs))
    · exact h₂ hU'
    · exact h₃ hU'
  /- Off both boundaries, the parity of a good ray decides: the old region and the triangle
  share no such point, so the new count is odd exactly when one of the others is. -/
  have key : ∀ X : Point, ¬ loopBoundary (O :: (ws ++ [Z, W])) X →
      ¬ loopBoundary (O :: (ws ++ [Z])) X →
      (loopInside (O :: (ws ++ [Z, W])) X ↔
        loopInside (O :: (ws ++ [Z])) X ∨ OnOrInsideTriangle X O Z W) := by
    intro X hXn hXo
    obtain ⟨hTs, hTr⟩ := triangle_region hT
    have hXt : ¬ loopBoundary [O, Z, W] X := by
      rintro ⟨s, hs, hXs⟩
      have e : sides [O, Z, W] = [(O, Z), (Z, W), (W, O)] := rfl
      rw [e] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact hXo ((hbo X).mpr (Or.inr (LoopFacts.onFiniteLine_comm.mp hXs)))
      · exact hXn ((hbn X).mpr (Or.inr (Or.inl hXs)))
      · exact hXn ((hbn X).mpr (Or.inr (Or.inr hXs)))
    obtain ⟨Q, hQ⟩ := good_ray_exists hnew hXn
    have hQo : GoodRay (O :: (ws ++ [Z])) X Q := ⟨hQ.1, fun V hV => hQ.2 V (hsub V hV)⟩
    have hQt : GoodRay [O, Z, W] X Q := ⟨hQ.1, fun V hV => hQ.2 V (htsub V hV)⟩
    have ht : OnOrInsideTriangle X O Z W ↔ crossingCount [O, Z, W] X Q % 2 = 1 := by
      rw [← hTr X, ← loop_inside_iff hTs hXt hQt]
      exact ⟨fun hr => hr.resolve_left hXt, Or.inr⟩
    have hnot : ¬ (crossingCount (O :: (ws ++ [Z])) X Q % 2 = 1 ∧
        crossingCount [O, Z, W] X Q % 2 = 1) := by
      rintro ⟨h₁, h₂⟩
      exact hXo ((hbo X).mpr (Or.inr (LoopFacts.onFiniteLine_comm.mp
        (hmeet X (Or.inr ⟨hXo, Q, hQo, h₁⟩) (ht.mpr h₂)))))
    have hc := count_glue O Z W ws X Q
    rw [loop_inside_iff hnew hXn hQ, loop_inside_iff hold hXo hQo, ht]
    constructor
    · intro h'
      omega
    · intro h'
      omega
  refine ⟨hnew, fun X => ?_⟩
  by_cases hXn : loopBoundary (O :: (ws ++ [Z, W])) X
  · /- On the new boundary: on the old one, or on a side of the triangle. -/
    refine ⟨fun _ => ?_, fun _ => Or.inl hXn⟩
    rcases (hbn X).mp hXn with hs | hX | hX
    · exact Or.inl (Or.inl ((hbo X).mpr (Or.inl hs)))
    · exact Or.inr (side_closed (Or.inr (Or.inl hX)))
    · exact Or.inr (side_closed (Or.inr (Or.inr hX)))
  by_cases hXo : loopBoundary (O :: (ws ++ [Z])) X
  · /- Strictly within ZO, no longer a side. A finite straight line through no corner joins X
    to a point Y inside the triangle, meeting neither boundary on the way; Y is inside the
    new outline, and so is X. -/
    have hXZO : OnFiniteLine X Z O := by
      rcases (hbo X).mp hXo with hs | hX
      · exact absurd ((hbn X).mpr (Or.inl hs)) hXn
      · exact hX
    have hXT : OnOrInsideTriangle X O Z W :=
      side_closed (Or.inl (LoopFacts.onFiniteLine_comm.mp hXZO))
    have hVX : ∀ V ∈ O :: (ws ++ [Z, W]), V ≠ X := by
      intro V hV e
      obtain ⟨E, hE⟩ := outgoing_side hV
      exact hXn ⟨(V, E), hE, Or.inl e.symm⟩
    let line (V : Point) : Line := Classical.choose (collinear_of_two X V)
    have hline (V : Point) : OnLine X (line V) ∧ OnLine V (line V) :=
      Classical.choose_spec (collinear_of_two X V)
    obtain ⟨Y, hY, hYa⟩ := triangle_point_avoiding hT ((O :: (ws ++ [Z, W])).map line)
    have hXY : X ≠ Y := by
      intro e
      subst e
      exact (inside_off_sides hT hY).1 (LoopFacts.onFiniteLine_comm.mp hXZO)
    obtain ⟨ℓ, hXℓ, hYℓ⟩ := Postulate1 X Y hXY
    have hoff : ∀ V ∈ O :: (ws ++ [Z, W]), ¬ OnLine V ℓ := by
      intro V hV hVℓ
      have he : line V = ℓ := line_unique (hVX V hV).symm (hline V).1 (hline V).2 hXℓ hVℓ
      exact hYa (line V) (List.mem_map_of_mem hV) (he ▸ hYℓ)
    have hseg : ∀ U : Point, Between X U Y → ¬ loopBoundary (O :: (ws ++ [Z, W])) U :=
      fun U hU => (hoffT U (Ext.between_triangle_open hT hXT hY hU)).1
    have hin : loopInside (O :: (ws ++ [Z, W])) X := by
      rw [CoverFacts.inside_of_segment hnew hXY hXℓ hYℓ hoff hXn (hoffT Y hY).1 hseg]
      exact (key Y (hoffT Y hY).1 (hoffT Y hY).2).mpr (Or.inr (Or.inl hY))
    exact ⟨fun _ => Or.inl (Or.inl hXo), fun _ => Or.inr hin⟩
  · /- Off both boundaries. -/
    have hk := key X hXn hXo
    unfold loopRegion
    constructor
    · rintro (hb | hi)
      · exact absurd hb hXn
      · rcases hk.mp hi with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · rintro ((hb | hi) | ht)
      · exact absurd hb hXo
      · exact Or.inr (hk.mpr (Or.inl hi))
      · exact Or.inr (hk.mpr (Or.inr ht))

/-! ## The whole fan -/

/-- The fan's triangles over the chain from Z through W: the triangle O Z W, then the rest. -/
theorem tris_append (O Z W : Point) (ws rest : List Point) :
    (segments (ws ++ [Z] ++ W :: rest)).map (fun s => (O, s.1, s.2)) =
      (segments (ws ++ [Z])).map (fun s => (O, s.1, s.2)) ++
        (O, Z, W) :: (segments (W :: rest)).map (fun s => (O, s.1, s.2)) := by
  have e₁ := segments_join (ws ++ [Z]) rest W
  have e₂ := segments_join ws [W] Z
  simp only [List.append_assoc, List.cons_append, List.nil_append] at e₁ e₂ ⊢
  rw [e₁, e₂]
  simp [segments]

/-- A point within or on one of a list of triangles and one more: within or on one of the
list, or on the last. -/
theorem covers_concat (ts : List (Point × Point × Point)) (t : Point × Point × Point)
    (X : Point) :
    Covers (ts ++ [t]) X ↔ Covers ts X ∨ OnOrInsideTriangle X t.1 t.2.1 t.2.2 := by
  unfold Covers
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_and_right,
    exists_or, exists_eq_left]

/-- **Gluing the fan's triangles in order.** Given an outline from O round the chain `init`,
simple, with region the fan's triangles over `init`, and the triangles over the longer chain
`init ++ rest`, each meeting every earlier one only along its glued side: the outline round
the longer chain is simple, with region its fan's triangles. -/
theorem fan_chain (O : Point) : ∀ (rest init : List Point), init ≠ [] →
    SimpleLoop (O :: init) →
    (∀ X : Point, loopRegion (O :: init) X ↔
      Covers ((segments init).map fun s => (O, s.1, s.2)) X) →
    (∀ s ∈ segments (init ++ rest), Triangle O s.1 s.2) →
    ((segments (init ++ rest)).map fun s => (O, s.1, s.2)).Pairwise (fun s t => ∀ Y : Point,
      OnOrInsideTriangle Y t.1 t.2.1 t.2.2 → OnOrInsideTriangle Y s.1 s.2.1 s.2.2 →
        OnFiniteLine Y t.1 t.2.1) →
    SimpleLoop (O :: (init ++ rest)) ∧
      ∀ X : Point, loopRegion (O :: (init ++ rest)) X ↔
        Covers ((segments (init ++ rest)).map fun s => (O, s.1, s.2)) X
  | [], init, _, hs, hr, _, _ => by simpa using ⟨hs, hr⟩
  | W :: rest, init, hne, hs, hr, htri, hpw => by
    obtain ⟨ws, Z, rfl⟩ : ∃ ws Z, init = ws ++ [Z] := by
      rcases List.eq_nil_or_concat init with e | ⟨ws, Z, e⟩
      · exact absurd e hne
      · exact ⟨ws, Z, by simpa using e⟩
    have hT : Triangle O Z W := htri (Z, W) (by
      rw [show segments (ws ++ [Z] ++ W :: rest) =
          segments (ws ++ [Z] ++ [W]) ++ segments (W :: rest) from segments_join _ _ _]
      refine List.mem_append_left _ ?_
      rw [List.append_assoc, List.singleton_append, segments_join ws [W] Z]
      simp [segments])
    /- The triangle O Z W meets the region so far, the earlier triangles, only along OZ. -/
    rw [tris_append, List.pairwise_append] at hpw
    have hmeet : ∀ X : Point, loopRegion (O :: (ws ++ [Z])) X → OnOrInsideTriangle X O Z W →
        OnFiniteLine X O Z := by
      intro X hX hXT
      obtain ⟨t, ht, hXt⟩ := (hr X).mp hX
      exact hpw.2.2 t ht (O, Z, W) List.mem_cons_self X hXT hXt
    obtain ⟨hs', hr'⟩ := glue hs hT hmeet
    have he : ws ++ [Z] ++ W :: rest = ws ++ [Z, W] ++ rest := by simp
    have hseg : (segments (ws ++ [Z, W])).map (fun s => (O, s.1, s.2)) =
        (segments (ws ++ [Z])).map (fun s => (O, s.1, s.2)) ++ [(O, Z, W)] := by
      have e := tris_append O Z W ws []
      simpa [segments] using e
    have hr'' : ∀ X : Point, loopRegion (O :: (ws ++ [Z, W])) X ↔
        Covers ((segments (ws ++ [Z, W])).map fun s => (O, s.1, s.2)) X := by
      intro X
      rw [hr' X, hseg, covers_concat, hr X]
    rw [he] at htri ⊢
    have hpw' : ((segments (ws ++ [Z, W] ++ rest)).map fun s => (O, s.1, s.2)).Pairwise
        (fun s t => ∀ Y : Point, OnOrInsideTriangle Y t.1 t.2.1 t.2.2 →
          OnOrInsideTriangle Y s.1 s.2.1 s.2.2 → OnFiniteLine Y t.1 t.2.1) := by
      rw [← he, tris_append, List.pairwise_append]
      exact hpw
    exact fan_chain O rest (ws ++ [Z, W]) (by simp) hs' hr'' htri hpw'

/-- **The outline of a checked fan.** The triangles O s.1 s.2 over the consecutive corners of
A, B, ps, each meeting every earlier one only along its glued side, have the outline
O, A, B, ps: it is simple, and its region is exactly their closed union. -/
theorem fan_loop {O A B : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A :: B :: ps), Triangle O s.1 s.2)
    (hpw : ((segments (A :: B :: ps)).map fun s => (O, s.1, s.2)).Pairwise
      (fun s t => ∀ Y : Point, OnOrInsideTriangle Y t.1 t.2.1 t.2.2 →
        OnOrInsideTriangle Y s.1 s.2.1 s.2.2 → OnFiniteLine Y t.1 t.2.1)) :
    SimpleLoop (O :: A :: B :: ps) ∧
      ∀ X : Point, loopRegion (O :: A :: B :: ps) X ↔
        Covers ((segments (A :: B :: ps)).map fun s => (O, s.1, s.2)) X := by
  have hOAB : Triangle O A B := htri (A, B) List.mem_cons_self
  obtain ⟨hs, hr⟩ := triangle_region hOAB
  have hr' : ∀ X : Point, loopRegion [O, A, B] X ↔
      Covers ((segments [A, B]).map fun s => (O, s.1, s.2)) X := by
    intro X
    rw [hr X]
    simp [Covers, segments]
  exact fan_chain O ps [A, B] (List.cons_ne_nil _ _) hs hr' htri hpw

end FanBoundary

end Elements.Figures
