import Elements.Figure.Cells

/-!
# Staging: cells that lie apart, divided by their fans

The last step of brief 0013's arrangement route to `division_exists`: the cells selected from
an arrangement have disjoint insides, and drawing the fan in each cell and putting the fans
together gives triangles that lie apart and cover exactly the cells' closed regions. Inside
one cell the fan's triangles lie apart (`fan_apart`); across two cells they lie apart because
the inside of each fan triangle lies inside its cell (`fan_inside_core`).
-/

namespace Elements.Figures

namespace DivisionFacts

open Tacit

/-- A convex outline's fan has a triangle: there are three corners at least. -/
theorem fan_ne_nil {cs : List Point} (h : ConvexOutline cs) : fan cs ≠ [] := by
  obtain ⟨A, B, C, rest, rfl⟩ := CellFacts.three_corners h
  simp [fan, segments]

/-- **A fan triangle's inside is inside its cell**: every corner of the cell is on the closed
inward side of each side, so a point inside a triangle on three corners is strictly on that
side (`cut_inside_closed_half`). -/
theorem fan_inside_core (P : ConvexCell) {t : Point × Point × Point}
    (ht : t ∈ fan P.corners) {Y : Point} (hY : InsideTriangle Y t.1 t.2.1 t.2.2) :
    P.core Y := by
  intro s hs D hD hD₁ hD₂
  have h := P.convex
  obtain ⟨hA, hB, hC⟩ := Ext.fan_mem ht
  have hss := h.2.2 s hs D hD D hD hD₁ hD₂ hD₁ hD₂
  obtain ⟨L, h₁, h₂⟩ := Postulate1 s.1 s.2 hss.1
  exact SameSideOf.of_line hss.1 h₁ h₂ (cut_inside_closed_half
    (corner_half h hs hD hD₁ hD₂ hA h₁ h₂)
    (corner_half h hs hD hD₁ hD₂ hB h₁ h₂)
    (corner_half h hs hD hD₁ hD₂ hC h₁ h₂) hY)

/-- **Cells with disjoint insides, divided by their fans**: the fans of a nonempty list of
cells, no point inside two of them, put together, are triangles that lie apart, and they cover
exactly the points of the cells' closed regions. -/
theorem cells_division (rs : List ConvexCell) (hne : rs ≠ [])
    (ha : rs.Pairwise (fun Q R => ∀ X : Point, Q.core X → ¬ R.core X)) :
    ∃ R : Apart, R.pieces = rs.flatMap (fun Q => fan Q.corners) ∧
      ∀ X : Point, Covers R.pieces X ↔ ∃ Q ∈ rs, Q.region X := by
  /- A cell gives at least one triangle, so the triangles are not none. -/
  have hpne : rs.flatMap (fun Q => fan Q.corners) ≠ [] := by
    obtain ⟨Q, hQ⟩ := List.exists_mem_of_ne_nil rs hne
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ (fan_ne_nil Q.convex)
    exact List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨Q, hQ, ht⟩)
  /- Each is a triangle of its cell's fan. -/
  have htri : ∀ t ∈ rs.flatMap (fun Q => fan Q.corners), Triangle t.1 t.2.1 t.2.2 := by
    intro t ht
    obtain ⟨Q, -, ht⟩ := List.mem_flatMap.mp ht
    exact fan_triangle Q.convex t ht
  /- Two triangles of one fan lie apart (`fan_apart`); two of different cells have their
  insides in the cells' insides, which have no point in common. -/
  have hapart : (rs.flatMap fun Q => fan Q.corners).Pairwise fun s s' => ∀ Y : Point,
      InsideTriangle Y s.1 s.2.1 s.2.2 → ¬ InsideTriangle Y s'.1 s'.2.1 s'.2.2 := by
    refine List.pairwise_flatMap.mpr ⟨fun Q _ => fan_apart Q.convex, ?_⟩
    exact ha.imp fun {Q₁ Q₂} h₁₂ s hs s' hs' Y hY hY' =>
      h₁₂ Y (fan_inside_core Q₁ hs hY) (fan_inside_core Q₂ hs' hY')
  /- Each fan covers exactly its cell's region (`fan_covers`). -/
  refine ⟨⟨_, hpne, htri, hapart⟩, rfl, fun X => ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht, hXt⟩
    obtain ⟨Q, hQ, ht⟩ := List.mem_flatMap.mp ht
    exact ⟨Q, hQ, (fan_covers Q.convex X).mp ⟨t, ht, hXt⟩⟩
  · rintro ⟨Q, hQ, hX⟩
    obtain ⟨t, ht, hXt⟩ := (fan_covers Q.convex X).mpr hX
    exact ⟨t, List.mem_flatMap.mpr ⟨Q, hQ, ht⟩, hXt⟩

end DivisionFacts

end Elements.Figures
