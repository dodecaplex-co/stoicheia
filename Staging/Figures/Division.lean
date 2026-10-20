import Staging.Figures.Outline
import Staging.Figures.Content
import Staging.Figures.ConvexCover
import Elements.Figure.Rectilineal

/-!
Division statements proposed by brief 0013. Their own proofs await approval.
The supplied Outline never contains a division witness.
-/

namespace Elements.Figures

/-- Every admitted outline has a division into nondegenerate triangles. -/
theorem division_exists (F : Outline) : ∃ R : Apart, Divides F.region R := by
  sorry

/-- Exact closed coverage and disjoint interiors are both part of a division.
This merely unpacks the proposed interface. -/
theorem division_coverage (F : Outline) (R : Apart) (h : Divides F.region R) :
    (∀ X : Point, Covers R.pieces X ↔ F.region X) ∧
      R.pieces.Pairwise (fun s t => ∀ X : Point,
        InsideTriangle X s.1 s.2.1 s.2.2 →
          ¬ InsideTriangle X t.1 t.2.1 t.2.2) :=
  ⟨h, R.apart⟩

/-- The explicit fan divides a strictly convex outline. This interface derivation
uses the staged triangle, separation and coverage theorems. -/
theorem convex_fan {cs : List Point} (h : ConvexOutline cs) :
    ∃ R : Apart, R.pieces = fan cs ∧ Divides (ConvexRegion cs) R := by
  have hne : fan cs ≠ [] := by
    rcases cs with _ | ⟨O, cs⟩
    · simp [ConvexOutline] at h
    rcases cs with _ | ⟨A, cs⟩
    · simp [ConvexOutline] at h
    rcases cs with _ | ⟨B, cs⟩
    · simp [ConvexOutline] at h
    simp [fan, segments]
  let R : Apart := ⟨fan cs, hne, fan_triangle h, fan_apart h⟩
  exact ⟨R, rfl, fun X => fan_covers h X⟩

/-- Every figure previously supplied as an Apart has an outline with exactly
the same region, including holes, separate pieces and contacts at corners. -/
theorem apart_has_outline (R : Apart) : ∃ F : Outline, Divides F.region R := by
  sorry

end Elements.Figures
