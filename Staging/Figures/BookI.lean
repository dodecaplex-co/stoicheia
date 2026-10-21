import Staging.Figures.OutlineArea
import Staging.Figures.FanBoundary
import Elements.BookI.Prop45

/-!
Proposed companions of I.45. The general construction below is an interface
derivation and remains conditional on the staged boundary and content results.
-/

namespace Elements.BookI.Staging

open Elements.Figures

/-- The existing checked fan encloses the outline through its stated vertices.
This bridge may cite I.13 through Fitted.fan, so it belongs beside I.45.
Its own proof awaits approval. -/
theorem Prop45.fan_boundary {O A B : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A :: B :: ps), Triangle O s.1 s.2)
    (hopp : ∀ t ∈ triples (A :: B :: ps),
      OppositeSidesOf t.1 t.2.2 O t.2.1)
    (hang : Magnitude.sum ((segments (A :: B :: ps)).map
      fun s => ∠ s.1 O s.2) < ∟ + ∟ + (∟ + ∟)) :
    ∃ F : Outline, F.loops = [O :: A :: B :: ps] ∧
      ∃ R : Apart,
        R.pieces = (segments (A :: B :: ps)).map (fun s => (O, s.1, s.2)) ∧
        Divides F.region R := by
  /- The triangles fit together (`Fitted.fan`, which cites I.13), so each meets the earlier
  ones only along the straight line from O across which it is glued
  (`FanBoundary.fitted_meet`). Glued onto the outline one at a time from the triangle OAB,
  each keeps it simple and adds exactly its own points to the region
  (`FanBoundary.fan_loop`). -/
  have hfit := Fitted.fan htri hopp hang
  obtain ⟨hs, hr⟩ := FanBoundary.fan_loop htri (FanBoundary.fitted_meet hfit)
  refine ⟨singleOutline _ hs, rfl, Rectilineal.toApart ⟨_, hfit⟩, rfl, fun X => ?_⟩
  rw [single_region]
  exact (hr X).symm

/-- Companion of I.45, certificate name I.45 outline. To construct, in the
given rectilineal angle, a parallelogram equal to a figure given by its
outline. The division is obtained by a theorem. This derivation remains
conditional on the staged existence and content results. -/
theorem Prop45.outline {E₁ E E₂ : Point} (F : Outline)
    (hE : Triangle E₁ E E₂) :
    ∃ K P L M : Point, Parallelogram K P L M ∧
      ∠ P K M = ∠ E₁ E E₂ ∧ quadArea K P L M = F.area := by
  obtain ⟨R, hR⟩ := division_exists F
  obtain ⟨K, P, L, M, hp, ha, he⟩ := Elements.BookI.Prop45.apart R hE
  exact ⟨K, P, L, M, hp, ha, he.trans (area_eq F R hR).symm⟩

end Elements.BookI.Staging
