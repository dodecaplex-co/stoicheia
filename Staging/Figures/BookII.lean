import Staging.Figures.OutlineArea
import Elements.BookII.Prop14

/-!
Proposed companions of II.14, with their proofs. The outline constructions take a division
of the outline (`division_exists`) and its area by the content theorem (`area_eq`), and rest
on Postulate 5 and superposition through II.14.
-/

namespace Elements.BookII.Staging

open Elements.Figures

/-- Companion of II.14, certificate name II.14 outline. To construct a drawn
square equal to a figure given by its outline. This derivation uses the
existing rectangle-to-square construction after obtaining a division
(`division_exists`), and every division gives the outline's area (`area_eq`). -/
theorem Prop14.outline (F : Outline) :
    ∃ P Q S T : Point, Square P Q S T ∧ Parallelogram P Q S T ∧
      quadArea P Q S T = F.area := by
  obtain ⟨R, hR⟩ := division_exists F
  obtain ⟨P, Q, S, T, hs, hp, he⟩ := Elements.BookII.Prop14.square R
  exact ⟨P, Q, S, T, hs, hp, he.trans (area_eq F R hR).symm⟩

/-- Companion of II.14, certificate name II.14 outline_side. The side form
of the construction also equals the outline's area, by a division
(`division_exists`) and the content theorem (`area_eq`). -/
theorem Prop14.outline_side (F : Outline) :
    ∃ P Q : Point, sq P Q = F.area := by
  obtain ⟨R, hR⟩ := division_exists F
  obtain ⟨P, Q, he⟩ := Elements.BookII.Prop14.apart R
  exact ⟨P, Q, he.trans (area_eq F R hR).symm⟩

end Elements.BookII.Staging
