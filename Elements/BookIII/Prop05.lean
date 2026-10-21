import Elements.Figure.Basics
import Elements.BookIII.Squares

/-!
# Book III, Proposition 5

Euclid's text, in Heath's translation: [`heath/III/05.md`](../../heath/III/05.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If two circles cut one another, they will not have the same centre. -/
theorem Prop5 {E : Point} {ABC CDG : Circle} (hcut : CirclesCut ABC CDG) :
    ¬ (Centre E ABC ∧ Centre E CDG) := by
  -- For let the circles ABC, CDG cut one another at the points B, C;
  obtain ⟨⟨B, C, -, -, -, hC_ABC, hC_CDG⟩, ⟨F, hF_ABC, hF_in⟩, -⟩ := hcut
  -- I say that they will not have the same centre.
  -- For, if possible, let it be E; let EC be joined, and let EFG be drawn through at random.
  rintro ⟨hE_ABC, hE_CDG⟩
  /- EC is drawn for the eye; our proof uses only its ends. EFG is drawn through F, a point
     of ABC within CDG, where the circles cut one another; produced beyond F, it meets CDG
     at G. One straight line from E meeting the circles at two points is all the argument
     needs, as Heath says under III.6. -/
  have hFE : F ≠ E := ne_of_centre_of_on hE_ABC hF_ABC
  obtain ⟨EFG, hE_EFG, hF_EFG⟩ := Postulate1 E F hFE.symm
  obtain ⟨G, hG_CDG, -, hGFE⟩ := line_circle_beyond hF_in hF_EFG hE_EFG hFE.symm
  -- Then, since the point E is the centre of the circle ABC,
  -- EC is equal to EF. [I. Def. 15]
  have hECF : ‖E C‖ = ‖E F‖ := Definition15 hE_ABC hC_ABC hF_ABC
  -- Again, since the point E is the centre of the circle CDG,
  -- EC is equal to EG.
  have hECG : ‖E C‖ = ‖E G‖ := Definition15 hE_CDG hC_CDG hG_CDG
  -- But EC was proved equal to EF also;
  -- therefore EF is also equal to EG, the less to the greater: which is impossible.
  have hEFG : ‖E F‖ = ‖E G‖ := hECF.symm.trans hECG
  /- F lies between E and G, so EF is the less, as in Euclid's figure. -/
  have hlt : ‖E F‖ < ‖E G‖ := len_lt_of_between (between_symm hGFE)
  rw [hEFG] at hlt
  exact lt_irrefl _ hlt
  -- Therefore the point E is not the centre of the circles ABC, CDG.
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
