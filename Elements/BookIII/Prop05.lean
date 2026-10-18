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
theorem Prop5 {E : Point} {ABC CDG : Circle} (hne : ABC ≠ CDG) (hcut : CirclesMeet ABC CDG) :
    ¬ (Centre E ABC ∧ Centre E CDG) := by
  -- For let the circles ABC, CDG cut one another at the points B, C;
  obtain ⟨B, C, -, -, -, hC_ABC, hC_CDG⟩ := hcut
  -- I say that they will not have the same centre.
  -- For, if possible, let it be E; let EC be joined, and let EFG be drawn through at random.
  rintro ⟨hE_ABC, hE_CDG⟩
  /- EC is drawn for the eye; our proof uses only its ends. An unlettered point
     chooses the direction of EFG, which meets both circles beyond E. -/
  obtain ⟨P, hP⟩ := exists_point [E]
  have hPE : P ≠ E := fun h => hP (h ▸ List.mem_singleton_self P)
  obtain ⟨EFG, hE_EFG, hP_EFG⟩ := Postulate1 E P hPE.symm
  obtain ⟨F, hF_ABC, hF_EFG, hFEP⟩ :=
    line_circle_beyond (centre_inside hE_ABC) hE_EFG hP_EFG hPE
  obtain ⟨G, hG_CDG, hG_EFG, hGEP⟩ :=
    line_circle_beyond (centre_inside hE_CDG) hE_EFG hP_EFG hPE
  -- Then, since the point E is the centre of the circle ABC,
  -- EC is equal to EF. [I. Def. 15]
  have hECF : ‖E C‖ = ‖E F‖ := Definition15 hE_ABC hC_ABC hF_ABC
  -- Again, since the point E is the centre of the circle CDG,
  -- EC is equal to EG.
  have hECG : ‖E C‖ = ‖E G‖ := Definition15 hE_CDG hC_CDG hG_CDG
  -- But EC was proved equal to EF also;
  -- therefore EF is also equal to EG, the less to the greater: which is impossible.
  have hEFG : ‖E F‖ = ‖E G‖ := hECF.symm.trans hECG
  /- That F and G are two points is the step Euclid leaves tacit. Were they one, the
     circles ABC and CDG, about the one centre E, would pass through one point, and a
     centre and a radius fix a circle (`circle_eq`, System E, Diagram-segment 2): they
     would be one circle, and they are two. -/
  have hFG : F ≠ G := by
    rintro rfl
    exact hne (circle_eq hE_ABC hE_CDG hF_ABC hG_CDG rfl)
  /- F and G both lie beyond E from the unlettered point, so E is not between them, and
     one of them lies between E and the other. Euclid's figure has F the nearer; we take
     either order, and the nearer makes the less equal to the greater. -/
  have hnot : ¬ Between F E G :=
    not_between_of_between_between (between_symm hFEP) (between_symm hGEP)
  rcases between_cases (ne_of_between hFEP).symm hFG (ne_of_between hGEP).symm
      hE_EFG hF_EFG hG_EFG with h | h | h
  · have hlt : ‖E F‖ < ‖E G‖ := len_lt_of_between h
    rw [hEFG] at hlt
    exact lt_irrefl _ hlt
  · exact hnot h
  · have hlt : ‖E G‖ < ‖E F‖ := len_lt_of_between h
    rw [hEFG] at hlt
    exact lt_irrefl _ hlt
  -- Therefore the point E is not the centre of the circles ABC, CDG.
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
