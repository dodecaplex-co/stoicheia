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
  /- EC is drawn for the eye; Lean needs only its ends. An unlettered point
     chooses the direction of EFG, which meets both circles beyond E. -/
  obtain ⟨P, hP⟩ := exists_point [E]
  have hPE : P ≠ E := by
    intro hPE
    subst P
    exact hP (List.Mem.head [])
  obtain ⟨EFG, hE_EFG, hP_EFG⟩ := Postulate1 E P hPE.symm
  obtain ⟨F, hF_ABC, -, -⟩ :=
    line_circle_beyond (centre_inside hE_ABC) hE_EFG hP_EFG hPE
  obtain ⟨G, hG_CDG, -, -⟩ :=
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
  /- Euclid sees F before G in the figure. Lean says why the supposed common
     centre cannot be: equal radii about one centre make one circle (System E,
     Diagram-segment 2), whereas ABC and CDG are two. -/
  exact hne (circle_eq hE_ABC hE_CDG hF_ABC hG_CDG hEFG)
  -- Therefore the point E is not the centre of the circles ABC, CDG.
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
