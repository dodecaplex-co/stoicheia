import Elements.Figure.Basics
import Elements.BookI.Prop01

/-!
# Book I, Proposition 2

Euclid's text, in Heath's translation: [`heath/I/02.md`](../../heath/I/02.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- To place at a given point (as an extremity) a straight line equal to a given straight
line. -/
theorem Prop2 (A B C : Point) (hBC : B ≠ C) :
    ∃ L : Point, ‖A L‖ = ‖B C‖ := by
  /- If the given point A is B itself, BC already does the job. Euclid's figure
     has A apart from B, and that is the case his proof treats. -/
  by_cases hAB' : A = B
  · exact ⟨C, by rw [hAB']⟩
  have hAB : A ≠ B := hAB'
  -- Let A be the given point, and BC the given straight line.
  -- Thus it is required to place at the point A (as an extremity) a straight line equal to
  -- the given straight line BC.
  -- From the point A to the point B let the straight line AB be joined; [Post. 1]
  -- and on it let the equilateral triangle DAB be constructed. [I. 1]
  /- Either side of AB will do, so no side is named: the point given for a side
     is A itself, which is on AB. -/
  obtain ⟨D, ⟨hABD, -, hBD_DA⟩, -⟩ := Prop1 A B hAB A
  have hDA_DB : ‖D A‖ = ‖D B‖ := hBD_DA.symm.trans (len_symm B D)
  have hDB : D ≠ B := hABD.ne₂₃.symm
  have hDA : D ≠ A := hABD.ne₁₃.symm
  -- Let the straight lines AE, BF be produced in a straight line with DA, DB; [Post. 2]
  obtain ⟨DF, hD_DF, hB_DF⟩ := Postulate1 D B hDB
  obtain ⟨DE, hD_DE, hA_DE⟩ := Postulate1 D A hDA
  -- with centre B and distance BC let the circle CGH be described; [Post. 3]
  obtain ⟨CGH, hB_CGH, hC_CGH⟩ := Postulate3 B C hBC
  /- Euclid's point G is where DB, produced beyond B, meets the circle CGH
     (System E, Intersections 5): B is the centre, so it lies inside. -/
  obtain ⟨G, hG_CGH, -, hGBD⟩ :=
    line_circle_beyond (centre_inside hB_CGH) hB_DF hD_DF hDB
  have hDBG : Between D B G := between_symm hGBD
  have hDG : D ≠ G := ne_of_between_ends hDBG
  -- and again, with centre D and distance DG let the circle GKL be described. [Post. 3]
  obtain ⟨GKL, hD_GKL, hG_GKL⟩ := Postulate3 D G hDG
  /- And L is where DA, produced beyond A, meets the circle GKL. That needs A
     inside GKL, which holds because DA is equal to DB, and DB is only a part
     of DG. -/
  have hDB_BG : ‖D B‖ + ‖B G‖ = ‖D G‖ := len_add_of_between hDBG
  have hA_GKL : InsideCircle A GKL := by
    apply inside_of_len_lt hD_GKL hG_GKL
    rw [hDA_DB, ← hDB_BG]
    exact CommonNotion5 (len_pos (ne_of_between hGBD).symm)
  obtain ⟨L, hL_GKL, -, hLAD⟩ := line_circle_beyond hA_GKL hA_DE hD_DE hDA
  -- Then, since the point B is the centre of the circle CGH,
  -- BC is equal to BG.
  have hBC_BG : ‖B C‖ = ‖B G‖ := Definition15 hB_CGH hC_CGH hG_CGH
  -- Again, since the point D is the centre of the circle GKL,
  -- DL is equal to DG.
  have hDL_DG : ‖D L‖ = ‖D G‖ := Definition15 hD_GKL hL_GKL hG_GKL
  -- And in these DA is equal to DB;
  have hDA_AL : ‖D A‖ + ‖A L‖ = ‖D L‖ := len_add_of_between (between_symm hLAD)
  -- therefore the remainder AL is equal to the remainder BG. [C.N. 3]
  have hAL_BG : ‖A L‖ = ‖B G‖ := by
    apply CommonNotion3 (c := ‖D A‖) (d := ‖D B‖) _ hDA_DB
    rw [add_comm, hDA_AL, hDL_DG, ← hDB_BG, add_comm]
  -- But BC was also proved equal to BG;
  -- therefore each of the straight lines AL, BC is equal to BG.
  -- And things which are equal to the same thing are also equal to one another; [C.N. 1]
  -- therefore AL is also equal to BC.
  have hAL_BC : ‖A L‖ = ‖B C‖ := CommonNotion1 hAL_BG hBC_BG
  -- Therefore at the given point A the straight line AL is placed equal to the given straight
  -- line BC.
  exact ⟨L, hAL_BC⟩
  -- (Being) what it was required to do.

end Elements.BookI
