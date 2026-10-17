import Elements.Figure.Basics

/-!
# Book I, Proposition 1

Euclid's text, in Heath's translation: [`heath/I/01.md`](../../heath/I/01.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

The statement says a little more than Euclid's: the triangle can be put on
whichever side of AB we please, the side of a given point P. (If P is on
AB, no side is asked for.) Euclid uses this without saying so in I.9, where
the triangle must fall on the side of DE away from A, and in I.11.
-/

namespace Elements.BookI

open Tacit

/-- What Euclid sees in the figure but never says: the point C, being as far
from A and from B as they are from each other, is not on the straight line
AB. So ABC really is a triangle. -/
theorem Prop1.figure {A B C : Point} (hAB : A ≠ B) (hCA : ‖C A‖ = ‖A B‖)
    (hCB : ‖C B‖ = ‖A B‖) : Triangle A B C := by
  rintro ⟨L, hA, hB, hC⟩
  have hne : ‖A B‖ ≠ 0 := len_ne_zero hAB
  have hAC : ‖A C‖ = ‖A B‖ := (len_symm A C).trans hCA
  have hBC : ‖B C‖ = ‖A B‖ := (len_symm B C).trans hCB
  have hCA' : C ≠ A := fun h => hne (by rw [← hCA, h, len_self])
  have hCB' : C ≠ B := fun h => hne (by rw [← hCB, h, len_self])
  /- On one straight line, one of the three points would lie between the other two,
     and then a length would equal itself taken twice. -/
  rcases between_cases hAB hCB'.symm hCA'.symm hA hB hC with h | h | h
  · have := len_add_of_between h
    rw [hBC, hAC] at this
    exact Magnitude.add_self_ne hne this
  · have := len_add_of_between h
    rw [len_symm B A, hAC, hBC] at this
    exact Magnitude.add_self_ne hne this
  · have := len_add_of_between h
    rw [hAC, hCB] at this
    exact Magnitude.add_self_ne hne this

/-- On a given finite straight line to construct an equilateral triangle. -/
theorem Prop1 (A B : Point) (hAB : A ≠ B) (P : Point) :
    ∃ C : Point, Equilateral A B C ∧ (¬ Collinear A B P → SameSideOf C P A B) := by
  -- Let AB be the given finite straight line.
  -- Thus it is required to construct an equilateral triangle on the straight line AB.
  -- With centre A and distance AB let the circle BCD be described; [Post. 3]
  obtain ⟨BCD, hA_BCD, hB_BCD⟩ := Postulate3 A B hAB
  -- again, with centre B and distance BA let the circle ACE be described; [Post. 3]
  obtain ⟨ACE, hB_ACE, hA_ACE⟩ := Postulate3 B A hAB.symm
  -- and from the point C, in which the circles cut one another, to the points A, B let the
  -- straight lines CA, CB be joined. [Post. 1]
  /- Euclid never says why the circles cut one another. Each passes through the
     other's centre, and a centre lies inside its circle, so they must cross
     (System E, Intersection 5). They cross on both sides of AB, so C may
     be taken on whichever side we please: on P's side, when P is off AB
     (System E, Intersections 8). Lean needs only the point C; the straight
     lines CA, CB are drawn for the eye. -/
  have hmeet := circles_meet hB_BCD (centre_inside hA_BCD) (centre_inside hB_ACE) hA_ACE
  obtain ⟨C, hC_BCD, hC_ACE, hside⟩ : ∃ C : Point, OnCircle C BCD ∧ OnCircle C ACE ∧
      (¬ Collinear A B P → SameSideOf C P A B) := by
    by_cases hP : Collinear A B P
    · obtain ⟨C, -, -, hC_BCD, hC_ACE, -⟩ := hmeet
      exact ⟨C, hC_BCD, hC_ACE, fun h => absurd hP h⟩
    · obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
      obtain ⟨C, hC_BCD, hC_ACE, hCP⟩ :=
        circles_meet_same_side hmeet hA_BCD hB_ACE hA_AB hB_AB (Triangle.off_line hP hA_AB hB_AB)
      exact ⟨C, hC_BCD, hC_ACE, fun _ => SameSideOf.of_line hAB hA_AB hB_AB hCP⟩
  -- Now, since the point A is the centre of the circle CDB,
  -- AC is equal to AB. [Def. 15]
  have hAC : ‖A C‖ = ‖A B‖ := Definition15 hA_BCD hC_BCD hB_BCD
  -- Again, since the point B is the centre of the circle CAE,
  -- BC is equal to BA. [Def. 15]
  have hBC : ‖B C‖ = ‖B A‖ := Definition15 hB_ACE hC_ACE hA_ACE
  -- But CA was also proved equal to AB;
  have hCA : ‖C A‖ = ‖A B‖ := (len_symm C A).trans hAC
  -- therefore each of the straight lines CA, CB is equal to AB.
  have hCB : ‖C B‖ = ‖A B‖ := (len_symm C B).trans (hBC.trans (len_symm B A))
  -- And things which are equal to the same thing are also equal to one another; [C.N. 1]
  -- therefore CA is also equal to CB.
  have hCA_CB : ‖C A‖ = ‖C B‖ := CommonNotion1 hCA hCB
  -- Therefore the three straight lines CA, AB, BC are equal to one another.
  have hAB_BC : ‖A B‖ = ‖B C‖ := (hBC.trans (len_symm B A)).symm
  have hBC_CA : ‖B C‖ = ‖C A‖ := (len_symm B C).trans (hCA_CB.symm)
  -- Therefore the triangle ABC is equilateral; and it has been constructed on the given finite
  -- straight line AB.
  exact ⟨C, ⟨Prop1.figure hAB hCA hCB, hAB_BC, hBC_CA⟩, hside⟩
  -- (Being) what it was required to do.

end Elements.BookI
