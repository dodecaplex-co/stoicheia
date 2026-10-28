import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop26
import Elements.BookI.Prop29

/-!
# Book I, Proposition 34

Euclid's text, in Heath's translation: [`heath/I/34.md`](../../heath/I/34.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- In parallelogrammic areas the opposite sides and angles are equal to one another, and the
diameter bisects the areas. -/
theorem Prop34 {A B C D : Point} (h : Parallelogram A C D B) :
    ‖A B‖ = ‖C D‖ ∧ ‖A C‖ = ‖B D‖ ∧ ∠ B A C = ∠ C D B ∧ ∠ A B D = ∠ A C D ∧
      △ A B C = △ D C B := by
  -- Let ACDB be a parallelogrammic area, and BC its diameter;
  have hBC : B ≠ C := h.2.symm.triangle.ne₁₃
  -- I say that the opposite sides and angles of the parallelogram ACDB are equal to one
  -- another, and the diameter BC bisects it.
  -- For, since AB is parallel to CD,
  have hpar₁ : AreParallel A B C D := h.2.symm.swap_left
  -- and the straight line BC has fallen upon them,
  have hAD : OppositeSidesOf A D B C := hpar₁.oppositeSidesOf h.sameSideOf.symm
  -- the alternate angles ABC, BCD are equal to one another. [I. 29]
  have hABC_BCD : ∠ A B C = ∠ B C D := Prop29.alternate hpar₁ hAD
  -- Again, since AC is parallel to BD,
  have hpar₂ : AreParallel A C B D := h.1.swap_right
  -- and BC has fallen upon them,
  have hAD_CB : OppositeSidesOf A D C B := hAD.swap
  -- the alternate angles ACB, CBD are equal to one another. [I. 29]
  have hACB_CBD : ∠ A C B = ∠ C B D := Prop29.alternate hpar₂ hAD_CB
  -- Therefore ABC, DCB are two triangles having the two angles ABC, BCA equal to the two
  -- angles DCB, CBD respectively, and one side equal to one side, namely that adjoining the
  -- equal angles and common to both of them, BC;
  have hABC : Triangle A B C := hpar₁.triangle
  have hDCB : Triangle D C B := hpar₁.symm.swap_left.swap_right.triangle
  have hDC : D ≠ C := hpar₁.2.1.symm
  have hAC : A ≠ C := hpar₂.1
  have hB : ∠ A B C = ∠ D C B := hABC_BCD.trans (angle_symm hBC hDC)
  have hC : ∠ B C A = ∠ C B D := (angle_symm hBC hAC).trans hACB_CBD
  -- therefore they will also have the remaining sides equal to the remaining sides
  -- respectively, and the remaining angle to the remaining angle; [I. 26]
  obtain ⟨hAB_DC, hAC_DB, -, hBAC_CDB⟩ :=
    Prop26 hABC hDCB hB hC (Or.inl (len_symm B C))
  -- therefore the side AB is equal to CD,
  have hAB_CD : ‖A B‖ = ‖C D‖ := hAB_DC.trans (len_symm D C)
  -- and AC to BD,
  have hAC_BD : ‖A C‖ = ‖B D‖ := hAC_DB.trans (len_symm D B)
  -- and further the angle BAC is equal to the angle CDB.
  have hBAC : ∠ B A C = ∠ C D B := hBAC_CDB
  -- And, since the angle ABC is equal to the angle BCD,
  -- and the angle CBD to the angle ACB,
  -- the whole angle ABD is equal to the whole angle ACD. [C.N. 2]
  /- BC falls within both angles: C within the angle ABD, and B within the
     angle ACD, as `Parallelogram.sameSideOf` says of the parallelogram named
     from each corner. -/
  have hABD : ∠ A B D = ∠ A B C + ∠ C B D :=
    angle_add_of_within h.rotate.rotate.rotate.sameSideOf h.rotate.rotate.sameSideOf.symm.swap
  have hACD : ∠ A C D = ∠ A C B + ∠ B C D :=
    angle_add_of_within h.sameSideOf.symm.swap h.rotate.sameSideOf
  have hABD_ACD : ∠ A B D = ∠ A C D := by
    rw [hABD, hACD, add_comm (∠ A C B)]
    exact CommonNotion2 hABC_BCD hACB_CBD.symm
  -- And the angle BAC was also proved equal to the angle CDB.
  -- Therefore in parallelogrammic areas the opposite sides and angles are equal to one
  -- another.
  refine ⟨hAB_CD, hAC_BD, hBAC, hABD_ACD, ?_⟩
  -- I say, next, that the diameter also bisects the areas.
  -- For, since AB is equal to CD,
  have hBA_CD : ‖B A‖ = ‖C D‖ := (len_symm B A).trans hAB_CD
  -- and BC is common,
  have hBC_CB : ‖B C‖ = ‖C B‖ := len_symm B C
  -- the two sides AB, BC are equal to the two sides DC, CB respectively;
  -- and the angle ABC is equal to the angle BCD;
  -- therefore the base AC is also equal to DB,
  /- I.4 takes the corner of the given angle first: BAC and CDB, as in I.33. -/
  obtain ⟨hAC_DB', hBAC_CDB_area, -, -⟩ := Prop4 hABC.bac hDCB.bac hBA_CD hBC_CB hB
  -- and the triangle ABC is equal to the triangle DCB. [I. 4]
  have harea : △ A B C = △ D C B := by
    rw [area_bac A B C, hBAC_CDB_area, area_bac C D B]
  -- Therefore the diameter BC bisects the parallelogram ACDB.
  exact harea
  -- Q. E. D.

/-- The diameter bisects the parallelogram, said of its area: the parallelogram
ABCD, measured by its diameter AC, is double the triangle ABC. From I.37 on, Heath's
reference for this halving is I.34 (I.37: "the triangle ABC is half of the
parallelogram EBCA; for the diameter AB bisects it"), and the Lean uses this form of
it in I.37, I.38, I.41, I.44 and I.46, and in Book II's rectangles. To halve by the
other diameter, name the parallelogram from the next corner (`Parallelogram.rotate`)
and turn its area round with `Parallelogram.quadArea_rotate`. [I. 34] -/
theorem Prop34.bisect {A B C D : Point} (h : Parallelogram A B C D) :
    quadArea A B C D = △ A B C + △ A B C := by
  have hhalf : △ B A C = △ D C A :=
    (Prop34 (A := B) (B := A) (C := C) (D := D) h.rotate).2.2.2.2
  unfold quadArea
  rw [area_cba A C D, ← hhalf, ← area_bac A B C]

end Elements.BookI
