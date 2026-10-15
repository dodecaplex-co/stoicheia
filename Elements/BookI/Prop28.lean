import Elements.Figure.Basics
import Elements.BookI.Prop13
import Elements.BookI.Prop15
import Elements.BookI.Prop27

/-!
# Book I, Proposition 28

Euclid's text, in Heath's translation: [`heath/I/28.md`](../../heath/I/28.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If a straight line falling on two straight lines make the exterior angle equal to the interior
and opposite angle on the same side, or the interior angles on the same side equal to two right
angles, the straight lines will be parallel to one another. -/
theorem Prop28 {A B C D E F G H : Point} (hAGB : Between A G B) (hCHD : Between C H D)
    (hEGH : Between E G H) (hGHF : Between G H F) (hBD : SameSideOf B D E F)
    (h : ∠ E G B = ∠ G H D ∨ ∠ B G H + ∠ G H D = ∟ + ∟) :
    AreParallel A B C D := by
  -- For let the straight line EF falling on the two straight lines AB, CD make the exterior
  -- angle EGB equal to the interior and opposite angle GHD, or the interior angles on the same
  -- side, namely BGH, GHD, equal to two right angles;
  /- `EF` is the straight line `GH`, so `B` and `D` lie on one side of `GH` too
     (`SameSideOf.inner`); and `B`, on one side of it, is off it, which the angles
     below will need. -/
  have hBD_GH : SameSideOf B D G H := hBD.inner hEGH hGHF
  -- I say that AB is parallel to CD.
  rcases h with hext | hint
  -- For, since the angle EGB is equal to the angle GHD,
  · have hEGB_GHD : ∠ E G B = ∠ G H D := hext
    -- while the angle EGB is equal to the angle AGH, [I. 15]
    have hEHB : Triangle E H B := by
      rintro ⟨L, hE, hH, hB⟩
      exact hBD_GH.triangle ⟨L, on_line_of_between_ends hEGH hE hH, hH, hB⟩
    have hEGB_AGH : ∠ E G B = ∠ A G H :=
      (Prop15 hEGH (between_symm hAGB) hEHB).1
    -- the angle AGH is also equal to the angle GHD;
    have hAGH_GHD : ∠ A G H = ∠ G H D := CommonNotion1 hEGB_AGH.symm hEGB_GHD.symm
    -- and they are alternate;
    have hAD : OppositeSidesOf A D G H := hBD_GH.oppositeSidesOf_of_between hAGB
    -- therefore AB is parallel to CD. [I. 27]
    exact Prop27 hAGB hCHD hAD hAGH_GHD
  -- Again, since the angles BGH, GHD are equal to two right angles, and the angles AGH, BGH
  -- are also equal to two right angles, [I. 13]
  · have hABH : Triangle A B H := by
      rintro ⟨L, hA, hB, hH⟩
      exact hBD_GH.triangle ⟨L, on_line_of_between_ends hAGB hA hB, hH, hB⟩
    have htwo : ∠ A G H + ∠ B G H = ∟ + ∟ := by
      rw [angle_symm (ne_of_between (between_symm hAGB)) (ne_of_between hGHF).symm]
      exact Prop13 hAGB hABH
    -- the angles AGH, BGH are equal to the angles BGH, GHD.
    have hsums : ∠ A G H + ∠ B G H = ∠ B G H + ∠ G H D := CommonNotion1 htwo hint
    -- Let the angle BGH be subtracted from each;
    /- Each sum is written with the angle `BGH` last, for Common Notion 3 to take it
       away. -/
    have hsums' : ∠ A G H + ∠ B G H = ∠ G H D + ∠ B G H := hsums.trans (add_comm _ _)
    -- therefore the remaining angle AGH is equal to the remaining angle GHD;
    have hAGH_GHD : ∠ A G H = ∠ G H D := CommonNotion3 hsums' rfl
    -- and they are alternate;
    have hAD : OppositeSidesOf A D G H := hBD_GH.oppositeSidesOf_of_between hAGB
    -- therefore AB is parallel to CD. [I. 27]
    exact Prop27 hAGB hCHD hAD hAGH_GHD
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
