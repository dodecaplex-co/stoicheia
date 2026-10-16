import Elements.Figure.Basics
import Elements.BookI.Prop13
import Elements.BookI.Prop15

/-!
# Book I, Proposition 29

Euclid's text, in Heath's translation: [`heath/I/29.md`](../../heath/I/29.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Here Postulate 5 is used for the first time. Euclid proves that the angle `AGH` is
not greater than the angle `GHD`, and says nothing of the other case, where `GHD` is
the greater. That case is the same argument from `H`'s end of `GH`, on the side of
`A` and `C`, with I.13 at `H`. So the Lean makes the argument once, for any two
parallels and any straight line falling on them, and uses it twice.

After the proposition, `Prop29.alternate`, `Prop29.interior` and `Prop29.exterior`
say it of any straight line falling on two parallels, with Book Zero drawing
Euclid's figure about it; I.30 and the propositions after it cite them.
-/

namespace Elements.BookI

open Tacit

/-- A straight line falling on parallel straight lines makes the alternate angles equal to one
another, the exterior angle equal to the interior and opposite angle, and the interior angles on
the same side equal to two right angles. -/
theorem Prop29 {A B C D E F G H : Point} (hpar : AreParallel A B C D) (hAGB : Between A G B)
    (hCHD : Between C H D) (hEGH : Between E G H) (hGHF : Between G H F)
    (hBD : SameSideOf B D E F) :
    ∠ A G H = ∠ G H D ∧ ∠ E G B = ∠ G H D ∧ ∠ B G H + ∠ G H D = ∟ + ∟ := by
  -- For let the straight line EF fall on the parallel straight lines AB, CD;
  /- It falls on `AB` at `G` and on `CD` at `H`, with `B` and `D` on one side of it, and so
     on one side of `GH`, which is the same straight line (`SameSideOf.inner`). -/
  have hBD_GH : SameSideOf B D G H := hBD.inner hEGH hGHF
  -- I say that it makes the alternate angles AGH, GHD equal, the exterior angle EGB equal to
  -- the interior and opposite angle GHD, and the interior angles on the same side, namely BGH,
  -- GHD, equal to two right angles.
  -- For, if the angle AGH is unequal to the angle GHD, one of them is greater.
  /- Euclid lets the angle `AGH` be the greater and shows that it cannot be. If the angle
     `GHD` is the greater, the same argument runs from `H`'s end: with `D`, `C`, `B`, `A`
     for `A`, `B`, `C`, `D` and `H`, `G` for `G`, `H`, the angles `AGH`, `GHD` change places,
     and `A`, `C` are the two on one side of `GH`. So we give his argument for any two
     parallels and any straight line falling on them, in his letters, and use it twice
     below. -/
  have not_greater : ∀ {A B C D G H : Point}, AreParallel A B C D → Between A G B →
      Between C H D → SameSideOf B D G H → ¬ ∠ G H D < ∠ A G H := by
    intro A B C D G H hpar hAGB hCHD hBD
    obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hpar.1
    obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hpar.2.1
    obtain ⟨GH, hG_GH, hH_GH⟩ := Postulate1 G H hBD.1
    have hG_AB : OnLine G AB := on_line_of_between_ends hAGB hA_AB hB_AB
    have hH_CD : OnLine H CD := on_line_of_between_ends hCHD hC_CD hD_CD
    -- Let the angle AGH be greater.
    intro hGHD_AGH
    -- Let the angle BGH be added to each;
    /- Adding the same thing to both keeps "less than", a tacit law of magnitudes
       (`add_lt_add_right`), as in I.17. -/
    have hadd : ∠ G H D + ∠ B G H < ∠ A G H + ∠ B G H :=
      add_lt_add_right (∠ B G H) hGHD_AGH
    -- therefore the angles AGH, BGH are greater than the angles BGH, GHD.
    have hgreater : ∠ B G H + ∠ G H D < ∠ A G H + ∠ B G H := by
      rw [add_comm (∠ B G H)]
      exact hadd
    -- But the angles AGH, BGH are equal to two right angles; [I. 13]
    /- `GH` stands on `AB` at `G`: `H` is off `AB`, for otherwise `G`, `B` and `H` would
       be on one straight line, and `B` is off `GH`. The angle `HGB` of I.13 is the angle
       `BGH`, read the other way round. -/
    have hABH : Triangle A B H := by
      rintro ⟨L, hA, hB, hH⟩
      exact hBD.triangle.acb ⟨L, on_line_of_between_ends hAGB hA hB, hB, hH⟩
    have hAGH_BGH : ∠ A G H + ∠ B G H = ∟ + ∟ := by
      rw [← angle_symm hBD.1.symm (ne_of_between (between_symm hAGB))]
      exact Prop13 hAGB hABH
    -- therefore the angles BGH, GHD are less than two right angles.
    have hless : ∠ B G H + ∠ G H D < ∟ + ∟ := by
      rw [← hAGH_BGH]
      exact hgreater
    -- But straight lines produced indefinitely from angles less than two right angles
    -- meet; [Post. 5]
    -- therefore AB, CD, if produced indefinitely, will meet;
    /- Postulate 5 asks for what Euclid leaves to the figure: the straight lines `GB` and
       `HD` start from the points where `GH` meets them, and `B` and `D` lie on one side
       of `GH`. It also says on which side they meet, which is not needed here. -/
    have hmeet : ∃ P : Point, OnLine P AB ∧ OnLine P CD :=
      (Postulate5 hB_AB hG_AB hG_GH hH_GH hH_CD hD_CD hBD.1 (hBD.sameSide hG_GH hH_GH)
        hless).imp fun _ h => ⟨h.1, h.2.1⟩
    -- but they do not meet, because they are by hypothesis parallel.
    /- That is Definition 23, said of the straight lines `AB` and `CD`. -/
    exact (hpar.parallel hA_AB hB_AB hC_CD hD_CD).2 hmeet
  -- Therefore the angle AGH is not unequal to the angle GHD,
  /- Neither is the greater. The angle `AGH` is not, by Euclid's argument. Nor is the
     angle `GHD`, by the same argument from `H`'s end: `DC` is parallel to `BA`, `H` lies
     between `D` and `C`, `G` between `B` and `A`, and `C` and `A` lie on one side of
     `HG`. For `A` is across `GH` from `B`, and so from `D`
     (`SameSideOf.oppositeSidesOf_of_between`), and `C` is across it from `D` too
     (`OppositeSidesOf.sameSideOf_of_between`). The angles `HGA`, `DHG` are the angles
     `AGH`, `GHD`, read the other way round. -/
  have hnot_gt : ¬ ∠ G H D < ∠ A G H := not_greater hpar hAGB hCHD hBD_GH
  have hCA : SameSideOf C A H G :=
    (hBD_GH.oppositeSidesOf_of_between hAGB).symm.swap.sameSideOf_of_between
      (between_symm hCHD)
  have hnot_lt : ¬ ∠ A G H < ∠ G H D := by
    rw [angle_symm (ne_of_between hAGB) hBD_GH.1.symm,
      angle_symm hBD_GH.1 (ne_of_between (between_symm hCHD))]
    exact not_greater hpar.symm.swap_left.swap_right (between_symm hCHD) (between_symm hAGB)
      hCA
  -- and is therefore equal to it.
  have hAGH_GHD : ∠ A G H = ∠ G H D :=
    ((lt_trichotomy (∠ A G H) (∠ G H D)).resolve_left hnot_lt).resolve_right hnot_gt
  -- Again, the angle AGH is equal to the angle EGB; [I. 15]
  /- `AB` and `HE` cut one another at `G`, and `H` is off `AB`, as above. -/
  have hABH : Triangle A B H := by
    rintro ⟨L, hA, hB, hH⟩
    exact hBD_GH.triangle.acb ⟨L, on_line_of_between_ends hAGB hA hB, hB, hH⟩
  have hAGH_EGB : ∠ A G H = ∠ E G B := (Prop15 hAGB (between_symm hEGH) hABH).1
  -- therefore the angle EGB is also equal to the angle GHD. [C.N. 1]
  have hEGB_GHD : ∠ E G B = ∠ G H D := CommonNotion1 hAGH_EGB.symm hAGH_GHD.symm
  -- Let the angle BGH be added to each;
  -- therefore the angles EGB, BGH are equal to the angles BGH, GHD. [C.N. 2]
  have hsums : ∠ E G B + ∠ B G H = ∠ B G H + ∠ G H D := by
    rw [add_comm (∠ B G H)]
    exact CommonNotion2 hEGB_GHD rfl
  -- But the angles EGB, BGH are equal to two right angles; [I. 13]
  /- `GB` stands on `EH` at `G`: `B` is off `EH`, which is the straight line `GH`. -/
  have hEHB : Triangle E H B := by
    rintro ⟨L, hE, hH, hB⟩
    exact hBD_GH.triangle ⟨L, on_line_of_between_ends hEGH hE hH, hH, hB⟩
  have hEGB_BGH : ∠ E G B + ∠ B G H = ∟ + ∟ := Prop13 hEGH hEHB
  -- therefore the angles BGH, GHD are also equal to two right angles.
  have hBGH_GHD : ∠ B G H + ∠ G H D = ∟ + ∟ := hsums.symm.trans hEGB_BGH
  -- Therefore etc.
  exact ⟨hAGH_GHD, hEGB_GHD, hBGH_GHD⟩
  -- Q. E. D.

/-! ## I.29 said of any straight line falling on two parallels -/

/-- The alternate angles. If the straight line `PG` is parallel to `HQ`, and `P` and
`Q` lie on opposite sides of `GH`, then the alternate angles `PGH`, `GHQ` are equal.
Book Zero draws Euclid's figure about `GH` (`AreParallel.figure_alternate`), and I.29
does the rest. [I. 29] -/
theorem Prop29.alternate {P G H Q : Point} (hpar : AreParallel P G H Q)
    (hPQ : OppositeSidesOf P Q G H) : ∠ P G H = ∠ G H Q := by
  obtain ⟨B, C, E, F, h₁, h₂, h₃, h₄, hpar', hside⟩ := hpar.figure_alternate hPQ
  exact (Prop29 hpar' h₁ h₂ h₃ h₄ hside).1

/-- The interior angles on the same side. If the straight line `GP` is parallel to
`HQ`, and `P` and `Q` lie on one side of `GH`, then the angles `PGH`, `GHQ` are
equal to two right angles. [I. 29] -/
theorem Prop29.interior {P G H Q : Point} (hpar : AreParallel G P H Q)
    (hPQ : SameSideOf P Q G H) : ∠ P G H + ∠ G H Q = ∟ + ∟ := by
  obtain ⟨A, C, E, F, h₁, h₂, h₃, h₄, hpar', hside⟩ := hpar.figure_interior hPQ
  exact (Prop29 hpar' h₁ h₂ h₃ h₄ hside).2.2

/-- The exterior angle. If the straight line `GP` is parallel to `HQ`, `P` and `Q` lie
on one side of `GH`, and `E` lies on `HG` produced beyond `G`, then the exterior
angle `EGP` is equal to the interior and opposite angle `GHQ`. [I. 29] -/
theorem Prop29.exterior {P G H Q E : Point} (hpar : AreParallel G P H Q)
    (hPQ : SameSideOf P Q G H) (hEGH : Between E G H) : ∠ E G P = ∠ G H Q := by
  obtain ⟨A, C, E', F, h₁, h₂, h₃, h₄, hpar', hside⟩ := hpar.figure_interior hPQ
  have hE : OnRay E G E' := OnRay.of_between_between (between_symm h₃) (between_symm hEGH)
  rw [angle_onRay_left hE hpar.1.symm]
  exact (Prop29 hpar' h₁ h₂ h₃ h₄ hside).2.1

end Elements.BookI
