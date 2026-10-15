import Elements.Figure.Basics
import Elements.BookI.Prop13

/-!
# Book I, Proposition 15

Euclid's text, in Heath's translation: [`heath/I/15.md`](../../heath/I/15.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- Two straight lines that cut one another at `E` are two different straight
lines, so an end of one, other than `E`, is off the other. If `E` lies between `A`
and `B` and between `C` and `D`, and `C` is off the straight line `AB`, then `A` is
off `CD` and `D` is off `AB`. That is what I.13 asks when Euclid says that `AE`
"stands on" `CD`, and `DE` on `AB`.

Euclid's figure shows it at a glance. In Lean: a second point that `AB` and `CD`
shared besides `E` would make them one straight line (System E, Generalities 1),
and then `C` would be on `AB`. -/
theorem Prop15.figure {A B C D E : Point} (hAEB : Between A E B) (hCED : Between C E D)
    (hC : ¬ Collinear A B C) : Triangle C D A ∧ Triangle A B D := by
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B (ne_of_between_ends hAEB)
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D (ne_of_between_ends hCED)
  have hE_AB : OnLine E AB := on_line_of_between_ends hAEB hA_AB hB_AB
  have hE_CD : OnLine E CD := on_line_of_between_ends hCED hC_CD hD_CD
  have hC_AB : ¬ OnLine C AB := fun h => hC ⟨AB, hA_AB, hB_AB, h⟩
  /- The two straight lines meet only at `E`. -/
  have only_E : ∀ {P : Point}, P ≠ E → OnLine P AB → ¬ OnLine P CD := fun hPE hP_AB hP_CD =>
    hC_AB (line_unique hPE hP_CD hE_CD hP_AB hE_AB ▸ hC_CD)
  have hA_CD : ¬ OnLine A CD := only_E (ne_of_between hAEB) hA_AB
  have hD_AB : ¬ OnLine D AB := fun hD_AB =>
    only_E (ne_of_between (between_symm hCED)) hD_AB hD_CD
  exact ⟨Triangle.of_line hC_CD hD_CD (ne_of_between_ends hCED) hA_CD,
    Triangle.of_line hA_AB hB_AB (ne_of_between_ends hAEB) hD_AB⟩

/-- If two straight lines cut one another, they make the vertical angles equal to one another. -/
theorem Prop15 {A B C D E : Point} (hAEB : Between A E B) (hCED : Between C E D)
    (hC : ¬ Collinear A B C) :
    ∠ A E C = ∠ D E B ∧ ∠ C E B = ∠ A E D := by
  -- For let the straight lines AB, CD cut one another at the point E;
  /- The statement gives `E` between `A` and `B` and between `C` and `D`, with `C`
     off `AB`. That the two straight lines really cross, so that `A` is off `CD` and
     `D` is off `AB`, is what Euclid sees in his figure: `Prop15.figure`. -/
  obtain ⟨hCDA, hABD⟩ := Prop15.figure hAEB hCED hC
  have hA_E : A ≠ E := ne_of_between hAEB
  have hB_E : B ≠ E := ne_of_between (between_symm hAEB)
  have hC_E : C ≠ E := ne_of_between hCED
  have hD_E : D ≠ E := ne_of_between (between_symm hCED)
  -- I say that the angle AEC is equal to the angle DEB,
  -- and the angle CEB to the angle AED.
  -- For, since the straight line AE stands on the straight line CD, making the angles CEA,
  -- AED,
  -- the angles CEA, AED are equal to two right angles. [I. 13]
  have hCEA_AED : ∠ C E A + ∠ A E D = ∟ + ∟ := Prop13 hCED hCDA
  -- Again, since the straight line DE stands on the straight line AB, making the angles AED,
  -- DEB,
  -- the angles AED, DEB are equal to two right angles. [I. 13]
  have hAED_DEB : ∠ A E D + ∠ D E B = ∟ + ∟ := Prop13 hAEB hABD
  -- But the angles CEA, AED were also proved equal to two right angles;
  -- therefore the angles CEA, AED are equal to the angles AED, DEB. [Post. 4 and C.N. 1]
  /- Postulate 4 is already at work inside I.13: its two right angles are `∟ + ∟`,
     where `∟` names the one size that all right angles share. So here only C.N. 1
     is left to cite. -/
  have hsums : ∠ C E A + ∠ A E D = ∠ A E D + ∠ D E B := CommonNotion1 hCEA_AED hAED_DEB
  -- Let the angle AED be subtracted from each;
  -- therefore the remaining angle CEA is equal to the remaining angle BED. [C.N. 3]
  /- The angle `DEB` is the angle `BED`, read the other way round (`angle_symm`). -/
  have hCEA_BED : ∠ C E A = ∠ B E D := by
    apply CommonNotion3 (c := ∠ A E D) (d := ∠ A E D) _ rfl
    rw [hsums, add_comm (∠ A E D), angle_symm hD_E hB_E]
  -- Similarly it can be proved that the angles CEB, DEA are also equal.
  /- Euclid's "similarly": this time `CE` stands on `AB`, making the angles `AEC`,
     `CEB`, which are equal to two right angles [I. 13]; so are the angles `CEA`,
     `AED`, as proved; and the angle `AEC`, which is the angle `CEA`, is subtracted
     from each [C.N. 1, C.N. 3]. -/
  have hAEC_CEB : ∠ A E C + ∠ C E B = ∟ + ∟ := Prop13 hAEB hC
  have hCEB_DEA : ∠ C E B = ∠ D E A := by
    apply CommonNotion3 (c := ∠ A E C) (d := ∠ C E A) _ (angle_symm hA_E hC_E)
    rw [add_comm (∠ C E B), hAEC_CEB, ← hCEA_AED, add_comm (∠ D E A), angle_symm hD_E hA_E]
  -- Therefore etc.
  /- Euclid's angles `CEA` and `BED` are the angles `AEC` and `DEB` of the enunciation,
     and `DEA` is `AED`, each read the other way round. -/
  exact ⟨by rw [angle_symm hA_E hC_E, hCEA_BED, angle_symm hB_E hD_E],
    by rw [hCEB_DEA, angle_symm hD_E hA_E]⟩
  -- Q. E. D.
  -- [PORISM. From this it is manifest that, if two straight lines cut one another, they will
  -- make the angles at the point of section equal to four right angles.]
  /- Heath, after Heiberg, brackets the Porism as probably not Euclid's, and the
     enunciation does not ask for it, so it is not part of `Prop15`. It is proved just
     below all the same, as `Prop15.porism`: the four angles at `E` are the two pairs
     that I.13 has just shown to be equal to two right angles each. -/

/-- The Porism to I.15: if two straight lines cut one another, the four angles at the point
of section, `AEC`, `CEB`, `BED` and `DEA`, are together equal to four right angles. It falls
out of I.13, used twice as in I.15 itself, with C.N. 2 to add the two pairs. -/
theorem Prop15.porism {A B C D E : Point} (hAEB : Between A E B) (hCED : Between C E D)
    (hC : ¬ Collinear A B C) :
    ∠ A E C + ∠ C E B + (∠ B E D + ∠ D E A) = ∟ + ∟ + (∟ + ∟) := by
  obtain ⟨-, hABD⟩ := Prop15.figure hAEB hCED hC
  have hA_E : A ≠ E := ne_of_between hAEB
  have hB_E : B ≠ E := ne_of_between (between_symm hAEB)
  have hD_E : D ≠ E := ne_of_between (between_symm hCED)
  /- `CE` stands on `AB`, and so does `DE` [I. 13]. -/
  have hAEC_CEB : ∠ A E C + ∠ C E B = ∟ + ∟ := Prop13 hAEB hC
  have hBED_DEA : ∠ B E D + ∠ D E A = ∟ + ∟ := by
    rw [add_comm (∠ B E D), angle_symm hD_E hA_E, angle_symm hB_E hD_E]
    exact Prop13 hAEB hABD
  exact CommonNotion2 hAEC_CEB hBED_DEA

end Elements.BookI
