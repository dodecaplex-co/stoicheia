import Elements.BookII.Rectangles
import Elements.BookI.Prop31
import Elements.BookI.Prop43
import Elements.BookI.Prop46

namespace Elements.BookII
open Tacit

/-- II.4's reckoning, once the figure is drawn: given Euclid's figure (the square ADEB,
CF and HK through G on the diameter BD), the conclusion follows from I.43, the porism
(`Square.about_diameter`), I.34 and `Parallelogram.about_diameter`. -/
theorem T04reckon {A B C D E F G H K : Point} (hACB : Between A C B) (hsq : Square A D E B)
    (hp : Parallelogram A D E B) (hBGD : Between B G D) (hDFE : Between D F E)
    (hAHD : Between A H D) (hEKB : Between E K B) (hBCGK : Parallelogram B C G K)
    (hGHDF : Parallelogram G H D F) :
    sq A B = sq A C + sq C B + (rect A C C B + rect A C C B) := by
  have hBADE : Parallelogram B A D E := hp.rotate.rotate.rotate
  have hsqB : Square B A D E := hsq.rotate.rotate.rotate
  have hBCA : Between B C A := between_symm hACB
  -- CGKB and HF are squares: the parallelograms about the diameter of a square
  have hCK : Square B C G K := hsqB.about_diameter hBADE hBGD hBCA (between_symm hEKB) hBCGK
  have hHF : Square D F G H :=
    hsq.rotate.about_diameter hp.rotate (between_symm hBGD) hDFE (between_symm hAHD)
      hGHDF.rotate.rotate
  -- the four areas are the whole
  have hwhole := hBADE.about_diameter hBGD hBCA hAHD hDFE hEKB hBCGK hGHDF
  -- AG is equal to GE [I. 43]
  have h43 := BookI.Prop43 hBADE hBGD hBCA hAHD hDFE hEKB hBCGK hGHDF
  obtain ⟨hCAHG, -⟩ := hBADE.complements hBGD hBCA hAHD hDFE hEKB hBCGK hGHDF
  -- the squares HF, CK are the squares on AC, CB
  have hsq₁ : quadArea B C G K = sq C B := (hCK.eq_sq hBCGK).trans (sq_symm B C)
  have hsq₂ : quadArea G H D F = sq A C := by
    rw [← quadArea_rotate₂ G H D F, hHF.eq_sq hGHDF.rotate.rotate]
    obtain ⟨-, hCA_GH, -, -, -⟩ := BookI.Prop34 (A := C) (B := G) (C := A) (D := H) hCAHG
    exact sq_congr ((hHF.1.trans hHF.2.1).trans (hCA_GH.symm.trans (len_symm C A)))
  -- AG is the rectangle AC, CB, for GC is equal to CB
  have hAG : quadArea C A H G = rect A C C B := by
    obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B (ne_of_between_ends hACB)
    have hG_AB : ¬ OnLine G AB := fun hG =>
      (hBCGK.triangle).off_line hB_AB (on_line_of_between_ends hACB hA_AB hB_AB) hG
    have hright : ∠ G C A = ∟ := by
      have h := hCK.2.2.2.2.1
      rw [adjacent_eq_of_right hB_AB hA_AB hBCA hG_AB h] at h
      exact h
    refine (Rectangle.of_right hCAHG hright).eq_rect (len_symm C A) ?_
    exact hCK.1.symm.trans (len_symm B C)
  rw [sq_congr hsq.len_eq, ← hsq.eq_sq hp, hBADE.quadArea_rotate, hwhole, hsq₁, hsq₂, ← h43, hAG]
  ac_rfl

/-- II.4 in full: the square [I. 46], the figure [I. 31], the reckoning. -/
theorem T04 {A B C : Point} (hACB : Between A C B) :
    sq A B = sq A C + sq C B + (rect A C C B + rect A C C B) := by
  have hAB : A ≠ B := ne_of_between_ends hACB
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  obtain ⟨D, E, hsq, hD, hE⟩ := BookI.Prop46 hAB hP
  obtain ⟨hp, -⟩ := Square.described hsq hD hE
  obtain ⟨F, G, H, K, hBGD, hDFE, hAHD, hEKB, -, -, hBCGK, hGHDF⟩ := hp.figure hACB
  exact T04reckon hACB hsq hp hBGD hDFE hAHD hEKB hBCGK hGHDF

end Elements.BookII
