import Elements.BookII.Rectangles
import Elements.BookI.Prop31
import Elements.BookI.Prop36
import Elements.BookI.Prop43
import Elements.BookI.Prop46

namespace Elements.BookII
open Tacit

/-- II.5: the case split for D on either side of C, and the first steps of Euclid's
figure in his letters. -/
theorem T05 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖) (hADB : Between A D B)
    (hDC : D ≠ C) :
    rect A D D B + sq C D = sq C B := by
  /- Euclid's case: `D` between `C` and `B`. -/
  have euclid : ∀ {A B C D : Point}, Between A C B → ‖A C‖ = ‖C B‖ → Between C D B →
      rect A D D B + sq C D = sq C B := by
    intro A B C D hACB hAC hCDB
    have hCB : C ≠ B := ne_of_between_ends hCDB
    -- For let the square CEFB be described on CB, [I. 46]
    obtain ⟨P, hP, -⟩ := exists_off_line hCB []
    obtain ⟨E, F, hsq, hE, hF⟩ := BookI.Prop46 hCB hP
    obtain ⟨hp, hCEFB⟩ := Square.described hsq hE hF
    -- and let BE be joined; through D let DG be drawn parallel to either CE or BF, through H
    -- again let KM be drawn parallel to either AB or EF,
    obtain ⟨G, H, L, M, hBHE, hEGF, hCLE, hFMB, hDHG, hLHM, hDBMH, hHLEG⟩ := hp.figure hCDB
    -- the gnomon NOP and LG are the whole square CEFB
    have hwhole := (hp.rotate.rotate.rotate).about_diameter hBHE (between_symm hCDB) hCLE hEGF
      hFMB hDBMH hHLEG
    -- LG is a square, on LH, that is CD
    have hLG : Square E G H L :=
      hsq.rotate.about_diameter hp.rotate (between_symm hBHE) hEGF (between_symm hCLE)
        hHLEG.rotate.rotate
    sorry
  /- Otherwise `D` lies between `A` and `C`: exchange `A` and `B`. -/
  have hCray : OnRay C A B := OnRay.of_between hACB
  have hDray : OnRay D A B := OnRay.of_between hADB
  rcases lt_trichotomy ‖A D‖ ‖A C‖ with h | h | h
  · have hADC : Between A D C := hDray.between_of_len_lt hCray h
    have := euclid (between_symm hACB) (by rw [len_symm B C, len_symm C A]; exact hAC.symm)
      (between_symm hADC)
    rw [rect_comm, rect_congr (len_symm D A) (len_symm B D),
      sq_congr ((len_symm C A).trans hAC)] at this
    exact this
  · obtain ⟨L, hA, hB⟩ := Postulate1 A B (ne_of_between_ends hACB)
    have hDray' : OnRay D A C := ⟨ne_of_between hACB, (ne_of_between hADB).symm,
      ⟨L, hA, on_line_of_between_ends hACB hA hB, on_line_of_between_ends hADB hA hB⟩,
      hDray.not_between hCray⟩
    exact absurd (hDray'.eq_of_len_eq h) hDC
  · exact euclid hACB hAC (between_inner (hCray.between_of_len_lt hDray h) hADB)

end Elements.BookII
