import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop04
import Elements.BookI.Prop05
import Elements.BookI.Prop06
import Elements.BookI.Prop28
import Elements.BookI.Prop29
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop43
import Elements.BookI.Prop46
import Elements.BookI.HelpersParallels

/-!
# Book II, Proposition 7

Euclid's text, in Heath's translation: [`heath/II/07.md`](../../heath/II/07.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut at random, the square on the whole and that on one of the segments
both together are equal to twice the rectangle contained by the whole and the said segment and
the square on the remaining segment. -/
theorem Prop7 {A B C : Point} (hACB : Between A C B) :
    sq A B + sq B C = rect A B B C + rect A B B C + sq C A := by
  -- For let a straight line AB be cut at random at the point C;
  have hAB : A ≠ B := ne_of_between_ends hACB
  -- I say that the squares on AB, BC are equal to twice the rectangle contained by AB, BC and
  -- the square on CA.
  -- For let the square ADEB be described on AB, [I. 46]
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  obtain ⟨D, E, hsq, hD, hE⟩ := BookI.Prop46 hAB hP
  obtain ⟨hp, hADEB⟩ := Square.described hsq hD hE
  -- and let the figure be drawn.
  obtain ⟨N, G, H, F, hBGD, hDNE, hAHD, hEFB, hCGN, hHGF, hBCGF, hGHDN⟩ := hp.figure hACB
  have hBADE : Parallelogram B A D E := hp.rotate.rotate.rotate
  obtain ⟨hCAHG, hFGNE⟩ :=
    hBADE.complements hBGD (between_symm hACB) hAHD hDNE hEFB hBCGF hGHDN
  -- Then, since AG is equal to GE, [I. 43]
  have h43 : quadArea C A H G = quadArea F G N E :=
    BookI.Prop43 hBADE hBGD (between_symm hACB) hAHD hDNE hEFB hBCGF hGHDN
  -- let CF be added to each;
  have hadd : quadArea C A H G + quadArea B C G F =
      quadArea F G N E + quadArea B C G F := CommonNotion2 h43 rfl
  -- therefore the whole AF is equal to the whole CE.
  have hAFparts : quadArea A H F B = quadArea C A H G + quadArea B C G F := by
    rw [quadArea_add_of_parallelograms hCAHG.rotate hBCGF.rotate hACB hHGF,
      hCAHG.quadArea_rotate, hBCGF.quadArea_rotate]
  have hCEparts : quadArea B C N E = quadArea B C G F + quadArea F G N E :=
    quadArea_add_of_parallelograms hBCGF hFGNE (between_symm hEFB) hCGN
  have hAFCE : quadArea A H F B = quadArea B C N E := by
    rw [hAFparts, hadd, hCEparts]
    ac_rfl
  -- Therefore AF, CE are double of AF.
  have hdouble : quadArea A H F B + quadArea B C N E =
      quadArea A H F B + quadArea A H F B := by rw [← hAFCE]
  -- But AF, CE are the gnomon KLM and the square CF;
  let gnomon : Area := quadArea C A H G + quadArea B C G F + quadArea F G N E
  have hpieces : quadArea A H F B + quadArea B C N E = gnomon + quadArea B C G F := by
    rw [hAFparts, hCEparts]
    dsimp [gnomon]
    ac_rfl
  -- therefore the gnomon KLM and the square CF are double of AF.
  have hgnomonDouble : gnomon + quadArea B C G F =
      quadArea A H F B + quadArea A H F B := hpieces.symm.trans hdouble
  -- But twice the rectangle AB, BC is also double of AF; for BF is equal to BC;
  have hCF : Square B C G F :=
    hsq.rotate.rotate.rotate.about_diameter hBADE hBGD (between_symm hACB)
      (between_symm hEFB) hBCGF
  have hBF : ‖B F‖ = ‖B C‖ := hCF.len_eq
  /- AF has the same parallels as the pieces and the right angle at B of ADEB. -/
  have hBAHF : Parallelogram B A H F := by
    constructor
    · refine ⟨hAB.symm, ne_of_between_ends hHGF, ?_⟩
      intro L M hB hA hH hF
      exact hBCGF.1.2.2 L M hB (on_line_of_between_ends hACB hA hB)
        (on_line_of_between_ends hHGF hH hF) hF
    · refine ⟨ne_of_between hAHD, (ne_of_between (between_symm hEFB)).symm, ?_⟩
      intro L M hA hH hF hB
      exact hp.1.2.2 L M hA (on_line_of_between hAHD hA hH)
        (on_line_of_between (between_symm hEFB) hB hF) hB
  have hAF : quadArea A H F B = rect A B B C := by
    rw [hBAHF.quadArea_rotate]
    refine (Rectangle.of_right hBAHF ?_).eq_rect (len_symm B A) hBF
    rw [angle_onRay_left (OnRay.of_between (between_symm hEFB)) hAB]
    exact hsq.2.2.2.2.2.2
  have hrectDouble : rect A B B C + rect A B B C =
      quadArea A H F B + quadArea A H F B := by rw [hAF]
  -- therefore the gnomon KLM and the square CF are equal to twice the rectangle AB, BC.
  have hgnomon : gnomon + quadArea B C G F = rect A B B C + rect A B B C :=
    hgnomonDouble.trans hrectDouble.symm
  -- Let DG, which is the square on AC, be added to each;
  have hDG : Square D N G H :=
    hsq.rotate.about_diameter hp.rotate (between_symm hBGD) hDNE (between_symm hAHD)
      hGHDN.rotate.rotate
  have hDGsq : quadArea G H D N = sq A C := by
    rw [← quadArea_rotate₂ G H D N, hDG.eq_sq hGHDN.rotate.rotate]
    obtain ⟨-, hCA_GH, -, -, -⟩ :=
      BookI.Prop34 (A := C) (B := G) (C := A) (D := H) hCAHG
    exact sq_congr ((hDG.1.trans hDG.2.1).trans (hCA_GH.symm.trans (len_symm C A)))
  have hadded := CommonNotion2 hgnomon hDGsq
  -- therefore the gnomon KLM and the squares BG, GD are equal to twice the rectangle contained
  -- by AB, BC and the square on AC.
  have hsum : gnomon + (quadArea B C G F + quadArea G H D N) =
      rect A B B C + rect A B B C + sq A C := by
    rw [← add_assoc]
    exact hadded
  -- But the gnomon KLM and the squares BG, GD are the whole ADEB and CF,
  have hwhole := hBADE.about_diameter hBGD (between_symm hACB) hAHD hDNE hEFB hBCGF hGHDN
  have hreassemble : gnomon + (quadArea B C G F + quadArea G H D N) =
      quadArea A D E B + quadArea B C G F := by
    rw [hBADE.quadArea_rotate, hwhole]
    dsimp [gnomon]
    ac_rfl
  -- which are squares described on AB, BC;
  have hCFsq : quadArea B C G F = sq B C := hCF.eq_sq hBCGF
  -- therefore the squares on AB, BC are equal to twice the rectangle contained by AB, BC
  -- together with the square on AC.
  have hresult : sq A B + sq B C = rect A B B C + rect A B B C + sq A C := by
    rw [← hADEB, ← hCFsq, ← hreassemble]
    exact hsum
  -- Therefore etc.
  exact hresult.trans (by rw [sq_symm A C])
  -- Q. E. D.

end Elements.BookII
