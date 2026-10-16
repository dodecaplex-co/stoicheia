import Elements.BookII.Prop06
import Elements.BookI.Prop02
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop19
import Elements.BookI.Prop20
import Elements.BookI.Prop31
import Elements.BookI.Prop32
import Elements.BookI.Prop43
import Elements.BookI.Prop46

namespace Elements.BookII
open Tacit

/-- II.1, first steps: the perpendicular BF [I. 11], BG equal to A, the parallels, and
the first rectangle named. -/
theorem T01 {A₁ A₂ B C D E : Point} (hA : A₁ ≠ A₂) (hBDE : Between B D E) (hDEC : Between D E C) :
    rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D E + rect A₁ A₂ E C := by
  have hBDC : Between B D C := between_of_between_right hBDE hDEC
  have hBEC : Between B E C := between_symm (between_of_between_right (between_symm hDEC)
    (between_symm hBDE))
  have hBC : B ≠ C := ne_of_between_ends hBDC
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hBC
  -- For let BF be drawn from B at right angles to BC; [I. 11]
  obtain ⟨Q, hQ, -⟩ := exists_off_line hBC []
  obtain ⟨F, hFQ, hright⟩ := BookI.Prop11 hBC ⟨BC, hB_BC, hC_BC, hB_BC⟩ hQ
  have hCBF : ∠ C B F = ∟ := hright C ⟨BC, hB_BC, hC_BC, hC_BC⟩ hBC.symm
  -- let BG be made equal to A, [I. 3]
  obtain ⟨L, hL⟩ := BookI.Prop2 B A₁ A₂ hA
  have hBL : B ≠ L := ne_of_len_eq hL hA
  obtain ⟨G, hG, hBG⟩ := OnRay.exists_len_eq hBL hFQ.triangle.ne₁₃
  have hBG_A : ‖B G‖ = ‖A₁ A₂‖ := hBG.trans hL
  -- through G let GH be drawn parallel to BC, [I. 31]
  have hGBC : Triangle B C G := (SameSideOf.of_onRay hG hFQ).triangle
  obtain ⟨U, V, hUGV, hUV⟩ := BookI.Prop31 hBC hGBC
  sorry

/-- II.3, first steps: the square CDEB on CB [I. 46], and DB the square on CB. -/
theorem T03 {A B C : Point} (hACB : Between A C B) :
    rect A B B C = rect A C C B + sq B C := by
  have hCB : C ≠ B := (ne_of_between (between_symm hACB)).symm
  obtain ⟨P, hP, -⟩ := exists_off_line hCB []
  -- For let the square CDEB be described on CB; [I. 46]
  obtain ⟨D, E, hsq, hD, hE⟩ := BookI.Prop46 hCB hP
  -- and DB is the square on CB.
  obtain ⟨hp, hDB⟩ := Square.described hsq hD hE
  have : quadArea C D E B = sq B C := hDB.trans (sq_symm C B)
  sorry

/-- II.6, first steps: the square CEFD on CD and the figure in Euclid's letters. -/
theorem T06 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖) (hABD : Between A B D) :
    rect A D D B + sq C B = sq C D := by
  have hCBD : Between C B D := between_inner hACB hABD
  have hCD : C ≠ D := ne_of_between_ends hCBD
  obtain ⟨P, hP, -⟩ := exists_off_line hCD []
  -- For let the square CEFD be described on CD, [I. 46]
  obtain ⟨E, F, hsq, hE, hF⟩ := BookI.Prop46 hCD hP
  obtain ⟨hp, hCEFD⟩ := Square.described hsq hE hF
  -- and let DE be joined; through the point B let BG be drawn parallel to either EC or DF,
  -- through the point H let KM be drawn parallel to either AB or EF,
  obtain ⟨G, H, L, M, hDHE, hEGF, hCLE, hFMD, hBHG, hLHM, hDBHM, hHLEG⟩ := hp.figure hCBD
  -- But CH is equal to HF. [I. 43]
  have h43 := BookI.Prop43 hp.rotate.rotate.rotate hDHE (between_symm hCBD) hCLE hEGF hFMD
    hDBHM hHLEG
  sorry

/-- II.7, first steps: the square ADEB on AB, and "let the figure be drawn". -/
theorem T07 {A B C : Point} (hACB : Between A C B) :
    sq A B + sq B C = rect A B B C + rect A B B C + sq C A := by
  have hAB : A ≠ B := ne_of_between_ends hACB
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  -- For let the square ADEB be described on AB, [I. 46]
  obtain ⟨D, E, hsq, hD, hE⟩ := BookI.Prop46 hAB hP
  obtain ⟨hp, hADEB⟩ := Square.described hsq hD hE
  -- and let the figure be drawn.
  obtain ⟨F, G, H, K, hBGD, hDFE, hAHD, hEKB, hCGF, hHGK, hBCGK, hGHDF⟩ := hp.figure hACB
  -- Then, since AG is equal to GE, [I. 43]
  have h43 := BookI.Prop43 hp.rotate.rotate.rotate hBGD (between_symm hACB) hAHD hDFE hEKB
    hBCGK hGHDF
  sorry

/-- II.8, first steps: BD produced and made equal to CB, the square AEFD on AD, and the
figure drawn double (twice the figure of Book II). -/
theorem T08 {A B C : Point} (hACB : Between A C B) :
    ∀ D : Point, Between A B D → ‖B D‖ = ‖C B‖ →
      rect A B B C + rect A B B C + rect A B B C + rect A B B C + sq A C = sq A D := by
  -- For let [the straight line] BD be produced in a straight line [with AB], and let BD be
  -- made equal to CB;
  intro D hABD hBD
  have hAD : A ≠ D := ne_of_between_ends hABD
  have hACD : Between A C D := between_of_between_left hABD hACB
  obtain ⟨P, hP, -⟩ := exists_off_line hAD []
  -- let the square AEFD be described on AD, and let the figure be drawn double.
  obtain ⟨E, F, hsq, hE, hF⟩ := BookI.Prop46 hAD hP
  obtain ⟨hp, hAEFD⟩ := Square.described hsq hE hF
  obtain ⟨-, K, -, -, hDKE, -, -, -, -, -, -, -⟩ := hp.figure hABD
  obtain ⟨-, H', -, -, hDHE, -, -, -, -, -, -, -⟩ := hp.figure hACD
  sorry

/-- II.9, first steps: CE at right angles to AB and equal to AC, EA and EB joined, and
the angles at A and E half a right angle [I. 32]. -/
theorem T09 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖) (hADB : Between A D B)
    (hDC : D ≠ C) :
    sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D) := by
  have hAB : A ≠ B := ne_of_between_ends hACB
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hC_AB : OnLine C AB := on_line_of_between_ends hACB hA_AB hB_AB
  -- For let CE be drawn from C at right angles to AB, and let it be made equal to either AC
  -- or CB;
  obtain ⟨Q, hQ, -⟩ := exists_off_line hAB []
  obtain ⟨X, hXQ, hright⟩ := BookI.Prop11 hAB ⟨AB, hA_AB, hB_AB, hC_AB⟩ hQ
  have hCX : C ≠ X := fun e => (hXQ.sameSide hA_AB hB_AB |> not_on_line_of_same_side) (e ▸ hC_AB)
  obtain ⟨E, hE, hCE⟩ := OnRay.exists_len_eq (ne_of_between hACB).symm hCX
  have hACE : ∠ A C E = ∟ := by
    rw [angle_onRay_right hE (ne_of_between hACB)]
    exact hright A ⟨AB, hA_AB, hB_AB, hA_AB⟩ (ne_of_between hACB)
  -- Then, since AC is equal to CE, the angle EAC is also equal to the angle AEC.
  sorry

/-- II.11, first steps: the square ABDC on AB [I. 46], AC bisected at E [I. 10], CA drawn
through to F with EF equal to BE, and II.6 cited. -/
theorem T11 {A B : Point} (hAB : A ≠ B) :
    ∃ H : Point, Between A H B ∧ rect A B B H = sq A H := by
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  -- For let the square ABDC be described on AB; [I. 46]
  obtain ⟨C, D, hsq, hC, hD⟩ := BookI.Prop46 hAB hP
  obtain ⟨hp, hABDC⟩ := Square.described hsq hC hD
  -- let AC be bisected at the point E, and let BE be joined;
  obtain ⟨E, hAEC, hAE⟩ := BookI.Prop10 hp.1.1
  -- let CA be drawn through to F, and let EF be made equal to BE;
  obtain ⟨X, hCAX⟩ := produce hp.1.1.symm
  have hEB : E ≠ B := sorry
  have hEX : E ≠ X := sorry
  obtain ⟨F, hF, hEF⟩ := OnRay.exists_len_eq hEB hEX
  have hCAF : Between C A F := sorry -- EF = EB > EA (I.19), so F lies beyond A
  -- the rectangle contained by CF, FA together with the square on AE is equal to the square
  -- on EF. [II. 6]
  have h6 := Prop6 (between_symm hAEC) (by rw [len_symm C E, len_symm E A]; exact hAE.symm) hCAF
  sorry

/-- II.10, first steps: CE at right angles [I. 11] and equal to AC [I. 3], and the
parallels EF, FD [I. 31]. -/
theorem T10 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖)
    (hABD : Between A B D) :
    sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D) := by
  have hAD : A ≠ D := ne_of_between_ends hABD
  obtain ⟨AD, hA_AD, hD_AD⟩ := Postulate1 A D hAD
  have hC_AD : OnLine C AD :=
    on_line_of_between_ends hACB hA_AD (on_line_of_between_ends hABD hA_AD hD_AD)
  have hAC' : A ≠ C := ne_of_between hACB
  -- For let CE be drawn from the point C at right angles to AB [I. 11], and let it be made
  -- equal to either AC or CB [I. 3];
  obtain ⟨Q, hQ, -⟩ := exists_off_line hAD []
  obtain ⟨X, hXQ, hright⟩ := BookI.Prop11 hAD ⟨AD, hA_AD, hD_AD, hC_AD⟩ hQ
  have hX_AD : ¬ OnLine X AD := not_on_line_of_same_side (hXQ.sameSide hA_AD hD_AD)
  have hCX : C ≠ X := fun e => hX_AD (e ▸ hC_AD)
  obtain ⟨E, hE, hCE⟩ := OnRay.exists_len_eq hAC'.symm hCX
  have hE_AD : ¬ OnLine E AD := fun h => by
    obtain ⟨-, hEC, ⟨M, hC_M, hX_M, hE_M⟩, -⟩ := hE
    exact hX_AD ((line_unique hEC.symm hC_M hE_M hC_AD h) ▸ hX_M)
  -- through E let EF be drawn parallel to AD,
  obtain ⟨U, V, hUEV, hUV⟩ := BookI.Prop31 hAD fun ⟨L, hA, hD, hE'⟩ =>
    hE_AD ((line_unique hAD hA hD hA_AD hD_AD) ▸ hE')
  sorry

end Elements.BookII
