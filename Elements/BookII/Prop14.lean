import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop04
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop28
import Elements.BookI.Prop29
import Elements.BookI.Prop34
import Elements.BookI.Prop45
import Elements.BookI.Prop46
import Elements.BookI.Prop47
import Elements.BookII.Prop05

/-!
# Book II, Proposition 14

Euclid's text, in Heath's translation: [`heath/II/14.md`](../../heath/II/14.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- To construct a square equal to a given rectilineal figure. -/
theorem Prop14 {A₁ A₂ A₃ A₄ : Point} (h₁ : Triangle A₁ A₂ A₄) (h₂ : Triangle A₄ A₂ A₃) :
    ∃ E H : Point, sq E H = △ A₁ A₂ A₄ + △ A₄ A₂ A₃ := by
  -- Let A be the given rectilineal figure;
  -- thus it is required to construct a square equal to the rectilineal figure A.
  -- For let there be constructed the rectangular parallelogram BD equal to the rectilineal
  -- figure A. [I. 45]
  /- I.45 takes a given angle; I.11 supplies a right one. -/
  obtain ⟨L, hA₁, hA₂⟩ := Postulate1 A₁ A₂ h₁.ne₁₂
  obtain ⟨R, hR, hright⟩ := BookI.Prop11 h₁.ne₁₂ ⟨L, hA₁, hA₂, hA₁⟩ h₁
  have hR' : ∠ A₂ A₁ R = ∟ := hright A₂ ⟨L, hA₁, hA₂, hA₂⟩ h₁.ne₁₂.symm
  obtain ⟨E, B, C, D, hp, hang, hBD⟩ := BookI.Prop45 h₁ h₂ hR.triangle.bac
  have hrect : Rectangle E B C D := by
    refine Rectangle.of_right hp ?_
    rw [angle_symm hp.2.2.1 hp.1.1.symm, hang, hR']
  -- Then, if BE is equal to ED, that which was enjoined will have been done; for a square BD
  -- has been constructed equal to the rectilineal figure A.
  by_cases heq : ‖B E‖ = ‖E D‖
  · exact ⟨E, B, by
      rw [← hBD, hrect.eq_rect rfl ((len_symm E B).trans heq).symm]
      rfl⟩
  -- But, if not, one of the straight lines BE, ED is greater.
  have hlt : ‖E D‖ < ‖E B‖ ∨ ‖E B‖ < ‖E D‖ := by
    rcases lt_trichotomy ‖E D‖ ‖E B‖ with h | h | h
    · exact Or.inl h
    · exact False.elim (heq ((len_symm B E).trans h.symm))
    · exact Or.inr h
  /- Euclid's case is written once. If ED is greater, read the rectangle the
     other way round. The order B, G, E, F then remains that of II.5. -/
  have greater : ∀ {E B C D : Point}, Rectangle E B C D →
      quadArea E B C D = △ A₁ A₂ A₄ + △ A₄ A₂ A₃ → ‖E D‖ < ‖E B‖ →
      ∃ E H : Point, sq E H = △ A₁ A₂ A₄ + △ A₄ A₂ A₃ := by
    intro E B C D h hBD hlt
    -- Let BE be greater, and let it be produced to F;
    have hEB : E ≠ B := h.1.1.1
    have hDE : D ≠ E := h.1.2.2.1
    obtain ⟨X, hBEX⟩ := produce hEB.symm
    -- let EF be made equal to ED, and let BF be bisected at G.
    obtain ⟨F, hF, hEF⟩ :=
      OnRay.exists_len_eq hDE.symm (ne_of_between (between_symm hBEX)).symm
    have hBEF : Between B E F := hF.between hBEX
    obtain ⟨G, hBGF, hBG⟩ := BookI.Prop10 (ne_of_between_ends hBEF)
    -- With centre G and distance one of the straight lines GB, GF let the semicircle BHF be
    -- described; let DE be produced to H, and let GH be joined.
    obtain ⟨BHF, hG_BHF, hB_BHF⟩ := Postulate3 G B (ne_of_between hBGF).symm
    have hF_BHF : OnCircle F BHF :=
      on_circle_of_len_eq hG_BHF hB_BHF (by rw [← hBG, len_symm G B])
    have hlt' : ‖E F‖ < ‖B E‖ := by rw [hEF, len_symm B E]; exact hlt
    /- G lies between B and E because BE is greater than EF, so E lies between
       the centre G and F and is within the circle by Definition I.15. -/
    have hBGE : Between B G E := by
      have hBF : ‖B F‖ = ‖B G‖ + ‖B G‖ := by
        rw [← len_add_of_between hBGF, ← hBG]
      have hBF' : ‖B F‖ = ‖B E‖ + ‖E F‖ := (len_add_of_between hBEF).symm
      refine OnRay.between_of_len_lt (OnRay.of_between hBGF) (OnRay.of_between hBEF) ?_
      rcases lt_trichotomy ‖B G‖ ‖B E‖ with h' | h' | h'
      · exact h'
      · exfalso
        rw [h', hBF'] at hBF
        have : ‖E F‖ = ‖B E‖ := CommonNotion3 (by rw [add_comm]; exact hBF) rfl
        exact lt_irrefl _ (this ▸ hlt')
      · exfalso
        have := Magnitude.add_self_lt_add_self h'
        rw [← hBF, hBF'] at this
        exact lt_irrefl _ (lt_trans hlt' (Magnitude.lt_of_add_lt_add_left this))
    have hE_BHF : InsideCircle E BHF :=
      InsideCircle.of_between_centre hG_BHF hF_BHF (between_inner hBGE hBEF)
    obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDE
    obtain ⟨H, hH_BHF, hH_DE, hHED⟩ := line_circle_beyond hE_BHF hE_DE hD_DE hDE
    /- H lies beyond E from D, on the semicircle away from the rectangle.
       GH is the side of the triangle used below. -/
    -- Then, since the straight line BF has been cut into equal segments at G, and into unequal
    -- segments at E,
    have hEG : E ≠ G := ne_of_between (between_symm hBGE)
    -- the rectangle contained by BE, EF together with the square on EG is equal to the square on
    -- GF. [II. 5]
    have h5 : rect B E E F + sq G E = sq G F := Prop5 hBGF hBG hBEF hEG
    -- But GF is equal to GH;
    have hGF_GH : ‖G F‖ = ‖G H‖ := Definition15 hG_BHF hF_BHF hH_BHF
    -- therefore the rectangle BE, EF together with the square on GE is equal to the square on
    -- GH.
    have hsum : rect B E E F + sq G E = sq G H := h5.trans (sq_congr hGF_GH)
    -- But the squares on HE, EG are equal to the square on GH; [I. 47]
    obtain ⟨BF, hB_BF, hF_BF⟩ := Postulate1 B F (ne_of_between_ends hBEF)
    have hE_BF : OnLine E BF := on_line_of_between_ends hBEF hB_BF hF_BF
    have hG_BF : OnLine G BF := on_line_of_between_ends hBGF hB_BF hF_BF
    have hDEB : Triangle D E B := h.1.rotate.rotate.rotate.triangle
    have hD_BF : ¬ OnLine D BF := hDEB.bca.off_line hE_BF hB_BF
    have hHE : H ≠ E := ne_of_between hHED
    have hH_BF : ¬ OnLine H BF := fun hH =>
      hD_BF ((line_unique hHE hH_DE hE_DE hH hE_BF) ▸ hD_DE)
    /- The angle HEG is right: it is the angle HEB, beside the rectangle's right angle
       DEB, and G lies on EB. -/
    have hBEH : ∠ B E H = ∟ := by
      rw [← adjacent_eq_of_right hD_DE hH_DE (between_symm hHED)
        (hDEB.off_line hD_DE hE_DE) h.2.1]
      exact h.2.1
    have hHEG : ∠ H E G = ∟ := by
      rw [angle_symm hHE (Ne.symm hEG),
        angle_onRay_left (OnRay.of_between (between_symm hBGE)) hHE]
      exact hBEH
    have h47 := BookI.Prop47.sq (Triangle.of_line hE_BF hG_BF hEG hH_BF).acb hHEG
    -- therefore the rectangle BE, EF together with the square on GE is equal to the squares on
    -- HE, EG.
    have hequal : rect B E E F + sq G E = sq H E + sq E G :=
      hsum.trans ((sq_symm G H).trans h47)
    -- Let the square on GE be subtracted from each;
    have hrem : rect B E E F = sq H E := CommonNotion3 hequal (sq_symm G E)
    -- therefore the rectangle contained by BE, EF which remains is equal to the square on EH.
    have hEH : rect B E E F = sq E H := hrem.trans (sq_symm H E)
    -- But the rectangle BE, EF is BD, for EF is equal to ED;
    have hrectangle : quadArea E B C D = rect B E E F :=
      h.eq_rect (len_symm E B) hEF.symm
    -- therefore the parallelogram BD is equal to the square on HE.
    have hBD_HE : quadArea E B C D = sq H E :=
      hrectangle.trans (hEH.trans (sq_symm E H))
    -- And BD is equal to the rectilineal figure A.
    have hBD_A : quadArea E B C D = △ A₁ A₂ A₄ + △ A₄ A₂ A₃ := hBD
    -- Therefore the rectilineal figure A is also equal to the square which can be described on
    -- EH.
    have hA_EH : △ A₁ A₂ A₄ + △ A₄ A₂ A₃ = sq E H :=
      hBD_A.symm.trans (hBD_HE.trans (sq_symm H E))
    -- Therefore a square, namely that which can be described on EH, has been constructed equal
    -- to the given rectilineal figure A.
    exact ⟨E, H, hA_EH.symm⟩
    -- Q. E. F.
  rcases hlt with h | h
  · exact greater hrect hBD h
  · exact greater hrect.reverse ((quadArea_reverse E B C D).trans hBD) h

end Elements.BookII
