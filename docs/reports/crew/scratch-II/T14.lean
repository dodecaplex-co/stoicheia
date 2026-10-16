import Elements.BookII.Prop05
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop45

namespace Elements.BookII
open Tacit

/-- II.14 in full along Euclid's route, citing I.45, II.5 and I.47. -/
theorem T14 {A₁ A₂ A₃ A₄ : Point} (h₁ : Triangle A₁ A₂ A₄) (h₂ : Triangle A₄ A₂ A₃) :
    ∃ E H : Point, sq E H = △ A₁ A₂ A₄ + △ A₄ A₂ A₃ := by
  /- The main step, for a rectangle `EBCD` whose side `EB` is the greater. -/
  have key : ∀ {E B C D : Point}, Rectangle E B C D → ‖E D‖ < ‖E B‖ →
      ∃ X Y : Point, sq X Y = quadArea E B C D := by
    intro E B C D h hlt
    have hEB : E ≠ B := h.1.1.1
    have hDE : D ≠ E := h.1.2.2.1
    -- Let BE be greater, and let it be produced to F;
    obtain ⟨X, hBEX⟩ := produce hEB.symm
    -- let EF be made equal to ED, and let BF be bisected at G.
    obtain ⟨F, hF, hEF⟩ := OnRay.exists_len_eq hDE.symm (ne_of_between (between_symm hBEX)).symm
    have hBEF : Between B E F := hF.between hBEX
    obtain ⟨G, hBGF, hBG⟩ := BookI.Prop10 (ne_of_between_ends hBEF)
    have hlt' : ‖E F‖ < ‖B E‖ := by rw [hEF, len_symm B E]; exact hlt
    /- `G` lies between `B` and `E`, since `BE` is the greater. -/
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
    have hGE : E ≠ G := ne_of_between (between_symm hBGE)
    -- With centre G and distance one of the straight lines GB, GF let the semicircle BHF be
    -- described; let DE be produced to H, and let GH be joined.
    obtain ⟨α, hGα, hBα⟩ := Postulate3 G B (ne_of_between hBGF).symm
    have hFα : OnCircle F α := on_circle_of_len_eq hGα hBα (by rw [← hBG, len_symm G B])
    have hEα : InsideCircle E α := inside_of_between (Or.inr hBα) (Or.inr hFα) hBEF
    obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDE
    obtain ⟨H, hHα, hH_DE, hHED⟩ := line_circle_beyond hEα hE_DE hD_DE hDE
    -- Then, since the straight line BF has been cut into equal segments at G, and into
    -- unequal segments at E, ... [II. 5]
    have h5 := Prop5 hBGF hBG hBEF hGE
    -- But GF is equal to GH;
    have hGF_GH : ‖G F‖ = ‖G H‖ := Definition15 hGα hFα hHα
    -- But the squares on HE, EG are equal to the square on GH; [I. 47]
    obtain ⟨BF, hB_BF, hF_BF⟩ := Postulate1 B F (ne_of_between_ends hBEF)
    have hE_BF : OnLine E BF := on_line_of_between_ends hBEF hB_BF hF_BF
    have hG_BF : OnLine G BF := on_line_of_between_ends hBGF hB_BF hF_BF
    have hDEB : Triangle D E B := h.1.rotate.rotate.rotate.triangle
    have hD_BF : ¬ OnLine D BF := hDEB.bca.off_line hE_BF hB_BF
    have hHE : H ≠ E := ne_of_between hHED
    have hH_BF : ¬ OnLine H BF := fun hH =>
      hD_BF ((line_unique hHE hH_DE hE_DE hH hE_BF) ▸ hD_DE)
    have hBEH : ∠ B E H = ∟ := by
      rw [← adjacent_eq_of_right hD_DE hH_DE (between_symm hHED) (hDEB.off_line hD_DE hE_DE) h.2.1]
      exact h.2.1
    have hHEG : ∠ H E G = ∟ := by
      rw [angle_symm hHE (Ne.symm hGE), angle_onRay_left (OnRay.of_between (between_symm hBGE)) hHE]
      exact hBEH
    have h47 := BookI.Prop47.sq (Triangle.of_line hE_BF hG_BF hGE hH_BF).acb hHEG
    -- Let the square on GE be subtracted from each;
    -- therefore the rectangle contained by BE, EF which remains is equal to the square on EH.
    have hrem : rect B E E F = sq H E := by
      refine CommonNotion3 (c := sq G E) (d := sq E G) ?_ (sq_symm G E)
      rw [h5, sq_congr hGF_GH, sq_symm G H, h47]
    -- But the rectangle BE, EF is BD, for EF is equal to ED;
    refine ⟨H, E, ?_⟩
    rw [← hrem, h.contained]
    exact rect_congr (len_symm B E) hEF
  -- For let there be constructed the rectangular parallelogram BD equal to the rectilineal
  -- figure A. [I. 45]
  obtain ⟨L, hA₁, hA₂⟩ := Postulate1 A₁ A₂ h₁.ne₁₂
  obtain ⟨R, hR, hright⟩ := BookI.Prop11 h₁.ne₁₂ ⟨L, hA₁, hA₂, hA₁⟩ h₁
  have hR' : ∠ A₂ A₁ R = ∟ := hright A₂ ⟨L, hA₁, hA₂, hA₂⟩ h₁.ne₁₂.symm
  obtain ⟨K, F, M, N, hp, hang, harea⟩ := BookI.Prop45 h₁ h₂ hR.triangle.bac
  have hrect : Rectangle K F M N := by
    refine Rectangle.of_right hp ?_
    rw [angle_symm hp.2.2.1 hp.1.1.symm, hang, hR']
  rw [← harea]
  rcases lt_trichotomy ‖K N‖ ‖K F‖ with h | h | h
  · exact key hrect h
  · exact ⟨K, F, by rw [hrect.contained]; exact rect_congr rfl h.symm⟩
  · obtain ⟨X, Y, hXY⟩ := key hrect.reverse h
    exact ⟨X, Y, hXY.trans (quadArea_reverse K F M N)⟩

end Elements.BookII
