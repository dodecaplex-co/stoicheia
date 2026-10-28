import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Feet
import Elements.BookI.Prop03
import Elements.BookI.Prop11
import Elements.BookI.Prop13
import Elements.BookI.Prop17
import Elements.BookI.Prop19
import Elements.BookI.Prop20
import Elements.BookI.Prop24
import Elements.BookIII.Prop02
import Elements.BookIII.Prop14

/-!
# Book III, Proposition 15

Euclid's text, in Heath's translation: [`heath/III/15.md`](../../heath/III/15.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

`Prop15` is Euclid's worked configuration: a diameter AD and two straight lines BC, FG,
neither through the centre, FG the more remote. His enunciation has two clauses, and the
companions after it take each for every straight line in the circle. "The diameter is
greatest" is `Prop15.le_diameter`: no straight line in the circle is greater than the
diameter, and only one through the centre is equal to it, without a more remote straight
line beside it. "Of the rest the nearer to the centre is always greater than the more
remote" is `Prop15.nearer`, with distances measured to the feet of the perpendiculars
(`Foot`), so that the nearer may be a diameter. For two straight lines not through the
centre it is Euclid's argument, by `Prop15` itself; for a diameter, `Prop15.le_diameter`.
-/

namespace Elements.BookIII

open Tacit

/-- This is half of Euclid's "the angle MEN greater than the angle FEG". Where MN cuts EF,
at X, the point X is within the circle and on M's side of EK, so it lies between M and L,
and the angle FEK, which is the angle XEL, is a part of the angle MEL. -/
theorem Prop15.half {E F K L M : Point} {α : Circle} {EK MN : Line}
    (hE : Centre E α) (hF : OnCircle F α) (hM : OnCircle M α)
    (hE_EK : OnLine E EK) (hL_EK : OnLine L EK) (hELK : Between E L K)
    (hL_MN : OnLine L MN) (hM_MN : OnLine M MN) (hE_MN : ¬ OnLine E MN)
    (hL_in : InsideCircle L α) (hEF : OppositeSides E F MN)
    (hMF : SameSide M F EK) (hF_EK : ¬ OnLine F EK) :
    ∠ F E K < ∠ M E L := by
  obtain ⟨X, hX_MN, hEXF⟩ := hEF.exists_between
  have hX_in : InsideCircle X α := InsideCircle.of_between_centre hE hF hEXF
  have hX_EK : ¬ OnLine X EK := fun h => hF_EK (on_line_of_between hEXF hE_EK h)
  have hXF : SameSide X F EK := pasch2 hEXF hE_EK hX_EK
  have hXM : SameSide X M EK := same_side_trans (same_side_symm hXF) (same_side_symm hMF)
  have hMX : M ≠ X := fun e => inside_not_on hX_in (e ▸ hM)
  have hXL : X ≠ L := fun e => hX_EK (e ▸ hL_EK)
  have hML : M ≠ L := fun e => not_on_line_of_same_side hMF (e ▸ hL_EK)
  have hMXL : Between M X L := by
    rcases between_cases hMX hXL hML hM_MN hX_MN hL_MN with h | h | h
    · exact h
    · exact absurd hM (inside_not_on (Prop2.within (Or.inl hX_in) (Or.inl hL_in) h))
    · exact absurd (same_side_symm hXM) (pasch3 h hL_EK)
  have hMLE : Triangle M L E := Triangle.of_line hM_MN hL_MN hML hE_MN
  rw [← angle_eq_of_onRay (OnRay.of_between hEXF) (OnRay.of_between hELK)]
  exact angle_lt_of_between hMLE hMXL

/-- When M, L, N lie in that order and the angle ELM is right, EL makes a right angle
with every ray of MN issuing from L. Euclid carries LM through to N and uses this
perpendicular to compare distances from the centre. -/
theorem Prop15.perp {E L M N : Point} {MN : Line} (hM_MN : OnLine M MN) (hN_MN : OnLine N MN)
    (hMLN : Between M L N) (hE_MN : ¬ OnLine E MN) (hELM : ∠ E L M = ∟) :
    ∀ P : Point, Collinear M N P → P ≠ L → ∠ E L P = ∟ := by
  have hEL : E ≠ L := fun e => hE_MN (e ▸ on_line_of_between_ends hMLN hM_MN hN_MN)
  have hML : M ≠ L := ne_of_between hMLN
  have hMLE : ∠ M L E = ∟ := (angle_symm hML hEL).trans hELM
  have hELN : ∠ E L N = ∟ := (adjacent_eq_of_right hM_MN hN_MN hMLN hE_MN hMLE).symm.trans hMLE
  intro P hP hPL
  obtain ⟨ν, hM_ν, hN_ν, hP_ν⟩ := hP
  rw [line_unique (ne_of_between_ends hMLN) hM_ν hN_ν hM_MN hN_MN] at hP_ν
  rcases OnRay.cases_of_between hMLN hM_MN hN_MN hP_ν hPL with h | h
  · exact (angle_onRay_right h hEL).trans hELM
  · exact (angle_onRay_right h hEL).trans hELN

/-- Of straight lines in a circle the diameter is greatest, and of the rest the nearer to the centre
is always greater than the more remote. -/
theorem Prop15 {A B C D E F G H K : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hF : OnCircle F ABCD)
    (hG : OnCircle G ABCD) (hE_BC : ¬ Collinear B C E) (hE_FG : ¬ Collinear F G E)
    (hH : Collinear B C H) (hEH : ∀ P : Point, Collinear B C P → P ≠ H → ∠ E H P = ∟)
    (hK : Collinear F G K) (hEK : ∀ P : Point, Collinear F G P → P ≠ K → ∠ E K P = ∟)
    (hnearer : ‖E H‖ < ‖E K‖) :
    ‖B C‖ < ‖A D‖ ∧ ‖F G‖ < ‖B C‖ := by
  -- Let ABCD be a circle, let AD be its diameter and E the centre; and let BC be nearer to the
  -- diameter AD, and FG more remote;
  -- I say that AD is greatest and BC greater than FG.
  -- For from the centre E let EH, EK be drawn perpendicular to BC, FG.
  /- Our statement gives the perpendiculars, and the foot K falls between F and G
     (`foot_between`, as in III.14). -/
  have hFKG : Between F K G := foot_between hE hF hG hE_FG hK hEK
  -- Then, since BC is nearer to the centre and FG more remote, EK is greater than
  -- EH. [III. Def. 5]
  /- Our statement assumes this. -/
  -- Let EL be made equal to EH, through L let LM be drawn at right angles to EK and carried
  -- through to N, and let ME, EN, FE, EG be joined.
  /- We cut EL off EK, equal to EH [I. 3]. -/
  have hEH' : E ≠ H := fun e => hE_BC (e ▸ hH)
  obtain ⟨L, hELK, hEL⟩ := BookI.Prop3 hEH' hnearer
  have hEK' : E ≠ K := ne_of_between_ends hELK
  obtain ⟨EK, hE_EK, hK_EK⟩ := Postulate1 E K hEK'
  have hL_EK : OnLine L EK := on_line_of_between_ends hELK hE_EK hK_EK
  obtain ⟨FG, hF_FG, hG_FG⟩ := Postulate1 F G (ne_of_between_ends hFKG)
  have hK_FG : OnLine K FG := on_line_of_between_ends hFKG hF_FG hG_FG
  have hE_FG_line : ¬ OnLine E FG := fun h => hE_FG ⟨FG, hF_FG, hG_FG, h⟩
  have hF_EK : ¬ OnLine F EK := fun h =>
    hE_FG_line (line_unique (ne_of_between hFKG) h hK_EK hF_FG hK_FG ▸ hE_EK)
  have hG_EK : ¬ OnLine G EK := fun h =>
    hE_FG_line (line_unique (ne_of_between (between_symm hFKG)) h hK_EK hG_FG hK_FG ▸ hE_EK)
  /- We draw LM at right angles to EK, on F's side [I. 11]. -/
  obtain ⟨R, hRF, hR⟩ := BookI.Prop11 hEK' ⟨EK, hE_EK, hK_EK, hL_EK⟩
    (fun ⟨l, h1, h2, h3⟩ => hF_EK (line_unique hEK' h1 h2 hE_EK hK_EK ▸ h3))
  have hR_EK : ¬ OnLine R EK := not_on_line_of_same_side (hRF.sameSide hE_EK hK_EK)
  have hRL : R ≠ L := fun e => hR_EK (e ▸ hL_EK)
  obtain ⟨MN, hL_MN, hR_MN⟩ := Postulate1 L R hRL.symm
  /- L is within the circle, so the straight line LM, carried through, meets the circle on
     each side of L, at N and at M. -/
  have hK_in : InsideCircle K ABCD := Prop2 hF hG K hFKG
  have hL_in : InsideCircle L ABCD :=
    InsideCircle.of_between_centre_of_inside hE hF hK_in hELK
  obtain ⟨N, hN, hN_MN, hNLR⟩ := line_circle_beyond hL_in hL_MN hR_MN hRL
  obtain ⟨M, hM, hM_MN, hMLN⟩ := line_circle_beyond hL_in hL_MN hN_MN (ne_of_between hNLR)
  /- MN meets EK at L alone. -/
  have only_L : ∀ P, OnLine P MN → OnLine P EK → P = L := fun P hPMN hPEK =>
    Classical.byContradiction fun hPL => hR_EK (line_unique hPL hPMN hL_MN hPEK hL_EK ▸ hR_MN)
  have hE_MN_line : ¬ OnLine E MN := fun h => (ne_of_between hELK) (only_L E h hE_EK)
  have hM_EK : ¬ OnLine M EK := fun h => (ne_of_between hMLN) (only_L M hM_MN h)
  have hN_EK : ¬ OnLine N EK := fun h => (ne_of_between (between_symm hMLN)) (only_L N hN_MN h)
  /- M lies on F's side of EK, and N on G's. -/
  have hNR : OppositeSides N R EK := ⟨hN_EK, hR_EK, pasch3 hNLR hL_EK⟩
  have hNM : OppositeSides N M EK := ⟨hN_EK, hM_EK, pasch3 (between_symm hMLN) hL_EK⟩
  have hMF : SameSide M F EK :=
    same_side_trans (same_side_of_opposite_sides hNR hNM) (hRF.sameSide hE_EK hK_EK)
  have hFG : OppositeSides F G EK := ⟨hF_EK, hG_EK, pasch3 hFKG hK_EK⟩
  have hFN : OppositeSides F N EK :=
    ⟨hF_EK, hN_EK, fun h => hNR.2.2 (same_side_trans h (same_side_symm (hRF.sameSide hE_EK hK_EK)))⟩
  have hNG : SameSide N G EK := same_side_of_opposite_sides hFN hFG
  /- The perpendicular makes right angles with both rays of MN from L. -/
  have hMLR : OnRay M L R := OnRay.of_between_between hNLR (between_symm hMLN)
  have hELM : ∠ E L M = ∟ :=
    (angle_onRay_right hMLR (ne_of_between hELK)).trans
      (hR E ⟨EK, hE_EK, hK_EK, hE_EK⟩ (ne_of_between hELK))
  have hEL_perp := Prop15.perp hM_MN hN_MN hMLN hE_MN_line hELM
  /- Joining ME and EN makes the triangle MEN. -/
  have hE_MN : ¬ Collinear M N E := fun ⟨l, h1, h2, h3⟩ =>
    hE_MN_line (line_unique (ne_of_between_ends hMLN) h1 h2 hM_MN hN_MN ▸ h3)
  have hL : Collinear M N L := ⟨MN, hM_MN, hN_MN, hL_MN⟩
  -- Then, since EH is equal to EL,
  have hEH_EL : ‖E H‖ = ‖E L‖ := hEL.symm
  -- BC is also equal to MN. [III. 14]
  have hBC_MN : ‖B C‖ = ‖M N‖ :=
    (Prop14 hE hB hC hM hN hE_BC hE_MN hH hEH hL hEL_perp).2 hEH_EL
  -- Again, since AE is equal to EM, and ED to EN,
  have hAE : ‖A E‖ = ‖E M‖ := (len_symm A E).trans (Definition15 hE hA hM)
  have hED : ‖E D‖ = ‖E N‖ := Definition15 hE hD hN
  -- AD is equal to ME, EN.
  have hAD : ‖A D‖ = ‖M E‖ + ‖E N‖ := by
    rw [← len_add_of_between hAED, hAE, hED, len_symm M E]
  -- But ME, EN are greater than MN, [I. 20]
  have h20 : ‖M N‖ < ‖M E‖ + ‖E N‖ := (BookI.Prop20 (Triangle.cab hE_MN)).1
  -- and MN is equal to BC;
  rw [← hBC_MN] at h20
  -- therefore AD is greater than BC.
  have hdiameter : ‖B C‖ < ‖A D‖ := by
    rw [hAD]
    exact h20
  -- And, since the two sides ME, EN are equal to the two sides FE, EG,
  have hEM : ‖E M‖ = ‖E F‖ := Definition15 hE hM hF
  have hEN : ‖E N‖ = ‖E G‖ := Definition15 hE hN hG
  -- and the angle MEN greater than the angle FEG,
  /- FG and MN never meet, for at a common point Z the triangle ZLK would have two right
     angles, against I.17. So F and G are on K's side of MN, and E is on the other. -/
  have par : Parallel FG MN := Parallel.of_not_meet hF_FG fun Z hZFG hZMN => by
    have hZL : Z ≠ L := by
      intro e
      have hFG_EK := line_unique (ne_of_between (between_symm hELK)).symm
        (e ▸ hZFG) hK_FG hL_EK hK_EK
      exact hE_FG_line (hFG_EK ▸ hE_EK)
    have hZ_EK : ¬ OnLine Z EK := fun h => hZL (only_L Z hZMN h)
    have hZK : Z ≠ K := fun e => hZ_EK (e ▸ hK_EK)
    have hELZ : ∠ E L Z = ∟ := hEL_perp Z ⟨MN, hM_MN, hN_MN, hZMN⟩ hZL
    have hZLK : ∠ Z L K = ∟ := by
      have h := adjacent_eq_of_right hE_EK hK_EK hELK hZ_EK hELZ
      exact h.symm.trans hELZ
    have hLKZ : ∠ L K Z = ∟ := by
      have hEKZ : ∠ E K Z = ∟ := hEK Z ⟨FG, hF_FG, hG_FG, hZFG⟩ hZK
      rw [angle_onRay_left (OnRay.of_between (between_symm hELK)) hZK]
      exact hEKZ
    have hZLK' : Triangle Z L K :=
      (Triangle.of_line hL_EK hK_EK (ne_of_between (between_symm hELK)).symm hZ_EK).cab
    have h17 := (BookI.Prop17 hZLK').1
    rw [hZLK, hLKZ] at h17
    exact lt_irrefl _ h17
  have hEK_MN : ¬ SameSide E K MN := pasch3 hELK hL_MN
  have hEF_MN : OppositeSides E F MN :=
    ⟨hE_MN_line, par.not_onLine hF_FG, fun h => hEK_MN (same_side_trans (same_side_symm h)
      (par.sameSide hF_FG hK_FG))⟩
  have hEG_MN : OppositeSides E G MN :=
    ⟨hE_MN_line, par.not_onLine hG_FG, fun h => hEK_MN (same_side_trans (same_side_symm h)
      (par.sameSide hG_FG hK_FG))⟩
  have h1 : ∠ F E K < ∠ M E L :=
    Prop15.half hE hF hM hE_EK hL_EK hELK hL_MN hM_MN hE_MN_line hL_in hEF_MN hMF hF_EK
  have h2 : ∠ G E K < ∠ N E L :=
    Prop15.half hE hG hN hE_EK hL_EK hELK hL_MN hN_MN hE_MN_line hL_in hEG_MN hNG hG_EK
  have hMEN : ∠ F E G < ∠ M E N := by
    rw [angle_add_of_between hE_FG hFKG, angle_add_of_between hE_MN hMLN,
      angle_symm hEK'.symm (fun e : G = E => hG_EK (e ▸ hE_EK)),
      angle_symm (ne_of_between hELK).symm (fun e : N = E => hN_EK (e ▸ hE_EK))]
    exact lt_trans (add_lt_add_right _ h1) (by
      rw [add_comm (∠ M E L), add_comm (∠ M E L)]; exact add_lt_add_right _ h2)
  -- therefore the base MN is greater than the base FG. [I. 24]
  have h24 : ‖F G‖ < ‖M N‖ := BookI.Prop24 (Triangle.cab hE_MN) (Triangle.cab hE_FG) hEM hEN hMEN
  -- But MN was proved equal to BC.
  rw [← hBC_MN] at h24
  -- Therefore the diameter AD is greatest and BC greater than FG.
  exact ⟨hdiameter, h24⟩
  -- Therefore etc.
  -- Q. E. D.

/-- **III.15, the diameter is greatest** (companion of III.15). Of the straight lines in a
circle, none is greater than the diameter AD, and a straight line BC in it is equal to the
diameter exactly when it passes through the centre E: when it is a diameter too. If BC is
not through the centre, BE, EC together are greater than BC [I. 20], and they are equal to
AD. BC may be a point, and then it is nothing. -/
theorem Prop15.le_diameter {A B C D E : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) :
    ‖B C‖ ≤ ‖A D‖ ∧ (‖B C‖ = ‖A D‖ ↔ Between B E C) := by
  /- AD is two radii, BE and EC (`Prop14.diameter_sum`, as in III.14 general). -/
  have hAD_sum : ‖A D‖ = ‖B E‖ + ‖E C‖ :=
    Prop14.diameter_sum hE hA hD hB hC hAED
  by_cases hBC : B = C
  · /- BC is a point: its length is nothing, and E cannot lie between its equal ends. -/
    subst C
    rw [len_self]
    refine ⟨not_lt_zero _, ?_⟩
    exact ⟨fun h => False.elim (len_ne_zero (ne_of_between_ends hAED) h.symm),
      fun h => False.elim (ne_of_between_ends h rfl)⟩
  · by_cases hE_BC : Collinear B C E
    · /- BC passes through E: it too is a diameter, equal to the same two radii. -/
      obtain ⟨L, hB_L, hC_L, hE_L⟩ := hE_BC
      have hBEC : Between B E C :=
        between_of_centre_chord hE_L hB_L hC_L hE hB hC hBC
      have hBC_AD : ‖B C‖ = ‖A D‖ := (len_add_of_between hBEC).symm.trans hAD_sum.symm
      refine ⟨?_, ⟨fun _ => hBEC, fun _ => hBC_AD⟩⟩
      rw [hBC_AD]
      exact lt_irrefl _
    · /- BC does not pass through E: BE and EC together exceed BC by I.20. -/
      have hBC_AD : ‖B C‖ < ‖A D‖ := by
        rw [hAD_sum]
        exact (BookI.Prop20 (Triangle.cab hE_BC)).1
      have hnot_between : ¬ Between B E C := by
        intro hBEC
        obtain ⟨L, hB_L, hE_L, hC_L⟩ := collinear_of_between hBEC
        exact hE_BC ⟨L, hB_L, hC_L, hE_L⟩
      exact ⟨fun h => lt_irrefl _ (lt_trans hBC_AD h),
        ⟨fun h => False.elim (Magnitude.ne_of_lt hBC_AD h),
          fun h => False.elim (hnot_between h)⟩⟩

/-- **III.15, the nearer is greater** (companion of III.15). Of two straight lines BC, FG in
a circle, the one nearer to the centre E is the greater: if EH is less than EK, H and K being
the feet of the perpendiculars from E, then FG is less than BC. The nearer, BC, may be a
diameter, at no distance; the more remote cannot be. (Nor can FG be a point: its foot would
be E, and EK nothing.) -/
theorem Prop15.nearer {B C E F G H K : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hF : OnCircle F ABCD)
    (hG : OnCircle G ABCD) (hBC : B ≠ C) (hH : Foot E B C H) (hK : Foot E F G K)
    (hnearer : ‖E H‖ < ‖E K‖) :
    ‖F G‖ < ‖B C‖ := by
  /- FG cannot pass through E, even with coincident ends: its foot would be E. -/
  have hE_FG : ¬ Collinear F G E := by
    intro h
    have hK_E : K = E := hK.2.1 h
    rw [hK_E, len_self] at hnearer
    exact not_lt_zero _ hnearer
  by_cases hE_BC : Collinear B C E
  · /- BC is a diameter. The diameter bound is strict for FG, which does not pass through E. -/
    obtain ⟨L, hB_L, hC_L, hE_L⟩ := hE_BC
    have hBEC : Between B E C :=
      between_of_centre_chord hE_L hB_L hC_L hE hB hC hBC
    obtain ⟨hbound, hequal⟩ := Prop15.le_diameter hE hB hC hBEC hF hG
    have hunequal : ‖F G‖ ≠ ‖B C‖ := by
      intro h
      obtain ⟨M, hF_M, hE_M, hG_M⟩ := collinear_of_between (hequal.mp h)
      exact hE_FG ⟨M, hF_M, hG_M, hE_M⟩
    rcases lt_trichotomy ‖F G‖ ‖B C‖ with h | h | h
    · exact h
    · exact False.elim (hunequal h)
    · exact False.elim (hbound h)
  · /- Neither straight line passes through E: this is III.15's worked configuration. Draw
       the diameter through B, carrying BE on through the centre to A on the circle; III.15's
       second conclusion is then that FG is less than BC. -/
    have hB_E : B ≠ E := ne_of_centre_of_on hE hB
    obtain ⟨L, hE_L, hB_L⟩ := Postulate1 E B hB_E.symm
    obtain ⟨A, hA, -, hAEB⟩ := line_circle_beyond (centre_inside hE) hE_L hB_L hB_E
    exact (Prop15 hE hA hB hAEB hB hC hF hG hE_BC hE_FG
      hH.1 (hH.2.2 hE_BC) hK.1 (hK.2.2 hE_FG) hnearer).2

/-- The check: the statement of `Prop15` follows from `Prop15.le_diameter` and
`Prop15.nearer` (checked by Lean). BC is not through the centre, so it is less than the
diameter. -/
example : type_of% @Elements.BookIII.Prop15 := by
  intro A B C D E F G H K ABCD hE hA hD hAED hB hC hF hG hE_BC hE_FG hH hEH hK hEK hnearer
  obtain ⟨hle, hiff⟩ := Prop15.le_diameter hE hA hD hAED hB hC
  refine ⟨?_, Prop15.nearer hE hB hC hF hG (Triangle.ne₁₂ hE_BC)
    ⟨hH, fun h => absurd h hE_BC, fun _ => hEH⟩ ⟨hK, fun h => absurd h hE_FG, fun _ => hEK⟩
    hnearer⟩
  have hne : ‖B C‖ ≠ ‖A D‖ := fun h => by
    obtain ⟨L, hB_L, hE_L, hC_L⟩ := collinear_of_between (hiff.mp h)
    exact hE_BC ⟨L, hB_L, hC_L, hE_L⟩
  rcases lt_trichotomy ‖B C‖ ‖A D‖ with h | h | h
  · exact h
  · exact absurd h hne
  · exact absurd h hle

end Elements.BookIII
