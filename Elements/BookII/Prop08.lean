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
import Elements.BookI.HelpersParallels
import Elements.BookI.Prop46
import Elements.BookI.Prop36
import Elements.BookI.Prop43

/-!
# Book II, Proposition 8

Euclid's text, in Heath's translation: [`heath/II/08.md`](../../heath/II/08.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- The four corners where two pairs of parallels meet form a parallelogram.
Euclid reads each cell of the figure drawn double in this way. -/
theorem Prop8.cell {X Y Z W : Point} {h h' v v' : Line}
    (hh : Parallel h h') (hv : Parallel v v')
    (hX : OnLine X h) (hY : OnLine Y h) (hZ : OnLine Z h') (hW : OnLine W h')
    (vX : OnLine X v) (vW : OnLine W v) (vY : OnLine Y v') (vZ : OnLine Z v') :
    Parallelogram X Y Z W := by
  have hXY : X ≠ Y := fun e => hv.not_onLine vX (e ▸ vY)
  have hZW : Z ≠ W := fun e => hv.not_onLine vW (e ▸ vZ)
  have hYZ : Y ≠ Z := fun e => hh.not_onLine hY (e ▸ hZ)
  have hWX : W ≠ X := fun e => hh.not_onLine hX (e ▸ hW)
  exact ⟨AreParallel.of_parallel hXY hZW hX hY hZ hW hh,
    AreParallel.of_parallel hYZ hWX vY vZ vW vX hv.symm⟩

/-- If a straight line be cut at random, four times the rectangle contained by the whole and one of
the segments together with the square on the remaining segment is equal to the square described
on the whole and the aforesaid segment as on one straight line. -/
theorem Prop8 {A B C : Point} (hACB : Between A C B) :
    ∀ D : Point, Between A B D → ‖B D‖ = ‖C B‖ →
      rect A B B C + rect A B B C + rect A B B C + rect A B B C + sq A C = sq A D := by
  -- For let a straight line AB be cut at random at the point C;
  -- I say that four times the rectangle contained by AB, BC together with the square on AC is
  -- equal to the square described on AB, BC as on one straight line.
  -- For let [the straight line] BD be produced in a straight line [with AB], and let BD be
  -- made equal to CB;
  intro D hABD hBD
  have hAD : A ≠ D := ne_of_between_ends hABD
  have hACD : Between A C D := between_of_between_left hABD hACB
  have hCBD : Between C B D := between_inner hACB hABD
  -- let the square AEFD be described on AD, and let the figure be drawn double.
  /- I.46 describes the square on the side of a point off AD, and `Square.described`
     says it is the square on AD. "The figure drawn double" is II.4's figure, drawn
     twice in the square with its diameter DE (`Parallelogram.figure`): through B, BL
     parallel to AE, cutting DE at K, and MN through K parallel to AD; through C, CH,
     cutting DE at Q, and OP through Q. Each figure's complements are parallelograms
     (`Parallelogram.complements`). -/
  obtain ⟨X, hX, -⟩ := exists_off_line hAD []
  obtain ⟨E, F, hsq, hE, hF⟩ := BookI.Prop46 hAD hX
  obtain ⟨hp, hAEFD⟩ := Square.described hsq hE hF
  obtain ⟨L, K, M, N, hDKE, hELF, hAME, hFND, hBKL, hMKN, hDBKN, hKMEL⟩ :=
    hp.figure hABD
  obtain ⟨H, Q, O, P, hDQE, hEHF, hAOE, hFPD, hCQH, hOQP, hDCQP, hQOEH⟩ :=
    hp.figure hACD
  have hDAEF := hp.rotate.rotate.rotate
  obtain ⟨hBAMK, -⟩ := hDAEF.complements hDKE (between_symm hABD)
    hAME hELF hFND hDBKN hKMEL
  obtain ⟨hCAOQ, hPQHF⟩ := hDAEF.complements hDQE (between_symm hACD)
    hAOE hEHF hFPD hDCQP hQOEH
  /- We name the straight lines of the two figures. -/
  obtain ⟨AD, hA_AD, hD_AD⟩ := Postulate1 A D hAD
  obtain ⟨EF, hE_EF, hF_EF⟩ := Postulate1 E F hp.2.1
  obtain ⟨AE, hA_AE, hE_AE⟩ := Postulate1 A E hp.1.1
  obtain ⟨DF, hD_DF, hF_DF⟩ := Postulate1 D F hp.1.2.1.symm
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E (ne_of_between_ends hDKE)
  obtain ⟨MN, hM_MN, hN_MN⟩ := Postulate1 M N (ne_of_between_ends hMKN)
  obtain ⟨OP, hO_OP, hP_OP⟩ := Postulate1 O P (ne_of_between_ends hOQP)
  obtain ⟨CH, hC_CH, hH_CH⟩ := Postulate1 C H (ne_of_between_ends hCQH)
  obtain ⟨BL, hB_BL, hL_BL⟩ := Postulate1 B L (ne_of_between_ends hBKL)
  have hB_AD := on_line_of_between_ends hABD hA_AD hD_AD
  have hC_AD := on_line_of_between_ends hACD hA_AD hD_AD
  have hL_EF := on_line_of_between_ends hELF hE_EF hF_EF
  have hH_EF := on_line_of_between_ends hEHF hE_EF hF_EF
  have hM_AE := on_line_of_between_ends hAME hA_AE hE_AE
  have hO_AE := on_line_of_between_ends hAOE hA_AE hE_AE
  have hN_DF := on_line_of_between_ends hFND hF_DF hD_DF
  have hP_DF := on_line_of_between_ends hFPD hF_DF hD_DF
  have hK_DE := on_line_of_between_ends hDKE hD_DE hE_DE
  have hQ_DE := on_line_of_between_ends hDQE hD_DE hE_DE
  have hK_MN := on_line_of_between_ends hMKN hM_MN hN_MN
  have hQ_OP := on_line_of_between_ends hOQP hO_OP hP_OP
  have hK_BL := on_line_of_between_ends hBKL hB_BL hL_BL
  have hQ_CH := on_line_of_between_ends hCQH hC_CH hH_CH
  have hCH_DF : Parallel CH DF := hDCQP.2.parallel hC_CH hQ_CH hP_DF hD_DF
  have hBL_DF : Parallel BL DF := hDBKN.2.parallel hB_BL hK_BL hN_DF hD_DF
  have hAE_CH : Parallel AE CH := hCAOQ.2.parallel hA_AE hO_AE hQ_CH hC_CH
  have hMN_AD : Parallel MN AD := hDBKN.1.symm.parallel hK_MN hN_MN hD_AD hB_AD
  have hOP_AD : Parallel OP AD := hDCQP.1.symm.parallel hQ_OP hP_OP hD_AD hC_AD
  have hOP_EF : Parallel OP EF := hQOEH.1.parallel hQ_OP hO_OP hE_EF hH_EF
  have hCH_BL : Parallel CH BL := BookI.Prop30.parallel hCH_DF hBL_DF (by
    intro e
    exact hBL_DF.not_onLine (on_line_of_between hCBD (e ▸ hC_CH) hB_BL) hD_DF)
  have hDKQ : Between D K Q := Parallel.between hBL_DF.symm hCH_BL
    hD_DF hB_BL hC_CH (between_symm hCBD) hD_DF hK_BL hQ_CH
    ⟨DE, hD_DE, hK_DE, hQ_DE⟩
  have hMN_OP : Parallel MN OP := BookI.Prop30.parallel hMN_AD hOP_AD (by
    intro e
    have hDE_OP : DE = OP := line_unique (ne_of_between (between_symm hDKQ)).symm
      hK_DE hQ_DE (e ▸ hK_MN) hQ_OP
    exact hOP_AD.not_onLine (hDE_OP ▸ hD_DE) hD_AD)
  /- Each meeting follows from I.30. -/
  obtain ⟨G, hG_MN, hG_CH⟩ := BookI.Prop30.meet hCH_DF hN_DF hN_MN (by
    intro e
    exact hMN_AD.not_onLine (e ▸ hD_DF) hD_AD)
  obtain ⟨R, hR_OP, hR_BL⟩ := BookI.Prop30.meet hBL_DF hP_DF hP_OP (by
    intro e
    exact hOP_AD.not_onLine (e ▸ hD_DF) hD_AD)
  /- The two figures cross and cut the square into nine cells, and where they cross,
     G and R, Euclid reads off his figure. The order follows from Book Zero: points on
     three parallels keep their order on every straight line crossing them
     (`Parallel.between`). So M, G, K lie on MN as A, C, B lie on AD, and K, R, L lie on
     BL as K, Q, E lie on the diameter, and so for every row and column. -/
  have hMGK : Between M G K := Parallel.between hAE_CH hCH_BL.symm
    hA_AE hC_CH hB_BL hACB hM_AE hG_CH hK_BL ⟨MN, hM_MN, hG_MN, hK_MN⟩
  have hCGQ : Between C G Q := Parallel.between hMN_AD.symm hMN_OP.symm
    hD_AD hK_MN hQ_OP hDKQ hC_AD hG_MN hQ_OP ⟨CH, hC_CH, hG_CH, hQ_CH⟩
  have hAMO : Between A M O := Parallel.between hMN_AD.symm hMN_OP.symm
    hD_AD hK_MN hQ_OP hDKQ hA_AD hM_MN hO_OP ⟨AE, hA_AE, hM_AE, hO_AE⟩
  have hDNP : Between D N P := Parallel.between hMN_AD.symm hMN_OP.symm
    hD_AD hK_MN hQ_OP hDKQ hD_AD hN_MN hP_OP ⟨DF, hD_DF, hN_DF, hP_DF⟩
  have hQRP : Between Q R P := Parallel.between hCH_BL hBL_DF.symm
    hC_CH hB_BL hD_DF hCBD hQ_CH hR_BL hP_DF ⟨OP, hQ_OP, hR_OP, hP_OP⟩
  have hHLF : Between H L F := Parallel.between hCH_BL hBL_DF.symm
    hC_CH hB_BL hD_DF hCBD hH_CH hL_BL hF_DF ⟨EF, hH_EF, hL_EF, hF_EF⟩
  have hKQE : Between K Q E := between_inner hDKQ hDQE
  have hKRL : Between K R L := Parallel.between hMN_OP hOP_EF.symm
    hK_MN hQ_OP hE_EF hKQE hK_MN hR_OP hL_EF ⟨BL, hK_BL, hR_BL, hL_BL⟩
  have hMOE : Between M O E := between_inner hAMO hAOE
  have hEHL : Between E H L := between_inner (between_symm hHLF) (between_symm hEHF)
    |> between_symm
  /- The cells of the figure are parallelograms, named as the proof reads them; OH is
     the second figure's. -/
  have hCBKG : Parallelogram C B K G := Prop8.cell hMN_AD.symm hCH_BL
    hC_AD hB_AD hK_MN hG_MN hC_CH hG_CH hB_BL hK_BL
  have hBDNK : Parallelogram B D N K := hDBKN.reverse.rotate.rotate.rotate
  have hGKRQ : Parallelogram G K R Q := Prop8.cell hMN_OP hCH_BL
    hG_MN hK_MN hR_OP hQ_OP hG_CH hQ_CH hK_BL hR_BL
  have hKNPR : Parallelogram K N P R := Prop8.cell hMN_OP hBL_DF
    hK_MN hN_MN hP_OP hR_OP hK_BL hR_BL hN_DF hP_DF
  have hAMGC : Parallelogram A M G C := Prop8.cell hAE_CH hMN_AD.symm
    hA_AE hM_AE hG_CH hC_CH hA_AD hC_AD hM_MN hG_MN
  have hMOQG : Parallelogram M O Q G := Prop8.cell hAE_CH hMN_OP
    hM_AE hO_AE hQ_CH hG_CH hM_MN hG_MN hO_OP hQ_OP
  have hHLRQ : Parallelogram H L R Q := Prop8.cell hOP_EF.symm hCH_BL
    hH_EF hL_EF hR_OP hQ_OP hH_CH hQ_CH hL_BL hR_BL
  have hLFPR : Parallelogram L F P R := Prop8.cell hOP_EF.symm hBL_DF
    hL_EF hF_EF hP_OP hR_OP hL_BL hR_BL hF_DF hP_DF
  have hKGQR : Parallelogram K G Q R := hGKRQ.reverse.rotate.rotate.rotate
  -- Then, since CB is equal to BD,
  have hCB_BD : ‖C B‖ = ‖B D‖ := hBD.symm
  -- while CB is equal to GK, and BD to KN,
  have hCB_GK : ‖C B‖ = ‖G K‖ := (BookI.Prop34 hCBKG).2.1
  have hBD_KN : ‖B D‖ = ‖K N‖ := (BookI.Prop34 hBDNK).2.1
  -- therefore GK is also equal to KN.
  have hGK_KN : ‖G K‖ = ‖K N‖ := hCB_GK.symm.trans (hCB_BD.trans hBD_KN)
  -- For the same reason
  have hGK_QR : ‖G K‖ = ‖Q R‖ := (BookI.Prop34 hGKRQ).2.1
  have hKN_RP : ‖K N‖ = ‖R P‖ := (BookI.Prop34 hKNPR).2.1
  -- QR is also equal to RP.
  have hQR_RP : ‖Q R‖ = ‖R P‖ := hGK_QR.symm.trans (hGK_KN.trans hKN_RP)
  -- And, since BC is equal to BD, and GK to KN,
  let CK := quadArea B C G K
  let KD := quadArea D B K N
  let GR := quadArea K G Q R
  let RN := quadArea N K R P
  -- therefore CK is also equal to KD, and GR to RN. [I. 36]
  have hCK_KD : CK = KD := by
    have h := BookI.Prop36 hCBKG.rotate.rotate.rotate hBDNK.rotate.rotate.rotate hCB_BD
      ⟨MN, hG_MN, hK_MN, hK_MN, hN_MN⟩ ⟨AD, hC_AD, hB_AD, hB_AD, hD_AD⟩
    rw [quadArea_rotate₂ B K G C, quadArea_reverse B C G K,
      quadArea_rotate₂ D N K B, quadArea_reverse D B K N] at h
    exact h
  have hGR_RN : GR = RN := by
    have h := BookI.Prop36 hGKRQ.rotate.rotate.rotate hKNPR.rotate.rotate.rotate hGK_KN
      ⟨OP, hQ_OP, hR_OP, hR_OP, hP_OP⟩ ⟨MN, hG_MN, hK_MN, hK_MN, hN_MN⟩
    rw [quadArea_rotate₂ K R Q G, quadArea_reverse K G Q R,
      quadArea_rotate₂ N P R K, quadArea_reverse N K R P] at h
    exact h
  -- But CK is equal to RN, for they are complements of the parallelogram CP; [I. 43]
  have hCK_RN : CK = RN := BookI.Prop43 hDCQP hDKQ (between_symm hCBD)
    hCGQ hQRP (between_symm hDNP) hDBKN hKGQR
  -- therefore KD is also equal to GR;
  have hKD_GR : KD = GR := hCK_KD.symm.trans (hCK_RN.trans hGR_RN.symm)
  -- therefore the four areas DK, CK, GR, RN are equal to one another.
  have hGR_CK : GR = CK := hKD_GR.symm.trans hCK_KD.symm
  have hRN_CK : RN = CK := hCK_RN.symm
  -- Therefore the four are quadruple of CK.
  have hfourCK : KD + CK + GR + RN = CK + CK + CK + CK := by
    rw [← hCK_KD, hGR_CK, hRN_CK]
  -- Again, since CB is equal to BD,
  -- while BD is equal to BK, that is CG,
  have hKDsq : Square D B K N := hsq.rotate.rotate.rotate.about_diameter hDAEF
    hDKE (between_symm hABD) (between_symm hFND) hDBKN
  have hBD_BK : ‖B D‖ = ‖B K‖ := (len_symm B D).trans hKDsq.1
  have hBK_CG : ‖B K‖ = ‖C G‖ := (BookI.Prop34 hCBKG).1.symm
  have hBD_CG : ‖B D‖ = ‖C G‖ := hBD_BK.trans hBK_CG
  -- and CB is equal to GK, that is GQ,
  have hCPsq : Square D C Q P := hsq.rotate.rotate.rotate.about_diameter hDAEF
    hDQE (between_symm hACD) (between_symm hFPD) hDCQP
  have hGRsq : Square Q R K G := hCPsq.rotate.rotate.about_diameter hDCQP.rotate.rotate
    (between_symm hDKQ) hQRP (between_symm hCGQ) hKGQR.rotate.rotate
  have hGK_GQ : ‖G K‖ = ‖G Q‖ := (len_symm G K).trans hGRsq.2.2.1
  have hCB_GQ : ‖C B‖ = ‖G Q‖ := hCB_GK.trans hGK_GQ
  -- therefore CG is also equal to GQ.
  have hCG_GQ : ‖C G‖ = ‖G Q‖ := hBD_CG.symm.trans (hCB_BD.symm.trans hCB_GQ)
  -- And, since CG is equal to GQ, and QR to RP,
  let AG := quadArea C A M G
  let MQ := quadArea G M O Q
  let QL := quadArea R Q H L
  let RF := quadArea P R L F
  -- AG is also equal to MQ, and QL to RF. [I. 36]
  have hAG_MQ : AG = MQ := by
    have h := BookI.Prop36 hAMGC.reverse hMOQG.reverse hCG_GQ
      ⟨AE, hA_AE, hM_AE, hM_AE, hO_AE⟩ ⟨CH, hC_CH, hG_CH, hG_CH, hQ_CH⟩
    rw [quadArea_reverse A M G C, quadArea_reverse M O Q G,
      hAMGC.rotate.rotate.rotate.quadArea_rotate,
      hMOQG.rotate.rotate.rotate.quadArea_rotate] at h
    exact h
  have hQL_RF : QL = RF := by
    have h := BookI.Prop36 hHLRQ.reverse hLFPR.reverse hQR_RP
      ⟨EF, hH_EF, hL_EF, hL_EF, hF_EF⟩ ⟨OP, hQ_OP, hR_OP, hR_OP, hP_OP⟩
    rw [quadArea_rotate₂ R L H Q, quadArea_reverse R Q H L,
      quadArea_rotate₂ P F L R, quadArea_reverse P R L F] at h
    exact h
  -- But MQ is equal to QL, for they are complements of the parallelogram ML; [I. 43]
  have hMQ_QL : MQ = QL := BookI.Prop43 hKMEL hKQE (between_symm hMGK)
    hMOE hEHL (between_symm hKRL) hKGQR hQOEH
  -- therefore AG is also equal to RF;
  have hAG_RF : AG = RF := hAG_MQ.trans (hMQ_QL.trans hQL_RF)
  -- therefore the four areas AG, MQ, QL, RF are equal to one another.
  have hMQ_AG : MQ = AG := hAG_MQ.symm
  have hQL_AG : QL = AG := hMQ_QL.symm.trans hMQ_AG
  -- Therefore the four are quadruple of AG.
  have hfourAG : AG + MQ + QL + RF = AG + AG + AG + AG := by
    rw [hMQ_AG, hQL_AG, ← hAG_RF]
  -- But the four areas CK, KD, GR, RN were proved to be quadruple of CK;
  have hfourCK' : CK + KD + GR + RN = CK + CK + CK + CK := by
    calc
      CK + KD + GR + RN = KD + CK + GR + RN := by ac_rfl
      _ = CK + CK + CK + CK := hfourCK
  -- therefore the eight areas, which contain the gnomon STU, are quadruple of AK.
  /- The gnomon STU is the parallelogram CP about the diameter with its two complements,
     AQ and QF (Definition II.2). We cut CP into its four cells KD, CK, GR, RN
     (`Parallelogram.about_diameter`), and AQ and QF into two each
     (`quadArea_add_of_parallelograms`): the eight areas. -/
  let AK := quadArea B A M K
  let STU := quadArea D C Q P + quadArea C A O Q + quadArea P Q H F
  have hCPsplit : quadArea D C Q P = KD + CK + GR + RN :=
    hDCQP.about_diameter hDKQ (between_symm hCBD) hCGQ hQRP
      (between_symm hDNP) hDBKN hKGQR
  have hAQsplit : quadArea C A O Q = AG + MQ :=
    quadArea_add_of_parallelograms hAMGC.rotate.rotate.rotate hMOQG.rotate.rotate.rotate
      hCGQ hAMO
  have hQFsplit : quadArea P Q H F = RF + QL := by
    rw [← hPQHF.quadArea_rotate,
      quadArea_add_of_parallelograms hHLRQ.rotate.rotate.rotate hLFPR.rotate.rotate.rotate
        hQRP hHLF,
      hHLRQ.rotate.rotate.quadArea_rotate, hLFPR.rotate.rotate.quadArea_rotate]
    change QL + RF = RF + QL
    ac_rfl
  have hAKsplit : AK = AG + CK := by
    have h := quadArea_add_of_parallelograms hAMGC hCBKG.reverse hACB hMGK
    rw [hBAMK.quadArea_rotate, hAMGC.rotate.rotate.rotate.quadArea_rotate,
      hCBKG.reverse.rotate.rotate.rotate.quadArea_rotate] at h
    exact h
  have hSTUfour : STU = AK + AK + AK + AK := by
    calc
      STU = (CK + KD + GR + RN) + (AG + MQ + QL + RF) := by
        dsimp [STU]
        rw [hCPsplit, hAQsplit, hQFsplit]
        ac_rfl
      _ = (CK + CK + CK + CK) + (AG + AG + AG + AG) := by rw [hfourCK', hfourAG]
      _ = AK + AK + AK + AK := by rw [hAKsplit]; ac_rfl
  -- Now, since AK is the rectangle AB, BD, for BK is equal to BD,
  have hAKrect : Rectangle A M K B := Rectangle.of_right hBAMK.rotate
    ((angle_eq_of_onRay (OnRay.of_between hABD) (OnRay.of_between hAME)).trans hsq.2.2.2.1)
  have hAKnamed : AK = rect A B B D :=
    hAKrect.rotate.rotate.rotate.eq_rect (len_symm B A) hBD_BK.symm
  -- therefore four times the rectangle AB, BD is quadruple of AK.
  have hfourRect : rect A B B D + rect A B B D + rect A B B D + rect A B B D =
      AK + AK + AK + AK := by rw [hAKnamed]
  -- But the gnomon STU was also proved to be quadruple of AK;
  have hgnomon : AK + AK + AK + AK = STU := hSTUfour.symm
  -- therefore four times the rectangle AB, BD is equal to the gnomon STU.
  have hrect_STU : rect A B B D + rect A B B D + rect A B B D + rect A B B D = STU :=
    hfourRect.trans hgnomon
  -- Let OH, which is equal to the square on AC, be added to each;
  have hOHsq : Square E H Q O := hsq.rotate.about_diameter hp.rotate
    (between_symm hDQE) hEHF (between_symm hAOE) hQOEH.rotate.rotate
  have hCA_QO : ‖C A‖ = ‖Q O‖ := (BookI.Prop34 hCAOQ).2.1
  have hOH : quadArea Q O E H = sq A C :=
    (hOHsq.rotate.rotate.eq_sq hQOEH).trans ((sq_congr hCA_QO.symm).trans (sq_symm C A))
  -- therefore four times the rectangle AB, BD together with the square on AC is equal to the
  -- gnomon STU and OH.
  have hadded : rect A B B D + rect A B B D + rect A B B D + rect A B B D + sq A C =
      STU + quadArea Q O E H := CommonNotion2 hrect_STU hOH.symm
  -- But the gnomon STU and OH are the whole square AEFD,
  have hwhole : STU + quadArea Q O E H = quadArea A E F D := by
    have h := hDAEF.about_diameter hDQE (between_symm hACD) hAOE hEHF hFPD hDCQP hQOEH
    rw [hDAEF.quadArea_rotate, h]
    dsimp [STU]
    ac_rfl
  -- which is described on AD;
  have hwhole_sq : quadArea A E F D = sq A D := hAEFD
  -- therefore four times the rectangle AB, BD together with the square on AC is equal to the
  -- square on AD.
  have hADsq : rect A B B D + rect A B B D + rect A B B D + rect A B B D + sq A C =
      sq A D := hadded.trans (hwhole.trans hwhole_sq)
  -- But BD is equal to BC;
  have hBD_BC : ‖B D‖ = ‖B C‖ := hBD.trans (len_symm C B)
  -- therefore four times the rectangle contained by AB, BC together with the square on AC is
  -- equal to the square on AD, that is to the square described on AB and BC as on one straight
  -- line.
  have hrect : rect A B B D = rect A B B C := rect_congr rfl hBD_BC
  rw [hrect] at hADsq
  -- Therefore etc.
  exact hADsq
  -- Q. E. D.

end Elements.BookII
