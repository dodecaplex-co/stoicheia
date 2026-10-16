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
# Book II, Proposition 4

Euclid's text, in Heath's translation: [`heath/II/04.md`](../../heath/II/04.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut at random, the square on the whole is equal to the squares on the
segments and twice the rectangle contained by the segments. -/
theorem Prop4 {A B C : Point} (hACB : Between A C B) :
    sq A B = sq A C + sq C B + (rect A C C B + rect A C C B) := by
  -- For let the straight line AB be cut at random at C;
  have hAB : A ≠ B := ne_of_between_ends hACB
  have hBCA : Between B C A := between_symm hACB
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hC_AB : OnLine C AB := on_line_of_between_ends hACB hA_AB hB_AB
  -- I say that the square on AB is equal to the squares on AC, CB and twice the rectangle
  -- contained by AC, CB.
  -- For let the square ADEB be described on AB, [I. 46]
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  obtain ⟨D, E, hsq, hD, hE⟩ := BookI.Prop46 hAB hP
  obtain ⟨hp, hADEB⟩ := Square.described hsq hD hE
  -- let BD be joined;
  have hBADE : Parallelogram B A D E := hp.rotate.rotate.rotate
  have hBD : B ≠ D := hBADE.triangle.ne₁₃
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hBD
  -- through C let CF be drawn parallel to either AD or EB,
  -- and through G let HK be drawn parallel to either AB or DE. [I. 31]
  /- G is where CF cuts BD; F, H, K are where the parallels meet the sides. -/
  obtain ⟨F, G, H, K, hBGD, hDFE, hAHD, hEKB, hCGF, -, hBCGK, hGHDF⟩ := hp.figure hACB
  -- Then, since CF is parallel to AD,
  obtain ⟨AD, hA_AD, hD_AD⟩ := Postulate1 A D hp.1.1
  obtain ⟨CF, hC_CF, hF_CF⟩ := Postulate1 C F (ne_of_between_ends hCGF)
  have hG_CF : OnLine G CF := on_line_of_between_ends hCGF hC_CF hF_CF
  have hH_AD : OnLine H AD := on_line_of_between_ends hAHD hA_AD hD_AD
  have hCF_AD : Parallel CF AD := (hGHDF.2.parallel hH_AD hD_AD hF_CF hG_CF).symm
  have hGC_DA : AreParallel G C D A :=
    AreParallel.of_parallel (ne_of_between hCGF).symm hp.1.1.symm hG_CF hC_CF hD_AD hA_AD hCF_AD
  -- and BD has fallen on them,
  have hG_BD : OnLine G BD := on_line_of_between_ends hBGD hB_BD hD_BD
  have hGD : G ≠ D := ne_of_between (between_symm hBGD) |>.symm
  have hC_BD : ¬ OnLine C BD := fun h =>
    hBADE.triangle.off_line hB_BD ((line_unique (ne_of_between hBCA) hB_AB hC_AB hB_BD h) ▸ hA_AB) hD_BD
  have hCA : SameSideOf C A G D :=
    SameSideOf.of_line hGD hG_BD hD_BD (pasch2 hBCA hB_BD hC_BD)
  -- the exterior angle CGB is equal to the interior and opposite angle ADB. [I. 29]
  have h29 : ∠ B G C = ∠ G D A := BookI.Prop29.exterior hGC_DA hCA hBGD
  have hGB : G ≠ B := (ne_of_between hBGD).symm
  have hCG : C ≠ G := ne_of_between hCGF
  have hCB : C ≠ B := (ne_of_between hBCA).symm
  have hAD : A ≠ D := hp.1.1
  have hCGB : ∠ C G B = ∠ A D B := by
    rw [angle_symm hCG hGB.symm, h29, angle_onRay_left (OnRay.of_between (between_symm hBGD)) hAD,
      angle_symm hBD hAD]
  -- But the angle ADB is equal to the angle ABD,
  -- since the side BA is also equal to AD; [I. 5]
  have h5 : ∠ A D B = ∠ A B D :=
    BookI.Prop5.base hBADE.triangle.bac.acb hsq.len_eq.symm
  -- therefore the angle CGB is also equal to the angle GBC,
  have hGBC : ∠ C G B = ∠ G B C := by
    rw [hCGB, h5, angle_eq_of_onRay (OnRay.of_between hBGD) (OnRay.of_between hBCA),
      angle_symm hAB hBD.symm]
  -- so that the side BC is also equal to the side CG. [I. 6]
  have hBC_CG : ‖C B‖ = ‖C G‖ := by
    have hCBG : Triangle C B G := hBCGK.triangle.bac
    exact BookI.Prop6 hCBG (by rw [angle_symm hCB hGB]; exact hGBC.symm)
  -- But CB is equal to GK, and CG to KB; [I. 34]
  obtain ⟨hCB_GK, hCG_BK, -, -, -⟩ :=
    BookI.Prop34 (A := C) (B := B) (C := G) (D := K) hBCGK.rotate
  -- therefore GK is also equal to KB;
  have hGK_KB : ‖G K‖ = ‖K B‖ := by
    rw [← hCB_GK, hBC_CG, hCG_BK, len_symm B K]
  -- therefore CGKB is equilateral.
  have hequil : ‖C G‖ = ‖G K‖ ∧ ‖G K‖ = ‖K B‖ ∧ ‖K B‖ = ‖B C‖ :=
    ⟨hBC_CG.symm.trans hCB_GK, hGK_KB,
      hGK_KB.symm.trans (hCB_GK.symm.trans (len_symm C B))⟩
  -- I say next that it is also right-angled.
  -- For, since CG is parallel to BK,
  -- the angles KBC, GCB are equal to two right angles. [I. 29]
  have h29' : ∠ K B C + ∠ B C G = ∟ + ∟ :=
    BookI.Prop29.interior hBCGK.2.symm.swap_left hBCGK.sameSideOf.symm
  -- But the angle KBC is right;
  have hKBC : ∠ K B C = ∟ := by
    rw [angle_eq_of_onRay (OnRay.of_between (between_symm hEKB)) (OnRay.of_between hBCA)]
    exact hsq.2.2.2.2.2.2
  -- therefore the angle BCG is also right,
  have hBCG : ∠ B C G = ∟ := by
    rw [hKBC, add_comm] at h29'
    exact CommonNotion3 h29' rfl
  -- so that the opposite angles CGK, GKB are also right. [I. 34]
  obtain ⟨-, -, hGCB_GKB, hCBK_CGK, -⟩ :=
    BookI.Prop34 (A := C) (B := B) (C := G) (D := K) hBCGK.rotate
  have hCGK : ∠ C G K = ∟ := by
    rw [← hCBK_CGK, angle_symm hCB (ne_of_between (between_symm hEKB)).symm]; exact hKBC
  have hGKB : ∠ G K B = ∟ := hGCB_GKB ▸ hBCG
  -- Therefore CGKB is right-angled;
  have hright : ∠ B C G = ∟ ∧ ∠ C G K = ∟ ∧ ∠ G K B = ∟ ∧ ∠ K B C = ∟ :=
    ⟨hBCG, hCGK, hGKB, hKBC⟩
  -- and it was also proved equilateral;
  -- therefore it is a square;
  have hCK : Square C G K B := ⟨hequil.1, hequil.2.1, hequil.2.2, hright⟩
  -- and it is described on CB.
  have hsq₁ : quadArea B C G K = sq C B := by
    rw [← hBCGK.quadArea_rotate, hCK.eq_sq hBCGK.rotate, sq_congr hBC_CG.symm]
  -- For the same reason
  -- HF is also a square;
  have hHF : Square D F G H :=
    hsq.rotate.about_diameter hp.rotate (between_symm hBGD) hDFE (between_symm hAHD)
      hGHDF.rotate.rotate
  -- and it is described on HG, that is AC. [I. 34]
  obtain ⟨hCAHG, -⟩ := hBADE.complements hBGD hBCA hAHD hDFE hEKB hBCGK hGHDF
  have hsq₂ : quadArea G H D F = sq A C := by
    rw [← quadArea_rotate₂ G H D F, hHF.eq_sq hGHDF.rotate.rotate]
    obtain ⟨-, hCA_GH, -, -, -⟩ := BookI.Prop34 (A := C) (B := G) (C := A) (D := H) hCAHG
    exact sq_congr ((hHF.1.trans hHF.2.1).trans (hCA_GH.symm.trans (len_symm C A)))
  -- Therefore the squares HF, KC are the squares on AC, CB.
  have hsquares : quadArea G H D F + quadArea B C G K = sq A C + sq C B := by
    rw [hsq₂, hsq₁]
  -- Now, since AG is equal to GE,
  have h43 : quadArea C A H G = quadArea K G F E :=
    BookI.Prop43 hBADE hBGD hBCA hAHD hDFE hEKB hBCGK hGHDF
  -- and AG is the rectangle AC, CB, for GC is equal to CB,
  have hAG : quadArea C A H G = rect A C C B := by
    have hG_AB : ¬ OnLine G AB := fun hG =>
      (hBCGK.triangle).off_line hB_AB hC_AB hG
    have hright : ∠ G C A = ∟ := by
      have h := hBCG
      rw [adjacent_eq_of_right hB_AB hA_AB hBCA hG_AB h] at h
      exact h
    exact (Rectangle.of_right hCAHG hright).eq_rect (len_symm C A) hBC_CG.symm
  -- therefore GE is also equal to the rectangle AC, CB.
  have hGE : quadArea K G F E = rect A C C B := h43 ▸ hAG
  -- Therefore AG, GE are equal to twice the rectangle AC, CB.
  have hrectangles : quadArea C A H G + quadArea K G F E = rect A C C B + rect A C C B := by
    rw [hAG, hGE]
  -- But the squares HF, CK are also the squares on AC, CB;
  -- therefore the four areas HF, CK, AG, GE are equal to the squares on AC, CB and twice the
  -- rectangle contained by AC, CB.
  have hfour : quadArea G H D F + quadArea B C G K +
      (quadArea C A H G + quadArea K G F E) =
      sq A C + sq C B + (rect A C C B + rect A C C B) := by
    rw [hsquares, hrectangles]
  -- But HF, CK, AG, GE are the whole ADEB,
  have hwhole := hBADE.about_diameter hBGD hBCA hAHD hDFE hEKB hBCGK hGHDF
  -- which is the square on AB.
  have hsqAB : quadArea B A D E = sq A B := hBADE.quadArea_rotate.symm.trans hADEB
  -- Therefore the square on AB is equal to the squares on AC, CB and twice the rectangle
  -- contained by AC, CB.
  calc
    sq A B = quadArea B A D E := hsqAB.symm
    _ =quadArea B C G K + quadArea C A H G + quadArea G H D F + quadArea K G F E := hwhole
    _ = quadArea G H D F + quadArea B C G K + (quadArea C A H G + quadArea K G F E) := by ac_rfl
    _ = sq A C + sq C B + (rect A C C B + rect A C C B) := hfour
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookII
