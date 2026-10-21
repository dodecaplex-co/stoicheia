import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.HelpersParallels
import Elements.BookI.Prop13
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop36
import Elements.BookI.Prop43
import Elements.BookI.Prop46

/-!
# Book II, Proposition 5

Euclid's text, in Heath's translation: [`heath/II/05.md`](../../heath/II/05.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut into equal and unequal segments, the rectangle contained by the
unequal segments of the whole together with the square on the straight line between the points
of section is equal to the square on the half. -/
theorem Prop5 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖) (hADB : Between A D B)
    (hDC : D ≠ C) :
    rect A D D B + sq C D = sq C B := by
  -- For let a straight line AB be cut into equal segments at C and into unequal segments at D;
  -- I say that the rectangle contained by AD, DB together with the square on CD is equal to
  -- the square on CB.
  /- Euclid's figure puts D between C and B; the other side is the same with A
     and B exchanged. -/
  have euclid : ∀ {A B C D : Point}, Between A C B → ‖A C‖ = ‖C B‖ → Between C D B →
      rect A D D B + sq C D = sq C B := by
    intro A B C D hACB hAC hCDB
    have hCB : C ≠ B := ne_of_between_ends hCDB
    -- For let the square CEFB be described on CB, [I. 46]
    obtain ⟨X, hX, -⟩ := exists_off_line hCB []
    obtain ⟨E, F, hsq, hE, hF⟩ := BookI.Prop46 hCB hX
    obtain ⟨hp, hCEFB⟩ := Square.described hsq hE hF
    -- and let BE be joined;
    -- through D let DG be drawn parallel to either CE or BF,
    -- through H again let KM be drawn parallel to either AB or EF,
    obtain ⟨G, H, L, M, hBHE, hEGF, hCLE, hFMB, hDHG, hLHM, hBDHM, hHLEG⟩ := hp.figure hCDB
    -- and again through A let AK be drawn parallel to either CL or BM. [I. 31]
    obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B (ne_of_between_ends hACB)
    have hC_AB : OnLine C AB := on_line_of_between_ends hACB hA_AB hB_AB
    have hD_AB : OnLine D AB := on_line_of_between_ends hCDB hC_AB hB_AB
    obtain ⟨KM, hL_KM, hM_KM⟩ := Postulate1 L M (ne_of_between_ends hLHM)
    have hH_KM : OnLine H KM := on_line_of_between_ends hLHM hL_KM hM_KM
    have hKM_AB : Parallel KM AB := (hBDHM.1.parallel hB_AB hD_AB hH_KM hM_KM).symm
    obtain ⟨K, hK_KM, hLCAK⟩ :=
      BookI.Prop31.parallelogram hKM_AB hL_KM hC_AB hA_AB (ne_of_between hACB).symm
    -- Then, since the complement CH is equal to the complement HF, [I. 43]
    have hBCEF : Parallelogram B C E F := hp.rotate.rotate.rotate
    have hBDC : Between B D C := between_symm hCDB
    have h43 : quadArea D C L H = quadArea M H G F :=
      BookI.Prop43 hBCEF hBHE hBDC hCLE hEGF hFMB hBDHM hHLEG
    obtain ⟨hDCLH, hMHGF⟩ := hBCEF.complements hBHE hBDC hCLE hEGF hFMB hBDHM hHLEG
    -- let DM be added to each;
    have hadd := CommonNotion2 h43 (rfl : quadArea B D H M = quadArea B D H M)
    -- therefore the whole CM is equal to the whole DF.
    have hCM : quadArea L C B M = quadArea L C D H + quadArea H D B M :=
      quadArea_add_of_parallelograms hDCLH.rotate.rotate.reverse hBDHM.rotate.rotate.reverse hLHM
        hCDB
    have hDF : quadArea D B F G = quadArea D B M H + quadArea H M F G :=
      quadArea_add_of_parallelograms hBDHM.rotate.reverse hMHGF.rotate.reverse hDHG
        (between_symm hFMB)
    have hCM_DF : quadArea L C B M = quadArea D B F G := by
      rw [hCM, hDF, quadArea_reverse L H D C, hDCLH.rotate.quadArea_rotate, hDCLH.quadArea_rotate,
        quadArea_reverse H M B D, hBDHM.rotate.quadArea_rotate, hBDHM.quadArea_rotate,
        quadArea_reverse D H M B, hBDHM.quadArea_rotate, quadArea_reverse H G F M,
        hMHGF.quadArea_rotate]
      exact hadd.trans (add_comm _ _)
    -- But CM is equal to AL,
    -- since AC is also equal to CB; [I. 36]
    obtain ⟨CE, hC_CE, hE_CE⟩ := Postulate1 C E hp.1.1
    obtain ⟨BF, hB_BF, hF_BF⟩ := Postulate1 B F hp.1.2.1.symm
    have hL_CE : OnLine L CE := on_line_of_between_ends hCLE hC_CE hE_CE
    have hM_BF : OnLine M BF := on_line_of_between_ends hFMB hF_BF hB_BF
    have hCE_BF : Parallel CE BF := hp.1.parallel hC_CE hE_CE hF_BF hB_BF
    have hLCBM : Parallelogram L C B M :=
      ⟨AreParallel.of_parallel (ne_of_between hCLE).symm (ne_of_between (between_symm hFMB))
          hL_CE hC_CE hB_BF hM_BF hCE_BF,
        AreParallel.of_parallel hCB (ne_of_between_ends hLHM).symm hC_AB hB_AB hM_KM hL_KM
          hKM_AB.symm⟩
    have h36 : quadArea L C B M = quadArea K A C L :=
      BookI.Prop36 hLCBM hLCAK.rotate.rotate.rotate.reverse hAC.symm
        ⟨KM, hL_KM, hM_KM, hK_KM, hL_KM⟩ ⟨AB, hC_AB, hB_AB, hA_AB, hC_AB⟩
    -- therefore AL is also equal to DF.
    have hAL_DF : quadArea K A C L = quadArea D B F G := CommonNotion1 h36.symm hCM_DF.symm
    -- Let CH be added to each;
    have hadd₂ := CommonNotion2 hAL_DF (rfl : quadArea D C L H = quadArea D C L H)
    -- therefore the whole AH is equal to the gnomon NOP.
    /- AH is AL and CH together: C lies between A and D, and L between K and H,
       the parallels AK, CL, DH keeping order. -/
    have hACD : Between A C D := between_cut hACB hCDB
    obtain ⟨AK, hA_AK, hK_AK⟩ := Postulate1 A K hLCAK.1.2.1
    obtain ⟨DG, hD_DG, hG_DG⟩ := Postulate1 D G (ne_of_between_ends hDHG)
    have hH_DG : OnLine H DG := on_line_of_between_ends hDHG hD_DG hG_DG
    have hAK_CE : Parallel AK CE := (hLCAK.1.parallel hL_CE hC_CE hA_AK hK_AK).symm
    have hDG_CE : Parallel DG CE := (hDCLH.2.parallel hC_CE hL_CE hH_DG hD_DG).symm
    have hKLH : Between K L H := Parallel.between hAK_CE hDG_CE hA_AK hC_CE hD_DG hACD hK_AK
      hL_CE hH_DG ⟨KM, hK_KM, hL_KM, hH_KM⟩
    have hAH : quadArea A K H D = quadArea A K L C + quadArea C L H D :=
      quadArea_add_of_parallelograms hLCAK.rotate.rotate hDCLH.rotate hACD hKLH
    have hgnomon : quadArea A K H D = quadArea D C L H + quadArea B D H M + quadArea M H G F := by
      calc
        quadArea A K H D = quadArea K A C L + quadArea D C L H := by
          rw [hAH, ← hLCAK.rotate.rotate.quadArea_rotate, quadArea_reverse K A C L,
            hDCLH.quadArea_rotate]
        _ = quadArea D B F G + quadArea D C L H := hadd₂
        _ = quadArea D C L H + quadArea B D H M + quadArea M H G F := by
          rw [hDF, quadArea_reverse D H M B, hBDHM.quadArea_rotate,
            quadArea_reverse H G F M, hMHGF.quadArea_rotate]
          ac_rfl
    -- But AH is the rectangle AD, DB, for DH is equal to DB,
    have hDM : Square B D H M :=
      hsq.rotate.rotate.rotate.about_diameter hBCEF hBHE hBDC (between_symm hFMB) hBDHM
    have hDH_DB : ‖D H‖ = ‖D B‖ := hDM.1.symm.trans (len_symm B D)
    have hAD : A ≠ D := ne_of_between_ends hACD
    have hAK_DG : Parallel AK DG := BookI.Prop30.parallel hAK_CE hDG_CE fun e => by
      have hAB_DG : AB = DG := line_unique hAD hA_AB hD_AB (e ▸ hA_AK) hD_DG
      exact hKM_AB.not_onLine hH_KM (hAB_DG ▸ hH_DG)
    have hDAKH : Parallelogram D A K H :=
      ⟨AreParallel.of_parallel hAD.symm (ne_of_between_ends hKLH) hD_AB hA_AB hK_KM hH_KM
          hKM_AB.symm,
        AreParallel.of_parallel hLCAK.1.2.1 (ne_of_between hDHG).symm hA_AK hK_AK hH_DG hD_DG
          hAK_DG⟩
    have hH_AB : ¬ OnLine H AB := fun h => hKM_AB.not_onLine hH_KM h
    have hright : ∠ H D A = ∟ := by
      have h := hDM.2.2.2.2.1
      rw [adjacent_eq_of_right hB_AB hA_AB (between_of_between_left (between_symm hACB) hBDC)
        hH_AB h] at h
      exact h
    have hAHrect : quadArea D A K H = rect A D D B :=
      (Rectangle.of_right hDAKH hright).eq_rect (len_symm D A) hDH_DB
    -- therefore the gnomon NOP is also equal to the rectangle AD, DB.
    have hNOP : quadArea D C L H + quadArea B D H M + quadArea M H G F = rect A D D B :=
      (hgnomon.symm.trans hDAKH.quadArea_rotate).trans hAHrect
    -- Let LG, which is equal to the square on CD, be added to each;
    have hLG : Square E G H L :=
      hsq.rotate.about_diameter hp.rotate (between_symm hBHE) hEGF (between_symm hCLE)
        hHLEG.rotate.rotate
    obtain ⟨-, hDC_HL, -, -, -⟩ := BookI.Prop34 (A := D) (B := H) (C := C) (D := L) hDCLH
    have hLGsq : quadArea H L E G = sq C D := by
      rw [quadArea_rotate₂ E G H L, hLG.eq_sq hHLEG.rotate.rotate]
      exact sq_congr ((hLG.1.trans hLG.2.1).trans (hDC_HL.symm.trans (len_symm D C)))
    -- therefore the gnomon NOP and LG are equal to the rectangle contained by AD, DB and the
    -- square on CD.
    have hadd₃ := CommonNotion2 hNOP hLGsq
    -- But the gnomon NOP and LG are the whole square CEFB, which is described on CB;
    have hwhole := hBCEF.about_diameter hBHE hBDC hCLE hEGF hFMB hBDHM hHLEG
    -- therefore the rectangle contained by AD, DB together with the square on CD is equal to the
    -- square on CB.
    rw [← hadd₃, ← hCEFB, hBCEF.quadArea_rotate, hwhole]
    ac_rfl
  /- D falls between A and C, or between C and B, for it cannot be C itself, the
     segments being unequal. The second is Euclid's case; for the first we exchange
     A and B. -/
  have hCray : OnRay C A B := OnRay.of_between hACB
  have hDray : OnRay D A B := OnRay.of_between hADB
  rcases lt_trichotomy ‖A D‖ ‖A C‖ with h | h | h
  · have hADC : Between A D C := hDray.between_of_len_lt hCray h
    have := euclid (between_symm hACB) (by rw [len_symm B C, len_symm C A]; exact hAC.symm)
      (between_symm hADC)
    rw [rect_comm, rect_congr (len_symm D A) (len_symm B D),
      sq_congr ((len_symm C A).trans hAC)] at this
    exact this
  · obtain ⟨AB, hA, hB⟩ := Postulate1 A B (ne_of_between_ends hACB)
    have hDray' : OnRay D A C := ⟨ne_of_between hACB, (ne_of_between hADB).symm,
      ⟨AB, hA, on_line_of_between_ends hACB hA hB, on_line_of_between_ends hADB hA hB⟩,
      hDray.not_between hCray⟩
    exact absurd (hDray'.eq_of_len_eq h) hDC
  · exact euclid hACB hAC (between_inner (hCray.between_of_len_lt hDray h) hADB)
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookII
