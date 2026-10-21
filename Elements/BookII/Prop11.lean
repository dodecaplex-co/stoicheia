import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop04
import Elements.BookI.Prop10
import Elements.BookI.Prop13
import Elements.BookI.Prop17
import Elements.BookI.Prop19
import Elements.BookI.Prop20
import Elements.BookI.Prop28
import Elements.BookI.Prop29
import Elements.BookI.Prop30
import Elements.BookI.Prop34
import Elements.BookI.Prop46
import Elements.BookI.Prop47
import Elements.BookI.HelpersParallels
import Elements.BookII.Prop06

/-!
# Book II, Proposition 11

Euclid's text, in Heath's translation: [`heath/II/11.md`](../../heath/II/11.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- To cut a given straight line so that the rectangle contained by the whole and one of the
segments is equal to the square on the remaining segment. -/
theorem Prop11 {A B : Point} (hAB : A ≠ B) :
    ∃ H : Point, Between A H B ∧ rect A B B H = sq A H := by
  -- Let AB be the given straight line;
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  -- thus it is required to cut AB so that the rectangle contained by the whole and one of the
  -- segments is equal to the square on the remaining segment.
  -- For let the square ABDC be described on AB; [I. 46]
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  obtain ⟨C, D, hsq, hC, hD⟩ := BookI.Prop46 hAB hP
  obtain ⟨hp, hAD⟩ := Square.described hsq hC hD
  have hAC : A ≠ C := hp.1.1
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hAC
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hp.1.2.1.symm
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hp.2.1
  have hAC_BD : Parallel AC BD := hp.1.parallel hA_AC hC_AC hD_BD hB_BD
  have hCD_AB : Parallel CD AB := hp.2.parallel hC_CD hD_CD hB_AB hA_AB
  have hB_AC : ¬ OnLine B AC := fun h => hAC_BD.not_onLine h hB_BD
  -- let AC be bisected at the point E, and let BE be joined;
  obtain ⟨E, hAEC, hAE⟩ := BookI.Prop10 hAC
  have hE_AC : OnLine E AC := on_line_of_between_ends hAEC hA_AC hC_AC
  have hAE' : A ≠ E := ne_of_between hAEC
  have hEB : E ≠ B := fun e => hB_AC (e ▸ hE_AC)
  have hAEB : Triangle A E B := Triangle.of_line hA_AC hE_AC hAE' hB_AC
  /- The angle at A is right. -/
  have hBAE : ∠ B A E = ∟ := by
    rw [angle_onRay_right (OnRay.of_between hAEC) hAB.symm]; exact hsq.2.2.2.1
  -- let CA be drawn through to F, and let EF be made equal to BE;
  /- EB is greater than EA: the angle ABE is less than a right angle [I. 17],
     and the greater angle is subtended by the greater side [I. 19]. -/
  have hABE : ∠ A B E < ∟ := by
    have h17 := (BookI.Prop17 hAEB.acb).2.2
    rw [angle_symm hAE'.symm hAB.symm, hBAE] at h17
    exact Magnitude.lt_of_add_lt_add_left h17
  have hEA_EB : ‖E A‖ < ‖E B‖ :=
    BookI.Prop19 hAEB.bac (by rw [angle_symm hAE'.symm hAB.symm, hBAE]; exact hABE)
  obtain ⟨F, hF, hEF⟩ := OnRay.exists_len_eq hEB hAE'.symm
  have hEAF : Between E A F :=
    OnRay.between_of_len_lt (OnRay.self hAE'.symm) hF (hEF ▸ hEA_EB)
  have hCAF : Between C A F :=
    between_symm (between_of_between_right (between_symm hEAF) hAEC)
  have hAF : A ≠ F := (ne_of_between (between_symm hCAF)).symm
  have hF_AC : OnLine F AC := on_line_of_between hCAF hC_AC hA_AC
  -- let the square FH be described on AF, and let GH be drawn through to K.
  obtain ⟨H, G, hsqF, hH, hG⟩ := BookI.Prop46 hAF (Triangle.of_line hA_AC hF_AC hAF hB_AC)
  obtain ⟨hpF, -⟩ := Square.described hsqF hH hG
  /- AH lies along AB: the angles FAH, FAB are right. -/
  have hFAB : ∠ F A B = ∟ := by
    have h := adjacent_eq_of_right hC_AC hF_AC hCAF hB_AC
      ((angle_symm hAC.symm hAB.symm).trans hsq.2.2.2.1)
    rw [angle_symm hAB.symm hAF.symm] at h
    exact h.symm.trans ((angle_symm hAC.symm hAB.symm).trans hsq.2.2.2.1)
  have hHray : OnRay H A B := onRay_of_angle_eq hH (hsqF.2.2.2.1.trans hFAB.symm)
  /- AF is less than AB [I. 20]. -/
  have hAF_AB : ‖A F‖ < ‖A B‖ := by
    have h20 := (BookI.Prop20 hAEB).1
    rw [← hEF, ← len_add_of_between hEAF] at h20
    exact Magnitude.lt_of_add_lt_add_left h20
  have hAHB : Between A H B :=
    OnRay.between_of_len_lt hHray (OnRay.self hAB) (hsqF.len_eq ▸ hAF_AB)
  have hH_AB : OnLine H AB := hHray.onLine hA_AB hB_AB
  obtain ⟨HG, hH_HG, hG_HG⟩ := Postulate1 H G hpF.2.1
  obtain ⟨GF, hG_GF, hF_GF⟩ := Postulate1 G F hpF.1.2.1
  have hHG_AC : Parallel HG AC := hpF.2.parallel hH_HG hG_HG hF_AC hA_AC
  have hAB_GF : Parallel AB GF := hpF.1.parallel hA_AB hH_AB hG_GF hF_GF
  have hHG_AB : HG ≠ AB := fun e => hAB_GF.not_onLine (e ▸ hG_HG) hG_GF
  obtain ⟨K, hK_HG, hK_CD⟩ := BookI.Prop30.meet hCD_AB hH_AB hH_HG hHG_AB
  have hCF : C ≠ F := ne_of_between_ends hCAF
  have hGF_CD : Parallel GF CD := BookI.Prop30.parallel hAB_GF.symm hCD_AB fun e =>
    hCD_AB.not_onLine ((line_unique hCF hC_AC hF_AC hC_CD (e ▸ hF_GF)) ▸ hA_AC) hA_AB
  have hGHK : Between G H K := Parallel.between hAB_GF.symm hCD_AB hF_GF hA_AB hC_CD
    (between_symm hCAF) hG_GF hH_AB hK_CD ⟨HG, hG_HG, hH_HG, hK_HG⟩
  have hHB : H ≠ B := (ne_of_between (between_symm hAHB)).symm
  have hBD_HG : Parallel BD HG := BookI.Prop30.parallel hAC_BD.symm hHG_AC fun e =>
    hAC_BD.not_onLine hA_AC ((line_unique hHB hH_AB hB_AB (e ▸ hH_HG) hB_BD) ▸ hA_AB)
  have hCKD : Between C K D := Parallel.between hHG_AC.symm hBD_HG hA_AC hH_HG hB_BD
    hAHB hC_AC hK_HG hD_BD ⟨CD, hC_CD, hK_CD, hD_CD⟩
  have hAH : A ≠ H := ne_of_between hAHB
  have hHK : H ≠ K := (ne_of_between (between_symm hGHK)).symm
  have hKC : K ≠ C := (ne_of_between hCKD).symm
  have hKD : K ≠ D := (ne_of_between (between_symm hCKD)).symm
  have hGK : G ≠ K := ne_of_between_ends hGHK
  have hFG : F ≠ G := hpF.1.2.1.symm
  /- The squares and the parallels bound the rectangles used below. -/
  have hFGHA : Parallelogram F G H A := hpF.reverse.rotate
  have hAHKC : Parallelogram A H K C :=
    ⟨AreParallel.of_parallel hAH hKC hA_AB hH_AB hK_CD hC_CD hCD_AB.symm,
      AreParallel.of_parallel hHK hAC.symm hH_HG hK_HG hC_AC hA_AC hHG_AC⟩
  have hFGKC : Parallelogram F G K C :=
    ⟨AreParallel.of_parallel hFG hKC hF_GF hG_GF hK_CD hC_CD hGF_CD,
      AreParallel.of_parallel hGK hCF hG_HG hK_HG hC_AC hF_AC hHG_AC⟩
  have hACKH : Parallelogram A C K H := hAHKC.reverse
  have hHKDB : Parallelogram H K D B :=
    ⟨AreParallel.of_parallel hHK hp.1.2.1 hH_HG hK_HG hD_BD hB_BD hBD_HG.symm,
      AreParallel.of_parallel hKD hHB.symm hK_CD hD_CD hB_AB hH_AB hCD_AB⟩
  -- I say that AB has been cut at H so as to make the rectangle contained by AB, BH equal to
  -- the square on AH.
  refine ⟨H, hAHB, ?_⟩
  -- For, since the straight line AC has been bisected at E, and FA is added to it,
  -- the rectangle contained by CF, FA together with the square on AE is equal to the square on
  -- EF. [II. 6]
  have h6 : rect C F F A + sq A E = sq E F := by
    rw [← sq_symm E A]
    exact Prop6 (between_symm hAEC) (by rw [len_symm C E, len_symm E A]; exact hAE.symm) hCAF
  -- But EF is equal to EB;
  have hEFsq : sq E F = sq E B := sq_congr hEF
  -- therefore the rectangle CF, FA together with the square on AE is equal to the square on
  -- EB.
  rw [hEFsq] at h6
  -- But the squares on BA, AE are equal to the square on EB, for the angle at A is
  -- right; [I. 47]
  have h47 : sq E B = sq B A + sq A E := (sq_symm E B).trans (BookI.Prop47.sq hAEB.acb hBAE)
  -- therefore the rectangle CF, FA together with the square on AE is equal to the squares on
  -- BA, AE.
  rw [h47] at h6
  -- Let the square on AE be subtracted from each;
  have hremBA : rect C F F A = sq B A := CommonNotion3 h6 rfl
  -- therefore the rectangle CF, FA which remains is equal to the square on AB.
  have hrem : rect C F F A = sq A B := hremBA.trans (sq_symm B A)
  -- Now the rectangle CF, FA is FK, for AF is equal to FG;
  have hFK : quadArea F G K C = rect C F F A := by
    rw [← quadArea_reverse F G K C]
    refine (Rectangle.of_right hFGKC.reverse ?_).eq_rect (len_symm F C) ?_
    · rw [← angle_onRay_right (OnRay.of_between (between_symm hCAF)) hFG.symm]
      exact hsqF.2.2.2.2.2.2
    · rw [len_symm F G]; exact hsqF.2.2.1
  -- and the square on AB is AD;
  have hsqAB : sq A B = quadArea A C D B := hAD.symm
  -- therefore FK is equal to AD.
  have hFK_AD : quadArea F G K C = quadArea A C D B := (hFK.trans hrem).trans hsqAB
  -- Let AK be subtracted from each;
  have hcut₁ := quadArea_add_of_parallelograms hFGHA hAHKC (between_symm hCAF) hGHK
  have hcut₂ := quadArea_add_of_parallelograms hACKH hHKDB hAHB hCKD
  rw [quadArea_reverse A H K C] at hcut₂
  -- therefore FH which remains is equal to HD.
  have hFH_HD : quadArea F G H A = quadArea H K D B := by
    rw [hcut₁, hcut₂, add_comm (quadArea A H K C)] at hFK_AD
    exact CommonNotion3 hFK_AD rfl
  -- And HD is the rectangle AB, BH, for AB is equal to BD;
  have hHD : quadArea H K D B = rect A B B H := by
    rw [← hHKDB.quadArea_rotate, ← quadArea_rotate₂ K D B H, ← quadArea_reverse B H K D]
    refine (Rectangle.of_right hHKDB.rotate.rotate.rotate.reverse ?_).eq_rect ?_ rfl
    · rw [angle_onRay_left (OnRay.of_between (between_symm hAHB)) hp.1.2.1]
      rw [angle_symm hAB hp.1.2.1]; exact hsq.2.2.2.2.2.2
    · rw [len_symm B D, len_symm A B]; exact hsq.2.2.1
  -- and FH is the square on AH;
  have hFH : quadArea F G H A = sq A H := by
    rw [hpF.reverse.quadArea_rotate, quadArea_reverse A H G F]
    exact Square.eq_sq hsqF hpF
  -- therefore the rectangle contained by AB, BH is equal to the square on HA.
  have hresult : rect A B B H = sq H A := by
    rw [← hHD, ← hFH_HD, hFH, sq_symm A H]
  -- therefore the given straight line AB has been cut at H so as to make the rectangle
  -- contained by AB, BH equal to the square on HA.
  exact hresult.trans (sq_symm H A)
  -- Q. E. F.

end Elements.BookII
