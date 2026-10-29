import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop04

/-!
# Book I, Proposition 5

Euclid's text, in Heath's translation: [`heath/I/05.md`](../../heath/I/05.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- In isosceles triangles the angles at the base are equal to one another, and, if the equal
straight lines be produced further, the angles under the base will be equal to one another. -/
theorem Prop5 {A B C D E : Point} (hABC : Triangle A B C) (hAB : ‖A B‖ = ‖A C‖)
    (hD : Between A B D) (hE : Between A C E) :
    ∠ A B C = ∠ A C B ∧ ∠ C B D = ∠ B C E := by
  -- Let ABC be an isosceles triangle having the side AB equal to the side AC;
  have hA_B : A ≠ B := hABC.ne₁₂
  have hB_C : B ≠ C := hABC.ne₂₃
  have hA_C : A ≠ C := hABC.ne₁₃
  -- and let the straight lines BD, CE be produced further in a straight line with AB,
  -- AC. [Post. 2]
  /- The statement hands us D and E already produced, so this step names AB and AC
     without producing them. The proof still rests on Postulate 2 through proved rules:
     `OnRay.between_of_len_lt` below reaches it through `between_of_between_right`.
     Since ABC is a triangle, C is off AB, and B is off AC. -/
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hA_B
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hA_C
  have hC_AB : ¬ OnLine C AB := fun h => hABC ⟨AB, hA_AB, hB_AB, h⟩
  have hB_AC : ¬ OnLine B AC := fun h => hABC ⟨AC, hA_AC, h, hC_AC⟩
  have hE_AC : OnLine E AC := on_line_of_between hE hA_AC hC_AC
  -- I say that the angle ABC is equal to the angle ACB, and the angle CBD to the angle BCE.
  -- Let a point F be taken at random on BD;
  /- At random, but not too far out, for in the next breath AE is "the greater" and
     AF "the less". AB, being equal to AC, is less than AE, so F can be taken nearer
     to A than E is (`exists_between_nearer` in Book Zero, with a circle about A
     through E). Then F lies beyond B on the straight line AB. -/
  have hAB_AE : ‖A B‖ < ‖A E‖ := by
    rw [hAB]
    exact len_lt_of_between hE
  obtain ⟨F, hBFD, hAF_AE⟩ :=
    exists_between_nearer (ne_of_between (between_symm hD)).symm (Or.inr hD) hAB_AE
  have hABF : Between A B F := between_cut hD hBFD
  have hF_AB : OnLine F AB := on_line_of_between hABF hA_AB hB_AB
  have hA_F : A ≠ F := ne_of_between_ends hABF
  -- from AE the greater let AG be cut off equal to AF the less; [I. 3]
  obtain ⟨G, hAGE, hAG_AF⟩ := Prop3 hA_F hAF_AE
  have hG_AC : OnLine G AC := on_line_of_between_ends hAGE hA_AC hE_AC
  have hA_G : A ≠ G := ne_of_between hAGE
  -- and let the straight lines FC, GB be joined. [Post. 1]
  /- FC and GB are named by their ends, as sides of the triangles AFC and AGB, so
     nothing is drawn for the joins. -/
  -- Then, since AF is equal to AG and AB to AC,
  have hAF_AG : ‖A F‖ = ‖A G‖ := hAG_AF.symm
  -- the two sides FA, AC are equal to the two sides GA, AB, respectively;
  have hAC_AB : ‖A C‖ = ‖A B‖ := hAB.symm
  -- and they contain a common angle, the angle FAG.
  /- Common, because B lies on AF and C lies on AG. For C that takes a word Euclid
     does not say: AG, being equal to AF, is greater than AB, that is, than AC; so G
     lies beyond C. -/
  have hAB_AF : ‖A B‖ < ‖A F‖ := by
    rw [← len_add_of_between hABF]
    exact CommonNotion5 (len_pos (ne_of_between hBFD))
  have hACG : Between A C G :=
    (OnRay.of_between hE).between_of_len_lt (OnRay.of_between hAGE)
      (by rw [hAC_AB, ← hAF_AG]; exact hAB_AF)
  have hFAC_GAB : ∠ F A C = ∠ G A B := by
    rw [angle_onRay_left (OnRay.of_beyond hABF) hA_C.symm, angle_symm hA_B.symm hA_C.symm,
      angle_onRay_left (OnRay.of_beyond hACG) hA_B.symm]
  -- Therefore the base FC is equal to the base GB,
  have hAFC : Triangle A F C := Triangle.of_line hA_AB hF_AB hA_F hC_AB
  have hAGB : Triangle A G B := Triangle.of_line hA_AC hG_AC hA_G hB_AC
  have hI4 := Prop4 hAFC hAGB hAF_AG hAC_AB hFAC_GAB
  have hFC_GB : ‖F C‖ = ‖G B‖ := hI4.1
  -- and the triangle AFC is equal to the triangle AGB,
  have : △ A F C = △ A G B := hI4.2.1
  -- and the remaining angles will be equal to the remaining angles respectively, namely those
  -- which the equal sides subtend,
  -- that is, the angle ACF to the angle ABG,
  have hACF_ABG : ∠ A C F = ∠ A B G := hI4.2.2.2
  -- and the angle AFC to the angle AGB. [I. 4]
  have hAFC_AGB : ∠ A F C = ∠ A G B := hI4.2.2.1
  -- And, since the whole AF is equal to the whole AG,
  have hAB_BF : ‖A B‖ + ‖B F‖ = ‖A F‖ := len_add_of_between hABF
  have hAC_CG : ‖A C‖ + ‖C G‖ = ‖A G‖ := len_add_of_between hACG
  -- and in these AB is equal to AC,
  -- the remainder BF is equal to the remainder CG.
  have hBF_CG : ‖B F‖ = ‖C G‖ := by
    apply CommonNotion3 (c := ‖A B‖) (d := ‖A C‖) _ hAB
    rw [add_comm, hAB_BF, hAF_AG, ← hAC_CG, add_comm]
  -- But FC was also proved equal to GB;
  -- therefore the two sides BF, FC are equal to the two sides CG, GB respectively;
  have hFB_GC : ‖F B‖ = ‖G C‖ := by rw [len_symm F B, hBF_CG, len_symm C G]
  -- and the angle BFC is equal to the angle CGB,
  /- These are the angles AFC and AGB over again, since B lies on FA and C on GA. -/
  have hF_C : F ≠ C := fun h => hC_AB (h ▸ hF_AB)
  have hG_B : G ≠ B := fun h => hB_AC (h ▸ hG_AC)
  have hBFC_CGB : ∠ B F C = ∠ C G B := by
    rw [← angle_onRay_left (OnRay.of_beyond (between_symm hABF)) hF_C.symm,
      ← angle_onRay_left (OnRay.of_beyond (between_symm hACG)) hG_B.symm]
    exact hAFC_AGB
  -- while the base BC is common to them;
  /- Euclid is quoting I.4 ahead of time, as Heath explains: the bases are equal
     because they are one and the same base. -/
  -- therefore the triangle BFC is also equal to the triangle CGB,
  have hFBC : Triangle F B C :=
    Triangle.of_line hF_AB hB_AB (ne_of_between (between_symm hABF)) hC_AB
  have hGCB : Triangle G C B :=
    Triangle.of_line hG_AC hC_AC (ne_of_between (between_symm hACG)) hB_AC
  have hI4' := Prop4 hFBC hGCB hFB_GC hFC_GB hBFC_CGB
  have : △ B F C = △ C G B := by
    rw [← area_rotate F C B, ← area_swap F B C, hI4'.2.1, area_swap G C B, area_rotate G B C]
  -- and the remaining angles will be equal to the remaining angles respectively, namely those
  -- which the equal sides subtend;
  -- therefore the angle FBC is equal to the angle GCB,
  have hFBC_GCB : ∠ F B C = ∠ G C B := hI4'.2.2.1
  -- and the angle BCF to the angle CBG.
  have hBCF_CBG : ∠ B C F = ∠ C B G := by
    rw [angle_symm hB_C hF_C, angle_symm hB_C.symm hG_B]
    exact hI4'.2.2.2
  -- Accordingly, since the whole angle ABG was proved equal to the angle ACF,
  /- Whole, because C lies between A and G, so that BC falls within the angle ABG;
     likewise B lies between A and F, so that CB falls within the angle ACF. -/
  have hABG : ∠ A B G = ∠ A B C + ∠ C B G :=
    angle_add_of_between hAGB hACG
  have hACF : ∠ A C F = ∠ A C B + ∠ B C F :=
    angle_add_of_between hAFC hABF
  -- and in these the angle CBG is equal to the angle BCF,
  -- the remaining angle ABC is equal to the remaining angle ACB;
  have hbase : ∠ A B C = ∠ A C B := by
    apply CommonNotion3 (c := ∠ C B G) (d := ∠ B C F) _ hBCF_CBG.symm
    rw [← hABG, ← hACF, hACF_ABG]
  -- and they are at the base of the triangle ABC.
  -- But the angle FBC was also proved equal to the angle GCB;
  -- and they are under the base.
  /- Under the base: the angle CBD is the angle CBF, since F lies on BD, and the angle
     BCE is the angle BCG, since G lies between C and E. -/
  have hCGE : Between C G E := between_inner hACG hAGE
  have hunder : ∠ C B D = ∠ B C E := by
    rw [angle_symm hB_C.symm (ne_of_between (between_symm hD)),
      angle_onRay_left (OnRay.of_beyond hBFD) hB_C.symm, hFBC_GCB,
      ← angle_onRay_left (OnRay.of_beyond hCGE) hB_C,
      angle_symm (ne_of_between (between_symm hE)) hB_C]
  -- Therefore etc.
  exact ⟨hbase, hunder⟩
  -- Q. E. D.

end Elements.BookI
