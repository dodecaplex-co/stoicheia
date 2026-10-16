import Elements.Figure.Basics
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop38
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 40

Euclid's text, in Heath's translation: [`heath/I/40.md`](../../heath/I/40.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Equal triangles which are on equal bases and on the same side are also in the same parallels. -/
theorem Prop40 {A B C D E : Point} (hABC : Triangle A B C) (hCDE : Triangle C D E)
    (hBCE : Between B C E) (hbase : ‖B C‖ = ‖C E‖) (heq : △ A B C = △ C D E)
    (hside : SameSideOf A D B E) (hAD : A ≠ D) :
    AreParallel A D B E := by
  -- Let ABC, CDE be equal triangles on equal bases BC, CE and on the same side.
  have hBE : B ≠ E := ne_of_between_ends hBCE
  obtain ⟨BE, hB, hE⟩ := Postulate1 B E hBE
  have hC : OnLine C BE := on_line_of_between_ends hBCE hB hE
  have hA_BE : ¬ OnLine A BE := hABC.bca.off_line hB hC
  have hD_BE : ¬ OnLine D BE := hCDE.acb.off_line hC hE
  -- I say that they are also in the same parallels.
  -- For let AD be joined;
  /- The parallel drawn through A will pass through D, and so be AD. -/
  -- I say that AD is parallel to BE.
  -- For, if not, let AF be drawn through A parallel to BE [I. 31], and let FE be joined.
  /- U and V name the unlettered ends of the straight line supplied by I.31;
     K is that straight line. F is where it meets CD, by I.30. -/
  obtain ⟨U, V, hUAV, hUV⟩ := Prop31 hBE (Triangle.of_line hB hE hBE hA_BE)
  obtain ⟨K, hU_K, hV_K⟩ := Postulate1 U V hUV.1
  have hA_K : OnLine A K := on_line_of_between_ends hUAV hU_K hV_K
  have hKBE : Parallel K BE := hUV.parallel hU_K hV_K hB hE
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hCDE.ne₁₂
  obtain ⟨F, hF_CD, hF_K⟩ :=
    Prop30.meet hKBE hC hC_CD (fun e => hD_BE (e ▸ hD_CD))
  have hF_BE : ¬ OnLine F BE := hKBE.not_onLine hF_K
  have hFCE : Triangle F C E := (Triangle.of_line hC hE hCDE.ne₁₃ hF_BE).cab
  -- Therefore the triangle ABC is equal to the triangle FCE; for they are on equal bases BC,
  -- CE and in the same parallels BE, AF. [I. 38]
  have h38 : △ A B C = △ F C E :=
    Prop38 hABC hFCE hbase ⟨K, BE, hKBE, hA_K, hF_K, hB, hC, hC, hE⟩
  -- But the triangle ABC is equal to the triangle DCE; therefore the triangle DCE is also
  -- equal to the triangle FCE, [C.N. 1] the greater to the less: which is impossible.
  have h1 : △ D C E = △ F C E :=
    CommonNotion1 ((area_bac C D E).symm.trans heq.symm) h38.symm
  /- F and D lie on the same side of CE, which is the straight line BE.
     Thus F lies on the ray from C through D. -/
  have hFD_side : SameSideOf F D C E :=
    SameSideOf.of_line hCDE.ne₁₃ hC hE
      (((SameSideOf.of_line hBE hB hE (hKBE.sameSide hF_K hA_K)).trans hside).sameSide hB hE)
  have hray : OnRay F C D :=
    OnRay.of_sameSideOf hFD_side ⟨CD, hC_CD, hD_CD, hF_CD⟩ (fun e => hF_BE (e ▸ hC))
  have hFD : F = D := by
    rcases lt_trichotomy ‖C F‖ ‖C D‖ with hlt | heq' | hgt
    · /- Euclid's case: F lies between C and D. -/
      have hCFD : Between C F D :=
        hray.between_of_len_lt (OnRay.self hCDE.ne₁₂) hlt
      have hless := area_lt_of_cut hCDE.cab hCFD
      rw [← area_cba F C E, ← area_cba D C E, h1] at hless
      exact absurd rfl (Magnitude.ne_of_lt hless)
    · exact hray.eq_of_len_eq heq'
    · /- F beyond D: DCE is now the part and FCE the whole. -/
      have hCDF : Between C D F :=
        (OnRay.self hCDE.ne₁₂).between_of_len_lt hray hgt
      have hless := area_lt_of_cut hFCE.cba hCDF
      rw [← area_cba F C E, ← area_cba D C E, h1] at hless
      exact absurd rfl (Magnitude.ne_of_lt hless)
  -- Therefore AF is not parallel to BE.
  /- A parallel meeting CD away from D has been excluded: the parallel
     through A must pass through D itself. -/
  have hD_K : OnLine D K := hFD ▸ hF_K
  -- Similarly we can prove that neither is any other straight line except AD; therefore AD is
  -- parallel to BE.
  have hpar : AreParallel A D B E := AreParallel.of_parallel hAD hBE hA_K hD_K hB hE hKBE
  -- Therefore etc.
  exact hpar
  -- Q. E. D.]

end Elements.BookI
