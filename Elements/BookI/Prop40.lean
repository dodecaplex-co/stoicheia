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

`Prop40` is Euclid's worked configuration: the bases BC, CE meet end to end, as in his
figure. His words, "equal triangles which are on equal bases and on the same side", put the
bases anywhere on one straight line, and so do the companions after it: `Prop40.general`,
for equal bases anywhere on one straight line, by Euclid's argument; `Prop40.join`, that AD
is parallel to the bases when A and D are two points; and `Prop40.special`, the statement
of `Prop40` again, derived from the general one.
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
  /- AD names the straight line through the distinct vertices A and D; that it is
     parallel to BE remains to be proved. -/
  -- I say that AD is parallel to BE.
  have hpar : AreParallel A D B E := by
    -- For, if not, let AF be drawn through A parallel to BE [I. 31], and let FE be joined.
    refine Classical.byContradiction fun hnot => ?_
    /- The parallel through A is the straight line K (`Prop31.line`), and F is where
       it meets CD (`Prop30.meet`). FE is named by its ends, as a side of the
       triangle FCE, so nothing is drawn for the join. -/
    obtain ⟨K, hA_K, hKBE⟩ := Prop31.line hA_BE
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
    /- If F were D, the parallel through A would be AD, contrary to the supposition. -/
    have hFD : F ≠ D := fun e => hnot
      (AreParallel.of_parallel hAD hBE hA_K (e ▸ hF_K) hB hE hKBE)
    have hCF : C ≠ F := fun e => hF_BE (e ▸ hC)
    /- Euclid's case has F between C and D, making FCE less than DCE.
       Beyond D, DCE is less than FCE. The same-side condition excludes the opposite ray. -/
    rcases between_cases hCF hFD hCDE.ne₁₂ hC_CD hF_CD hD_CD with h | h | h
    · have hless := area_lt_of_cut hCDE.bac.cba h
      rw [← area_cba F C E, ← area_cba D C E] at hless
      exact Magnitude.ne_of_lt hless h1.symm
    · exact hray.2.2.2 h
    · have hless := area_lt_of_cut hFCE.cba h
      rw [← area_cba D C E, ← area_cba F C E] at hless
      exact Magnitude.ne_of_lt hless h1
  -- Therefore AF is not parallel to BE.
  -- Similarly we can prove that neither is any other straight line except AD; therefore AD is
  -- parallel to BE.
  -- Therefore etc.
  -- Q. E. D.]
  exact hpar

/-- **I.40, general** (companion of I.40). Equal triangles ABC, DEF on equal bases BC, EF
of one straight line L, and on the same side of it, are in the same parallels: A and D lie
on one straight line parallel to L. The bases may be apart, touching, overlapping or one,
and named either way along L; the vertices may be one point, and then the parallel is the
one through it. -/
theorem Prop40.general {A B C D E F : Point} {L : Line} (hABC : Triangle A B C)
    (hDEF : Triangle D E F) (hB : OnLine B L) (hC : OnLine C L) (hE : OnLine E L)
    (hF : OnLine F L) (hbase : ‖B C‖ = ‖E F‖) (heq : △ A B C = △ D E F)
    (hside : SameSide A D L) :
    ∃ M : Line, Parallel M L ∧ OnLine A M ∧ OnLine D M := by
  /- Suppose there is no parallel to L containing both A and D. -/
  refine Classical.byContradiction fun hnot => ?_
  /- "Let ABC, CDE be equal triangles": here the second triangle is DEF,
     and both bases lie on L. Each vertex is off that straight line. -/
  have hA_L : ¬ OnLine A L := hABC.bca.off_line hB hC
  have hD_L : ¬ OnLine D L := hDEF.bca.off_line hE hF
  /- "let AF be drawn through A parallel to BE [I. 31]": K is the parallel
     through A to the straight line L carrying both bases. -/
  obtain ⟨K, hA_K, hKL⟩ := Prop31.line hA_L
  /- "and let FE be joined": G, playing Euclid's F, is where K meets ED, as
     his F lies on CD (`Prop30.meet`). His FE is our GF, which closes the
     triangle GEF, his FCE. -/
  obtain ⟨ED, hE_ED, hD_ED⟩ := Postulate1 E D hDEF.ne₁₂.symm
  obtain ⟨G, hG_ED, hG_K⟩ :=
    Prop30.meet hKL hE hE_ED (fun e => hD_L (e ▸ hD_ED))
  have hG_L : ¬ OnLine G L := hKL.not_onLine hG_K
  have hGEF : Triangle G E F := (Triangle.of_line hE hF hDEF.ne₂₃ hG_L).cab
  /- "the triangle ABC is equal to the triangle FCE": ABC and GEF have equal
     bases on L and their vertices on K, so I.38 gives equal areas. -/
  have h38 : △ A B C = △ G E F :=
    Prop38 hABC hGEF hbase ⟨K, L, hKL, hA_K, hG_K, hB, hC, hE, hF⟩
  /- "the triangle DCE is also equal to the triangle FCE, [C.N. 1]":
     DEF and GEF are each equal to ABC. -/
  have h1 : △ D E F = △ G E F := CommonNotion1 heq.symm h38.symm
  /- "the greater to the less: which is impossible": G and A lie on the
     same side of L, hence G is on D's side. On ED this puts G on the ray
     from E through D. -/
  have hGD_L : SameSide G D L := same_side_trans (hKL.sameSide hA_K hG_K) hside
  have hGD_side : SameSideOf G D E F := SameSideOf.of_line hDEF.ne₂₃ hE hF hGD_L
  have hray : OnRay G E D :=
    OnRay.of_sameSideOf hGD_side ⟨ED, hE_ED, hD_ED, hG_ED⟩ (fun e => hG_L (e ▸ hE))
  /- If G were D, K would contain both vertices, even when A and D coincide,
     contrary to the supposition. -/
  have hGE : G ≠ E := fun e => hG_L (e ▸ hE)
  have hGD : G ≠ D := fun e => hnot ⟨K, hKL, hA_K, e ▸ hG_K⟩
  /- Between E and D, GEF is less than DEF; beyond D, DEF is less than GEF.
     Either order contradicts their equality, and the same-side condition excludes
     the opposite ray. -/
  rcases between_cases hGE.symm hGD hDEF.ne₁₂.symm hE_ED hG_ED hD_ED with h | h | h
  · have hless := area_lt_of_cut hDEF.cba h
    rw [← area_cba G E F, ← area_cba D E F] at hless
    exact Magnitude.ne_of_lt hless h1.symm
  · exact hray.2.2.2 h
  · have hless := area_lt_of_cut hGEF.cba h
    rw [← area_cba D E F, ← area_cba G E F] at hless
    exact Magnitude.ne_of_lt hless h1

/-- **I.40, the join** (companion of I.40). Under the hypotheses of `Prop40.general`, when
the vertices A and D are two points, the straight line AD joining them is parallel to the
base BC: Euclid's "AD is parallel to BE". -/
theorem Prop40.join {A B C D E F : Point} {L : Line} (hABC : Triangle A B C)
    (hDEF : Triangle D E F) (hB : OnLine B L) (hC : OnLine C L) (hE : OnLine E L)
    (hF : OnLine F L) (hbase : ‖B C‖ = ‖E F‖) (heq : △ A B C = △ D E F)
    (hside : SameSide A D L) (hAD : A ≠ D) :
    AreParallel A D B C := by
  /- "For let AD be joined": the general statement puts A and D on one
     parallel M to L, and the two distinct vertices determine that straight line. -/
  obtain ⟨M, hM, hA_M, hD_M⟩ :=
    Prop40.general hABC hDEF hB hC hE hF hbase heq hside
  /- "therefore AD is parallel to BE": the distinct points A and D name M,
     and the distinct ends B and C of the first base name L. -/
  exact AreParallel.of_parallel hAD hABC.ne₂₃ hA_M hD_M hB hC hM

/-- **I.40, special** (companion of I.40). The statement of `Prop40`, with the bases BC, CE
end to end, derived from `Prop40.general`: it shows that the general statement contains
Euclid's configuration. The second triangle, CDE, is the triangle DCE on the base
CE, and L is the straight line BE. -/
theorem Prop40.special {A B C D E : Point} (hABC : Triangle A B C) (hCDE : Triangle C D E)
    (hBCE : Between B C E) (hbase : ‖B C‖ = ‖C E‖) (heq : △ A B C = △ C D E)
    (hside : SameSideOf A D B E) (hAD : A ≠ D) :
    AreParallel A D B E := by
  have hBE : B ≠ E := ne_of_between_ends hBCE
  obtain ⟨BE, hB, hE⟩ := Postulate1 B E hBE
  have hC : OnLine C BE := on_line_of_between_ends hBCE hB hE
  obtain ⟨M, hM, hA_M, hD_M⟩ :=
    Prop40.general hABC hCDE.bac hB hC hC hE hbase (heq.trans (area_bac C D E))
      (hside.sameSide hB hE)
  exact AreParallel.of_parallel hAD hBE hA_M hD_M hB hE hM

/-- The check: `Prop40.special` has the statement of `Prop40` (checked by Lean, up to
unfolding definitions). -/
example : type_of% @Elements.BookI.Prop40 := @Prop40.special

end Elements.BookI
