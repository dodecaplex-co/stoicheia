import Elements

/-!
# Staging: I.40 for bases anywhere on one straight line

Brief 0006, stage 2. Companions of `Elements.BookI.Prop40`, which stays as Euclid's worked
configuration: there the bases BC, CE meet end to end, as in his figure. His words, "equal
triangles which are on equal bases and on the same side", put the bases anywhere on one
straight line. These companions do, and they move into `Elements/BookI/Prop40.lean` when
proved, as the certificate entries "I.40 general", "I.40 join" and "I.40 special".
-/

namespace Elements.BookI

open Tacit

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
  /- "Let ABC, CDE be equal triangles": here the second triangle is DEF,
     and both bases lie on L. Each vertex is off that straight line. -/
  have hA_L : ¬ OnLine A L := hABC.bca.off_line hB hC
  have hD_L : ¬ OnLine D L := hDEF.bca.off_line hE hF
  /- "let AF be drawn through A parallel to BE [I. 31]": K is the parallel
     through A to the straight line L carrying both bases. -/
  obtain ⟨K, hA_K, hKL⟩ := Prop31.line hA_L
  /- "and let FE be joined": G, playing Euclid's F, is where K meets ED
     (`Prop30.meet`). The triangle GEF plays his FCE. -/
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
  /- Between E and D, GEF would be the part of DEF; beyond D, DEF would be
     the part of GEF. Equal areas therefore put G at D itself. -/
  have hGD : G = D := hray.eq_of_area_eq hDEF h1.symm
  /- "they are also in the same parallels": the end of the reductio is direct.
     D lies on K, which is still the parallel through A when A and D coincide. -/
  have hD_K : OnLine D K := hGD ▸ hG_K
  exact ⟨K, hKL, hA_K, hD_K⟩

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

/-- **I.40, special** (companion of I.40). Today's statement of I.40, with the bases BC, CE
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

/-- The check: `Prop40.special` has today's statement of I.40 (checked by Lean, up to
unfolding definitions). -/
example : type_of% @Elements.BookI.Prop40 := @Prop40.special

end Elements.BookI
