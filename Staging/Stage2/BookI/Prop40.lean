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
  sorry

/-- **I.40, the join** (companion of I.40). Under the hypotheses of `Prop40.general`, when
the vertices A and D are two points, the straight line AD joining them is parallel to the
base BC: Euclid's "AD is parallel to BE". -/
theorem Prop40.join {A B C D E F : Point} {L : Line} (hABC : Triangle A B C)
    (hDEF : Triangle D E F) (hB : OnLine B L) (hC : OnLine C L) (hE : OnLine E L)
    (hF : OnLine F L) (hbase : ‖B C‖ = ‖E F‖) (heq : △ A B C = △ D E F)
    (hside : SameSide A D L) (hAD : A ≠ D) :
    AreParallel A D B C := by
  sorry

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
