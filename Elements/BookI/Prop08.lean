import Elements.Figure.Basics
import Elements.BookI.Prop07

/-!
# Book I, Proposition 8

Euclid's text, in Heath's translation: [`heath/I/08.md`](../../heath/I/08.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid lays the triangle ABC down on DEF. In Lean the copy of ABC that
superposition hands us has its own corners: `C'`, where C comes down, and `G`,
where A comes down. Euclid's G is exactly this point, the place A would occupy
if BA, AC "fell beside" ED, DF.
-/

namespace Elements.BookI

open Tacit

/-- The triangle `ABC`, read starting from `B`, is still a triangle: three points
that are not on one straight line, in whatever order we name them. -/
theorem Prop8.triangle {A B C : Point} (h : Triangle A B C) : Triangle B C A := by
  rintro ⟨L, hB, hC, hA⟩
  exact h ⟨L, hA, hB, hC⟩

/-- What Euclid sees when he lays BC along EF: a point `P` on the straight line
`EF`, on the same side of `E` as `F`, and as far from `E` as `F` is, is `F`
itself. -/
theorem Prop8.coincide {E F P : Point} {L : Line} (hE : OnLine E L) (hF : OnLine F L)
    (hP : OnLine P L) (hEF : E ≠ F) (hray : ¬ Between P E F) (h : ‖E P‖ = ‖E F‖) :
    P = F := by
  by_cases hPF : P = F
  · exact hPF
  have hEP : E ≠ P := ne_of_len_eq h hEF
  /- Of the three points E, P, F on one straight line, one lies between the other
     two. P can't be on the far side of E from F; and if P were short of F, or
     beyond it, then EF would be equal to EF together with something. -/
  rcases between_cases hEP hPF hEF hE hP hF with hEPF | hPEF | hEFP
  · have hsum : ‖E P‖ + ‖P F‖ = ‖E F‖ := len_add_of_between hEPF
    rw [h] at hsum
    have hlt : ‖E F‖ < ‖E F‖ + ‖P F‖ := CommonNotion5 (len_pos hPF)
    rw [hsum] at hlt
    exact absurd hlt (lt_irrefl _)
  · exact absurd hPEF hray
  · have hsum : ‖E F‖ + ‖F P‖ = ‖E P‖ := len_add_of_between hEFP
    rw [h] at hsum
    have hlt : ‖E F‖ < ‖E F‖ + ‖F P‖ := CommonNotion5 (len_pos (Ne.symm hPF))
    rw [hsum] at hlt
    exact absurd hlt (lt_irrefl _)

/-- Two points on the same side of the straight line through `E` and `F` are on
the same side of `EF`, whichever way we name that line: two points fix one
straight line. -/
theorem Prop8.sameSide {G D E F : Point} {L : Line} (hEF : E ≠ F) (hE : OnLine E L)
    (hF : OnLine F L) (h : SameSide G D L) : SameSideOf G D E F := by
  refine ⟨hEF, fun M hEM hFM => ?_⟩
  rw [← line_unique hEF hE hF hEM hFM]
  exact h

/-- If two triangles have the two sides equal to two sides respectively, and have also the base
equal to the base, they will also have the angles equal which are contained by the equal
straight lines. -/
theorem Prop8 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (hBC : ‖B C‖ = ‖E F‖) :
    ∠ B A C = ∠ E D F := by
  -- Let ABC, DEF be two triangles having the two sides AB, AC equal to the two sides DE, DF
  -- respectively, namely AB to DE, and AC to DF; and let them have the base BC equal to the
  -- base EF;
  -- I say that the angle BAC is also equal to the angle EDF.
  -- For, if the triangle ABC be applied to the triangle DEF, and if the point B be placed on
  -- the point E and the straight line BC on EF,
  /- To lay BC along EF we need the straight line EF itself (Postulate 1). The
     rule of superposition then sets B on E, sends C along the ray from E through
     F, and lets us choose the side of EF on which A comes down: D's side, so
     that the two triangles lie over one another, as Euclid's word "applied"
     means. The copy of ABC is `G E C'`: C lands at `C'` and A at `G`. -/
  have hEF : E ≠ F := hDEF.ne₂₃
  obtain ⟨EF, hE_EF, hF_EF⟩ := Postulate1 E F hEF
  have hD_EF : ¬ OnLine D EF := fun hD => hDEF ⟨EF, hD, hE_EF, hF_EF⟩
  obtain ⟨C', G, hC'_EF, hC'_ray, hGD_EF, hEC', hC'G, hGE, -, hEGC', -⟩ :=
    superposition (Prop8.triangle hABC) hE_EF hF_EF hEF hD_EF
  -- the point C will also coincide with F,
  -- because BC is equal to EF.
  have hC'F : C' = F := Prop8.coincide hE_EF hF_EF hC'_EF hEF hC'_ray (hEC'.trans hBC)
  -- Then, BC coinciding with EF,
  -- BA, AC will also coincide with ED, DF;
  /- The sides BA, AC have been carried to GE, GF, and they are equal to ED, DF. -/
  have hGE_DE : ‖G E‖ = ‖D E‖ := hGE.trans hAB
  have hGF_DF : ‖G F‖ = ‖D F‖ :=
    calc ‖G F‖ = ‖F G‖ := len_symm G F
      _ = ‖C' G‖ := by rw [hC'F]
      _ = ‖C A‖ := hC'G
      _ = ‖A C‖ := len_symm C A
      _ = ‖D F‖ := hAC
  -- for, if the base BC coincides with the base EF, and the sides BA, AC do not coincide with
  -- ED, DF but fall beside them as EG, GF,
  -- then, given two straight lines constructed on a straight line (from its extremities) and
  -- meeting in a point, there will have been constructed on the same straight line (from its
  -- extremities), and on the same side of it, two other straight lines meeting in another
  -- point and equal to the former two respectively, namely each to that which has the same
  -- extremity with it.
  /- G and D are on the same side of EF: superposition put G there. -/
  have hGD_side : SameSideOf G D E F := Prop8.sameSide hEF hE_EF hF_EF hGD_EF
  -- But they cannot be so constructed. [I. 7]
  -- Therefore it is not possible that, if the base BC be applied to the base EF, the sides BA,
  -- AC should not coincide with ED, DF;
  -- they will therefore coincide,
  /- Our I.7 is stated positively: two such points are one and the same point.
     So Euclid's reduction to the impossible is a single step here. -/
  have hGD : G = D := Prop7 hGD_side hGE_DE hGF_DF
  -- so that the angle BAC will also coincide with the angle EDF, and will be equal to it.
  /- The angle BAC was carried to the angle EGC', and G is D, C' is F. -/
  have hEGC'_EDF : ∠ E G C' = ∠ E D F := CommonNotion4.angle rfl hGD hC'F
  exact hEGC'.symm.trans hEGC'_EDF
  -- If therefore etc.
  -- Q. E. D.

end Elements.BookI
