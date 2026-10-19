import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop11
import Elements.BookI.Prop13
import Elements.BookI.Prop32
import Elements.BookIII.Prop02
import Elements.BookIII.Prop19
import Elements.BookIII.Prop21
import Elements.BookIII.Prop22
import Elements.BookIII.Prop31

/-!
# Book III, Proposition 32

Euclid's text, in Heath's translation: [`heath/III/32.md`](../../heath/III/32.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- Two points of a circle, neither of them the point B where the straight line EF
touches it, lie on the same side of EF. Euclid takes this for granted. Were they on
opposite sides, the straight line joining them would cross EF at a point within the
circle by III.2, and no point of a straight line touching a circle is within
it, as in III.18. -/
theorem Prop32.sameSide {B E F P Q : Point} {α : Circle} {L : Line}
    (hα : ∃ O : Point, Centre O α) (hEF : Touches E F α)
    (hE_L : OnLine E L) (hF_L : OnLine F L) (hB_L : OnLine B L) (hB : OnCircle B α)
    (hP : OnCircle P α) (hQ : OnCircle Q α) (hPB : P ≠ B) (hQB : Q ≠ B) : SameSide P Q L := by
  have off : ∀ {R : Point}, OnCircle R α → R ≠ B → ¬ OnLine R L := fun hR hRB h =>
    (hEF.2 L hE_L hF_L).2 ⟨B, _, hRB.symm, hB_L, hB, h, hR⟩
  refine Classical.byContradiction fun hs => ?_
  obtain ⟨Y, hY_L, hPYQ⟩ := OppositeSides.exists_between ⟨off hP hPB, off hQ hQB, hs⟩
  exact hEF.not_inside ⟨L, hE_L, hF_L, hY_L⟩ (Prop2 hP hQ Y hPYQ)

/-- If a straight line touch a circle, and from the point of contact there be drawn across, in the
circle, a straight line cutting the circle, the angles which it makes with the tangent will be
equal to the angles in the alternate segments of the circle. -/
theorem Prop32 {B D E F : Point} {ABCD : Circle} (hABCD : ∃ O : Point, Centre O ABCD)
    (hB : OnCircle B ABCD) (hD : OnCircle D ABCD) (hBD : B ≠ D) (hEF : Touches E F ABCD)
    (hEBF : Between E B F) :
    (∀ A : Point, OnCircle A ABCD → OppositeSidesOf A F B D → ∠ F B D = ∠ B A D) ∧
    (∀ C : Point, OnCircle C ABCD → SameSideOf C F B D → ∠ E B D = ∠ D C B) := by
  -- For let a straight line EF touch the circle ABCD at the point B, and from the point B let
  -- there be drawn across, in the circle ABCD, a straight line BD cutting it;
  have hEF' : E ≠ F := ne_of_between_ends hEBF
  obtain ⟨L, hE_L, hF_L⟩ := Postulate1 E F hEF'
  have hB_L : OnLine B L := on_line_of_between_ends hEBF hE_L hF_L
  have onL : ∀ {P : Point}, Collinear E F P → OnLine P L := fun ⟨M, h1, h2, h3⟩ =>
    (line_unique hEF' h1 h2 hE_L hF_L) ▸ h3
  have off : ∀ {R : Point}, OnCircle R ABCD → R ≠ B → ¬ OnLine R L := fun hR hRB h =>
    (hEF.2 L hE_L hF_L).2 ⟨B, _, hRB.symm, hB_L, hB, h, hR⟩
  have hD_L : ¬ OnLine D L := off hD hBD.symm
  -- I say that the angles which BD makes with the tangent EF will be equal to the angles in
  -- the alternate segments of the circle, that is, that the angle FBD is equal to the angle
  -- constructed in the segment BAD, and the angle EBD is equal to the angle constructed in the
  -- segment DCB.
  -- For let BA be drawn from B at right angles to EF,
  obtain ⟨X, hXD, hX⟩ := BookI.Prop11 hEF' ⟨L, hE_L, hF_L, hB_L⟩ (fun h => hD_L (onL h))
  have hX_L : ¬ OnLine X L := not_on_line_of_same_side (hXD.sameSide hE_L hF_L)
  have hXB : X ≠ B := fun e => hX_L (e ▸ hB_L)
  -- let a point C be taken at random on the circumference BD,
  /- The second conclusion takes any such C, and we bring C in when we prove it, below. -/
  -- and let AD, DC, CB be joined.
  -- Then, since a straight line EF touches the circle ABCD at B,
  -- and BA has been drawn from the point of contact at right angles to the tangent,
  -- the centre of the circle ABCD is on BA. [III. 19]
  obtain ⟨O, hO⟩ := hABCD
  have hXBO : Collinear X B O :=
    Prop19 hB hEF ⟨L, hE_L, hF_L, hB_L⟩ (fun h => hX_L (onL h))
      (fun P hP hPB => (angle_symm hXB hPB).trans (hX P hP hPB)) O hO
  -- Therefore BA is a diameter of the circle ABCD;
  obtain ⟨M, hX_M, hB_M, hO_M⟩ := hXBO
  obtain ⟨A, hA, hA_M, hAOB⟩ :=
    line_circle_beyond (centre_inside hO) hO_M hB_M (ne_of_centre_of_on hO hB)
  have hAB : A ≠ B := ne_of_between_ends hAOB
  /- A is on X's side of EF, the side of the circle, so the straight line BA is the one
     drawn at right angles to EF. -/
  have hAD_L : SameSide A D L :=
    Prop32.sameSide ⟨O, hO⟩ hEF hE_L hF_L hB_L hB hA hD hAB hBD.symm
  have hAX : OnRay A B X :=
    OnRay.of_sameSideOf (E := F) (SameSideOf.of_line (ne_of_between (between_symm hEBF)).symm
      hB_L hF_L (same_side_trans (same_side_symm hAD_L) (same_side_symm (hXD.sameSide hE_L hF_L))))
      ⟨M, hB_M, hX_M, hA_M⟩ hAB
  have hright : ∀ {P : Point}, OnLine P L → P ≠ B → ∠ A B P = ∟ := fun hP hPB => by
    rw [angle_symm hAB hPB, angle_onRay_right hAX hPB]
    exact hX _ ⟨L, hE_L, hF_L, hP⟩ hPB
  /- Euclid's figure has D on F's side of BA. We write the rest of his argument once, for
     whichever end of the tangent is on D's side, and take the case of D at A at the end. -/
  have key : ∀ {E F : Point}, Between E B F → OnLine E L → OnLine F L → SameSideOf D F B A →
      (∀ A' : Point, OnCircle A' ABCD → OppositeSidesOf A' F B D → ∠ F B D = ∠ B A' D) ∧
      (∀ C : Point, OnCircle C ABCD → SameSideOf C F B D → ∠ E B D = ∠ D C B) := by
    intro E F hEBF hE_L hF_L hDF
    have hFB : F ≠ B := (ne_of_between (between_symm hEBF))
    have hBAD : Triangle B A D := hDF.triangle
    -- therefore the angle ADB, being an angle in a semicircle, is right. [III. 31]
    have hADB : ∠ A D B = ∟ := (Prop31 hO hD hA hB hAOB hBAD.ne₂₃.symm hBD.symm).1
    -- Therefore the remaining angles BAD, ABD are equal to one right angle. [I. 32]
    obtain ⟨P, hADP⟩ := produce hBAD.ne₂₃
    have h32 := (BookI.Prop32 hBAD hADP).2
    rw [hADB, add_comm (∠ B A D) ∟, add_assoc, add_comm ∟,
      angle_symm hBD.symm hAB] at h32
    have hrem : ∠ B A D + ∠ A B D = ∟ := CommonNotion3 h32 rfl
    -- But the angle ABF is also right;
    have hABF : ∠ A B F = ∟ := hright hF_L hFB
    -- therefore the angle ABF is equal to the angles BAD, ABD.
    have h1 : ∠ A B F = ∠ B A D + ∠ A B D := hABF.trans hrem.symm
    -- Let the angle ABD be subtracted from each;
    have hDA_F : SameSideOf D A B F :=
      SameSideOf.of_line hFB.symm hB_L hF_L (same_side_symm hAD_L)
    have hsplit : ∠ A B F = ∠ A B D + ∠ D B F := angle_add_of_within hDF hDA_F
    -- therefore the angle DBF which remains is equal to the angle BAD in the alternate segment
    -- of the circle.
    have hDBF : ∠ D B F = ∠ B A D := CommonNotion3 (by rw [add_comm, ← hsplit, h1]) rfl
    /- A is on the other side of BD from F, for the straight line BD, within the angle
       ABF, crosses AF. -/
    obtain ⟨N, hB_N, hD_N⟩ := Postulate1 B D hBD
    obtain ⟨Y, hAYF, hY⟩ := crossbar hDF hDA_F
    obtain ⟨-, -, ⟨N', hB_N', hD_N', hY_N'⟩, -⟩ := hY
    have hY_N : OnLine Y N := (line_unique hBD hB_N' hD_N' hB_N hD_N) ▸ hY_N'
    have hF_N : ¬ OnLine F N := fun h =>
      hD_L ((line_unique hFB.symm hB_N h hB_L hF_L) ▸ hD_N)
    have hAF : OppositeSidesOf A F B D :=
      OppositeSidesOf.of_line hBD hB_N hD_N
        ⟨(Prop2.triangle hB hD hA hBD hBAD.ne₂₃.symm hAB.symm).off_line hB_N hD_N,
          hF_N, pasch3 hAYF hY_N⟩
    refine ⟨fun A' hA' hA'F => ?_, fun C hC hCF => ?_⟩
    · /- Any angle in that segment is the angle BAD [III. 21]. -/
      rw [angle_symm hFB hBD.symm, hDBF,
        Prop21 hA hB hD hA' (OppositeSidesOf.sameSideOf hAF.symm hA'F.symm)]
    -- Next, since ABCD is a quadrilateral in a circle,
    -- its opposite angles are equal to two right angles. [III. 22]
    have h22 := (Prop22 hA hB hC hD (hCF.trans_opposite hAF.symm).symm).2
    -- But the angles DBF, DBE are also equal to two right angles;
    have h13 : ∠ F B D + ∠ D B E = ∟ + ∟ :=
      BookI.Prop13 (between_symm hEBF) (fun ⟨K, hF_K, hE_K, hD_K⟩ =>
        hD_L ((line_unique (ne_of_between_ends hEBF).symm hF_K hE_K hF_L hE_L) ▸ hD_K))
    -- therefore the angles DBF, DBE are equal to the angles BAD, BCD,
    rw [angle_symm hFB hBD.symm, ← h22] at h13
    -- of which the angle BAD was proved equal to the angle DBF;
    rw [hDBF] at h13
    -- therefore the angle DBE which remains is equal to the angle DCB in the alternate segment
    -- DCB of the circle.
    have hEB : E ≠ B := ne_of_between hEBF
    rw [add_comm (∠ B A D), add_comm (∠ B A D)] at h13
    rw [angle_symm hEB hBD.symm]
    exact CommonNotion3 h13 rfl
  -- Therefore etc.
  have hEF_BD : OppositeSidesOf E F B D :=
    (OppositeSidesOf.of_between (Triangle.of_line hB_L hE_L (ne_of_between hEBF).symm hD_L).cab
      hEBF).swap
  by_cases hDA : D = A
  · /- When D is A, BD is the diameter: both segments are semicircles, and every angle
       in them is right by III.31, as are the angles FBD, EBD. -/
    subst hDA
    have hBOD : Between B O D := between_symm hAOB
    refine ⟨fun A' hA' hA'F => ?_, fun C hC hCF => ?_⟩
    · have hT := hA'F.triangle
      rw [angle_symm (ne_of_between (between_symm hEBF)) hBD.symm, hright hF_L
        (ne_of_between (between_symm hEBF))]
      exact ((Prop31 hO hA' hB hD hBOD hT.ne₁₃.symm hT.ne₂₃.symm).1).symm
    · have hT := hCF.triangle
      rw [angle_symm (ne_of_between hEBF) hBD.symm, hright hE_L (ne_of_between hEBF)]
      exact ((Prop31 hO hC hD hB hAOB hT.ne₂₃.symm hT.ne₁₃.symm).1).symm
  · have hDBA : ¬ OnLine D M := fun h =>
      (Prop2.triangle hD hB hA hBD.symm hAB.symm hDA) ⟨M, h, hB_M, hA_M⟩
    have hA_L : ¬ OnLine A L := off hA hAB
    have hEF_BA : OppositeSidesOf E F B A :=
      (OppositeSidesOf.of_between (Triangle.of_line hB_L hE_L (ne_of_between hEBF).symm hA_L).cab
        hEBF).swap
    by_cases hs : SameSideOf D F B A
    · exact key hEBF hE_L hF_L hs
    · have hDF : OppositeSidesOf D F B A :=
        OppositeSidesOf.of_line hAB.symm hB_M hA_M
          ⟨hDBA, fun h => hEF_BA.2 M hB_M hA_M |>.2.1 h,
            fun h => hs (SameSideOf.of_line hAB.symm hB_M hA_M h)⟩
      obtain ⟨k₁, k₂⟩ := key (between_symm hEBF) hF_L hE_L
        (OppositeSidesOf.sameSideOf hDF.symm hEF_BA.symm)
      refine ⟨fun A' hA' hA'F => ?_, fun C hC hCF => ?_⟩
      · have hT := hA'F.triangle
        rw [k₂ A' hA' (OppositeSidesOf.sameSideOf hA'F.symm hEF_BD.symm)]
        exact angle_symm hT.ne₂₃ hT.ne₁₃
      · have hT := hCF.triangle
        rw [k₁ C hC (hCF.trans_opposite hEF_BD.symm)]
        exact angle_symm hT.ne₁₃ hT.ne₂₃
  -- Q. E. D.

end Elements.BookIII
