import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop13
import Elements.BookI.Prop14
import Elements.BookI.Prop17
import Elements.BookI.Prop28
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop41
import Elements.BookI.Prop46
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 47

Euclid's text, in Heath's translation: [`heath/I/47.md`](../../heath/I/47.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

`Prop47` keeps Euclid's worked configuration: the squares described outward, on the
side of each base away from the triangle. The companion `Prop47.general` proves the
same area identity for squares independently on either side of each base, all eight
choices, with each square's far corners together on one side. It constructs outward
squares by I.46, applies `Prop47`, and carries each area across by `Prop46.square_eq`,
since squares on the same base have equal areas.

Before the proposition, `Prop47.within` says where the squares fall: a fact of
Euclid's figure, used in the angle additions and in dividing the square BDEC.
-/

namespace Elements.BookI

open Tacit

/-- Where the squares fall. If the angle ABC is less than a right angle, and BD
stands at right angles to BC on the other side of it from A, then C lies within
the angle ABD: on A's side of BD, and on D's side of BA. Euclid reads this
off his figure when he adds the angle ABC to the right angles DBC, FBA, and
again when he takes the parallelograms BL, CL to make up the square BDEC.

The straight line AD crosses BC, since it joins points on either side of it. Not
at B, for then the angles ABC, CBD would make two right angles [I. 13], and
CBD alone is right. Not beyond B from C, for then the angle ABD would be
greater than two right angles: the angle on the far side of AB from C is
greater than right [I. 13], and to it is added the right angle on the far side of
BD. So it crosses on the ray from B through C, and C lies where the crossing
point does. [I. 13] -/
theorem Prop47.within {A B C D : Point} (hABC : Triangle A B C) (hD : OppositeSidesOf D A B C)
    (hCBD : ∠ C B D = ∟) (hacute : ∠ A B C < ∟) :
    SameSideOf C A B D ∧ SameSideOf C D B A := by
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  have hop : OppositeSides A D BC := hD.symm.oppositeSides hB_BC hC_BC
  have hA_BC : ¬ OnLine A BC := hop.1
  have hD_BC : ¬ OnLine D BC := hop.2.1
  /- AD crosses BC at a point Y. -/
  obtain ⟨Y, hY_BC, hAYD⟩ := OppositeSides.exists_between hop
  obtain ⟨AD, hA_AD, hD_AD⟩ := Postulate1 A D (ne_of_between_ends hAYD)
  have hY_AD : OnLine Y AD := on_line_of_between_ends hAYD hA_AD hD_AD
  have hBD : B ≠ D := fun e => hD_BC (e ▸ hB_BC)
  have hBA : B ≠ A := fun e => hA_BC (e ▸ hB_BC)
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hBD
  obtain ⟨BA, hB_BA, hA_BA⟩ := Postulate1 B A hBA
  by_cases hYB : Y = B
  · /- It does not cross at B, for then the angles ABC, CBD would make two right
       angles. [I. 13] -/
    exfalso
    rw [hYB] at hAYD hY_AD
    have hC : ¬ Collinear A D C := fun ⟨K, hA_K, hD_K, hC_K⟩ => by
      have hK : K = AD := line_unique (ne_of_between_ends hAYD) hA_K hD_K hA_AD hD_AD
      rw [hK] at hC_K
      exact hA_BC ((line_unique hABC.ne₂₃ hY_AD hC_K hB_BC hC_BC) ▸ hA_AD)
    have h13 := Prop13 hAYD hC
    rw [hCBD] at h13
    exact Magnitude.ne_of_lt (add_lt_add_right ∟ hacute) h13
  · have hB_AD : ¬ OnLine B AD := fun hB =>
      hA_BC ((line_unique hYB hY_AD hB hY_BC hB_BC) ▸ hA_AD)
    have hY_BD : ¬ OnLine Y BD := fun hY =>
      hD_BC ((line_unique hYB hY hB_BD hY_BC hB_BC) ▸ hD_BD)
    have hY_BA : ¬ OnLine Y BA := fun hY =>
      hA_BC ((line_unique hYB hY hB_BA hY_BC hB_BC) ▸ hA_BA)
    by_cases hYBC : Between Y B C
    · /- Nor beyond B, for then the angle ABD would be greater than two right angles. -/
      exfalso
      have hADB : Triangle A D B := fun ⟨K, hA_K, hD_K, hB_K⟩ =>
        hB_AD ((line_unique (ne_of_between_ends hAYD) hA_K hD_K hA_AD hD_AD) ▸ hB_K)
      have hsum : ∠ A B D = ∠ A B Y + ∠ Y B D := angle_add_of_between hADB hAYD
      have hYCA : ¬ Collinear Y C A := fun ⟨K, hY_K, hC_K, hA_K⟩ =>
        hA_BC ((line_unique (ne_of_between_ends hYBC) hY_K hC_K hY_BC hC_BC) ▸ hA_K)
      have hYCD : ¬ Collinear Y C D := fun ⟨K, hY_K, hC_K, hD_K⟩ =>
        hD_BC ((line_unique (ne_of_between_ends hYBC) hY_K hC_K hY_BC hC_BC) ▸ hD_K)
      have h₁ : ∠ Y B A + ∠ A B C = ∟ + ∟ := Prop13 hYBC hYCA
      have h₂ : ∠ Y B D + ∠ D B C = ∟ + ∟ := Prop13 hYBC hYCD
      rw [(angle_symm hBD.symm hABC.ne₂₃.symm).trans hCBD] at h₂
      have hYBD : ∠ Y B D = ∟ := by
        rcases lt_trichotomy (∠ Y B D) ∟ with h | h | h
        · exact absurd h₂ (Magnitude.ne_of_lt (add_lt_add_right ∟ h))
        · exact h
        · exact absurd h₂.symm (Magnitude.ne_of_lt (add_lt_add_right ∟ h))
      have hgt : ∟ < ∠ A B Y := by
        have h₃ : ∠ A B C + ∠ Y B A < ∟ + ∠ Y B A := add_lt_add_right _ hacute
        rw [add_comm (∠ A B C), add_comm ∟, h₁] at h₃
        rw [angle_symm hBA.symm (ne_of_between hYBC)]
        exact Magnitude.lt_of_add_lt_add_right h₃
      have h₄ : ∟ + ∟ < ∠ A B D := by
        rw [hsum, hYBD]
        exact add_lt_add_right ∟ hgt
      exact lt_irrefl _ (lt_trans h₄ (Prop13.angle_lt_two_right hADB.acb))
    · /- So Y lies on the ray from B through C, and within the angle ABD. -/
      have hray : OnRay C B Y := OnRay.symm ⟨hABC.ne₂₃, hYB, ⟨BC, hB_BC, hC_BC, hY_BC⟩, hYBC⟩
      have h₁ : SameSideOf Y A B D :=
        SameSideOf.of_line hBD hB_BD hD_BD (pasch2 (between_symm hAYD) hD_BD hY_BD)
      have h₂ : SameSideOf Y D B A :=
        SameSideOf.of_line hBA hB_BA hA_BA (pasch2 hAYD hA_BA hY_BA)
      exact ⟨SameSideOf.of_onRay hray h₁, SameSideOf.of_onRay hray h₂⟩

/-- In right-angled triangles the square on the side subtending the right angle is equal to the
squares on the sides containing the right angle. -/
theorem Prop47 {A B C D E F G H K : Point} (hABC : Triangle A B C) (hright : ∠ B A C = ∟)
    (hBDEC : Square B D E C) (hD : OppositeSidesOf D A B C) (hE : OppositeSidesOf E A B C)
    (hABFG : Square A B F G) (hF : OppositeSidesOf F C A B) (hG : OppositeSidesOf G C A B)
    (hACKH : Square A C K H) (hK : OppositeSidesOf K B A C) (hH : OppositeSidesOf H B A C) :
    quadArea B D E C = quadArea A B F G + quadArea A C K H := by
  -- Let ABC be a right-angled triangle having the angle BAC right;
  -- I say that the square on BC is equal to the squares on BA, AC.
  -- For let there be described on BC the square BDEC, and on BA, AC the squares GB,
  -- HC; [I. 46]
  /- The three squares are given in the statement, so I.46 is not cited. Their
     opposite sides are parallel by `Prop28.square`. -/
  have hpsq : Parallelogram B D E C :=
    (Prop28.square hBDEC.rotate.rotate.rotate
      (OppositeSidesOf.sameSideOf hD.symm hE.symm).swap).rotate
  have hABFGpar : Parallelogram A B F G :=
    Prop28.square hABFG (OppositeSidesOf.sameSideOf hF.symm hG.symm)
  have hACKHpar : Parallelogram A C K H :=
    Prop28.square hACKH (OppositeSidesOf.sameSideOf hK.symm hH.symm)
  obtain ⟨hBD_DE, hDE_EC, hEC_CB, hCBD, -, -, hECB⟩ := id hBDEC
  have hBD_BC : ‖B D‖ = ‖B C‖ :=
    hBD_DE.trans (hDE_EC.trans (hEC_CB.trans (len_symm C B)))
  have hCE_CB : ‖C E‖ = ‖C B‖ := (len_symm C E).trans hEC_CB
  have hBCE : ∠ B C E = ∟ :=
    (angle_symm hABC.ne₂₃ hE.triangle.ne₂₃.symm).trans hECB
  have hright' : ∠ C A B = ∟ :=
    (angle_symm hABC.ne₁₃.symm hABC.ne₁₂.symm).trans hright
  /- I.17 makes the angles at B and C acute. With the outward squares,
     `Prop47.within` puts A between the straight lines BD and CE. -/
  have hacB : ∠ A B C < ∟ := by
    have h17 := (Prop17 hABC).2.2
    rw [hright'] at h17
    exact Magnitude.lt_of_add_lt_add_left h17
  have hacC : ∠ A C B < ∟ := by
    have h17 := (Prop17 hABC).2.1
    rw [hright] at h17
    exact Magnitude.lt_of_add_lt_add_left h17
  obtain ⟨hCA_BD, -⟩ := Prop47.within hABC hD hCBD hacB
  obtain ⟨hBA_CE, -⟩ := Prop47.within hABC.acb hE.swap hBCE hacC
  -- through A let AL be drawn parallel to either BD or CE,
  have hBD : B ≠ D := hCA_BD.1
  have hCE : C ≠ E := hBA_CE.1
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hBD
  obtain ⟨CE, hC_CE, hE_CE⟩ := Postulate1 C E hCE
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hpsq.2.1
  have hBD_CE : Parallel BD CE := hpsq.1.parallel hB_BD hD_BD hE_CE hC_CE
  have hDE_BC : Parallel DE BC := hpsq.2.parallel hD_DE hE_DE hC_BC hB_BC
  have hA_BD : ¬ OnLine A BD :=
    not_on_line_of_same_side (same_side_symm (hCA_BD.sameSide hB_BD hD_BD))
  obtain ⟨AL, hA_AL, hAL_BD⟩ := Prop31.line hA_BD
  have hA_CE : ¬ OnLine A CE :=
    not_on_line_of_same_side (same_side_symm (hBA_CE.sameSide hC_CE hE_CE))
  have hAL_CE : Parallel AL CE :=
    Prop30.parallel hAL_BD hBD_CE.symm (fun e => hA_CE (e ▸ hA_AL))
  /- The parallel meets DE at L and BC at its unlettered foot (`Prop30.meet`). -/
  have hDE_BD : DE ≠ BD := fun e => hDE_BC.not_onLine (e ▸ hB_BD) hB_BC
  obtain ⟨L, hL_DE, hL_AL⟩ := Prop30.meet hAL_BD hD_BD hD_DE hDE_BD
  have hBC_BD : BC ≠ BD := fun e => hD.triangle.off_line hB_BC hC_BC (e ▸ hD_BD)
  obtain ⟨X, hX_BC, hX_AL⟩ := Prop30.meet hAL_BD hB_BD hB_BC hBC_BD
  have hXL : X ≠ L := fun e => hDE_BC.not_onLine (e ▸ hL_DE) hX_BC
  have hDL : D ≠ L := fun e => hAL_BD.not_onLine (e ▸ hL_AL) hD_BD
  have hXB : X ≠ B := fun e => hAL_BD.not_onLine (e ▸ hX_AL) hB_BD
  have hLE : L ≠ E := fun e => hAL_CE.not_onLine hL_AL (e ▸ hE_CE)
  have hCX : C ≠ X := fun e => hAL_CE.not_onLine hX_AL (e ▸ hC_CE)
  have P₁ : Parallelogram B D L X :=
    ⟨AreParallel.of_parallel hBD hXL.symm hB_BD hD_BD hL_AL hX_AL hAL_BD.symm,
      AreParallel.of_parallel hDL hXB hD_DE hL_DE hX_BC hB_BC hDE_BC⟩
  have P₂ : Parallelogram X L E C :=
    ⟨AreParallel.of_parallel hXL hCE.symm hX_AL hL_AL hE_CE hC_CE hAL_CE,
      AreParallel.of_parallel hLE hCX hL_DE hE_DE hC_BC hX_BC hDE_BC⟩
  have hXLA : Collinear X L A := ⟨AL, hX_AL, hL_AL, hA_AL⟩
  -- and let AD, FC be joined.
  /- The joined straight lines are the sides of the triangles in I.4 below. -/
  -- Then, since each of the angles BAC, BAG is right, it follows that with a straight line BA,
  -- and at the point A on it, the two straight lines AC, AG not lying on the same side make
  -- the adjacent angles equal to two right angles; therefore CA is in a straight line with
  -- AG. [I. 14]
  have hCAG : Between C A G := Prop14 hG.symm.swap (by
    rw [hright, angle_symm hABC.ne₁₂.symm hG.triangle.ne₁₃.symm, hABFG.2.2.2.1])
  -- For the same reason BA is also in a straight line with AH.
  have hBAH : Between B A H := Prop14 hH.symm.swap (by
    rw [hright', angle_symm hABC.ne₁₃.symm hH.triangle.ne₁₃.symm, hACKH.2.2.2.1])
  /- Euclid proves one half and then says "similarly". We give these sentences
     once over any letters, using the straightness and acute angle already
     proved, and apply them at B and at C. -/
  have half : ∀ {A B C D F G X L : Point}, Triangle A B C →
      ‖B D‖ = ‖B C‖ → ∠ C B D = ∟ → OppositeSidesOf D A B C →
      Square A B F G → OppositeSidesOf F C A B → Parallelogram A B F G →
      Between C A G → ∠ A B C < ∟ → Parallelogram X B D L → Collinear X L A →
      quadArea X B D L = quadArea A B F G := by
    intro A B C D F G X L hABC hBD hCBD hD hsq hF hpsq hCAG hacute hp hX
    obtain ⟨hAB_BF, -, -, -, hABF, -, -⟩ := hsq
    -- And, since the angle DBC is equal to the angle FBA: for each is right: let the angle ABC
    -- be added to each; therefore the whole angle DBA is equal to the whole angle FBC. [C.N. 2]
    obtain ⟨hCA_BD, hCD_BA⟩ := Prop47.within hABC hD hCBD hacute
    obtain ⟨hAC_BF, hAF_BC⟩ := Prop47.within hABC.cba hF.swap hABF
      (by rw [angle_symm hABC.ne₂₃.symm hABC.ne₁₂]; exact hacute)
    have hDBA : ∠ D B A = ∠ D B C + ∠ C B A :=
      angle_add_of_within hCA_BD hCD_BA
    have hFBC : ∠ F B C = ∠ F B A + ∠ A B C :=
      angle_add_of_within hAC_BF hAF_BC
    have hBD_ne : B ≠ D := hCA_BD.1
    have hBF_ne : B ≠ F := hAC_BF.1
    have hrights : ∠ D B C = ∠ F B A := by
      rw [angle_symm hBD_ne.symm hABC.ne₂₃.symm, hCBD,
        angle_symm hBF_ne.symm hABC.ne₁₂, hABF]
    have hadd := CommonNotion2 hrights (Eq.refl (∠ A B C))
    have hang : ∠ D B A = ∠ F B C := by
      rw [hDBA, hFBC, angle_symm hABC.ne₂₃.symm hABC.ne₁₂]
      exact hadd
    -- And, since DB is equal to BC, and FB to BA, the two sides AB, BD are equal to the two
    -- sides FB, BC respectively; and the angle ABD is equal to the angle FBC; therefore the base
    -- AD is equal to the base FC, and the triangle ABD is equal to the triangle FBC. [I. 4]
    have hABD : ∠ A B D = ∠ F B C :=
      (angle_symm hABC.ne₁₂ hBD_ne.symm).trans hang
    obtain ⟨hAD_FC, h4, -, -⟩ :=
      Prop4 hCD_BA.symm.triangle hAC_BF.symm.triangle
        ((len_symm B A).trans hAB_BF) hBD hABD
    -- Now the parallelogram BL is double of the triangle ABD, for they have the same base BD and
    -- are in the same parallels BD, AL. [I. 41]
    have h41a : quadArea X B D L = △ B A D + △ B A D := Prop41 hp hX
    -- And the square GB is double of the triangle FBC, for they again have the same base FB and
    -- are in the same parallels FB, GC. [I. 41]
    obtain ⟨GC, hC_GC, hA_GC, hG_GC⟩ := collinear_of_between hCAG
    have h41b : quadArea G F B A = △ F C B + △ F C B :=
      Prop41 hpsq.rotate.rotate.rotate.reverse ⟨GC, hG_GC, hA_GC, hC_GC⟩
    -- [But the doubles of equals are equal to one another.]
    have hdouble := CommonNotion2 h4 h4
    -- Therefore the parallelogram BL is also equal to the square GB.
    calc
      quadArea X B D L = △ B A D + △ B A D := h41a
      _ = △ B F C + △ B F C := hdouble
      _ = △ F C B + △ F C B := by rw [area_bca B F C]
      _ = quadArea G F B A := h41b.symm
      _ = quadArea A B F G := by
        rw [quadArea_reverse, hpsq.rotate.rotate.rotate.quadArea_rotate]
  have h₁ : quadArea X B D L = quadArea A B F G :=
    half hABC hBD_BC hCBD hD hABFG hF hABFGpar hCAG hacB P₁.rotate.rotate.rotate hXLA
  -- Similarly, if AE, BK be joined, the parallelogram CL can also be proved equal to the
  -- square HC; therefore the whole square BDEC is equal to the two squares GB, HC. [C.N. 2]
  have h₂ : quadArea X C E L = quadArea A C K H :=
    half hABC.acb hCE_CB hBCE hE.swap hACKH hK hACKHpar hBAH hacC P₂.reverse hXLA
  /- The foot of AL lies between B and C, and L between D and E: A lies
     between BD and CE, and AL is parallel to both (`Between.of_inside`). -/
  have ss : ∀ {P Q R : Point} {N : Line},
      SameSide P Q N → SameSide Q R N → SameSide P R N :=
    fun h₁ h₂ => same_side_trans (same_side_symm h₁) h₂
  have hAC_BD : SameSide A C BD := same_side_symm (hCA_BD.sameSide hB_BD hD_BD)
  have hAB_CE : SameSide A B CE := same_side_symm (hBA_CE.sameSide hC_CE hE_CE)
  have hBXC : Between B X C :=
    Between.of_inside hB_BD hC_CE ⟨BC, hB_BC, hX_BC, hC_BC⟩
      (ss (hAL_BD.sameSide hX_AL hA_AL) hAC_BD)
      (ss (hAL_CE.sameSide hX_AL hA_AL) hAB_CE)
  have hCE_BD : SameSide C E BD :=
    same_side_symm (hpsq.sameSideOf.sameSide hB_BD hD_BD)
  have hBD_CE' : SameSide B D CE := hpsq.rotate.rotate.sameSideOf.sameSide hE_CE hC_CE
  have hDLE : Between D L E :=
    Between.of_inside hD_BD hE_CE ⟨DE, hD_DE, hL_DE, hE_DE⟩
      (ss (ss (hAL_BD.sameSide hL_AL hA_AL) hAC_BD) hCE_BD)
      (ss (ss (hAL_CE.sameSide hL_AL hA_AL) hAB_CE) hBD_CE')
  have hwhole : quadArea B D E C = quadArea X B D L + quadArea X C E L := by
    rw [quadArea_add_of_parallelograms P₁ P₂ hBXC hDLE,
      P₁.rotate.rotate.rotate.quadArea_rotate, quadArea_reverse X C E L]
  have hequal := hwhole.trans (CommonNotion2 h₁ h₂)
  -- And the square BDEC is described on BC, and the squares GB, HC on BA, AC.
  /- These are the three given squares. -/
  -- Therefore the square on the side BC is equal to the squares on the sides BA, AC.
  -- Therefore etc.
  -- Q. E. D.
  exact hequal

/-- The area identity for squares on either side of each base. Each square's far
corners lie together on one side of its base, with no prescribed side relative to
the triangle or to the other squares.

We construct outward squares by I.46, apply `Prop47`, and transfer the result by
`Prop46.square_eq`, since squares on the same base have equal areas. Euclid's
angle-addition argument remains in the outward configuration. -/
theorem Prop47.general {A B C D E F G H K : Point}
    (hABC : Triangle A B C) (hright : ∠ B A C = ∟)
    (hBDEC : Square B D E C) (hDE : SameSideOf D E B C)
    (hABFG : Square A B F G) (hFG : SameSideOf F G A B)
    (hACKH : Square A C K H) (hKH : SameSideOf K H A C) :
    quadArea B D E C = quadArea A B F G + quadArea A C K H := by
  obtain ⟨X, hXA, _⟩ := exists_oppositeSidesOf hABC.bca []
  obtain ⟨D', E', hsBC, hD', hE'⟩ := Prop46 hABC.ne₂₃ hXA.triangle
  obtain ⟨Y, hYC, _⟩ := exists_oppositeSidesOf hABC.bac []
  obtain ⟨F', G', hsBA, hF', hG'⟩ := Prop46 hABC.ne₁₂.symm hYC.triangle
  obtain ⟨Z, hZB, _⟩ := exists_oppositeSidesOf hABC.cab []
  obtain ⟨K', H', hsCA, hK', hH'⟩ := Prop46 hABC.ne₁₃.symm hZB.triangle
  have hDE' : SameSideOf D' E' B C := hD'.trans hE'.symm
  have hBC : quadArea B D E C = quadArea B D' E' C := by
    /- BC is the closing side of BDEC. Rotate both squares to compare that
       side, then use the parallelograms to return to their original areas. -/
    have hp := Prop28.square hBDEC.rotate.rotate.rotate hDE.swap
    have hp' := Prop28.square hsBC.rotate.rotate.rotate hDE'.swap
    have heq := Prop46.square_eq hBDEC.rotate.rotate.rotate hDE.swap
      hsBC.rotate.rotate.rotate hDE'.swap rfl
    rw [hp.quadArea_rotate, hp'.quadArea_rotate]
    exact heq
  have hBA : quadArea A B F' G' = quadArea A B F G :=
    Prop46.square_eq hsBA.rotate.rotate.rotate (hF'.trans hG'.symm).swap
      hABFG hFG rfl
  have hCA : quadArea A C K' H' = quadArea A C K H :=
    Prop46.square_eq hsCA.rotate.rotate.rotate (hK'.trans hH'.symm).swap
      hACKH hKH rfl
  have h47 := Prop47 hABC hright hsBC
    (hD'.trans_opposite hXA) (hE'.trans_opposite hXA)
    hsBA.rotate.rotate.rotate
    (hF'.trans_opposite hYC).swap (hG'.trans_opposite hYC).swap
    hsCA.rotate.rotate.rotate
    (hK'.trans_opposite hZB).swap (hH'.trans_opposite hZB).swap
  exact hBC.trans (h47.trans (CommonNotion2 hBA hCA))

end Elements.BookI
