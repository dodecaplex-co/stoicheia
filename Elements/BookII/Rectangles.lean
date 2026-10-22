import Elements.Figure.Basics
import Elements.BookI.Helpers
import Elements.BookI.Prop02
import Elements.BookI.Prop03
import Elements.BookI.Prop04
import Elements.BookI.Prop06
import Elements.BookI.Prop11
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop46
import Elements.BookI.Prop47
import Elements.BookI.HelpersParallels

/-!
# Book II: rectangles and squares, from Book I

Book II draws rectangles and squares and then speaks of them by their sides: "BH is
the rectangle A, BC, for it is contained by GB, BC, and BG is equal to A" (II.1);
"AE is the square on AB" (II.2). Euclid takes for granted that a parallelogram with
one right angle has all four right; that rectangles contained by equal straight lines
are equal, so that the rectangle drawn is the rectangle named; that a parallelogram
about the diameter of a square is a square; and that a parallelogram cut by two
parallels through a point of its diameter is the four parallelograms it is cut into,
so that "the gnomon NOP and LG are the whole square CEFB" (II.5). Each of these
cites a proposition of Book I, so they live here, before Book II's propositions,
and not in Book Zero.

At the end, I.47 is said once more of the squares on straight lines (`Prop47.sq`),
as Book II cites it again and again: "the square on EA is equal to the squares on
AC, CE, for the angle ACE is right [I. 47]".

The certificate walks through these steps as it walks through any helper, so a proof
that uses one is recorded as citing the propositions inside it; each docstring ends
with them.
-/

namespace Elements

open Tacit BookI

variable {A B C D E F G H K P Q R S P' Q' R' S' : Point}

/-! ## Rectangles -/

/-- One right angle makes a rectangle: a parallelogram ABCD whose angle at A is
right has all four of its angles right. The angles DAB, ABC stand on the parallels
AD, BC, so together they make two right angles [I. 29], and the angle at B is
right; in the same way so are the angles at C and D. Euclid says so in II.4 ("the
angles KBC, GCB are equal to two right angles"), and elsewhere in Book II takes it
for granted, as Heath remarks of II.4 that "there can be no need to repeat exactly
that part of the proof of I. 46 which shows that all the angles of the figure there
constructed are right when one is" (vol. 1, p. 381). [I. 29] -/
theorem Rectangle.of_right (h : Parallelogram A B C D) (hA : ∠ D A B = ∟) :
    Rectangle A B C D := by
  have next : ∀ {A B C D : Point}, Parallelogram A B C D → ∠ D A B = ∟ → ∠ A B C = ∟ := by
    intro A B C D h hA
    have h29 : ∠ D A B + ∠ A B C = ∟ + ∟ :=
      Prop29.interior h.2.symm.swap_left h.sameSideOf.symm
    rw [hA, add_comm] at h29
    exact CommonNotion3 h29 rfl
  have hB := next h hA
  have hC := next h.rotate hB
  have hD := next h.rotate.rotate hC
  exact ⟨h, hA, hB, hC, hD⟩

/-- Rectangles contained by equal straight lines are equal: if the rectangles PQRS,
P'Q'R'S' have PQ equal to P'Q' and PS to P'S', they are equal. The diameter
QS cuts off the triangle SPQ, right-angled at P, which is half the rectangle
[I. 34]; and the two halves are equal [I. 4]. Euclid takes this for granted whenever
he names a rectangle by its sides. [I. 4, I. 34] -/
theorem Rectangle.congr (h : Rectangle P Q R S) (h' : Rectangle P' Q' R' S')
    (h₁ : ‖P Q‖ = ‖P' Q'‖) (h₂ : ‖P S‖ = ‖P' S'‖) :
    quadArea P Q R S = quadArea P' Q' R' S' := by
  have half : ∀ {P Q R S : Point}, Rectangle P Q R S →
      quadArea P Q R S = △ P S Q + △ P S Q := by
    intro P Q R S h
    have hp : Parallelogram S P Q R := h.1.rotate.rotate.rotate
    rw [hp.quadArea_rotate, Prop34.bisect hp, area_bac S P Q]
  have hp : Parallelogram S P Q R := h.1.rotate.rotate.rotate
  have hp' : Parallelogram S' P' Q' R' := h'.1.rotate.rotate.rotate
  have t : △ P S Q = △ P' S' Q' :=
    (Prop4 hp.triangle.bac hp'.triangle.bac h₂ h₁ (h.2.1.trans h'.2.1.symm)).2.1
  rw [half h, half h', t]

/-- **A rectangle is contained by its sides** (Definition II.1): the rectangle PQRS is
the rectangle contained by PQ, PS, the two straight lines containing its right
angle at P. `rect` chose some rectangle contained by straight lines equal to these,
and by `Rectangle.congr` the two are equal. [I. 4, I. 34] -/
theorem Rectangle.contained (h : Rectangle P Q R S) : quadArea P Q R S = rect P Q P S := by
  have hex : ∃ x, Contain ‖P Q‖ ‖P S‖ x := ⟨_, Or.inr ⟨P, Q, R, S, h, rfl, rfl, rfl⟩⟩
  unfold rect
  rcases Classical.epsilon_spec hex with ⟨h0 | h0, -⟩ | ⟨P', Q', R', S', h', h₁, h₂, hx⟩
  · exact absurd (eq_of_len_eq_zero h0) h.1.1.1
  · exact absurd (eq_of_len_eq_zero h0).symm h.1.2.2.1
  · rw [← hx]
    exact h.congr h' h₁.symm h₂.symm

/-- Euclid's way of naming a rectangle: "BH is the rectangle A, BC, for it is contained
by GB, BC, and BG is equal to A" (II.1). If the sides PQ, PS of the rectangle
PQRS are equal to AB, CD, it is the rectangle contained by AB, CD.
[I. 4, I. 34] -/
theorem Rectangle.eq_rect (h : Rectangle P Q R S) (h₁ : ‖P Q‖ = ‖A B‖) (h₂ : ‖P S‖ = ‖C D‖) :
    quadArea P Q R S = rect A B C D :=
  h.contained.trans (rect_congr h₁ h₂)

/-- Euclid takes for granted that the rectangle contained by two given straight
lines can be described. We carry out, from Book I, the construction that II.1
makes: raise a perpendicular to AB at A on P's side [I. 11], produce it far
enough to cut off AE equal to CD [I. 2, I. 3], and complete ABFE by parallels
[I. 30, I. 31]. Both E and F lie on P's side of AB. Its angles are right (`Rectangle.of_right`), and its area is
the rectangle contained by AB, CD (`Rectangle.eq_rect`).
[I. 2, I. 3, I. 4, I. 11, I. 29, I. 30, I. 31, I. 34] -/
theorem exists_rect {A B C D P : Point} (hAB : A ≠ B) (hCD : C ≠ D) (hP : ¬ Collinear A B P) :
    ∃ E F : Point, Rectangle A B F E ∧ ‖A E‖ = ‖C D‖ ∧ SameSideOf E P A B ∧
      SameSideOf F P A B ∧ quadArea A B F E = rect A B C D := by
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  obtain ⟨Q, hQP, hright⟩ := BookI.Prop11 hAB ⟨AB, hA_AB, hB_AB, hA_AB⟩ hP
  have hBAQ : ∠ B A Q = ∟ := hright B ⟨AB, hA_AB, hB_AB, hB_AB⟩ hAB.symm
  obtain ⟨R, hAR⟩ := BookI.Prop2 A C D hCD
  have hAQ : A ≠ Q := hQP.triangle.ne₁₃
  obtain ⟨Y, hQAY⟩ := produce hAQ.symm
  obtain ⟨X, hYAX, hlt⟩ :=
    produce_longer (ne_of_between (between_symm hQAY)) (ne_of_len_eq hAR hCD)
  have hX : OnRay X A Q := OnRay.of_between_between (between_symm hQAY) hYAX
  obtain ⟨E, hAEX, hAE⟩ := BookI.Prop3 hCD (hAR ▸ hlt)
  have hBAE : ∠ B A E = ∟ := by
    rw [angle_onRay_right (OnRay.of_between hAEX) hAB.symm, angle_onRay_right hX hAB.symm]
    exact hBAQ
  have hEP : SameSideOf E P A B :=
    SameSideOf.of_onRay (OnRay.of_between hAEX) (SameSideOf.of_onRay hX hQP)
  have hE_AB : ¬ OnLine E AB := not_on_line_of_same_side (hEP.sameSide hA_AB hB_AB)
  obtain ⟨EF, hE_EF, hEF_AB⟩ := BookI.Prop31.line hE_AB
  obtain ⟨F, -, hEABF⟩ := BookI.Prop31.parallelogram hEF_AB hE_EF hA_AB hB_AB hAB
  have hrect : Rectangle A B F E := Rectangle.of_right hEABF.rotate
    ((angle_symm (ne_of_between hAEX).symm hAB.symm).trans hBAE)
  exact ⟨E, F, hrect, hAE, hEP, hrect.1.sameSideOf.trans hEP, hrect.eq_rect rfl hAE⟩

/-! ## Squares -/

/-- A square is the square on its side: the square ABCD, a parallelogram, is the
square on AB. [I. 4, I. 34] -/
theorem Square.eq_sq (h : Square A B C D) (hp : Parallelogram A B C D) :
    quadArea A B C D = sq A B :=
  (h.rectangle hp).eq_rect rfl h.len_eq

/-- The square ADEB that I.46 describes on AB, with D and E on the side of AB
where P is, is a parallelogram [I. 28], and it is the square on AB: "AE is the
square on AB" (II.2). [I. 4, I. 28, I. 34] -/
theorem Square.described (h : Square A D E B) (hD : SameSideOf D P A B)
    (hE : SameSideOf E P A B) : Parallelogram A D E B ∧ quadArea A D E B = sq A B := by
  have hp : Parallelogram A D E B :=
    (Prop28.square h.rotate.rotate.rotate (hD.trans hE.symm).swap).rotate
  exact ⟨hp, (h.eq_sq hp).trans (sq_congr h.len_eq.symm)⟩

/-- **In square areas the parallelograms about the diameter are squares.** If ABCD is a
square and a parallelogram, K lies on its diameter AC, and AEKH is a
parallelogram with E on AB and H on AD, then AEKH is a square.

Heath's note on II.4 quotes this from the Greek text, where it stands as a porism,
"undoubtedly interpolated" (vol. 1, p. 381), and his 1908 text leaves it out. Euclid
proves its first case inside II.4 ("CGKB is equilateral ... it is also
right-angled"), says "for the same reason" for the second, and in II.5–II.8 takes it
for granted: "LG, which is equal to the square on CD".

The angle EKA is equal to the alternate angle KAH [I. 29], that is to CAD, which
is equal to the alternate angle ACB [I. 29], and so to BAC [I. 5]. So the angles
EAK, EKA are equal, and EK is equal to EA [I. 6]; the opposite sides are
equal [I. 34]; and the angle at A is the square's, so all four are right
(`Rectangle.of_right`). [I. 5, I. 6, I. 29, I. 34] -/
theorem Square.about_diameter (h : Square A B C D) (hp : Parallelogram A B C D)
    (hK : Between A K C) (hE : Between A E B) (hH : Between A H D)
    (hAEKH : Parallelogram A E K H) : Square A E K H := by
  have hABC : Triangle A B C := hp.triangle
  /- The angles BAC, BCA at the base of the isosceles triangle BAC are equal. [I. 5] -/
  have h₁ : ∠ B A C = ∠ B C A := Prop5.base hABC.bac (len_symm B A ▸ h.1)
  /- The alternate angles BCA, CAD are equal. [I. 29] -/
  have h₂ : ∠ B C A = ∠ C A D :=
    Prop29.alternate hp.2.swap_right (hp.2.swap_right.oppositeSidesOf hp.sameSideOf.swap)
  /- The alternate angles EKA, KAH are equal. [I. 29] -/
  have h₃ : ∠ E K A = ∠ K A H :=
    Prop29.alternate hAEKH.2.swap_right
      (hAEKH.2.swap_right.oppositeSidesOf hAEKH.sameSideOf.swap)
  have hKray : OnRay K A C := OnRay.of_between hK
  have h₄ : ∠ K A H = ∠ C A D := angle_eq_of_onRay hKray (OnRay.of_between hH)
  have h₅ : ∠ E A K = ∠ B A C := angle_eq_of_onRay (OnRay.of_between hE) hKray
  have hEAK : Triangle E A K := hAEKH.triangle.bac
  /- So EA is equal to EK. [I. 6] -/
  have hEA_EK : ‖E A‖ = ‖E K‖ :=
    Prop6 hEAK (h₅.trans (h₁.trans (h₂.trans (h₄.symm.trans h₃.symm))))
  /- The opposite sides of AEKH are equal. [I. 34] -/
  obtain ⟨hAH_EK, hAE_HK, -, -, -⟩ := Prop34 (A := A) (B := H) (C := E) (D := K) hAEKH
  have hrect : Rectangle A E K H := by
    refine Rectangle.of_right hAEKH ?_
    rw [angle_eq_of_onRay (OnRay.of_between hH) (OnRay.of_between hE)]
    exact h.2.2.2.1
  refine ⟨?_, ?_, ?_, hrect.2⟩
  · rw [len_symm A E]; exact hEA_EK
  · rw [len_symm K H, ← hAE_HK, len_symm A E]; exact hEA_EK.symm
  · rw [len_symm K H, ← hAE_HK, len_symm H A, hAH_EK, len_symm A E]; exact hEA_EK

/-! ## The parallelograms about a diameter, and the gnomon -/

/-- The complements are parallelograms. In I.43's figure, the parallelogram ABCD with
the parallelograms AEKH, KGCF about its diameter AC, the complements EBGK and
HKFD are parallelograms too: each straight line through K is parallel to the side
it runs beside, both being parallel to the opposite side [I. 30]. [I. 30] -/
theorem Parallelogram.complements (hABCD : Parallelogram A B C D) (hK : Between A K C)
    (hE : Between A E B) (hG : Between B G C) (hF : Between C F D) (hH : Between D H A)
    (hEH : Parallelogram A E K H) (hFG : Parallelogram K G C F) :
    Parallelogram E B G K ∧ Parallelogram H K F D := by
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hABCD.1.1
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hABCD.1.2.1
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABCD.2.1
  obtain ⟨DA, hD_DA, hA_DA⟩ := Postulate1 D A hABCD.2.2.1
  have hE_AB : OnLine E AB := on_line_of_between_ends hE hA_AB hB_AB
  have hG_BC : OnLine G BC := on_line_of_between_ends hG hB_BC hC_BC
  have hF_CD : OnLine F CD := on_line_of_between_ends hF hC_CD hD_CD
  have hH_DA : OnLine H DA := on_line_of_between_ends hH hD_DA hA_DA
  have hAB_CD : Parallel AB CD := hABCD.1.parallel hA_AB hB_AB hC_CD hD_CD
  have hBC_DA : Parallel BC DA := hABCD.2.parallel hB_BC hC_BC hD_DA hA_DA
  have hC_AB : ¬ OnLine C AB := hAB_CD.symm.not_onLine hC_CD
  have hA_BC : ¬ OnLine A BC := hBC_DA.symm.not_onLine hA_DA
  have hK_AB : ¬ OnLine K AB := fun h => hC_AB (on_line_of_between hK hA_AB h)
  have hK_BC : ¬ OnLine K BC := fun h => hA_BC (on_line_of_between (between_symm hK) hC_BC h)
  have hK_CD : ¬ OnLine K CD := fun h =>
    hAB_CD.not_onLine hA_AB (on_line_of_between (between_symm hK) hC_CD h)
  have hK_DA : ¬ OnLine K DA := fun h =>
    hBC_DA.not_onLine hC_BC (on_line_of_between hK hA_DA h)
  obtain ⟨KG, hK_KG, hG_KG⟩ := Postulate1 K G hFG.1.1
  obtain ⟨KE, hK_KE, hE_KE⟩ := Postulate1 K E hEH.2.1.symm
  obtain ⟨KH, hK_KH, hH_KH⟩ := Postulate1 K H hEH.1.2.1
  obtain ⟨KF, hK_KF, hF_KF⟩ := Postulate1 K F hFG.2.2.1.symm
  have hKG_CD : Parallel KG CD := hFG.1.parallel hK_KG hG_KG hC_CD hF_CD
  have hKE_DA : Parallel KE DA := hEH.2.swap_left.parallel hK_KE hE_KE hH_DA hA_DA
  have hKH_AB : Parallel KH AB := hEH.1.symm.parallel hK_KH hH_KH hA_AB hE_AB
  have hKF_BC : Parallel KF BC := hFG.2.symm.swap_left.parallel hK_KF hF_KF hG_BC hC_BC
  have h₁ : Parallel AB KG := Prop30.parallel hAB_CD hKG_CD (fun e => hK_AB (e ▸ hK_KG))
  have h₂ : Parallel BC KE := Prop30.parallel hBC_DA hKE_DA (fun e => hK_BC (e ▸ hK_KE))
  have h₃ : Parallel KH CD := Prop30.parallel hKH_AB hAB_CD.symm (fun e => hK_CD (e ▸ hK_KH))
  have h₄ : Parallel KF DA := Prop30.parallel hKF_BC hBC_DA.symm (fun e => hK_DA (e ▸ hK_KF))
  exact ⟨⟨AreParallel.of_parallel (ne_of_between (between_symm hE)).symm hFG.1.1.symm
        hE_AB hB_AB hG_KG hK_KG h₁,
      AreParallel.of_parallel (ne_of_between hG) hEH.2.1.symm hB_BC hG_BC hK_KE hE_KE h₂⟩,
    ⟨AreParallel.of_parallel hEH.1.2.1.symm (ne_of_between (between_symm hF)).symm
        hH_KH hK_KH hF_CD hD_CD h₃,
      AreParallel.of_parallel hFG.2.2.1.symm (ne_of_between hH) hK_KF hF_KF hD_DA hH_DA h₄⟩⟩

/-- **The gnomon and the rest are the whole.** In I.43's figure, the parallelogram
ABCD is the two parallelograms AEKH, KGCF about its diameter AC together with
the two complements EBGK, HKFD. So a gnomon (Definition II.2), one parallelogram
about the diameter with the two complements, makes the whole together with the other
parallelogram about the diameter: "the gnomon NOP and LG are the whole square CEFB"
(II.5). The complements are parallelograms (`Parallelogram.complements`), HKG and
EKF are straight lines, and the whole is cut along each in turn
(`quadArea_add_of_parallelograms`). [I. 30] -/
theorem Parallelogram.about_diameter (hABCD : Parallelogram A B C D) (hK : Between A K C)
    (hE : Between A E B) (hG : Between B G C) (hF : Between C F D) (hH : Between D H A)
    (hEH : Parallelogram A E K H) (hFG : Parallelogram K G C F) :
    quadArea A B C D =
      quadArea A E K H + quadArea E B G K + quadArea K G C F + quadArea H K F D := by
  obtain ⟨hEBGK, hHKFD⟩ := hABCD.complements hK hE hG hF hH hEH hFG
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABCD.2.1
  obtain ⟨DA, hD_DA, hA_DA⟩ := Postulate1 D A hABCD.2.2.1
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hABCD.1.1
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hABCD.1.2.1
  have hBC_DA : Parallel BC DA := hABCD.2.parallel hB_BC hC_BC hD_DA hA_DA
  have hAB_CD : Parallel AB CD := hABCD.1.parallel hA_AB hB_AB hC_CD hD_CD
  have hG_BC : OnLine G BC := on_line_of_between_ends hG hB_BC hC_BC
  have hH_DA : OnLine H DA := on_line_of_between_ends hH hD_DA hA_DA
  have hE_AB : OnLine E AB := on_line_of_between_ends hE hA_AB hB_AB
  have hK_DA : ¬ OnLine K DA := fun h =>
    hBC_DA.not_onLine hC_BC (on_line_of_between hK hA_DA h)
  have hK_BC : ¬ OnLine K BC := fun h =>
    hBC_DA.symm.not_onLine hA_DA (on_line_of_between (between_symm hK) hC_BC h)
  /- H, K, G lie on one straight line, parallel to AB: through K there is
     only one parallel to AB (`Prop30.meet`). -/
  obtain ⟨KH, hK_KH, hH_KH⟩ := Postulate1 K H hEH.1.2.1
  obtain ⟨KG, hK_KG, hG_KG⟩ := Postulate1 K G hEBGK.1.2.1.symm
  have hKH_AB : Parallel KH AB := hEH.1.symm.parallel hK_KH hH_KH hA_AB hE_AB
  have hKG_AB : Parallel KG AB :=
    (hEBGK.1.parallel hE_AB hB_AB hG_KG hK_KG).symm
  have hKG_KH : KG = KH := by
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨X, hX_KG, hX_AB⟩ := Prop30.meet hKH_AB.symm hK_KH hK_KG hne
    exact hKG_AB.not_onLine hX_KG hX_AB
  have hG_KH : OnLine G KH := hKG_KH ▸ hG_KG
  /- K lies between G and H, being between the parallels BC, DA. -/
  have hKG_DA : SameSide K G DA :=
    same_side_trans (same_side_symm (pasch2 hK hA_DA hK_DA))
      (same_side_symm (hBC_DA.sameSide hG_BC hC_BC))
  have hKH_BC : SameSide K H BC :=
    same_side_trans (same_side_symm (pasch2 (between_symm hK) hC_BC hK_BC))
      (same_side_symm (hBC_DA.symm.sameSide hH_DA hA_DA))
  have hGKH : Between G K H :=
    Between.of_inside hG_BC hH_DA ⟨KH, hG_KH, hK_KH, hH_KH⟩ hKH_BC hKG_DA
  have hGH : G ≠ H := ne_of_between_ends hGKH
  /- So ABGH and HGCD are parallelograms. -/
  have hABGH : Parallelogram A B G H :=
    ⟨AreParallel.of_parallel hABCD.1.1 hGH hA_AB hB_AB hG_KH hH_KH hKH_AB.symm,
      AreParallel.of_parallel (ne_of_between hG) (ne_of_between (between_symm hH)).symm hB_BC
        hG_BC hH_DA hA_DA hBC_DA⟩
  have hHGCD : Parallelogram H G C D :=
    ⟨AreParallel.of_parallel hGH.symm hABCD.1.2.1 hH_KH hG_KH hC_CD hD_CD
      (Prop30.parallel hKH_AB hAB_CD.symm fun e =>
        hAB_CD.not_onLine hA_AB (on_line_of_between (between_symm hK) hC_CD (e ▸ hK_KH))),
      AreParallel.of_parallel (ne_of_between (between_symm hG)).symm (ne_of_between hH)
        hG_BC hC_BC hD_DA hH_DA hBC_DA⟩
  /- We cut the whole along HG, then each part along EK and KF. -/
  have hwhole : quadArea A B C D = quadArea A B G H + quadArea H G C D :=
    quadArea_add_of_parallelograms hABGH hHGCD (between_symm hH) hG
  have hupper : quadArea B G H A = quadArea B G K E + quadArea E K H A :=
    quadArea_add_of_parallelograms hEBGK.rotate hEH.rotate (between_symm hE) hGKH
  have hlower : quadArea G C D H = quadArea G C F K + quadArea K F D H :=
    quadArea_add_of_parallelograms hFG.rotate hHKFD.rotate hGKH hF
  rw [hwhole, ← hABGH.quadArea_rotate, hupper, ← hHGCD.quadArea_rotate, hlower,
    hEBGK.quadArea_rotate, hEH.quadArea_rotate, hFG.quadArea_rotate, hHKFD.quadArea_rotate]
  ac_rfl

/-- **"Let the figure be drawn."** In the parallelogram ADEB, with C on its side AB,
draw the diameter BD; through C the parallel CF to AD, cutting BD at G and
DE at F; and through G the parallel HK to AB, cutting AD at H and BE at K
[I. 31]. Each point where a parallel is cut is found by `Prop30.meet`. Then G lies
between B and D, each other point between the ends of its side, G between C and
F and between H and K, and CGKB, GHDF are the parallelograms about the diameter:
everything I.43 asks for, and `Parallelogram.about_diameter` with it.

This is the figure of Book II. II.4 draws it line by line in these letters; II.7 says only
"let the figure be drawn"; II.5 and II.6 draw it in a square on CB and on CD, and II.8
draws it twice ("let the figure be drawn double"). [I. 30, I. 31] -/
theorem Parallelogram.figure (hp : Parallelogram A D E B) (hACB : Between A C B) :
    ∃ F G H K : Point, Between B G D ∧ Between D F E ∧ Between A H D ∧ Between E K B ∧
      Between C G F ∧ Between H G K ∧ Parallelogram B C G K ∧ Parallelogram G H D F := by
  have hAB : A ≠ B := hp.2.2.1.symm
  have hAD : A ≠ D := hp.1.1
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  obtain ⟨AD, hA_AD, hD_AD⟩ := Postulate1 A D hAD
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hp.2.1
  obtain ⟨BE, hB_BE, hE_BE⟩ := Postulate1 B E hp.1.2.1.symm
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D (hp.rotate.rotate.rotate.triangle.ne₁₃)
  have hC_AB : OnLine C AB := on_line_of_between_ends hACB hA_AB hB_AB
  have hAD_BE : Parallel AD BE := hp.1.parallel hA_AD hD_AD hE_BE hB_BE
  have hDE_AB : Parallel DE AB := hp.2.parallel hD_DE hE_DE hB_AB hA_AB
  have hD_AB : ¬ OnLine D AB := hDE_AB.not_onLine hD_DE
  have hB_AD : ¬ OnLine B AD := hAD_BE.symm.not_onLine hB_BE
  have hE_AD : ¬ OnLine E AD := hAD_BE.symm.not_onLine hE_BE
  have hB_DE : ¬ OnLine B DE := hDE_AB.symm.not_onLine hB_AB
  have hC_AD : ¬ OnLine C AD := fun h =>
    hD_AB ((line_unique (ne_of_between hACB) hA_AD h hA_AB hC_AB) ▸ hD_AD)
  have hC_BE : ¬ OnLine C BE := fun h =>
    hDE_AB.not_onLine hE_DE
      ((line_unique (ne_of_between (between_symm hACB)).symm h hB_BE hC_AB hB_AB) ▸ hE_BE)
  /- Through C we draw the parallel to AD; it meets BD at G and DE at F. -/
  obtain ⟨U, V, hUCV, hUV⟩ := Prop31 hAD fun ⟨L, hA, hD, hC⟩ =>
    hC_AD ((line_unique hAD hA hD hA_AD hD_AD) ▸ hC)
  obtain ⟨CF, hU_CF, hV_CF⟩ := Postulate1 U V hUV.1
  have hC_CF : OnLine C CF := on_line_of_between_ends hUCV hU_CF hV_CF
  have hCF_AD : Parallel CF AD := hUV.parallel hU_CF hV_CF hA_AD hD_AD
  obtain ⟨G, hG_BD, hG_CF⟩ :=
    Prop30.meet hCF_AD hD_AD hD_BD fun e => hB_AD (e ▸ hB_BD)
  obtain ⟨F, hF_DE, hF_CF⟩ :=
    Prop30.meet hCF_AD hD_AD hD_DE fun e => hE_AD (e ▸ hE_DE)
  have hCF_BE : Parallel CF BE := Prop30.parallel hCF_AD hAD_BE.symm fun e =>
    hC_BE (e ▸ hC_CF)
  have hBGD : Between B G D := Parallel.between hCF_BE.symm hCF_AD.symm hB_BE hC_CF hA_AD
    (between_symm hACB) hB_BE hG_CF hD_AD ⟨BD, hB_BD, hG_BD, hD_BD⟩
  have hDFE : Between D F E := Parallel.between hCF_AD.symm hCF_BE.symm hA_AD hC_CF hB_BE
    hACB hD_AD hF_CF hE_BE ⟨DE, hD_DE, hF_DE, hE_DE⟩
  /- Through G we draw the parallel to AB; it meets AD at H and BE at K. -/
  have hG_AB : ¬ OnLine G AB := fun h =>
    hD_AB (on_line_of_between hBGD hB_AB h)
  have hG_DE : ¬ OnLine G DE := fun h =>
    hB_DE (on_line_of_between (between_symm hBGD) hD_DE h)
  obtain ⟨U', V', hU'GV', hU'V'⟩ := Prop31 hAB fun ⟨L, hA, hB, hG⟩ =>
    hG_AB ((line_unique hAB hA hB hA_AB hB_AB) ▸ hG)
  obtain ⟨HK, hU'_HK, hV'_HK⟩ := Postulate1 U' V' hU'V'.1
  have hG_HK : OnLine G HK := on_line_of_between_ends hU'GV' hU'_HK hV'_HK
  have hHK_AB : Parallel HK AB := hU'V'.parallel hU'_HK hV'_HK hA_AB hB_AB
  obtain ⟨H, hH_AD, hH_HK⟩ :=
    Prop30.meet hHK_AB hA_AB hA_AD fun e => hD_AB (e ▸ hD_AD)
  obtain ⟨K, hK_BE, hK_HK⟩ :=
    Prop30.meet hHK_AB hB_AB hB_BE fun e => hDE_AB.not_onLine hE_DE (e ▸ hE_BE)
  have hHK_DE : Parallel HK DE := Prop30.parallel hHK_AB hDE_AB fun e =>
    hG_DE (e ▸ hG_HK)
  /- Parallels keep order. -/
  have hAHD : Between A H D := Parallel.between hHK_AB.symm hHK_DE.symm hB_AB hG_HK hD_DE
    hBGD hA_AB hH_HK hD_DE ⟨AD, hA_AD, hH_AD, hD_AD⟩
  have hEKB : Between E K B := Parallel.between hHK_DE.symm hHK_AB.symm hD_DE hG_HK hB_AB
    (between_symm hBGD) hE_DE hK_HK hB_AB ⟨BE, hE_BE, hK_BE, hB_BE⟩
  have hCGF : Between C G F := Parallel.between hHK_AB.symm hHK_DE.symm hB_AB hG_HK hD_DE
    hBGD hC_AB hG_HK hF_DE ⟨CF, hC_CF, hG_CF, hF_CF⟩
  have hHGK : Between H G K := Parallel.between hCF_AD.symm hCF_BE.symm hA_AD hC_CF hB_BE
    hACB hH_AD hG_CF hK_BE ⟨HK, hH_HK, hG_HK, hK_HK⟩
  refine ⟨F, G, H, K, hBGD, hDFE, hAHD, hEKB, hCGF, hHGK, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact AreParallel.of_parallel (ne_of_between (between_symm hACB))
      (ne_of_between (between_symm hHGK)).symm hB_AB hC_AB hG_HK hK_HK hHK_AB.symm
  · exact AreParallel.of_parallel (ne_of_between hCGF) (ne_of_between (between_symm hEKB)).symm
      hC_CF hG_CF hK_BE hB_BE hCF_BE
  · exact AreParallel.of_parallel (ne_of_between hHGK).symm (ne_of_between hDFE) hG_HK hH_HK
      hD_DE hF_DE hHK_DE
  · exact AreParallel.of_parallel (ne_of_between (between_symm hAHD)).symm
      (ne_of_between (between_symm hCGF)) hH_AD hD_AD hF_CF hG_CF hCF_AD.symm

/-! ## I.47, said of the squares on straight lines -/

/-- **I.47 for the squares on straight lines.** In the triangle ABC right-angled at
A, the square on BC is equal to the squares on BA, AC. Book II cites I.47 in
this form: "the square on EA is equal to the squares on AC, CE, for the angle ACE is
right" (II.9). The three squares are described outward [I. 46], I.47 compares them,
and each is the square on its side (`Square.described`).
[I. 4, I. 28, I. 34, I. 46, I. 47] -/
theorem BookI.Prop47.sq (hABC : Triangle A B C) (hright : ∠ B A C = ∟) :
    sq B C = sq B A + sq A C := by
  /- The square on BC is described on the other side of BC from A. -/
  obtain ⟨P, hP, -⟩ := exists_oppositeSidesOf hABC.bca []
  obtain ⟨D, E, hBDEC, hD, hE⟩ := Prop46 hABC.ne₂₃ hP.triangle
  /- The square on AB is described on the other side of AB from C. -/
  obtain ⟨Q, hQ, -⟩ := exists_oppositeSidesOf hABC []
  obtain ⟨G, F, hAGFB, hG, hF⟩ := Prop46 hABC.ne₁₂ hQ.triangle
  /- The square on AC is described on the other side of AC from B. -/
  obtain ⟨R, hR, -⟩ := exists_oppositeSidesOf hABC.acb []
  obtain ⟨H, K, hAHKC, hH, hK⟩ := Prop46 hABC.ne₁₃ hR.triangle
  obtain ⟨-, hsq₁⟩ := Square.described hBDEC hD hE
  obtain ⟨hp₂, hsq₂⟩ := Square.described hAGFB hG hF
  obtain ⟨hp₃, hsq₃⟩ := Square.described hAHKC hH hK
  have h47 := Prop47 hABC hright hBDEC (hD.trans_opposite hP) (hE.trans_opposite hP)
    (hAGFB.reverse hp₂) (hF.trans_opposite hQ) (hG.trans_opposite hQ)
    (hAHKC.reverse hp₃) (hK.trans_opposite hR) (hH.trans_opposite hR)
  rw [quadArea_reverse A G F B, quadArea_reverse A H K C, hsq₁, hsq₂, hsq₃] at h47
  rw [h47, sq_symm A B]

end Elements
