import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop04
import Elements.BookI.Prop20
import Elements.BookI.Prop21
import Elements.BookI.Prop23
import Elements.BookI.Prop24
import Elements.BookIII.Prop01
import Elements.BookIII.Prop02

/-!
# Book III, Proposition 8

Euclid's text, in Heath's translation: [`heath/III/08.md`](../../heath/III/08.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

`Prop8` is Euclid's worked configuration: the nearer and the more remote are compared only
when both lie on one side of the straight line DA, as in his figure. The companion after it,
`Prop8.general`, compares any two, on one side or on opposite sides, within each of Euclid's
two classes, and never across them.

The classes are read as `Prop8` reads them. A point E of the circle is on the concave
circumference when a straight line from D meets the circle at some point before reaching E:
some point H of the circle is between D and E. A point K is on the convex circumference when
the straight line from D through K meets the circle again beyond K: K is between D and some
point C of the circle. "Nearer" is the less angle at D with the ray DA, the ray through the
centre. On the concave circumference the less angle has the greater straight line; on the
convex, the less angle has the less. The two orders are kept apart, for they disagree: the
two points where one straight line from D meets the circle make the same angle with DA, and
are at different distances from D.

A straight line touching the circle from D falls on neither class. This is a convention,
read from Euclid's "drawn through to the circle": a straight line that touches does not meet
the circle at two points (Definition III.2), so its point of contact has no point of the
circle between it and D and none beyond it. That step follows from Definition III.2, and is
not stated in Lean; the comparisons say nothing of the point of contact. The last clause
does: every point of the circle off DA, a point of contact included, has one partner on the
other side as far from D, and no third.

That no third straight line from D is equal to DK is proved by Euclid's own step, "which was
proved impossible". On DA, a third point N would be A or G, and DA is the greatest and DG the
least. Off DA, DN and the straight line it is compared with, DB or DK, are on one side of
DA, and the one making the less angle with DA is the nearer to DG. Where the nearer falls on
the convex circumference it is the less, by the order proved earlier in the proof, so the
two cannot be equal; where it falls on the concave, a case Euclid's figure leaves aside, it
is the greater, by that circumference's own order. Euclid's argument for each order asks only
that the nearer be on its circumference, by I.21 within the triangle on the more remote point
or by I.24 at the centre M, so the more remote may be on the other circumference, or a point
of contact, which is on neither and ends both orders: no point of the circle on its side makes
a greater angle with DA (`Prop8.contact_last`), so it is never the nearer.

`Prop8.partner` is the step the companion needs: the partner on the other side makes the
same angle with DA, and is in the same class. Equal distance alone does not carry a
comparison across DA: the comparison on one side asks for the angle and the class, and the
step proves both of the partner.
-/

namespace Elements.BookIII

open Tacit

/-- This is the second of Augustus De Morgan's assumptions: E falls outside the triangle
DFM, so that the angle EMD is greater than the angle FMD. As in III.7, DE crosses MF at
a point Y within the circle, and Y is between H and E (System E, Circle 1), so E lies
beyond MF. -/
theorem Prop8.outside {D M E F H : Point} {α : Circle} (hM : Centre M α) (hE : OnCircle E α)
    (hF : OnCircle F α) (hH : OnCircle H α) (hDHE : Between D H E) (hEF : SameSideOf E F D M)
    (hlt : ∠ M D E < ∠ M D F) : ∠ F M D < ∠ E M D := by
  have hEM : SameSideOf E M D F := BookI.Prop24.within hEF.symm hlt
  obtain ⟨Y, hMYF, hY⟩ := crossbar hEF hEM
  have hY_in : InsideCircle Y α := InsideCircle.of_between_centre hM hF hMYF
  obtain ⟨-, -, ⟨L, hD_L, hE_L, hY_L⟩, -⟩ := hY
  have hH_L : OnLine H L := on_line_of_between_ends hDHE hD_L hE_L
  have hHE : H ≠ E := ne_of_between (between_symm hDHE) |>.symm
  have hHYE : Between H Y E := between_of_inside_chord hY_L hH_L hE_L hY_in hH hE hHE
  have hEYD : Between E Y D := between_of_between_left (between_symm hDHE) (between_symm hHYE)
  have hEDM : Triangle E D M := hEF.triangle.cab
  have h1 : ∠ Y M D < ∠ E M D := angle_lt_of_between hEDM hEYD
  rwa [angle_onRay_left (OnRay.of_between hMYF) hEF.1] at h1

/-- This is De Morgan's first assumption: K falls within the triangle DLM. DK crosses ML
at a point Z within the circle, and K is between D and Z. -/
theorem Prop8.within {D M K L C : Point} {α : Circle} (hM : Centre M α) (hK : OnCircle K α)
    (hL : OnCircle L α) (hC : OnCircle C α) (hDKC : Between D K C) (hKL : SameSideOf K L D M)
    (hlt : ∠ M D K < ∠ M D L) : InsideTriangle K L M D := by
  have hKM : SameSideOf K M D L := BookI.Prop24.within hKL.symm hlt
  obtain ⟨Z, hMZL, hZ⟩ := crossbar hKL hKM
  have hZ_in : InsideCircle Z α := InsideCircle.of_between_centre hM hL hMZL
  obtain ⟨-, -, ⟨N, hD_N, hK_N, hZ_N⟩, -⟩ := hZ
  have hC_N : OnLine C N := on_line_of_between hDKC hD_N hK_N
  have hKC : K ≠ C := (ne_of_between (between_symm hDKC)).symm
  have hKZC : Between K Z C := between_of_inside_chord hZ_N hK_N hC_N hZ_in hK hC hKC
  have hDKZ : Between D K Z := between_cut hDKC hKZC
  /- K is on D's side of LM, for Z is on LM and K is between D and Z. -/
  have hLM : L ≠ M := ne_of_between_ends (between_symm hMZL)
  obtain ⟨P, hL_P, hM_P⟩ := Postulate1 L M hLM
  have hZ_P : OnLine Z P := on_line_of_between_ends hMZL hM_P hL_P
  have hD_P : ¬ OnLine D P := hKL.symm.triangle.cba.off_line hL_P hM_P
  have hK_P : ¬ OnLine K P := fun hK_P =>
    hD_P (on_line_of_between (between_symm hDKZ) hZ_P hK_P)
  exact ⟨hKL.swap, hKM, SameSideOf.of_line hLM hL_P hM_P (pasch2 (between_symm hDKZ) hZ_P hK_P)⟩

/-- A point of contact is at the end of both orders. Let T be a point of the circle with no
point of the circle between D and T, and none on DT produced beyond T: a point where a
straight line from D touches the circle, on neither circumference. Then no point R of the
circle on T's side of DM makes a greater angle with DM at D. Otherwise DT, within the angle
MDR, crosses the radius MR at a point Y within the circle (`crossbar`,
`InsideCircle.of_between_centre`), and Y is not T. If Y is between D and T, the straight
line meets the circle between D and Y (System E, Intersections 4); if T is between D and Y,
it meets it again beyond Y (Intersections 5). Either way T has a point of the circle before
it or beyond it. -/
theorem Prop8.contact_last {D M T R : Point} {α : Circle} (hM : Centre M α)
    (hD : OutsideCircle D α) (hT : OnCircle T α) (hR : OnCircle R α)
    (hC : ¬ ∃ C : Point, OnCircle C α ∧ Between D T C)
    (hH : ¬ ∃ H : Point, OnCircle H α ∧ Between D H T)
    (hTR : SameSideOf T R D M) : ¬ ∠ M D T < ∠ M D R := by
  intro hlt
  have hTM : SameSideOf T M D R := BookI.Prop24.within hTR.symm hlt
  obtain ⟨Y, hMYR, hY⟩ := crossbar hTR hTM
  have hY_in : InsideCircle Y α := InsideCircle.of_between_centre hM hR hMYR
  obtain ⟨hDT, hYD, ⟨N, hD_N, hT_N, hY_N⟩, hYDT⟩ := hY
  have hYT : Y ≠ T := fun e => inside_not_on hY_in (e ▸ hT)
  rcases between_cases hYD.symm hYT hDT hD_N hY_N hT_N with h | h | h
  · obtain ⟨F, hF, -, hYFD⟩ := line_circle_between hY_in hY_N hD hD_N
    exact hH ⟨F, hF, between_of_between_left h (between_symm hYFD)⟩
  · exact hYDT h
  · obtain ⟨C, hC', -, hCYD⟩ := line_circle_beyond hY_in hY_N hD_N hYD.symm
    exact hC ⟨C, hC', between_of_between_left (between_symm hCYD) h⟩

/-- A point of the circle on the straight line DA is A or G, for no three points of a
circle lie on one straight line. -/
theorem Prop8.on_diameter {A G N : Point} {α : Circle} {L : Line}
    (hA : OnCircle A α)
    (hG : OnCircle G α) (hN : OnCircle N α) (hAG : A ≠ G) (hA_L : OnLine A L)
    (hG_L : OnLine G L) (hN_L : OnLine N L) : N = A ∨ N = G := by
  refine Classical.byContradiction fun h => ?_
  have hNA : N ≠ A := fun e => h (Or.inl e)
  have hNG : N ≠ G := fun e => h (Or.inr e)
  exact Prop2.triangle hA hG hN hAG hNG.symm hNA.symm ⟨L, hA_L, hG_L, hN_L⟩

/-- If a point be taken outside a circle and from the point straight lines be drawn through to the
circle, one of which is through the centre and the others are drawn at random, then, of the
straight lines which fall on the concave circumference, that through the centre is greatest,
while of the rest the nearer to that through the centre is always greater than the more remote,
but, of the straight lines falling on the convex circumference, that between the point and the
diameter is least, while of the rest the nearer to the least is always less than the more
remote, and only two equal straight lines will fall on the circle from the point, one on each
side of the least. -/
theorem Prop8 {A D G : Point} {ABC : Circle}
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A) :
    (∀ E : Point, OnCircle E ABC → E ≠ A → ‖D E‖ < ‖D A‖) ∧
    (∀ E F : Point, OnCircle E ABC → OnCircle F ABC →
      (∃ H : Point, OnCircle H ABC ∧ Between D H E) →
      (∃ L : Point, OnCircle L ABC ∧ Between D L F) →
      SameSideOf E F D A → ∠ A D E < ∠ A D F → ‖D F‖ < ‖D E‖) ∧
    (∀ K : Point, OnCircle K ABC → K ≠ G → ‖D G‖ < ‖D K‖) ∧
    (∀ K L : Point, OnCircle K ABC → OnCircle L ABC →
      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →
      (∃ F : Point, OnCircle F ABC ∧ Between D L F) →
      SameSideOf K L D A → ∠ A D K < ∠ A D L → ‖D K‖ < ‖D L‖) ∧
    (∀ K : Point, OnCircle K ABC → ¬ Collinear D A K → ∃ B : Point, OnCircle B ABC ∧
      OppositeSidesOf B K D A ∧ ‖D B‖ = ‖D K‖ ∧
      ∀ N : Point, OnCircle N ABC → ‖D N‖ = ‖D K‖ → N = K ∨ N = B) := by
  -- Let ABC be a circle, and let a point D be taken outside ABC; let there be drawn through
  -- from it straight lines DA, DE, DF, DC, and let DA be through the centre;
  -- I say that, of the straight lines falling on the concave circumference AEFC, the straight
  -- line DA through the centre is greatest,
  -- while DE is greater than DF and DF than DC;
  -- but, of the straight lines falling on the convex circumference HLKG, the straight line DG
  -- between the point and the diameter AG is least; and the nearer to the least DG is always
  -- less than the more remote, namely DK than DL, and DL than DH.
  -- For let the centre of the circle ABC be taken [III. 1], and let it be M; let ME, MF, MC,
  -- MK, ML, MH be joined.
  /- The centre is found by III.1's construction, on a straight line drawn through the
     circle at random (`Prop1.of_circle`), as Euclid finds it. The proof keeps the centre
     alone, which is what Euclid takes from III.1. -/
  obtain ⟨-, -, M, -, -, -, -, -, hM, -⟩ := Prop1.of_circle ABC
  have hAG : A ≠ G := ne_of_between (between_symm hDGA)
  have hGMA : Between G M A := hGA M hM
  have hDGM : Between D G M := between_cut hDGA hGMA
  have hDMA : Between D M A :=
    between_symm (between_of_between_left (between_symm hDGA) (between_symm hGMA))
  have hDM : D ≠ M := ne_of_between hDMA
  obtain ⟨Ld, hD_Ld, hA_Ld⟩ := Postulate1 D A (ne_of_between_ends hDGA)
  have hM_Ld : OnLine M Ld := on_line_of_between_ends hDMA hD_Ld hA_Ld
  have hG_Ld : OnLine G Ld := on_line_of_between_ends hDGA hD_Ld hA_Ld
  have hMA : ∀ P, OnCircle P ABC → ‖M P‖ = ‖M A‖ := fun P hP => Definition15 hM hP hA
  have hDP : ∀ P, OnCircle P ABC → P ≠ D := fun P hP e => hD.2 (e ▸ hP)
  /- A point off the straight line DA makes a triangle with M and D. -/
  have tri : ∀ P, ¬ OnLine P Ld → Triangle M P D := fun P hP =>
    (Triangle.of_line hM_Ld hD_Ld hDM.symm hP).acb
  have side : ∀ P Q, SameSideOf P Q D A → SameSideOf P Q D M := fun P Q h =>
    SameSideOf.of_line hDM hD_Ld hM_Ld (h.sameSide hD_Ld hA_Ld)
  have ang : ∀ P, P ≠ D → ∠ A D P = ∠ M D P := fun P hP =>
    (angle_onRay_left (OnRay.of_between hDMA) hP).symm
  have offL : ∀ P Q, SameSideOf P Q D A → ¬ OnLine P Ld := fun P Q h =>
    not_on_line_of_same_side (h.sameSide hD_Ld hA_Ld)
  have greatest : ∀ E : Point, OnCircle E ABC → E ≠ A → ‖D E‖ < ‖D A‖ := by
    intro E hE hEA
    /- On DA, E must be G: the part DG is less than the whole DA. -/
    by_cases hE_Ld : OnLine E Ld
    · rcases Prop8.on_diameter hA hG hE hAG hA_Ld hG_Ld hE_Ld with rfl | rfl
      · exact absurd rfl hEA
      · exact len_lt_of_between hDGA
    -- Then, since AM is equal to EM,
    have hAM_EM : ‖A M‖ = ‖E M‖ := by
      rw [len_symm A M, len_symm E M]
      exact (hMA E hE).symm
    -- let MD be added to each;
    have hadd : ‖A M‖ + ‖M D‖ = ‖E M‖ + ‖M D‖ := by rw [hAM_EM]
    -- therefore AD is equal to EM, MD.
    have hAD : ‖A D‖ = ‖E M‖ + ‖M D‖ := by
      rw [← len_add_of_between (between_symm hDMA)]
      exact hadd
    -- But EM, MD are greater than ED; [I. 20]
    have h20 : ‖E D‖ < ‖E M‖ + ‖M D‖ := (BookI.Prop20 (tri E hE_Ld)).1
    -- therefore AD is also greater than ED.
    rw [len_symm D E, len_symm D A, hAD]
    exact h20
  /- Euclid's argument asks only that E, the nearer, be on the concave circumference, so
     F may be any point of the circle making the greater angle with DA. -/
  have concave : ∀ E F : Point, OnCircle E ABC → OnCircle F ABC →
      (∃ H : Point, OnCircle H ABC ∧ Between D H E) →
      SameSideOf E F D A → ∠ A D E < ∠ A D F → ‖D F‖ < ‖D E‖ := by
    intro E F hE hF ⟨H, hH, hDHE⟩ hEF hlt
    -- Again, since ME is equal to MF,
    have hME_MF : ‖M E‖ = ‖M F‖ := (hMA E hE).trans (hMA F hF).symm
    -- and MD is common,
    have hMD : ‖M D‖ = ‖M D‖ := rfl
    -- therefore EM, MD are equal to FM, MD;
    have hsides := And.intro hME_MF hMD
    -- and the angle EMD is greater than the angle FMD;
    /- The less angle at D puts E beyond MF, outside the triangle DFM (`Prop8.outside`). -/
    rw [ang E (hDP E hE), ang F (hDP F hF)] at hlt
    have hout := Prop8.outside hM hE hF hH hDHE (side E F hEF) hlt
    -- therefore the base ED is greater than the base FD. [I. 24]
    have h24 := BookI.Prop24 (tri E (offL E F hEF)) (tri F (offL F E hEF.symm))
      hsides.1 hsides.2 hout
    rwa [len_symm D F, len_symm D E]
  -- Similarly we can prove that FD is greater than CD;
  -- therefore DA is greatest, while DE is greater than DF,
  -- and DF than DC.
  /- The comparison above holds for any two such points, F and C among them. -/
  have least : ∀ K : Point, OnCircle K ABC → K ≠ G → ‖D G‖ < ‖D K‖ := by
    intro K hK hKG
    /- On DA, K must be A, and DG is a part of DA. -/
    by_cases hK_Ld : OnLine K Ld
    · rcases Prop8.on_diameter hA hG hK hAG hA_Ld hG_Ld hK_Ld with rfl | rfl
      · exact len_lt_of_between hDGA
      · exact absurd rfl hKG
    -- Next, since MK, KD are greater than MD, [I. 20]
    have h20 : ‖M D‖ < ‖M K‖ + ‖K D‖ := (BookI.Prop20 (tri K hK_Ld)).2.1
    -- and MG is equal to MK,
    have hMG_MK : ‖M G‖ = ‖M K‖ := (hMA G hG).trans (hMA K hK).symm
    -- therefore the remainder KD is greater than the remainder GD,
    have hMD : ‖M D‖ = ‖M G‖ + ‖G D‖ := len_add_of_between (between_symm hDGM) |>.symm
    rw [hMD, ← hMG_MK] at h20
    have hGD_KD : ‖G D‖ < ‖K D‖ := Magnitude.lt_of_add_lt_add_left h20
    -- so that GD is less than KD.
    rw [len_symm D G, len_symm D K]
    exact hGD_KD
  /- As on the concave circumference, the argument asks only that K, the nearer, be on the
     convex circumference: L may be any point of the circle making the greater angle. -/
  have convex : ∀ K L : Point, OnCircle K ABC → OnCircle L ABC →
      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →
      SameSideOf K L D A → ∠ A D K < ∠ A D L → ‖D K‖ < ‖D L‖ := by
    intro K L hK hL ⟨C, hC, hDKC⟩ hKL hlt
    -- And, since on MD, one of the sides of the triangle MLD, two straight lines MK, KD were
    -- constructed meeting within the triangle,
    /- K is within the triangle DLM, De Morgan's other placement (`Prop8.within`). -/
    rw [ang K (hDP K hK), ang L (hDP L hL)] at hlt
    have hin := Prop8.within hM hK hL hC hDKC (side K L hKL) hlt
    -- therefore MK, KD are less than ML, LD; [I. 21]
    have h21 : ‖M K‖ + ‖K D‖ < ‖M L‖ + ‖L D‖ :=
      (BookI.Prop21 (tri L (offL L K hKL.symm)).bac hin).1
    -- and MK is equal to ML;
    have hMK_ML : ‖M K‖ = ‖M L‖ := (hMA K hK).trans (hMA L hL).symm
    -- therefore the remainder DK is less than the remainder DL.
    rw [hMK_ML] at h21
    rw [len_symm D K, len_symm D L]
    exact Magnitude.lt_of_add_lt_add_left h21
  -- Similarly we can prove that DL is also less than DH;
  -- therefore DG is least, while DK is less than DL, and DL than DH.
  /- The comparison above holds for any two such points, L and H among them. -/
  -- I say also that only two equal straight lines will fall from the point D on the circle,
  -- one on each side of the least DG.
  have two_equal : ∀ K : Point, OnCircle K ABC → ¬ Collinear D A K →
      ∃ B : Point, OnCircle B ABC ∧ OppositeSidesOf B K D A ∧ ‖D B‖ = ‖D K‖ ∧
      ∀ N : Point, OnCircle N ABC → ‖D N‖ = ‖D K‖ → N = K ∨ N = B := by
    intro K hK hKcol
    have hK_Ld : ¬ OnLine K Ld := fun h => hKcol ⟨Ld, hD_Ld, hA_Ld, h⟩
    have hMKD : Triangle M K D := tri K hK_Ld
    -- On the straight line MD, and at the point M on it,
    -- let the angle DMB be constructed equal to the angle KMD, and let DB be joined.
    /- This is the construction of I.23, on the other side of MD. Its unlettered
       points Q, F', G' choose the side and the two arms; B is on the circle. -/
    obtain ⟨Q, hQK, -⟩ := exists_oppositeSidesOf hMKD.acb []
    obtain ⟨G', F', hF', hG'Q, hang⟩ := BookI.Prop23 hDM.symm hMKD.bac hQK.triangle
    obtain ⟨B, hB_ray, hMB⟩ :=
      OnRay.exists_len_eq (ne_of_centre_of_on hM hK).symm hG'Q.triangle.ne₁₃
    have hB : OnCircle B ABC := on_circle_of_len_eq hM hK hMB
    have hDMB : ∠ D M B = ∠ K M D :=
      (angle_eq_of_onRay hF'.symm hB_ray).trans
        ((angle_symm hF'.2.1 hG'Q.triangle.ne₁₃.symm).trans hang)
    have hBK : OppositeSidesOf B K M D :=
      (SameSideOf.of_onRay hB_ray hG'Q).trans_opposite hQK
    have hBK' : OppositeSidesOf B K D A :=
      OppositeSidesOf.of_line (ne_of_between_ends hDGA) hD_Ld hA_Ld
        (hBK.oppositeSides hM_Ld hD_Ld)
    have hB_Ld : ¬ OnLine B Ld := (hBK.oppositeSides hM_Ld hD_Ld).1
    -- Then, since MK is equal to MB,
    have hMK_MB : ‖M K‖ = ‖M B‖ := (hMA K hK).trans (hMA B hB).symm
    -- and MD is common,
    have hMD : ‖M D‖ = ‖M D‖ := rfl
    -- the two sides KM, MD are equal to the two sides BM, MD respectively;
    have hsides := And.intro hMK_MB hMD
    -- and the angle KMD is equal to the angle BMD;
    have hKMD : ∠ K M D = ∠ B M D :=
      hDMB.symm.trans (angle_symm hDM (ne_of_centre_of_on hM hB))
    -- therefore the base DK is equal to the base DB. [I. 4]
    have hKD : ‖K D‖ = ‖B D‖ :=
      (BookI.Prop4 hMKD (tri B hB_Ld) hsides.1 hsides.2 hKMD).1
    have hDB : ‖D B‖ = ‖D K‖ := by rw [len_symm D B, len_symm D K, hKD]
    -- I say that no other straight line equal to the straight line DK will fall on the circle
    -- from the point D.
    refine ⟨B, hB, hBK', hDB, ?_⟩
    -- For, if possible, let a straight line so fall, and let it be DN.
    intro N hN hDN
    -- Then, since DK is equal to DN,
    have hDK_DN : ‖D K‖ = ‖D N‖ := hDN.symm
    -- while DK is equal to DB,
    have hDK_DB : ‖D K‖ = ‖D B‖ := hDB.symm
    -- DB is also equal to DN,
    have hDB_DN : ‖D B‖ = ‖D N‖ := hDK_DB.symm.trans hDK_DN
    -- that is, the nearer to the least DG equal to the more remote: which was proved impossible.
    /- Euclid compares DN with DB, on B's side of DA; on K's side, a placing his figure
       leaves aside, DN is compared with DK in the same way. So let P be B or K, on N's
       side, with DN equal to DP. -/
    have one_side : ∀ P, OnCircle P ABC → ∀ N, OnCircle N ABC →
        SameSide N P Ld → ‖D N‖ = ‖D P‖ → N = P := by
      intro P hP N hN hs hDN
      have hNP : SameSideOf N P D A := SameSideOf.of_line (ne_of_between_ends hDGA) hD_Ld hA_Ld hs
      /- Euclid's comparison. Of two points of the circle on one side of DA, the one making
         the less angle with DA is the nearer to the least DG. On the convex circumference it
         is the less, by the order proved there, and on the concave the greater, by that
         circumference's order, a case Euclid's figure leaves aside; either way the two are
         not equal. Each order asks only that the nearer be on its circumference, so the
         other may be on either circumference, or a point where a straight line from D
         touches the circle: such a point is at the end of both orders, and cannot be the
         nearer, for no point of the circle on its side makes a greater angle with DA
         (`Prop8.contact_last`). -/
      have unequal : ∀ X Y : Point, OnCircle X ABC → OnCircle Y ABC → SameSideOf X Y D A →
          ∠ A D X < ∠ A D Y → ‖D X‖ = ‖D Y‖ → False := by
        intro X Y hX hY hXY hlt hDXY
        by_cases hcx : ∃ C : Point, OnCircle C ABC ∧ Between D X C
        · have hless := convex X Y hX hY hcx hXY hlt
          rw [hDXY] at hless
          exact lt_irrefl _ hless
        by_cases hcv : ∃ H : Point, OnCircle H ABC ∧ Between D H X
        · have hless := concave X Y hX hY hcv hXY hlt
          rw [hDXY] at hless
          exact lt_irrefl _ hless
        rw [ang X (hDP X hX), ang Y (hDP Y hY)] at hlt
        exact Prop8.contact_last hM hD hX hY hcx hcv (side X Y hXY) hlt
      rcases lt_trichotomy (∠ A D N) (∠ A D P) with hl | he | hg
      · exact absurd hDN (unequal N P hN hP hNP hl)
      · /- Euclid takes DN to be a straight line other than DB, so that one of the two is
           the nearer. Were the angles ADN and ADP equal, N would lie on the ray DP, as far
           from D as P is, and so be P itself. -/
        exact OnRay.eq_of_len_eq (onRay_of_angle_eq hNP he) hDN
      · exact absurd hDN.symm (unequal P N hP hN hNP.symm hg)
    /- On DA itself, N is A or G, and DA is the greatest and DG the least, as proved above,
       so neither is as far from D as K. -/
    by_cases hN_Ld : OnLine N Ld
    · rcases Prop8.on_diameter hA hG hN hAG hA_Ld hG_Ld hN_Ld with rfl | rfl
      · have hlt := greatest K hK (fun e => hK_Ld (e ▸ hA_Ld))
        rw [← hDN] at hlt
        exact absurd hlt (lt_irrefl _)
      · have hlt := least K hK (fun e => hK_Ld (e ▸ hG_Ld))
        rw [hDN] at hlt
        exact absurd hlt (lt_irrefl _)
    by_cases hs : SameSide N K Ld
    · exact Or.inl (one_side K hK N hN hs hDN)
    · have hsB : SameSide N B Ld := same_side_of_opposite_sides
        ⟨hK_Ld, hN_Ld, fun h => hs (same_side_symm h)⟩
        (hBK.symm.oppositeSides hM_Ld hD_Ld)
      exact Or.inr (one_side B hB N hN hsB hDB_DN.symm)
  -- Therefore no more than two equal straight lines will fall on the circle ABC from the point
  -- D, one on each side of DG the least.
  -- Therefore etc.
  /- The statement's orders ask the more remote point to be on its circumference too; the
     comparisons above do not need it. -/
  exact ⟨greatest, fun E F hE hF hHE _ => concave E F hE hF hHE, least,
    fun K L hK hL hKC _ => convex K L hK hL hKC, two_equal⟩
  -- Q. E. D.

/-- **III.8, the partner equally inclined and in the same class** (a step of III.8
general). D is outside the circle ABC, and the straight line DA passes through the centre,
meeting the circle first at G and again at A. If K and B are points of the circle on
opposite sides of DA, and DB is equal to DK, then the angles ADB and ADK are equal; B is on
the convex circumference exactly when K is (the straight line from D meets the circle again
beyond it); and B is on the concave circumference exactly when K is (it meets the circle
before reaching it). Euclid's construction of B, the angle DMB made equal to KMD at the
centre M (I.23), gives the equal angles at D by I.4, and `Prop8`'s last clause, that no
third point of the circle is as far from D, shows that no other point is B; the class
follows from the equal angles: a point of the circle beyond K on the straight line DK has
its partner on the ray DB beyond B, and a point of the circle between D and K has its
partner between D and B. -/
theorem Prop8.partner {A D G K B : Point} {ABC : Circle}
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A)
    (hK : OnCircle K ABC) (hB : OnCircle B ABC) (hBK : OppositeSidesOf B K D A)
    (hDB : ‖D B‖ = ‖D K‖) :
    ∠ A D B = ∠ A D K ∧
    ((∃ C : Point, OnCircle C ABC ∧ Between D B C) ↔
      (∃ C : Point, OnCircle C ABC ∧ Between D K C)) ∧
    ((∃ H : Point, OnCircle H ABC ∧ Between D H B) ↔
      (∃ H : Point, OnCircle H ABC ∧ Between D H K)) := by
  have hpartner := (Prop8 hD hA hG hDGA hGA).2.2.2.2
  /- The centre M is found by III.1's construction, as in `Prop8` (`Prop1.of_circle`). -/
  obtain ⟨-, -, M, -, -, -, -, -, hM, -⟩ := Prop1.of_circle ABC
  have hDMA : Between D M A :=
    between_symm (between_of_between_left (between_symm hDGA)
      (between_symm (hGA M hM)))
  have hDM : D ≠ M := ne_of_between hDMA
  have hDA : D ≠ A := ne_of_between_ends hDGA
  obtain ⟨Ld, hD_Ld, hA_Ld⟩ := Postulate1 D A hDA
  have hM_Ld : OnLine M Ld := on_line_of_between_ends hDMA hD_Ld hA_Ld
  /- The equal angles, for any two partners K, B: Euclid's I.4 step at M. -/
  have hangle : ∀ K B : Point, OnCircle K ABC → OnCircle B ABC →
      OppositeSidesOf B K D A → ‖D B‖ = ‖D K‖ → ∠ A D B = ∠ A D K := by
    intro K B hK hB hBK hDB
    have hK_Ld : ¬ OnLine K Ld := (hBK.oppositeSides hD_Ld hA_Ld).2.1
    have hMKD : Triangle M K D :=
      (Triangle.of_line hM_Ld hD_Ld hDM.symm hK_Ld).acb
    /- Make DMB' equal to KMD on the other side of MD from K. -/
    obtain ⟨Q, hQK, -⟩ := exists_oppositeSidesOf hMKD.acb []
    obtain ⟨X, F', hF', hXQ, hang⟩ := BookI.Prop23 hDM.symm hMKD.bac hQK.triangle
    obtain ⟨B', hB'_ray, hMB'⟩ :=
      OnRay.exists_len_eq (ne_of_centre_of_on hM hK).symm hXQ.triangle.ne₁₃
    have hB' : OnCircle B' ABC := on_circle_of_len_eq hM hK hMB'
    have hDMB' : ∠ D M B' = ∠ K M D :=
      (angle_eq_of_onRay hF'.symm hB'_ray).trans
        ((angle_symm hF'.2.1 hXQ.triangle.ne₁₃.symm).trans hang)
    have hB'K_MD : OppositeSidesOf B' K M D :=
      (SameSideOf.of_onRay hB'_ray hXQ).trans_opposite hQK
    have hB'K : OppositeSidesOf B' K D A :=
      OppositeSidesOf.of_line hDA hD_Ld hA_Ld (hB'K_MD.oppositeSides hM_Ld hD_Ld)
    have hMB'D : Triangle M B' D := hB'K_MD.triangle.acb
    have hKMD : ∠ K M D = ∠ B' M D :=
      hDMB'.symm.trans (angle_symm hDM (ne_of_centre_of_on hM hB'))
    /- I.4 gives DB' equal to DK and MDB' equal to MDK. -/
    have h4 := BookI.Prop4 hMKD hMB'D hMB'.symm rfl hKMD
    have hDB' : ‖D B'‖ = ‖D K‖ := by
      rw [len_symm D B', len_symm D K]
      exact h4.1.symm
    have hang' : ∠ A D B' = ∠ A D K := by
      rw [← angle_onRay_left (OnRay.of_between hDMA) hMB'D.ne₂₃,
        ← angle_onRay_left (OnRay.of_between hDMA) hMKD.ne₂₃]
      exact h4.2.2.2.symm
    /- B and B' are both the unique partner of K on the other side of DA. -/
    obtain ⟨J, -, -, -, hunique⟩ := hpartner K hK hBK.symm.triangle
    have hBK_ne : B ≠ K := by
      intro e
      have hs := hBK.oppositeSides hD_Ld hA_Ld
      exact hs.2.2 (e ▸ same_side_refl hs.1)
    have hB'K_ne : B' ≠ K := by
      intro e
      have hs := hB'K.oppositeSides hD_Ld hA_Ld
      exact hs.2.2 (e ▸ same_side_refl hs.1)
    have hBJ : B = J := (hunique B hB hDB).resolve_left hBK_ne
    have hB'J : B' = J := (hunique B' hB' hDB').resolve_left hB'K_ne
    exact (hBJ.trans hB'J.symm) ▸ hang'
  /- If C is beyond K, its partner C' is beyond B on the ray DB. -/
  have hconvex : ∀ K B : Point, OnCircle K ABC → OnCircle B ABC →
      OppositeSidesOf B K D A → ‖D B‖ = ‖D K‖ →
      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →
      ∃ C : Point, OnCircle C ABC ∧ Between D B C := by
    intro K B hK hB hBK hDB ⟨C, hC, hDKC⟩
    have hCK : SameSideOf C K D A :=
      SameSideOf.of_onRay (OnRay.of_beyond hDKC) (OppositeSidesOf.sameSideOf hBK hBK)
    obtain ⟨C', hC', hC'C, hDC', -⟩ := hpartner C hC hCK.triangle
    have hC'B : SameSideOf C' B D A :=
      OppositeSidesOf.sameSideOf hC'C.symm (hCK.trans_opposite hBK.symm)
    have hang : ∠ A D C' = ∠ A D B :=
      (hangle C C' hC hC' hC'C hDC').trans
        ((angle_onRay_right (OnRay.of_beyond hDKC) hDA.symm).trans
          (hangle K B hK hB hBK hDB).symm)
    have hC'_ray : OnRay C' D B := onRay_of_angle_eq hC'B hang
    have hlt : ‖D B‖ < ‖D C'‖ := by
      rw [hDB, hDC']
      exact len_lt_of_between hDKC
    exact ⟨C', hC', (OnRay.self hBK.triangle.ne₁₃).between_of_len_lt hC'_ray hlt⟩
  /- If H is between D and K, its partner H' is between D and B. -/
  have hconcave : ∀ K B : Point, OnCircle K ABC → OnCircle B ABC →
      OppositeSidesOf B K D A → ‖D B‖ = ‖D K‖ →
      (∃ H : Point, OnCircle H ABC ∧ Between D H K) →
      ∃ H : Point, OnCircle H ABC ∧ Between D H B := by
    intro K B hK hB hBK hDB ⟨H, hH, hDHK⟩
    have hHK : SameSideOf H K D A :=
      SameSideOf.of_onRay (OnRay.of_between hDHK) (OppositeSidesOf.sameSideOf hBK hBK)
    obtain ⟨H', hH', hH'H, hDH', -⟩ := hpartner H hH hHK.triangle
    have hH'B : SameSideOf H' B D A :=
      OppositeSidesOf.sameSideOf hH'H.symm (hHK.trans_opposite hBK.symm)
    have hang : ∠ A D H' = ∠ A D B :=
      (hangle H H' hH hH' hH'H hDH').trans
        ((angle_onRay_right (OnRay.of_between hDHK) hDA.symm).trans
          (hangle K B hK hB hBK hDB).symm)
    have hH'_ray : OnRay H' D B := onRay_of_angle_eq hH'B hang
    have hlt : ‖D H'‖ < ‖D B‖ := by
      rw [hDH', hDB]
      exact len_lt_of_between hDHK
    exact ⟨H', hH', hH'_ray.between_of_len_lt (OnRay.self hBK.triangle.ne₁₃) hlt⟩
  exact ⟨hangle K B hK hB hBK hDB,
    ⟨hconvex B K hB hK hBK.symm hDB.symm, hconvex K B hK hB hBK hDB⟩,
    ⟨hconcave B K hB hK hBK.symm hDB.symm, hconcave K B hK hB hBK hDB⟩⟩

/-- **III.8, general** (companion of III.8). D is outside the circle ABC, and the straight
line DA passes through the centre, meeting the circle first at G and again at A. Of the
straight lines from D to the circle, DA is greater than every other, and DG less than every
other. Of any two points E, F of the concave circumference (each with a point of the circle
between it and D) off DA, on one side of it or on opposite sides, the one making the less
angle with the ray DA at D is the farther: if the angle ADE is less than the angle ADF, then
DF is less than DE. Of any two points K, L of the convex circumference (each with a point of
the circle beyond it) off DA, the one making the less angle is the nearer: if the angle ADK
is less than the angle ADL, then DK is less than DL. By convention, read from "drawn
through", a point where a straight line from D touches the circle is on neither
circumference; the comparisons speak only of points with a point of the circle before them
or beyond them, and that a point of contact has neither, which follows from Definition III.2,
is not stated here. Each point K of the circle off DA has one partner B on the other side
with DB equal to DK, and no third point of the circle is as far from D. -/
theorem Prop8.general {A D G : Point} {ABC : Circle}
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A) :
    (∀ E : Point, OnCircle E ABC → E ≠ A → ‖D E‖ < ‖D A‖) ∧
    (∀ E F : Point, OnCircle E ABC → OnCircle F ABC →
      (∃ H : Point, OnCircle H ABC ∧ Between D H E) →
      (∃ L : Point, OnCircle L ABC ∧ Between D L F) →
      ¬ Collinear D A E → ¬ Collinear D A F → ∠ A D E < ∠ A D F → ‖D F‖ < ‖D E‖) ∧
    (∀ K : Point, OnCircle K ABC → K ≠ G → ‖D G‖ < ‖D K‖) ∧
    (∀ K L : Point, OnCircle K ABC → OnCircle L ABC →
      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →
      (∃ F : Point, OnCircle F ABC ∧ Between D L F) →
      ¬ Collinear D A K → ¬ Collinear D A L → ∠ A D K < ∠ A D L → ‖D K‖ < ‖D L‖) ∧
    (∀ K : Point, OnCircle K ABC → ¬ Collinear D A K → ∃ B : Point, OnCircle B ABC ∧
      OppositeSidesOf B K D A ∧ ‖D B‖ = ‖D K‖ ∧
      ∀ N : Point, OnCircle N ABC → ‖D N‖ = ‖D K‖ → N = K ∨ N = B) := by
  obtain ⟨hgreatest, hconcave, hleast, hconvex, hpartner⟩ := Prop8 hD hA hG hDGA hGA
  have hDA : D ≠ A := ne_of_between_ends hDGA
  obtain ⟨Ld, hD_Ld, hA_Ld⟩ := Postulate1 D A hDA
  /- Two points off DA that are not on one side are on opposite sides. -/
  have hopposite : ∀ X Y : Point, ¬ Collinear D A X → ¬ Collinear D A Y →
      ¬ SameSideOf X Y D A → OppositeSidesOf X Y D A := by
    intro X Y hX hY hXY
    exact OppositeSidesOf.of_line hDA hD_Ld hA_Ld
      ⟨fun h => hX ⟨Ld, hD_Ld, hA_Ld, h⟩,
        fun h => hY ⟨Ld, hD_Ld, hA_Ld, h⟩,
        fun hs => hXY (SameSideOf.of_line hDA hD_Ld hA_Ld hs)⟩
  refine ⟨hgreatest, ?_, hleast, ?_, hpartner⟩
  · intro E F hE hF hHE hLF hE_DA hF_DA hlt
    by_cases hEF : SameSideOf E F D A
    · exact hconcave E F hE hF hHE hLF hEF hlt
    /- F's partner B is on E's side and remains on the concave circumference. -/
    have hEF' := hopposite E F hE_DA hF_DA hEF
    obtain ⟨B, hB, hBF, hDB, -⟩ := hpartner F hF hF_DA
    have hEB : SameSideOf E B D A := OppositeSidesOf.sameSideOf hEF'.symm hBF.symm
    obtain ⟨hang, -, hclass⟩ := Prop8.partner hD hA hG hDGA hGA hF hB hBF hDB
    have hlt' : ∠ A D E < ∠ A D B := by rw [hang]; exact hlt
    have hless := hconcave E B hE hB hHE (hclass.mpr hLF) hEB hlt'
    rwa [hDB] at hless
  · intro K L hK hL hKC hLF hK_DA hL_DA hlt
    by_cases hKL : SameSideOf K L D A
    · exact hconvex K L hK hL hKC hLF hKL hlt
    /- L's partner B is on K's side and remains on the convex circumference. -/
    have hKL' := hopposite K L hK_DA hL_DA hKL
    obtain ⟨B, hB, hBL, hDB, -⟩ := hpartner L hL hL_DA
    have hKB : SameSideOf K B D A := OppositeSidesOf.sameSideOf hKL'.symm hBL.symm
    obtain ⟨hang, hclass, -⟩ := Prop8.partner hD hA hG hDGA hGA hL hB hBL hDB
    have hlt' : ∠ A D K < ∠ A D B := by rw [hang]; exact hlt
    have hless := hconvex K B hK hB hKC (hclass.mpr hLF) hKB hlt'
    rwa [hDB] at hless

/-- The check: the statement of `Prop8` follows from `Prop8.general` (checked by Lean).
Two points on one side of DA are off it. -/
example : type_of% @Elements.BookIII.Prop8 := by
  intro A D G ABC hD hA hG hDGA hGA
  obtain ⟨hgreatest, hconcave, hleast, hconvex, hpartner⟩ :=
    Prop8.general hD hA hG hDGA hGA
  exact ⟨hgreatest,
    fun E F hE hF hHE hLF hEF hlt =>
      hconcave E F hE hF hHE hLF hEF.triangle hEF.symm.triangle hlt,
    hleast,
    fun K L hK hL hKC hLF hKL hlt =>
      hconvex K L hK hL hKC hLF hKL.triangle hKL.symm.triangle hlt,
    hpartner⟩

end Elements.BookIII
