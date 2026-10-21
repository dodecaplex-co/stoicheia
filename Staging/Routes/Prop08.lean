import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop04
import Elements.BookI.Prop20
import Elements.BookI.Prop21
import Elements.BookI.Prop23
import Elements.BookI.Prop24
import Elements.BookIII.Prop01
import Elements.BookIII.Prop02
import Elements.BookIII.Prop08

/-!
# Book III, Proposition 8, with Euclid's own last step

This file answers issue #125. It stages `Routes.Prop8`, main's statement of III.8 word for
word, with main's proof except for the last step, that no third straight line from D is
equal to DK. Main's proof takes that step by I.24 at the centre M for every point of the
circle. Here it is Euclid's: when N is off DA, DN and the straight line it is compared
with, DB or DK, are on one side of DA (on DA, N is A or G, and DA is the greatest and DG
the least), and if both fall on the convex circumference, the nearer to DG is the less by
the order proved earlier in the proof, so they cannot be equal, "which was proved
impossible". Two points of the concave circumference are compared by that circumference's
order in the same way, a case Euclid's figure leaves aside. I.24 at M stays for the cases
neither order reaches: the two points on different circumferences, or one of them a point
where a straight line from D touches the circle, which is on neither.

Main's helpers `Prop8.outside`, `Prop8.within` and `Prop8.on_diameter` are cited from
main's file. Status: staged to replace the proof in Elements/BookIII/Prop08.lean when Book
III's files are next moved.
-/

namespace Elements.BookIII.Routes

open Tacit

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
  have hAG : A ≠ G := ne_of_between (between_symm hDGA)
  obtain ⟨M, -, -, -, hM, -⟩ := Prop1 hA hG hAG
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
  have concave : ∀ E F : Point, OnCircle E ABC → OnCircle F ABC →
      (∃ H : Point, OnCircle H ABC ∧ Between D H E) →
      (∃ L : Point, OnCircle L ABC ∧ Between D L F) →
      SameSideOf E F D A → ∠ A D E < ∠ A D F → ‖D F‖ < ‖D E‖ := by
    intro E F hE hF ⟨H, hH, hDHE⟩ _ hEF hlt
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
  have convex : ∀ K L : Point, OnCircle K ABC → OnCircle L ABC →
      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →
      (∃ F : Point, OnCircle F ABC ∧ Between D L F) →
      SameSideOf K L D A → ∠ A D K < ∠ A D L → ‖D K‖ < ‖D L‖ := by
    intro K L hK hL ⟨C, hC, hDKC⟩ _ hKL hlt
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
    have one_side : ∀ P, OnCircle P ABC → ¬ OnLine P Ld → ∀ N, OnCircle N ABC →
        SameSide N P Ld → ‖D N‖ = ‖D P‖ → N = P := by
      intro P hP hP_Ld N hN hs hDN
      have hNP : SameSideOf N P D A := SameSideOf.of_line (ne_of_between_ends hDGA) hD_Ld hA_Ld hs
      /- Euclid's comparison, with N and P both on the convex circumference. The one making
         the less angle with DA is the nearer to the least DG, and so the less, by the order
         on the convex circumference proved above; but DN is equal to DP. -/
      by_cases hcx : (∃ C : Point, OnCircle C ABC ∧ Between D P C) ∧
          (∃ C : Point, OnCircle C ABC ∧ Between D N C)
      · rcases lt_trichotomy (∠ A D N) (∠ A D P) with hl | he | hg
        · have hlt := convex N P hN hP hcx.2 hcx.1 hNP hl
          rw [hDN] at hlt
          exact absurd hlt (lt_irrefl _)
        · /- Euclid takes DN to be a straight line other than DB, so that one of the two is
             the nearer. Were the angles ADN and ADP equal, N would lie on the ray DP, as far
             from D as P is, and so be P itself. -/
          exact OnRay.eq_of_len_eq (onRay_of_angle_eq hNP he) hDN
        · have hlt := convex P N hP hN hcx.1 hcx.2 hNP.symm hg
          rw [hDN] at hlt
          exact absurd hlt (lt_irrefl _)
      /- A case Euclid's figure leaves aside: N and P both on the concave circumference, as
         when K is taken there. The order proved above for that circumference does the same
         work, the less angle with DA having the greater straight line. -/
      by_cases hcv : (∃ H : Point, OnCircle H ABC ∧ Between D H P) ∧
          (∃ H : Point, OnCircle H ABC ∧ Between D H N)
      · rcases lt_trichotomy (∠ A D N) (∠ A D P) with hl | he | hg
        · have hlt := concave N P hN hP hcv.2 hcv.1 hNP hl
          rw [hDN] at hlt
          exact absurd hlt (lt_irrefl _)
        · exact OnRay.eq_of_len_eq (onRay_of_angle_eq hNP he) hDN
        · have hlt := concave P N hP hN hcv.1 hcv.2 hNP.symm hg
          rw [hDN] at hlt
          exact absurd hlt (lt_irrefl _)
      /- A case Euclid's figure leaves aside, which neither order reaches: N and P on
         different circumferences, or one of them a point where a straight line from D
         touches the circle, which is on neither. Each order compares two points of one
         circumference only, for the two points where one straight line from D meets the
         circle make one angle with DA and are at different distances from D. The angles at
         the centre M decide it instead: unequal angles there give unequal straight lines
         from D by I.24, and equal ones put N on the radius MP, so that N is P. -/
      have hN_Ld : ¬ OnLine N Ld := not_on_line_of_same_side hs
      have hNP' : SameSideOf N P M D := SameSideOf.of_line hDM.symm hM_Ld hD_Ld hs
      have hMN : ‖M P‖ = ‖M N‖ := (hMA P hP).trans (hMA N hN).symm
      rcases lt_trichotomy (∠ N M D) (∠ P M D) with hl | he | hg
      · have h24 := BookI.Prop24 (tri P hP_Ld) (tri N hN_Ld) hMN rfl hl
        rw [len_symm N D, len_symm P D, hDN] at h24
        exact absurd h24 (lt_irrefl _)
      · have hray : OnRay N M P := onRay_of_angle_eq hNP' (by
          rw [angle_symm hDM (ne_of_centre_of_on hM hN), he,
            angle_symm (ne_of_centre_of_on hM hP) hDM])
        exact OnRay.eq_of_len_eq hray hMN.symm
      · have h24 := BookI.Prop24 (tri N hN_Ld) (tri P hP_Ld) hMN.symm rfl hg
        rw [len_symm N D, len_symm P D, hDN] at h24
        exact absurd h24 (lt_irrefl _)
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
    · exact Or.inl (one_side K hK hK_Ld N hN hs hDN)
    · have hsB : SameSide N B Ld := same_side_of_opposite_sides
        ⟨hK_Ld, hN_Ld, fun h => hs (same_side_symm h)⟩
        (hBK.symm.oppositeSides hM_Ld hD_Ld)
      exact Or.inr (one_side B hB hB_Ld N hN hsB hDB_DN.symm)
  -- Therefore no more than two equal straight lines will fall on the circle ABC from the point
  -- D, one on each side of DG the least.
  -- Therefore etc.
  exact ⟨greatest, concave, least, convex, two_equal⟩
  -- Q. E. D.

/-- The check: `Routes.Prop8` proves main's statement of III.8 (checked by Lean). -/
example : type_of% @Elements.BookIII.Routes.Prop8 = type_of% @Elements.BookIII.Prop8 := rfl

end Elements.BookIII.Routes
