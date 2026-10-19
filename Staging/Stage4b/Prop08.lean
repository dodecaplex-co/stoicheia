import Elements.BookIII.Prop08

/-!
# Staging: III.8, nearer and more remote on either side of the diameter

Brief 0007, stage 4b. A companion of `Elements.BookIII.Prop8`, which stays as Euclid's
worked configuration: there the nearer and the more remote are compared only when both lie
on one side of the straight line DA. `Prop8.general` compares any two, on one side or on
opposite sides, within each of Euclid's two classes, and never across them.

The classes are read as today's statement reads them. A point E of the circle is on the
concave circumference when a straight line from D meets the circle at some point before
reaching E: some point H of the circle is between D and E. A point K is on the convex
circumference when the straight line from D through K meets the circle again beyond K: K
is between D and some point C of the circle. "Nearer" is the less angle at D with the ray
DA, the ray through the centre. On the concave circumference the less angle has the greater
straight line; on the convex, the less angle has the less. The two orders are kept
apart, for they disagree: the two points where one straight line from D meets the circle
make the same angle with DA, and are at different distances from D.

A straight line touching the circle from D falls on neither class. This is a convention,
read from Euclid's "drawn through to the circle": a straight line that touches does not
meet the circle at two points (Definition III.2), so its point of contact has no point of
the circle between it and D and none beyond it. That step follows from Definition III.2,
and is not stated in Lean (brief 0007, question 2); the comparisons say nothing of the
point of contact. The last clause, kept from today's statement, does: every point of the
circle off DA, a point of contact included, has one partner on the other side as far from
D, and no third.

`Prop8.partner` is the step the route needs: the partner on the other side makes the same
angle with DA, and is in the same class. Equal distance alone does not carry a comparison
across DA: the comparison on one side asks for the angle and the class, and the step
proves both of the partner. They move into
`Elements/BookIII/Prop08.lean` when proved, as "III.8 general", with `Prop8.partner` as a
helper before it.
-/

namespace Elements.BookIII

open Tacit

/-- **III.8, the partner equally inclined and in the same class** (a step of III.8
general). D is outside the circle ABC, and the straight line DA passes through the centre,
meeting the circle first at G and again at A. If K and B are points of the circle on
opposite sides of DA, and DB is equal to DK, then the angles ADB and ADK are equal; B is on
the convex circumference exactly when K is (the straight line from D meets the circle again
beyond it); and B is on the concave circumference exactly when K is (it meets the circle
before reaching it). Euclid's construction of B, the angle DMB made equal to KMD at the
centre M (I.23), gives the equal angles at D by I.4, and today's last clause, that no
third point of the circle is as far from D, shows that no other point is B; the class
follows from the equal angles: a point of the circle beyond K on the straight line DK has
its partner on the ray DB beyond B, and a point of the circle between D and K has its
partner between D and B. -/
theorem Prop8.partner {A D G K B : Point} {ABC : Circle} (hABC : ∃ M : Point, Centre M ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A)
    (hK : OnCircle K ABC) (hB : OnCircle B ABC) (hBK : OppositeSidesOf B K D A)
    (hDB : ‖D B‖ = ‖D K‖) :
    ∠ A D B = ∠ A D K ∧
    ((∃ C : Point, OnCircle C ABC ∧ Between D B C) ↔
      (∃ C : Point, OnCircle C ABC ∧ Between D K C)) ∧
    ((∃ H : Point, OnCircle H ABC ∧ Between D H B) ↔
      (∃ H : Point, OnCircle H ABC ∧ Between D H K)) := by
  have hpartner := (Prop8 hABC hD hA hG hDGA hGA).2.2.2.2
  /- Take the centre M from the given circle. -/
  obtain ⟨M, hM⟩ := hABC
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
theorem Prop8.general {A D G : Point} {ABC : Circle} (hABC : ∃ M : Point, Centre M ABC)
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
  obtain ⟨hgreatest, hconcave, hleast, hconvex, hpartner⟩ := Prop8 hABC hD hA hG hDGA hGA
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
    obtain ⟨hang, -, hclass⟩ := Prop8.partner hABC hD hA hG hDGA hGA hF hB hBF hDB
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
    obtain ⟨hang, hclass, -⟩ := Prop8.partner hABC hD hA hG hDGA hGA hL hB hBL hDB
    have hlt' : ∠ A D K < ∠ A D B := by rw [hang]; exact hlt
    have hless := hconvex K B hK hB hKC (hclass.mpr hLF) hKB hlt'
    rwa [hDB] at hless

/-- The check: today's statement of III.8 follows from `Prop8.general` (checked by Lean).
Two points on one side of DA are off it. -/
example : type_of% @Elements.BookIII.Prop8 := by
  intro A D G ABC hABC hD hA hG hDGA hGA
  obtain ⟨hgreatest, hconcave, hleast, hconvex, hpartner⟩ :=
    Prop8.general hABC hD hA hG hDGA hGA
  exact ⟨hgreatest,
    fun E F hE hF hHE hLF hEF hlt =>
      hconcave E F hE hF hHE hLF hEF.triangle hEF.symm.triangle hlt,
    hleast,
    fun K L hK hL hKC hLF hKL hlt =>
      hconvex K L hK hL hKC hLF hKL.triangle hKL.symm.triangle hlt,
    hpartner⟩

end Elements.BookIII
