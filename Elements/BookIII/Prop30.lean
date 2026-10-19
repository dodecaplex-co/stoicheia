import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop17
import Elements.BookIII.Prop02
import Elements.BookIII.Prop21
import Elements.BookIII.Prop22
import Elements.BookIII.Prop28

/-!
# Book III, Proposition 30

Euclid's text, in Heath's translation: [`heath/III/30.md`](../../heath/III/30.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- To bisect a given circumference. -/
theorem Prop30 {A B : Point} {ADB : Circle} (hA : OnCircle A ADB) (hB : OnCircle B ADB) :
    ∀ P : Point, ¬ Collinear A B P → ∃ D : Point, OnCircle D ADB ∧ SameSideOf D P A B ∧
      standing ADB A B D = standing ADB D A B := by
  -- Let ADB be the given circumference;
  /- The given circumference is the one on P's side of AB. -/
  intro P hP
  have hABP : Triangle A B P := hP
  have hAB : A ≠ B := hABP.ne₁₂
  -- thus it is required to bisect the circumference ADB.
  -- Let AB be joined and bisected at C; from the point C let CD be drawn at right angles to
  -- the straight line AB, and let AD, DB be joined.
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  obtain ⟨C, hACB, hAC⟩ := BookI.Prop10 hAB
  have hC_L : OnLine C L := on_line_of_between_ends hACB hA_L hB_L
  obtain ⟨X, hXP, hX⟩ := BookI.Prop11 hAB ⟨L, hA_L, hB_L, hC_L⟩ hP
  /- CX meets the circumference on P's side at D. C is within the circle
     by III.2, so when XC is produced beyond C to Y, the straight line meets
     the circle at D, beyond C from Y, on X's side (`line_circle_beyond`). -/
  have hC_in : InsideCircle C ADB := Prop2 hA hB C hACB
  have hX_L : ¬ OnLine X L := hXP.triangle.off_line hA_L hB_L
  have hCX : C ≠ X := fun e => hX_L (e ▸ hC_L)
  obtain ⟨N, hC_N, hX_N⟩ := Postulate1 C X hCX
  obtain ⟨Y, hY_N, hXCY, -⟩ := Postulate2 hX_N hC_N hCX.symm []
  obtain ⟨D, hD, hD_N, hDCY⟩ :=
    line_circle_beyond hC_in hC_N hY_N (ne_of_between (between_symm hXCY))
  have hDC : D ≠ C := fun e => inside_not_on hC_in (e ▸ hD)
  have hD_L : ¬ OnLine D L := fun hD_L =>
    hX_L ((line_unique hDC hD_N hC_N hD_L hC_L) ▸ hX_N)
  have hY_L : ¬ OnLine Y L := fun hY_L =>
    hX_L ((line_unique (ne_of_between (between_symm hXCY)) hY_N hC_N hY_L hC_L) ▸ hX_N)
  have hDX : SameSide D X L := same_side_of_opposite_sides
    ⟨hY_L, hD_L, fun h => pasch3 hDCY hC_L (same_side_symm h)⟩
    ⟨hY_L, hX_L, fun h => pasch3 hXCY hC_L (same_side_symm h)⟩
  have hDP : SameSideOf D P A B := (SameSideOf.of_line hAB hA_L hB_L hDX).trans hXP
  refine ⟨D, hD, hDP, ?_⟩
  have hABD : Triangle A B D := Triangle.of_line hA_L hB_L hAB hD_L
  -- Then, since AC is equal to CB,
  have hCA : ‖C A‖ = ‖C B‖ := by rw [len_symm C A, hAC]
  -- and CD is common,
  have hCD : ‖C D‖ = ‖C D‖ := rfl
  -- the two sides AC, CD are equal to the two sides BC, CD;
  -- and the angle ACD is equal to the angle BCD, for each is right;
  have hDray : OnRay D C X := OnRay.of_between_between (between_symm hXCY) (between_symm hDCY)
  have hACD : ∠ A C D = ∟ := by
    rw [angle_onRay_right hDray (ne_of_between hACB)]
    exact hX A ⟨L, hA_L, hB_L, hA_L⟩ (ne_of_between hACB)
  have hBCD : ∠ B C D = ∟ := by
    rw [angle_onRay_right hDray (ne_of_between (between_symm hACB))]
    exact hX B ⟨L, hA_L, hB_L, hB_L⟩ (ne_of_between (between_symm hACB))
  -- therefore the base AD is equal to the base DB. [I. 4]
  have hCAD : Triangle C A D := Triangle.of_line hC_L hA_L (ne_of_between hACB).symm hD_L
  have hCBD : Triangle C B D :=
    Triangle.of_line hC_L hB_L (ne_of_between (between_symm hACB)).symm hD_L
  obtain ⟨hAD, -, hA₁, -⟩ := BookI.Prop4 hCAD hCBD hCA hCD (hACD.trans hBCD.symm)
  have hAD' : ‖A D‖ = ‖D B‖ := by rw [hAD, len_symm B D]
  -- But equal straight lines cut off equal circumferences, the greater equal to the greater,
  -- and the less to the less; [III. 28]
  /- We use III.28 in one circle, which is equal to itself (`EqualCircles.refl`), and name
     the less circumferences by points Q, R beyond AD from B and beyond DB from A. -/
  obtain ⟨Q, hQB, -⟩ := exists_oppositeSidesOf hABD.acb []
  obtain ⟨R, hRA, -⟩ := exists_oppositeSidesOf hABD.cba []
  have h28 := Prop28 (EqualCircles.refl ADB) hA hD hD hB hQB.symm hRA.symm hAD'
  -- and each of the circumferences AD, DB is less than a semicircle;
  /- They are measured at B and A (`Circumference.standing`), by the angles ABD, DAB.
     These are equal, for I.4 gave them, C being on AB, and two of them are less than two
     right angles [I. 17]. -/
  have hbase : ∠ D A B = ∠ A B D := by
    rw [angle_symm hABD.ne₁₃.symm hAB.symm, ← angle_onRay_left (OnRay.of_between hACB) hABD.ne₁₃.symm, hA₁,
      angle_onRay_left (OnRay.of_between (between_symm hACB)) hABD.ne₂₃.symm]
  have h17 := (BookI.Prop17 hABD).2.2
  rw [hbase] at h17
  have hAQD : circumference ADB A Q D < ∟ + ∟ := by
    rw [← standing_eq_circumference hQB.symm, Circumference.standing hB hA hD hABD.acb]
    exact h17
  have hDRB : circumference ADB D R B < ∟ + ∟ := by
    rw [← standing_eq_circumference hRA.symm, Circumference.standing hA hD hB hABD.cba, hbase]
    exact h17
  /- So the circumferences ABD, DAB on the other sides are greater, for the two on each
     straight line make up the circle (`Circumference.whole`). -/
  have not_greater : ∀ {x y : Angle}, x < ∟ + ∟ → x + y = ∟ + ∟ + (∟ + ∟) → x ≤ y := by
    intro x y hx hxy hyx
    have h1 := add_lt_add_right y hx
    have h2 := add_lt_add_right (∟ + ∟) (lt_trans hyx hx)
    rw [add_comm y] at h2
    exact lt_irrefl _ (hxy ▸ lt_trans h1 h2)
  have hw₁ := Circumference.whole hA hD hQB.symm
  have hw₂ := Circumference.whole hD hB hRA.symm
  -- therefore the circumference AD is equal to the circumference DB.
  have hADDB := (h28 (not_greater hAQD hw₁) (not_greater hDRB hw₂)).2.1
  -- Therefore the given circumference has been bisected at the point D.
  rw [standing_eq_circumference hQB.symm, standing_eq_circumference hRA.symm]
  exact hADDB
  -- Q. E. F.

end Elements.BookIII
