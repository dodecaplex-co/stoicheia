import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookI.Prop06
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

/-- A point X of a circle on the straight line joining two others, U and V, is U or V:
three points of a circle are not on one straight line. [III. 2] -/
theorem Prop30.on_chord {U V X : Point} {α : Circle} (hU : OnCircle U α) (hV : OnCircle V α)
    (hX : OnCircle X α) (hUV : U ≠ V) (h : Collinear U V X) : X = U ∨ X = V := by
  by_cases hXU : X = U
  · exact Or.inl hXU
  by_cases hXV : X = V
  · exact Or.inr hXV
  exact absurd h (Prop2.triangle hU hV hX hUV (Ne.symm hXV) (Ne.symm hXU))

/-- No point X of a circle lies within the triangle of three others, A, B and D: on D's side
of AB, on B's side of AD and on A's side of DB. For then the straight line DX would separate
A from B (System E, Triple incidence 1), and meet AB at a point E between them, within the
circle [III. 2]. On DX, E is not between D and X, which are on one side of AB (Pasch 3); so
X lies between D and E, or D between X and E, and that point would be within the circle
(`Prop2.within`), not on it. [III. 2] -/
theorem Prop30.not_within {A B D X : Point} {α : Circle} (hA : OnCircle A α)
    (hB : OnCircle B α) (hD : OnCircle D α) (hX : OnCircle X α) (hXD : SameSideOf X D A B)
    (hXB : SameSideOf X B A D) (hXA : SameSideOf X A D B) : False := by
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hXD.1
  obtain ⟨K, hA_K, hD_K⟩ := Postulate1 A D hXB.1
  obtain ⟨N, hD_N, hB_N⟩ := Postulate1 D B hXA.1
  have hX_K : ¬ OnLine X K := not_on_line_of_same_side (hXB.sameSide hA_K hD_K)
  have hX_N : ¬ OnLine X N := not_on_line_of_same_side (hXA.sameSide hD_N hB_N)
  have hDX : D ≠ X := fun e => hX_K (e ▸ hD_K)
  obtain ⟨M, hD_M, hX_M⟩ := Postulate1 D X hDX
  /- The straight line DX separates A from B, X lying within the angle ADB. -/
  have hAB_M : ¬ SameSide A B M :=
    triple_incidence1 hD_K hD_M hD_N hA_K hX_M hB_N (hXB.sameSide hA_K hD_K)
      (same_side_symm (hXA.sameSide hD_N hB_N))
  have hA_M : ¬ OnLine A M := fun h => hX_K (line_unique hXB.1 h hD_M hA_K hD_K ▸ hX_M)
  have hB_M : ¬ OnLine B M := fun h => hX_N (line_unique hXA.1 hD_M h hD_N hB_N ▸ hX_M)
  obtain ⟨E, hE_M, hAEB⟩ := OppositeSides.exists_between ⟨hA_M, hB_M, hAB_M⟩
  have hE_in : InsideCircle E α := Prop2 hA hB E hAEB
  have hE_L : OnLine E L := on_line_of_between_ends hAEB hA_L hB_L
  have hDX_L : SameSide D X L := same_side_symm (hXD.sameSide hA_L hB_L)
  have hDE : D ≠ E := fun e => not_on_line_of_same_side hDX_L (e ▸ hE_L)
  have hXE : X ≠ E := fun e => not_on_line_of_same_side (same_side_symm hDX_L) (e ▸ hE_L)
  rcases between_cases hDX hXE hDE hD_M hX_M hE_M with h | h | h
  · exact inside_not_on (Prop2.within (Or.inr hD) (Or.inl hE_in) h) hX
  · exact inside_not_on (Prop2.within (Or.inr hX) (Or.inl hE_in) h) hD
  · exact pasch3 h hE_L hDX_L

/-- No point X of a circle lies in the angle vertical to the angle UVW of three others: across
VU from W and across VW from U. For XW would cross VU at a point M within the circle
[III. 2], on X's side of VW (Pasch 2), and so across VW from U. Then MU would cross VW, and
the straight lines VU, VW meet only at V; so V would lie between M and U, and be within the
circle (`Prop2.within`), not on it. [III. 2] -/
theorem Prop30.not_vertical {U V W X : Point} {α : Circle} (hU : OnCircle U α)
    (hV : OnCircle V α) (hW : OnCircle W α) (hX : OnCircle X α)
    (hXW : OppositeSidesOf X W V U) (hXU : OppositeSidesOf X U V W) : False := by
  obtain ⟨L, hV_L, hU_L⟩ := Postulate1 V U hXW.1
  obtain ⟨N, hV_N, hW_N⟩ := Postulate1 V W hXU.1
  have hXU_N : OppositeSides X U N := hXU.oppositeSides hV_N hW_N
  obtain ⟨M, hM_L, hXMW⟩ := (hXW.oppositeSides hV_L hU_L).exists_between
  have hM_in : InsideCircle M α := Prop2 hX hW M hXMW
  have hM_N : ¬ OnLine M N := fun h => hXU_N.1 (on_line_of_between (between_symm hXMW) hW_N h)
  have hMX : SameSide M X N := pasch2 (between_symm hXMW) hW_N hM_N
  have hMU_N : OppositeSides M U N :=
    ⟨hM_N, hXU_N.2.1, fun h => hXU_N.2.2 (same_side_trans hMX h)⟩
  obtain ⟨V', hV'_N, hMV'U⟩ := hMU_N.exists_between
  have hV'_L : OnLine V' L := on_line_of_between_ends hMV'U hM_L hU_L
  have hV' : V' = V := Classical.byContradiction fun hne =>
    hXU_N.2.1 (line_unique hne hV'_L hV_L hV'_N hV_N ▸ hU_L)
  rw [hV'] at hMV'U
  exact inside_not_on (Prop2.within (Or.inl hM_in) (Or.inr hU) hMV'U) hV

/-- **III.30's halves** (companion of III.30, "III.30 halves"). Let D be a point of the
circle ADB on P's side of AB, with the circumferences standing at B and at A equal, as
III.30 finds it. Then the circumference AD away from B, named by Q, and the circumference DB
away from A, named by R, are drawn and congruent; together they make up the given
circumference AB on P's side; every point of it lies on one or the other; and the two share
only D, ends included.

III.30's statement gives the equal measures, not the equal straight lines AD, DB that its
proof finds by I.4, so they are recovered here: the equal measures are twice the angles
ABD, DAB (`Circumference.standing`), so those angles are equal, and DA is equal to DB
[I. 6]. Each circumference is less than a semicircle [I. 17], so III.28's congruence of the
less circumferences applies. They add by `Circumference.add`, and the division point by
point follows from III.2 (`Prop30.on_chord`, `Prop30.not_within`, `Prop30.not_vertical`).
[I. 6, I. 17, III. 2, III. 28] -/
theorem Prop30.halves {A B D P : Point} {ADB : Circle}
    (hA : OnCircle A ADB) (hB : OnCircle B ADB)
    (hD : OnCircle D ADB) (hDP : SameSideOf D P A B)
    (hequal : standing ADB A B D = standing ADB D A B) :
    ∃ Q R : Point,
      OppositeSidesOf Q B A D ∧ OppositeSidesOf R A D B ∧
      Arc.Drawn ⟨ADB, A, D, Q⟩ ∧ Arc.Drawn ⟨ADB, D, B, R⟩ ∧
      Arc.Congruent ⟨ADB, A, D, Q⟩ ⟨ADB, D, B, R⟩ ∧
      circumference ADB A Q D + circumference ADB D R B =
        circumference ADB A P B ∧
      (∀ X : Point, OnArc X ⟨ADB, A, B, P⟩ ↔
        OnArc X ⟨ADB, A, D, Q⟩ ∨ OnArc X ⟨ADB, D, B, R⟩) ∧
      (∀ X : Point,
        (OnArc X ⟨ADB, A, D, Q⟩ ∧ OnArc X ⟨ADB, D, B, R⟩) ↔
          X = D) := by
  have hABD : Triangle A B D := hDP.triangle
  have hAB : A ≠ B := hABD.ne₁₂
  have hAD : A ≠ D := hABD.ne₁₃
  have hDB : D ≠ B := hABD.ne₂₃.symm
  obtain ⟨K, hA_K, hD_K⟩ := Postulate1 A D hAD
  obtain ⟨N, hD_N, hB_N⟩ := Postulate1 D B hDB
  /- A point is not across a straight line from itself. -/
  have hne : ∀ {U V W Z : Point}, OppositeSidesOf U V W Z → U ≠ V := by
    rintro U V W Z h rfl
    obtain ⟨L, hW, hZ⟩ := Postulate1 W Z h.1
    exact (h.oppositeSides hW hZ).2.2 (same_side_refl (h.oppositeSides hW hZ).1)
  /- Q names the side of AD away from B, and R the side of DB away from A, as in III.30. -/
  obtain ⟨Q, hQB, -⟩ := exists_oppositeSidesOf hABD.acb []
  obtain ⟨R, hRA, -⟩ := exists_oppositeSidesOf hABD.cba []
  refine ⟨Q, R, hQB, hRA, ⟨hA, hD, hQB.triangle⟩, ⟨hD, hB, hRA.triangle⟩, ?_,
    Circumference.add hA hD hB hDP hQB hRA, ?_, ?_⟩
  · /- The equal circumferences standing at B and at A are twice the angles ABD, DAB, so
       those angles are equal. -/
    have hbase : ∠ A B D = ∠ D A B := by
      have h := hequal
      rw [Circumference.standing hB hA hD hABD.acb,
        Circumference.standing hA hD hB hABD.cba] at h
      exact Magnitude.eq_of_add_self_eq h
    /- So DA is equal to DB. [I. 6] -/
    have hDA : ‖D A‖ = ‖D B‖ := BookI.Prop6 hABD.cab (by
      rw [angle_symm hDB hAB]
      exact hbase.symm)
    have hAD' : ‖A D‖ = ‖D B‖ := by rw [len_symm A D, hDA]
    /- Each circumference is less than a semicircle, measured at B and at A by the equal
       angles ABD, DAB, two angles of the triangle ABD. [I. 17] -/
    have h17 := (BookI.Prop17 hABD).2.2
    rw [← hbase] at h17
    have hAQD : circumference ADB A Q D < ∟ + ∟ := by
      rw [← standing_eq_circumference hQB.symm, Circumference.standing hB hA hD hABD.acb]
      exact h17
    have hDRB : circumference ADB D R B < ∟ + ∟ := by
      rw [← standing_eq_circumference hRA.symm, Circumference.standing hA hD hB hABD.cba,
        ← hbase]
      exact h17
    have not_greater : ∀ {x y : Angle}, x < ∟ + ∟ → x + y = ∟ + ∟ + (∟ + ∟) → x ≤ y := by
      intro x y hx hxy hyx
      have h1 := add_lt_add_right y hx
      have h2 := add_lt_add_right (∟ + ∟) (lt_trans hyx hx)
      rw [add_comm y] at h2
      exact lt_irrefl _ (hxy ▸ lt_trans h1 h2)
    /- So they are III.28's less circumferences on the equal straight lines AD, DB. -/
    exact (Prop28 (EqualCircles.refl ADB) hA hD hD hB hQB.symm hRA.symm hAD'
      (not_greater hAQD (Circumference.whole hA hD hQB.symm))
      (not_greater hDRB (Circumference.whole hD hB hRA.symm))).2.2
  · intro X
    constructor
    · /- A point of the given circumference on neither half would lie within the triangle
         ABD. -/
      rintro ⟨hX, hXP⟩
      rcases Prop28.sides (K := X) hQB.triangle with hXQ | hXAD | hXQ
      · exact Or.inl ⟨hX, Or.inl hXQ⟩
      · exact Or.inl ⟨hX, Or.inr hXAD⟩
      rcases Prop28.sides (K := X) hRA.triangle with hXR | hXDB | hXR
      · exact Or.inr ⟨hX, Or.inl hXR⟩
      · exact Or.inr ⟨hX, Or.inr hXDB⟩
      have hXB : SameSideOf X B A D := OppositeSidesOf.sameSideOf hXQ.symm hQB
      have hXA : SameSideOf X A D B := OppositeSidesOf.sameSideOf hXR.symm hRA
      exfalso
      rcases hXP with hXP | hXAB
      · exact Prop30.not_within hA hB hD hX (hXP.trans hDP.symm) hXB hXA
      · exact Prop2.triangle hA hB hX hAB hXA.triangle.ne₂₃ hXQ.triangle.ne₁₃ hXAB
    · /- A point of either half across AB from D would lie in the angle vertical to DAB or
         to DBA. -/
      rintro (⟨hX, hXQ⟩ | ⟨hX, hXR⟩)
      · refine ⟨hX, ?_⟩
        rcases Prop28.sides (K := X) hABD with hXD | hXAB | hXD
        · exact Or.inl (hXD.trans hDP)
        · exact Or.inr hXAB
        exfalso
        rcases hXQ with hXQ | hXAD
        · exact Prop30.not_vertical hB hA hD hX hXD (hXQ.trans_opposite hQB)
        · exact Prop2.triangle hA hD hX hAD (hne hXD).symm hXD.triangle.ne₁₃ hXAD
      · refine ⟨hX, ?_⟩
        rcases Prop28.sides (K := X) hABD with hXD | hXAB | hXD
        · exact Or.inl (hXD.trans hDP)
        · exact Or.inr hXAB
        exfalso
        rcases hXR with hXR | hXDB
        · exact Prop30.not_vertical hA hB hD hX hXD.swap (hXR.trans_opposite hRA).swap
        · exact Prop2.triangle hD hB hX hDB hXD.triangle.ne₂₃ (hne hXD).symm hXDB
  · intro X
    constructor
    · /- A point on both halves other than D would be one of the ends A, B, or lie in the
         angle vertical to ADB. -/
      rintro ⟨⟨hX, hXQ⟩, ⟨-, hXR⟩⟩
      rcases hXQ with hXQ | hXAD
      · rcases hXR with hXR | hXDB
        · exact (Prop30.not_vertical hA hD hB hX (hXQ.trans_opposite hQB).swap
            (hXR.trans_opposite hRA)).elim
        · rcases Prop30.on_chord hD hB hX hDB hXDB with h | h
          · exact h
          · rw [h] at hXQ
            exact absurd rfl (hne (hXQ.trans_opposite hQB))
      · rcases Prop30.on_chord hA hD hX hAD hXAD with h | h
        · rw [h] at hXR
          rcases hXR with hXR | hXDB
          · exact absurd rfl (hne (hXR.trans_opposite hRA))
          · exact absurd hXDB hABD.cba
        · exact h
    · rintro rfl
      exact ⟨⟨hD, Or.inr ⟨K, hA_K, hD_K, hD_K⟩⟩, ⟨hD, Or.inr ⟨N, hD_N, hB_N, hD_N⟩⟩⟩

end Elements.BookIII
