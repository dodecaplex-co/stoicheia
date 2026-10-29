import Elements.Figure.Basics
import Elements.BookIII.Circumferences
import Elements.BookIII.Prop02
import Elements.BookIII.Prop24
import Elements.BookIII.Prop28
import Elements.BookIII.Prop29

/-!
# Book III: what equal circumferences and equal segments come to

A circumference is measured by twice the angle that stands on it (`circumference`), a
measure that carries no radius, and two segments are equal when they coincide
(`Arc.Congruent`). These bridge theorems say what each comes to for drawn segments
(`Arc.Drawn`). In equal circles, the circumferences of two drawn segments are
equal in measure exactly when the straight lines that cut them off are equal and they are
of one kind, both less than semicircles, both semicircles, or both greater
(`Arc.measure_eq_iff`). And two drawn segments are congruent exactly when their circles are
equal and their circumferences equal in measure (`Arc.congruent_iff`).

They stand after III.29 so that the argument cannot go round in a circle: they rest on
III.24, III.28 and III.29, and III.26–III.29 must not rest on them. With III.24, this file
is one of the two places outside placement's own files that may cite `placement` or a lemma
of the `Placement` namespace; its theorems reach placement only through III.24.
-/

namespace Elements.BookIII

open Tacit

/-- **In equal circles, equal measure is equal chord and same kind.** For two drawn arcs in equal
circles, the measures are equal exactly when the straight lines joining their ends are equal and
the arcs are of the same kind (both less than semicircles, both semicircles, or both greater).

Proved one way by III.29, in its companion for circumferences equal in measure
(`Prop29.of_measure`: equal circumferences, equal straight lines), the kind read off from the
measure (`Prop29.size`); and the other way by III.28 (equal chords, kind decided by the
centre's side), with the comparison of each kind with a semicircle
(`Circumference.lt_semicircle`, `.semicircle`, `.gt_semicircle`).

A bridge theorem for the measure that III.26–III.29 compare. -/
theorem Arc.measure_eq_iff {a b : Arc} (ha : a.Drawn) (hb : b.Drawn)
    (hcircles : EqualCircles a.circle b.circle) :
    a.measure = b.measure ↔ ‖a.B a.C‖ = ‖b.B b.C‖ ∧ Arc.SameKind a b := by
  obtain ⟨hB, hC, hK⟩ := ha
  obtain ⟨hD, hE, hL⟩ := hb
  have hBCK : Triangle a.B a.C a.K := hK
  have hDEL : Triangle b.B b.C b.K := hL
  constructor
  · intro heq
    /- Equal circumferences in equal circles are subtended by equal straight lines
       [III. 29], here by its companion for circumferences equal in measure. -/
    refine ⟨Prop29.of_measure hcircles hB hC hD hE hK hL heq, ?_⟩
    /- Each measure is less than two right angles, equal to them, or greater, as its centre
       lies beyond the base, on it, or on the arc's side (`Prop29.size`). Equal measures fall
       in the same case, so the arcs are of one kind. -/
    change circumference a.circle a.B a.K a.C = circumference b.circle b.B b.K b.C at heq
    obtain ⟨G, hG⟩ := exists_centre a.circle
    obtain ⟨H, hH⟩ := exists_centre b.circle
    rcases Prop29.size hG hB hC hBCK with ⟨hGK, hlt⟩ | ⟨hBGC, hsemi⟩ | ⟨hGK, hgt⟩ <;>
      rcases Prop29.size hH hD hE hDEL with ⟨hHL, hlt'⟩ | ⟨hDHE, hsemi'⟩ | ⟨hHL, hgt'⟩
    · exact Or.inl ⟨⟨G, hG, hGK⟩, ⟨H, hH, hHL⟩⟩
    · rw [heq, hsemi'] at hlt; exact absurd hlt (lt_irrefl _)
    · rw [heq] at hlt; exact absurd (lt_trans hlt hgt') (lt_irrefl _)
    · rw [← heq, hsemi] at hlt'; exact absurd hlt' (lt_irrefl _)
    · obtain ⟨N, hB_N, hG_N, hC_N⟩ := collinear_of_between hBGC
      obtain ⟨M, hD_M, hH_M, hE_M⟩ := collinear_of_between hDHE
      exact Or.inr (Or.inl ⟨⟨G, hG, N, hB_N, hC_N, hG_N⟩, ⟨H, hH, M, hD_M, hE_M, hH_M⟩⟩)
    · rw [← heq, hsemi] at hgt'; exact absurd hgt' (lt_irrefl _)
    · rw [heq] at hgt; exact absurd (lt_trans hlt' hgt) (lt_irrefl _)
    · rw [heq, hsemi'] at hgt; exact absurd hgt (lt_irrefl _)
    · exact Or.inr (Or.inr ⟨⟨G, hG, hGK⟩, ⟨H, hH, hHL⟩⟩)
  · rintro ⟨hBC, hkind⟩
    /- We name the circumference on the other side of each base by a point there, X or Y. -/
    obtain ⟨X, hXK, -⟩ := exists_oppositeSidesOf hBCK []
    obtain ⟨Y, hYL, -⟩ := exists_oppositeSidesOf hDEL []
    rcases hkind with ⟨⟨G, hG, hGK⟩, ⟨H, hH, hHL⟩⟩ |
      ⟨⟨G, hG, N, hB_N, hC_N, hG_N⟩, ⟨H, hH, M, hD_M, hE_M, hH_M⟩⟩ |
      ⟨⟨G, hG, hGK⟩, ⟨H, hH, hHL⟩⟩
    · /- Both arcs are less than semicircles, the centres lying beyond the bases, and the
         circumferences on the other sides are greater (`Circumference.lt_semicircle`,
         `Circumference.gt_semicircle`): so the arcs are III.28's less circumferences. -/
      have hGX : SameSideOf G X a.B a.C := OppositeSidesOf.sameSideOf hGK.symm hXK.symm
      have hHY : SameSideOf H Y b.B b.C := OppositeSidesOf.sameSideOf hHL.symm hYL.symm
      have hle₁ : circumference a.circle a.B a.K a.C ≤ circumference a.circle a.B X a.C :=
        fun hlt => lt_irrefl _ (lt_trans hlt (lt_trans (Circumference.lt_semicircle hG hB hC hGK)
          (Circumference.gt_semicircle hG hB hC hGX)))
      have hle₂ : circumference b.circle b.B b.K b.C ≤ circumference b.circle b.B Y b.C :=
        fun hlt => lt_irrefl _ (lt_trans hlt (lt_trans (Circumference.lt_semicircle hH hD hE hHL)
          (Circumference.gt_semicircle hH hD hE hHY)))
      exact (Prop28 hcircles hB hC hD hE hXK hYL hBC hle₁ hle₂).2.1
    · /- Both arcs are semicircles: a centre on the base lies between its ends, within the
         circle, and each measure is two right angles (`Circumference.semicircle`). -/
      have hBGC := between_of_inside_chord hG_N hB_N hC_N (centre_inside hG) hB hC hBCK.ne₁₂
      have hDHE := between_of_inside_chord hH_M hD_M hE_M (centre_inside hH) hD hE hDEL.ne₁₂
      exact (Circumference.semicircle hG hB hC hBGC hBCK).trans
        (Circumference.semicircle hH hD hE hDHE hDEL).symm
    · /- Both arcs are greater than semicircles, the centres lying on their sides, and the
         circumferences on the other sides are less: so the arcs are III.28's greater
         circumferences. -/
      have hGX : OppositeSidesOf G X a.B a.C := hGK.trans_opposite hXK.symm
      have hHY : OppositeSidesOf H Y b.B b.C := hHL.trans_opposite hYL.symm
      have hle₁ : circumference a.circle a.B X a.C ≤ circumference a.circle a.B a.K a.C :=
        fun hlt => lt_irrefl _ (lt_trans hlt (lt_trans (Circumference.lt_semicircle hG hB hC hGX)
          (Circumference.gt_semicircle hG hB hC hGK)))
      have hle₂ : circumference b.circle b.B Y b.C ≤ circumference b.circle b.B b.K b.C :=
        fun hlt => lt_irrefl _ (lt_trans hlt (lt_trans (Circumference.lt_semicircle hH hD hE hHY)
          (Circumference.gt_semicircle hH hD hE hHL)))
      exact (Prop28 hcircles hB hC hD hE hXK.symm hYL.symm hBC hle₁ hle₂).1.1

/-- **Congruent is equal circles and equal measure.** Two drawn arcs are congruent exactly when
their circles are equal and their measures are equal.

Proved: one way, the measures are equal by `Prop24.equalMeasure`, and the circles by
`Prop24.equalCircles`, the congruence keeping the chord and, at a point of the arc and its
image, the angle in the segment [I. 8] (`Prop24.image`); neither is proved again here. The
other way, by `Arc.measure_eq_iff` the chords are equal; the circumferences on the other sides
of the bases are the remainders of the whole circles [C.N. 3], each twice the angle in its
segment (`Circumference.eq`), so the angles in the segments are equal, and III.24 (restated)
makes the segments congruent.

A bridge theorem for the congruence that III.24, III.26 and III.28 conclude. -/
theorem Arc.congruent_iff {a b : Arc} (ha : a.Drawn) (hb : b.Drawn) :
    Arc.Congruent a b ↔ EqualCircles a.circle b.circle ∧ a.measure = b.measure := by
  obtain ⟨hB, hC, hK⟩ := id ha
  obtain ⟨hD, hE, hL⟩ := id hb
  constructor
  · intro h
    /- A point P of the first arc off its base, and its image Q, show the segments similar
       on equal bases (`Prop24.image`, by I.8): so the circles are equal, by III.24's
       companion `Prop24.equalCircles`, and the measures, by `Prop24.equalMeasure`. -/
    obtain ⟨P, hP, hPK⟩ := Prop2.sameSide hB hC hK
    obtain ⟨hBC, Q, hQ, hQL, hPQ⟩ := Prop24.image ha hb h hP hPK
    exact ⟨(Prop24.equalCircles hB hC hP hD hE hQ hPK.triangle hQL.triangle
      hBC hPQ).1, Prop24.equalMeasure ha hb h⟩
  · rintro ⟨hcircles, hm⟩
    /- The chords are equal (`Arc.measure_eq_iff`). -/
    have hBC : ‖a.B a.C‖ = ‖b.B b.C‖ := ((Arc.measure_eq_iff ha hb hcircles).mp hm).1
    /- The angles in the segments, at points P and Q of the arcs off their bases, are equal.
       The circumferences on the other sides of the bases, named by points X and Y there, are
       the remainders of the whole circles when the equal arcs are taken away
       (`Circumference.whole`), so they are equal [C.N. 3]; and each is twice the angle at P
       or Q (`Circumference.eq`). -/
    obtain ⟨P, hP, hPK⟩ := Prop2.sameSide hB hC hK
    obtain ⟨Q, hQ, hQL⟩ := Prop2.sameSide hD hE hL
    obtain ⟨X, hXK, -⟩ := exists_oppositeSidesOf (show Triangle a.B a.C a.K from hK) []
    obtain ⟨Y, hYL, -⟩ := exists_oppositeSidesOf (show Triangle b.B b.C b.K from hL) []
    have hXY : circumference a.circle a.B X a.C = circumference b.circle b.B Y b.C :=
      CommonNotion3 ((Circumference.whole hB hC hXK.symm).trans
        (Circumference.whole hD hE hYL.symm).symm) hm
    rw [Circumference.eq hP hB hC (hPK.trans_opposite hXK.symm),
      Circumference.eq hQ hD hE (hQL.trans_opposite hYL.symm)] at hXY
    have hPQ : ∠ a.B P a.C = ∠ b.B Q b.C := Magnitude.eq_of_add_self_eq hXY
    /- So the segments named by P and Q are similar, and on equal bases they are congruent
       [III. 24]; only the side names a segment (`Arc.Congruent.congr_side`). -/
    exact (Prop24 hB hC hP hD hE hQ hPK.triangle hQL.triangle hBC
      hPQ).congr_side hPK hQL

end Elements.BookIII
