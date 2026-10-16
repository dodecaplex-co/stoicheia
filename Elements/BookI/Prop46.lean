import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop04
import Elements.BookI.Prop11
import Elements.BookI.Prop29
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 46

Euclid's text, in Heath's translation: [`heath/I/46.md`](../../heath/I/46.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

After the proposition come two corollaries that Euclid assumes in I.48 and that
Heath reports Proclus proving here: squares described on equal straight lines are
equal (`Prop46.square_eq`), and equal squares are described on equal straight
lines (`Prop46.side_eq`).
-/

namespace Elements.BookI

open Tacit

/-- On a given straight line to describe a square. -/
theorem Prop46 {A B P : Point} (hAB : A ≠ B) (hP : ¬ Collinear A B P) :
    ∃ D E : Point, Square A D E B ∧ SameSideOf D P A B ∧ SameSideOf E P A B := by
  -- Let AB be the given straight line; thus it is required to describe a square on the
  -- straight line AB.
  -- Let AC be drawn at right angles to the straight line AB from the point A on it [I. 11],
  -- and let AD be made equal to AB; through the point D let DE be drawn parallel to AB, and
  -- through the point B let BE be drawn parallel to AD. [I. 31]
  -- Therefore ADEB is a parallelogram; therefore AB is equal to DE, and AD to BE. [I. 34]
  -- But AB is equal to AD; therefore the four straight lines BA, AD, DE, EB are equal to one
  -- another; therefore the parallelogram ADEB is equilateral.
  -- I say next that it is also right-angled.
  -- For, since the straight line AD falls upon the parallels AB, DE, the angles BAD, ADE are
  -- equal to two right angles. [I. 29]
  -- But the angle BAD is right; therefore the angle ADE is also right.
  -- And in parallelogrammic areas the opposite sides and angles are equal to one
  -- another; [I. 34] therefore each of the opposite angles ABE, BED is also right.
  -- Therefore ADEB is right-angled.
  -- And it was also proved equilateral.
  -- Therefore it is a square; and it is described on the straight line AB.
  -- Q. E. F.
  sorry

/-- Squares described on equal straight lines are equal. Euclid assumes this in
I.48 ("since DA is equal to AB, the square on DA is also equal to the square on
AB"). Heath reports, under I.46, that Proclus proves it, and that it "is
immediately obvious if we divide the squares into two triangles by drawing a
diagonal in each" (vol. 1, p. 348). Each square is a parallelogram (`Prop28.square`), so the
diameter `AC` cuts it into the triangles `ABC` and `ACD`, right-angled at `B` and
`D`; and I.4 makes these equal to the triangles `A'B'C'` and `A'C'D'`. Here a
square `ABCD` is "described on `AB`" when its far corners `C`, `D` lie on one side
of `AB`. [I. 4, I. 28] -/
theorem Prop46.square_eq {A B C D A' B' C' D' : Point} (h : Square A B C D)
    (hCD : SameSideOf C D A B) (h' : Square A' B' C' D') (hCD' : SameSideOf C' D' A' B')
    (hAB : ‖A B‖ = ‖A' B'‖) : quadArea A B C D = quadArea A' B' C' D' := by
  have hp := Prop28.square h hCD
  have hp' := Prop28.square h' hCD'
  obtain ⟨h₁, h₂, h₃, -, hB, -, hD⟩ := h
  obtain ⟨h₁', h₂', h₃', -, hB', -, hD'⟩ := h'
  /- All four sides of each square are equal to its side `AB`. -/
  have hBC : ‖B C‖ = ‖B' C'‖ := h₁.symm.trans (hAB.trans h₁')
  have hCD₁ : ‖D C‖ = ‖D' C'‖ := by
    rw [len_symm D C, len_symm D' C', ← h₂, ← h₂']
    exact hBC
  have hDA : ‖D A‖ = ‖D' A'‖ := by
    rw [← h₃, ← h₃']
    exact (len_symm D C).symm.trans (hCD₁.trans (len_symm D' C'))
  have t₁ : △ B A C = △ B' A' C' :=
    (Prop4 hp.triangle.bac hp'.triangle.bac
      ((len_symm B A).trans (hAB.trans (len_symm A' B'))) hBC (hB.trans hB'.symm)).2.1
  have t₂ : △ D C A = △ D' C' A' :=
    (Prop4 hp.rotate.rotate.triangle.bac hp'.rotate.rotate.triangle.bac hCD₁ hDA
      (hD.trans hD'.symm)).2.1
  unfold quadArea
  rw [area_bac A B C, t₁, area_cba A C D, t₂, ← area_bac A' B' C', ← area_cba A' C' D']

/-- Conversely, equal squares are described on equal straight lines. Euclid assumes
this too in I.48 ("therefore the square on DC is equal to the square on BC, so that
the side DC is also equal to BC"). Heath reports, under I.46, Proclus' proof, which
places the two squares side by side. Lean takes another road. Were `AB` less than
`A'B'`, cut off from `A'B'` a straight line `A'X` equal to `AB` [I. 3], and describe
on it a square `A'ZYX` on the side of `C'` [I. 46]. It is equal to the square `ABCD`
(`Prop46.square_eq`); `Z` falls on `A'D'`, short of `D'`; and each square is double
the triangle its diameter cuts off from `A'` [I. 34]. But the triangle `XA'Z` is a
part of the triangle `B'A'D'`, and so less. [I. 3, I. 4, I. 28, I. 34, I. 46] -/
theorem Prop46.side_eq {A B C D A' B' C' D' : Point} (h : Square A B C D)
    (hCD : SameSideOf C D A B) (h' : Square A' B' C' D') (hCD' : SameSideOf C' D' A' B')
    (hsq : quadArea A B C D = quadArea A' B' C' D') : ‖A B‖ = ‖A' B'‖ := by
  /- The square on the less straight line is the less. -/
  have less : ∀ {A B C D A' B' C' D' : Point}, Square A B C D → SameSideOf C D A B →
      Square A' B' C' D' → SameSideOf C' D' A' B' → ‖A B‖ < ‖A' B'‖ →
      quadArea A B C D < quadArea A' B' C' D' := by
    intro A B C D A' B' C' D' h hCD h' hCD' hlt
    have hp' : Parallelogram A' B' C' D' := Prop28.square h' hCD'
    have hA'B' : A' ≠ B' := hCD'.1
    obtain ⟨L, hA'_L, hB'_L⟩ := Postulate1 A' B' hA'B'
    /- Cut off `A'X` equal to `AB`, and describe the square `A'ZYX` on it. -/
    obtain ⟨X, hA'XB', hA'X⟩ := Prop3 hCD.1 hlt
    have hX_L : OnLine X L := on_line_of_between_ends hA'XB' hA'_L hB'_L
    have hA'X_ne : A' ≠ X := ne_of_between hA'XB'
    have hC'_L : ¬ OnLine C' L := not_on_line_of_same_side (hCD'.sameSide hA'_L hB'_L)
    obtain ⟨Z, Y, hsqZ, hZ, hY⟩ :=
      Prop46 hA'X_ne fun ⟨K, hA'_K, hX_K, hC'_K⟩ =>
        hC'_L ((line_unique hA'X_ne hA'_K hX_K hA'_L hX_L) ▸ hC'_K)
    have hZY : SameSideOf Z Y X A' := (hZ.trans hY.symm).swap
    have hsq' : Square X A' Z Y := hsqZ.rotate.rotate.rotate
    have hps : Parallelogram X A' Z Y := Prop28.square hsq' hZY
    have heq : quadArea A B C D = quadArea X A' Z Y :=
      Prop46.square_eq h hCD hsq' hZY (hA'X.symm.trans (len_symm A' X))
    /- `Z` falls on `A'D'`, short of `D'`. -/
    have hZD' : SameSideOf Z D' A' B' :=
      (SameSideOf.of_line hA'B' hA'_L hB'_L (hZ.sameSide hA'_L hX_L)).trans hCD'
    have hZray : OnRay Z A' D' := by
      refine onRay_of_angle_eq hZD' ?_
      rw [angle_onRay_left (OnRay.of_beyond hA'XB') hZD'.triangle.ne₁₃.symm, hsqZ.2.2.2.1,
        angle_symm hA'B'.symm hCD'.symm.triangle.ne₁₃.symm, h'.2.2.2.1]
    have hA'Z : ‖A' Z‖ < ‖A' D'‖ := by
      rw [hsqZ.1.trans (hsqZ.2.1.trans hsqZ.2.2.1), len_symm X A', hA'X, len_symm A' D',
        ← h'.2.2.1, ← h'.2.1, ← h'.1]
      exact hlt
    have hA'ZD' : Between A' Z D' :=
      hZray.between_of_len_lt (OnRay.self hCD'.symm.triangle.ne₁₃) hA'Z
    /- Each square is double the triangle its diameter cuts off from `A'`. -/
    have hbig : quadArea A' B' C' D' = △ B' A' D' + △ B' A' D' := by
      rw [← hp'.quadArea_rotate, ← quadArea_reverse B' C' D' A']
      exact Prop34.bisect hp'.reverse.rotate.rotate.rotate
    /- And the triangle `XA'Z` is a part of the triangle `B'A'D'`. -/
    have hpart : △ X A' Z < △ B' A' D' := by
      rw [area_cba X A' Z]
      refine lt_trans (area_lt_of_cut hZD'.triangle.cab hA'XB') ?_
      rw [area_cba Z A' B']
      exact area_lt_of_cut hCD'.symm.triangle.bac hA'ZD'
    rw [heq, Prop34.bisect hps, hbig]
    exact Magnitude.add_self_lt_add_self hpart
  rcases lt_trichotomy ‖A B‖ ‖A' B'‖ with hlt | heq | hgt
  · exact absurd hsq (Magnitude.ne_of_lt (less h hCD h' hCD' hlt))
  · exact heq
  · exact absurd hsq.symm (Magnitude.ne_of_lt (less h' hCD' h hCD hgt))

end Elements.BookI
