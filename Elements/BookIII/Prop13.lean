import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop20
import Elements.BookI.Prop24
import Elements.BookIII.Prop02
import Elements.BookIII.MixedAngles
import Elements.BookIII.Prop11

/-!
# Book III, Proposition 13

Euclid's text, in Heath's translation: [`heath/III/13.md`](../../heath/III/13.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

After the proof, Definition III.3 is read at the point of contact, as Heath prefers to read
it, and that reading is shown to agree with our reading of the whole circles, for any two
circles: the companions `Prop13.touchesInternally_iff`, `Prop13.touchesExternally_iff` and
`Prop13.circlesTouch_iff`. Two of the steps on the way reach the conclusions of III.11 and
III.12 by another route; they come after III.13, and are not Euclid's proofs.
-/

namespace Elements.BookIII

open Tacit

/-- A circle does not touch a circle at more points than one, whether it touch it internally or
externally. -/
theorem Prop13 {A B C D : Point} {ABDC EBFD ACK : Circle} :
    ((TouchesInternally ABDC EBFD D ∨ TouchesInternally EBFD ABDC D) →
      OnCircle B ABDC → OnCircle B EBFD → B = D) ∧
    (TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC → C = A) := by
  have within : ∀ {α β : Circle}, TouchesInternally α β D → OnCircle B α → OnCircle B β → B = D := by
    intro α β ht hBα hBβ
    -- For, if possible, let the circle ABDC touch the circle EBFD, first internally, at more
    -- points than one, namely D, B.
    refine Classical.byContradiction fun hBD => ?_
    have htB : TouchesInternally α β B := ⟨hBα, hBβ, ht.2.2.1, ht.2.2.2⟩
    -- Let the centre G of the circle ABDC, and the centre H of EBFD, be taken.
    obtain ⟨G, hG⟩ := exists_centre α
    obtain ⟨H, hH⟩ := exists_centre β
    -- Therefore the straight line joined from G to H will fall on B, D. [III. 11]
    have hGHD : Between G H D := Prop11 hG hH ht
    have hGHB : Between G H B := Prop11 hG hH htB
    obtain ⟨L, hG_L, hH_L⟩ := Postulate1 G H (ne_of_between hGHD)
    have hD_L : OnLine D L := on_line_of_between hGHD hG_L hH_L
    have hB_L : OnLine B L := on_line_of_between hGHB hG_L hH_L
    -- Let it so fall, as BGHD.
    have hBGD : Between B G D :=
      between_of_inside_chord hG_L hB_L hD_L (centre_inside hG) hBα ht.1 hBD
    have hBGH : Between B G H := between_cut hBGD hGHD
    -- Then, since the point G is the centre of the circle ABCD,
    -- BG is equal to GD;
    have hBG_GD : ‖B G‖ = ‖G D‖ := (len_symm B G).trans (Definition15 hG hBα ht.1)
    -- therefore BG is greater than HD;
    have hHD_BG : ‖H D‖ < ‖B G‖ := by
      rw [hBG_GD, len_symm H D, len_symm G D]
      exact len_lt_of_between (between_symm hGHD)
    -- therefore BH is much greater than HD.
    have hHD_BH : ‖H D‖ < ‖B H‖ := lt_trans hHD_BG (len_lt_of_between hBGH)
    -- Again, since the point H is the centre of the circle EBFD,
    -- BH is equal to HD;
    have hBH_HD : ‖B H‖ = ‖H D‖ := (len_symm B H).trans (Definition15 hH hBβ ht.2.1)
    -- but it was also proved much greater than it: which is impossible.
    rw [hBH_HD] at hHD_BH
    exact lt_irrefl _ hHD_BH
  -- Therefore a circle does not touch a circle internally at more points than one.
  have hinternal : (TouchesInternally ABDC EBFD D ∨ TouchesInternally EBFD ABDC D) →
      OnCircle B ABDC → OnCircle B EBFD → B = D := by
    intro h hB₁ hB₂
    /- The same argument serves with the circles' names exchanged. -/
    rcases h with h | h
    · exact within h hB₁ hB₂
    · exact within h hB₂ hB₁
  -- I say further that neither does it so touch it externally.
  have hexternal : TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC →
      C = A := by
    intro h hC₁ hC₂
    -- For, if possible, let the circle ACK touch the circle ABDC at more points than one, namely
    -- A, C,
    obtain ⟨hA₁, hA₂, hout⟩ := h
    refine Classical.byContradiction fun hCA => ?_
    -- and let AC be joined.
    obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C (Ne.symm hCA)
    obtain ⟨P, -, hAPC, -⟩ := exists_point_between hA_AC hC_AC (Ne.symm hCA) []
    -- Then, since on the circumference of each of the circles ABDC, ACK two points A, C have
    -- been taken at random, the straight line joining the points will fall within each
    -- circle; [III. 2]
    have hP₂ : InsideCircle P ABDC := Prop2 hA₂ hC₂ P hAPC
    have hP₁ : InsideCircle P ACK := Prop2 hA₁ hC₁ P hAPC
    -- but it fell within the circle ABCD and outside ACK [III. Def. 3]: which is absurd.
    exact hout P hP₁ hP₂
  -- Therefore a circle does not touch a circle externally at more points than one.
  -- And it was proved that neither does it so touch it internally.
  -- Therefore etc.
  -- Q. E. D.
  exact ⟨hinternal, hexternal⟩

/-- **III.13 for circles touching within**, with only the two circles it speaks of: circles
touching within, either inside the other, have no common point but the point of contact.
A lemma beside III.13, its first clause alone; it rests on whatever III.13 rests on.
Without it, a citer of that clause names III.13's third circle, which the clause never
mentions. -/
theorem Prop13.internally {B D : Point} {α β : Circle}
    (h : TouchesInternally α β D ∨ TouchesInternally β α D) (hBα : OnCircle B α)
    (hBβ : OnCircle B β) : B = D :=
  (Prop13 (A := D) (C := D) (ACK := α)).1 h hBα hBβ

/-- **III.13 for circles touching without**, with only the two circles it speaks of: they
have no common point but the point of contact. A lemma beside III.13, its second clause
alone; it rests on whatever III.13 rests on. -/
theorem Prop13.externally {A C : Point} {α β : Circle} (h : TouchesExternally α β A)
    (hCα : OnCircle C α) (hCβ : OnCircle C β) : C = A :=
  (Prop13 (B := A) (D := A) (EBFD := β)).2 h hCα hCβ

/-! ## Definition III.3 read at the point of contact, after III.13

Euclid's Definition III.3 reads "Circles are said to touch one another which, meeting one
another, do not cut one another". Heath reports two readings of it (vol. 2, p. 3): that the
circles do not cut near the point of contact, or that they do not cut at all, and "Todhunter
thinks the latter opinion correct". Heath himself prefers to read it "as meaning simply that
the circles meet at a point but do not cut *at that point*". Our Lean reads it of the whole
circles (`TouchesInternally`, `TouchesExternally`, `CirclesTouch` in
`Elements/Foundations/DefinitionsIII.lean`), and so carries in the definition what Heath
says Euclid "does practically assume" in III.11 to III.13: that "circles touching at one
point do not intersect anywhere else".

Heath's reading, said at the point, is defined beside them. "Near C" is said with a circle
about C, as Euclid would draw it, and with no numbers (`Touching.Near`), as the mixed angles
of `Elements/Foundations/DefinitionsIII.lean` say "near the vertex". Touching within at C
(`TouchesInternallyAt`): the circles meet at C, they are two circles, and near C no point of
the inner circle falls outside the outer. Touching without at C (`TouchesExternallyAt`): they
meet at C, and near C no point is within both. Each is the whole-circle definition with
"every point" narrowed to "every point near C", save one clause: where `TouchesInternally`
asks for a point of the inner circle within the outer (brief 0008, section 7), contact within
at C asks that the circles be two, and the agreement below shows that the readings still say
the same. Nothing new is assumed, and no axiom is added.

Then the agreement: since every circle has a centre (`Tacit.exists_centre`), the reading at
the point and the reading of the whole circles say the same (`Prop13.touchesInternally_iff`,
`Prop13.touchesExternally_iff`, `Prop13.circlesTouch_iff`). That the whole-circle reading
gives the local one is immediate. The other way is the content, and it goes through the
straight line joining the centres. Were
the point of contact C off that straight line, a small circle about C would cut the inner
circle at a point on the far side of the radius GC from the outer centre F, and the angle at
G would put that point farther from F than C is [I. 24], as III.7 compares straight lines
from a point to a circle; without, the point on the near side would be within the other
circle, and a point of the chord joining it to C [III. 2] within both. Were C on that
straight line on the wrong side, I.20, or a point of a radius near C, would do the same.
So C lies on the straight line through the centres, beyond the inner centre within
(`TouchesInternallyAt.between`) and between the centres without
(`TouchesExternallyAt.between`); and from there I.20 and Definition I.15 give the whole
circles. The proofs use Book I, III.2 and System E's diagram and construction rules,
Intersections 8 and 9 among the latter, with the rule that every circle has a centre, and
nothing that rests on Circle 2 or Circle 3.

These two lemmas reach the conclusions of III.11 and III.12 by a route that is not
Euclid's. They come after III.13, and they are not meant to replace his proofs: the
statements of III.11 to III.13 keep the whole-circle reading.
-/

/-! ### Small facts the agreement needs

Five others are proved elsewhere, and are cited from there: `exists_circle_about` and
`onLine_of_collinear`, in `Elements/Figure/Regions.lean`, and `foot_nearest`,
`len_lt_of_add_lt` and `surrounds_sameSideOf`, in `Elements/BookIII/MixedAngles.lean`;
`onLine_of_collinear` and `foot_nearest` through `surrounds_sameSideOf`, which cites them. -/

/-- A point outside a circle is farther from the centre than the circumference: were it
nearer, it would be within; at the same distance, on it (System E, Diagram-segment 3
and 4). -/
theorem Touching.len_lt_of_outside {F C P : Point} {α : Circle} (hF : Centre F α)
    (hC : OnCircle C α) (hP : OutsideCircle P α) : ‖F C‖ < ‖F P‖ := by
  rcases lt_trichotomy ‖F P‖ ‖F C‖ with h | h | h
  · exact absurd (inside_of_len_lt hF hC h) hP.1
  · exact absurd (on_circle_of_len_eq hF hC h) hP.2
  · exact h

/-- **Near a point off a straight line, every point is on its side.** If C is off the
straight line GF, there is a point N other than C such that every point nearer C than N is
on C's side of GF. This is `surrounds_sameSideOf` (`Elements/BookIII/MixedAngles.lean`),
said with a distance in place of a circle, and it is cited from there: C is on its own side
of GF (System E, Same side 1), so every point within the circle about C through the foot of
the perpendicular from C to GF is on that side; N is a point of that circle (System E,
Points 7), and a point nearer C than N is within it (System E, Diagram-segment 4). -/
theorem Touching.sameSide_of_near {C F G : Point} (hGFC : Triangle G F C) :
    ∃ N : Point, N ≠ C ∧ ∀ X : Point, ‖C X‖ < ‖C N‖ → SameSideOf X C G F := by
  have hCC : SameSideOf C C G F := by
    obtain ⟨L, hG_L, hF_L⟩ := Postulate1 G F hGFC.ne₁₂
    exact SameSideOf.of_line hGFC.ne₁₂ hG_L hF_L (same_side_refl (hGFC.off_line hG_L hF_L))
  obtain ⟨δ, hδ, hall⟩ := surrounds_sameSideOf hCC
  obtain ⟨N, hN, -⟩ := exists_point_on_circle δ []
  exact ⟨N, ne_of_centre_of_on hδ hN, fun X hX => hall X (inside_of_len_lt hδ hN hX)⟩

/-- **A small circle about the point of contact.** Within any circle `γ` about a point C of
the circle `β`, with G its centre, which every circle has (`Tacit.exists_centre`), a circle
`δ` about C can be drawn that cuts `β`, and whose
points are all within `γ` and nearer C than a given point N. Its radius is CA, for a point A
of CG taken near C (`exists_between_nearer`, twice). A is within `β`, being between its
centre and C, and C, the centre of `δ`, is within `δ` and on `β`; so the circles cut
(System E, Intersection 5). -/
theorem Touching.small {β γ : Circle} {C N : Point} (hC : OnCircle C β)
    (hγ : Centre C γ) (hCN : C ≠ N) :
    ∃ δ : Circle, Centre C δ ∧ CirclesMeet δ β ∧
      ∀ X : Point, OnCircle X δ → InsideCircle X γ ∧ ‖C X‖ < ‖C N‖ := by
  obtain ⟨G, hG⟩ := exists_centre β
  obtain ⟨K, hK, -⟩ := exists_point_on_circle γ []
  have hCK : C ≠ K := (ne_of_centre_of_on hγ hK).symm
  have hCG : C ≠ G := ne_of_centre_of_on hG hC
  obtain ⟨A₁, hCA₁G, hA₁⟩ := exists_between_nearer (O := C) (P := C) (Q := G) (C := K) hCG
    (Or.inl rfl) (by rw [len_self]; exact len_pos hCK)
  obtain ⟨A, hCAA₁, hA⟩ := exists_between_nearer (O := C) (P := C) (Q := A₁) (C := N)
    (ne_of_between hCA₁G) (Or.inl rfl) (by rw [len_self]; exact len_pos hCN)
  have hCAG : Between C A G := between_of_between_left hCA₁G hCAA₁
  obtain ⟨δ, hδ, hAδ⟩ := Postulate3 C A (ne_of_between hCAG)
  have hAβ : InsideCircle A β := InsideCircle.of_between_centre hG hC (between_symm hCAG)
  refine ⟨δ, hδ, circles_meet hAδ (centre_inside hδ) hAβ hC, fun X hX => ?_⟩
  have hCX : ‖C X‖ = ‖C A‖ := Definition15 hδ hX hAδ
  refine ⟨inside_of_len_lt hγ hK ?_, ?_⟩
  · rw [hCX]; exact lt_trans (len_lt_of_between hCAA₁) hA₁
  · rw [hCX]; exact hA

/-! ### From the point to the straight line through the centres -/

/-- **Contact within at a point puts it on the straight line through the centres, beyond the
inner centre.** If `α`, with centre F, and `β`, with centre G, touch within at C, `β` within
`α`, then G lies between F and C.

Were it not so, we find a point X of `β`, as near C as we please, farther from F than C is,
and so outside `α`. Off the straight line FG, a small circle about C cuts `β` on the far side
of GC from F, and near enough to C to be on C's side of GF (`Touching.small`,
`Touching.sameSide_of_near`); then GC falls within the angle FGX, and the greater angle at G
gives the greater base [I. 24], GX and GC being radii. This is III.7's comparison, made at
the centre. On the straight line FG, with F between G and C, or C between the centres, any
point of the small circle's crossing off FG will do [I. 20].

The conclusion is III.11's, reached by another route. -/
theorem TouchesInternallyAt.between {α β : Circle} {C F G : Point} (hF : Centre F α)
    (hG : Centre G β) (h : TouchesInternallyAt α β C) : Between F G C := by
  obtain ⟨hCα, hCβ, hαβ, γ, hγ, hnear⟩ := h
  /- F and G are two points: about one centre, two circles through C would be one circle
     (System E, Diagram-segment 2). -/
  have hFG : F ≠ G := by
    rintro rfl
    exact hαβ (circle_eq hF hG hCα hCβ rfl)
  have hFC : F ≠ C := (ne_of_centre_of_on hF hCα).symm
  have hGC : G ≠ C := (ne_of_centre_of_on hG hCβ).symm
  refine Classical.byContradiction fun hFGC => ?_
  /- It is enough to find a point of `β` near C farther from F than C is: it is outside `α`,
     and the contact at C forbids it. -/
  suffices hX : ∃ X : Point, OnCircle X β ∧ InsideCircle X γ ∧ ‖F C‖ < ‖F X‖ by
    obtain ⟨X, hXβ, hXγ, hlt⟩ := hX
    exact hnear X hXγ hXβ (outside_of_len_gt hF hCα hlt)
  obtain ⟨L, hF_L, hG_L⟩ := Postulate1 F G hFG
  by_cases hC_L : OnLine C L
  · /- C on the straight line FG, but not beyond G. A small circle about C cuts `β` off FG,
       at X; GX is equal to GC. -/
    obtain ⟨δ, hδ, hmeet, hsmall⟩ := Touching.small (N := G) hCβ hγ hGC.symm
    obtain ⟨B, hB, -⟩ := exists_off_line hFG []
    obtain ⟨X, hXδ, hXβ, hXB⟩ :=
      circles_meet_same_side hmeet hδ hG hC_L hG_L (hB.off_line hF_L hG_L)
    have hFGX : Triangle F G X := Triangle.of_line hF_L hG_L hFG (not_on_line_of_same_side hXB)
    have hGX : ‖G X‖ = ‖G C‖ := Definition15 hG hXβ hCβ
    refine ⟨X, hXβ, (hsmall X hXδ).1, ?_⟩
    rcases between_cases hFG hGC hFC hF_L hG_L hC_L with h | h | h
    · exact absurd h hFGC
    · /- F between G and C: GF, FC make GC, that is GX, which is less than GF, FX
         [I. 20]. -/
      have h20 : ‖G X‖ < ‖G F‖ + ‖F X‖ := (BookI.Prop20 hFGX).1
      rw [hGX, ← len_add_of_between h] at h20
      exact Magnitude.lt_of_add_lt_add_left h20
    · /- C between the centres: FC, CG make FG, which is less than FX, XG [I. 20], and XG
         is CG. -/
      have h20 : ‖F G‖ < ‖F X‖ + ‖X G‖ := (BookI.Prop20 hFGX.cab).1
      rw [← len_add_of_between h, len_symm X G, hGX, len_symm G C] at h20
      exact Magnitude.lt_of_add_lt_add_right h20
  · /- C off the straight line FG. -/
    have hGFC : Triangle G F C := Triangle.of_line hG_L hF_L hFG.symm hC_L
    obtain ⟨N, hNC, hside⟩ := Touching.sameSide_of_near hGFC
    obtain ⟨δ, hδ, hmeet, hsmall⟩ := Touching.small hCβ hγ hNC.symm
    obtain ⟨M, hC_M, hG_M⟩ := Postulate1 C G hGC.symm
    have hF_M : ¬ OnLine F M := fun hF_M =>
      hC_L (line_unique hFG hF_M hG_M hF_L hG_L ▸ hC_M)
    /- The small circle cuts `β` at X, on the far side of GC from F (System E,
       Intersections 9), and on C's side of GF. -/
    obtain ⟨X, hXδ, hXβ, hXF⟩ := circles_meet_opposite_side hmeet hδ hG hC_M hG_M hF_M
    have hXγ : InsideCircle X γ := (hsmall X hXδ).1
    have hXC : SameSideOf X C G F := hside X (hsmall X hXδ).2
    have hX_M : ¬ OnLine X M := hXF.1
    have hGX : G ≠ X := fun e => hX_M (e ▸ hG_M)
    obtain ⟨N', hG_N', hX_N'⟩ := Postulate1 G X hGX
    /- So GC falls within the angle FGX (System E, Triple incidence 2), and the angle FGX
       is made up of FGC and CGX. -/
    have hFC_N' : SameSide F C N' :=
      triple_incidence2 hG_L hG_M hG_N' hF_L hC_M hX_N' (hXC.symm.sameSide hG_L hF_L)
        (fun hs => hXF.2.2 (same_side_symm hs)) hX_M hFG
    have hadd : ∠ F G X = ∠ F G C + ∠ C G X :=
      angle_add_of_within hXC.symm (SameSideOf.of_line hGX hG_N' hX_N' (same_side_symm hFC_N'))
    have hCGX : Triangle C G X := Triangle.of_line hC_M hG_M hGC.symm hX_M
    have hlt : ∠ F G C < ∠ F G X := by
      rw [hadd]; exact CommonNotion5 hCGX.angle_pos
    /- GF is common and GX equal to GC, so the greater angle at G stands on the greater
       base [I. 24]. -/
    exact ⟨X, hXβ, hXγ,
      BookI.Prop24 hXC.triangle hGFC rfl (Definition15 hG hXβ hCβ) hlt⟩

/-- **Contact without at a point puts it between the centres.** If `α`, with centre F, and
`β`, with centre G, touch without at C, then C lies between F and G.

Were it not so, we find a point within both circles, as near C as we please. With one centre,
or with the centres on one side of C on a straight line through it, a point between C and
the nearer centre will do. Off the straight line FG, a small circle about C cuts `β` at X on
F's side of GC, and near enough to C to be on C's side of GF (`Touching.small`,
`Touching.sameSide_of_near`); then GX falls within the angle FGC, and the less angle at G
gives the less base [I. 24], so X is within `α`. A point of the chord CX of `β` near C is
then within `β` [III. 2], within `α` (III.2 for points on or within the circle), and near C.

The conclusion is III.12's, reached by another route. -/
theorem TouchesExternallyAt.between {α β : Circle} {C F G : Point} (hF : Centre F α)
    (hG : Centre G β) (h : TouchesExternallyAt α β C) : Between F C G := by
  obtain ⟨hCα, hCβ, γ, hγ, hnear⟩ := h
  have hFC : F ≠ C := (ne_of_centre_of_on hF hCα).symm
  have hGC : G ≠ C := (ne_of_centre_of_on hG hCβ).symm
  obtain ⟨K, hK, -⟩ := exists_point_on_circle γ []
  have hCK : C ≠ K := (ne_of_centre_of_on hγ hK).symm
  refine Classical.byContradiction fun hFCG => ?_
  /- It is enough to find a point near C within both circles. -/
  suffices hP : ∃ P : Point, InsideCircle P γ ∧ InsideCircle P α ∧ InsideCircle P β by
    obtain ⟨P, hPγ, hPα, hPβ⟩ := hP
    exact hnear P hPγ hPα hPβ
  /- A point M that is a centre, or lies between C and it, for each circle: a point of CM
     near C is within `γ`, and within each circle, between its centre and C. -/
  have seg : ∀ M : Point, M ≠ C → (M = F ∨ Between C M F) → (M = G ∨ Between C M G) →
      ∃ P : Point, InsideCircle P γ ∧ InsideCircle P α ∧ InsideCircle P β := by
    intro M hMC hMF hMG
    obtain ⟨P, hCPM, hP⟩ := exists_between_nearer (O := C) (P := C) (Q := M) (C := K)
      hMC.symm (Or.inl rfl) (by rw [len_self]; exact len_pos hCK)
    have hin : ∀ {O : Point} {ε : Circle}, Centre O ε → OnCircle C ε →
        (M = O ∨ Between C M O) → InsideCircle P ε := by
      intro O ε hO hCε hMO
      refine InsideCircle.of_between_centre hO hCε (between_symm ?_)
      rcases hMO with e | hCMO
      · exact e ▸ hCPM
      · exact between_of_between_left hCMO hCPM
    exact ⟨P, inside_of_len_lt hγ hK hP, hin hF hCα hMF, hin hG hCβ hMG⟩
  by_cases hFG : F = G
  · /- One centre: a point of its radius near C is within both. -/
    exact seg F hFC (Or.inl rfl) (Or.inl hFG)
  obtain ⟨L, hF_L, hG_L⟩ := Postulate1 F G hFG
  by_cases hC_L : OnLine C L
  · /- C on the straight line FG, not between the centres: the nearer centre lies between
       C and the other. -/
    rcases between_cases hFG hGC hFC hF_L hG_L hC_L with h | h | h
    · exact seg G hGC (Or.inr (between_symm h)) (Or.inl rfl)
    · exact seg F hFC (Or.inl rfl) (Or.inr (between_symm h))
    · exact absurd h hFCG
  /- C off the straight line FG. -/
  have hGFC : Triangle G F C := Triangle.of_line hG_L hF_L (Ne.symm hFG) hC_L
  obtain ⟨N, hNC, hside⟩ := Touching.sameSide_of_near hGFC
  obtain ⟨δ, hδ, hmeet, hsmall⟩ := Touching.small hCβ hγ hNC.symm
  obtain ⟨M, hC_M, hG_M⟩ := Postulate1 C G hGC.symm
  have hF_M : ¬ OnLine F M := fun hF_M =>
    hC_L (line_unique hFG hF_M hG_M hF_L hG_L ▸ hC_M)
  /- The small circle cuts `β` at X, on F's side of GC (System E, Intersections 8), and on
     C's side of GF. -/
  obtain ⟨X, hXδ, hXβ, hXF⟩ := circles_meet_same_side hmeet hδ hG hC_M hG_M hF_M
  have hXγ : InsideCircle X γ := (hsmall X hXδ).1
  have hXC : SameSideOf X C G F := hside X (hsmall X hXδ).2
  have hXF' : SameSideOf X F G C := SameSideOf.of_line hGC hG_M hC_M hXF
  /- So GX falls within the angle FGC, which is made up of FGX and XGC. -/
  have hadd : ∠ F G C = ∠ F G X + ∠ X G C := angle_add_of_within hXC hXF'
  have hlt : ∠ F G X < ∠ F G C := by
    rw [hadd]; exact CommonNotion5 hXF'.triangle.cab.angle_pos
  /- GF is common and GX equal to GC, so the less angle at G stands on the less base
     [I. 24]: X is within `α`. -/
  have hFX : ‖F X‖ < ‖F C‖ :=
    BookI.Prop24 hGFC hXC.triangle rfl (Definition15 hG hCβ hXβ) hlt
  have hXα : InsideCircle X α := inside_of_len_lt hF hCα hFX
  /- A point P of the chord CX: within `γ`, as X is; within `β` [III. 2]; and within `α`,
     between C on it and X within it (III.2, for points on or within the circle). -/
  have hCX : C ≠ X := (ne_of_centre_of_on hδ hXδ).symm
  obtain ⟨T, hC_T, hX_T⟩ := Postulate1 C X hCX
  obtain ⟨P, -, hCPX, -⟩ := exists_point_between hC_T hX_T hCX []
  exact ⟨P, InsideCircle.of_between_centre_of_inside hγ hK hXγ hCPX,
    Prop2.within (Or.inr hCα) (Or.inl hXα) hCPX, Prop2 hCβ hXβ P hCPX⟩

/-! ### From the straight line through the centres to the whole circles -/

/-- **Contact within, from the line of the centres.** If the centre G of `β` lies between the
centre F of `α` and a common point C, no point P of `β` is outside `α`: FP is not greater than
FG, GP together [I. 20], and these are FG, GC (Definition I.15), which make FC. And a point
X of `β` off the straight line FG, where a straight line through G meets `β` (System E,
Intersections 5), is within `α`: FX is less than FG, GX together [I. 20], which are FG, GC
again. -/
theorem Touching.internally_of_between {α β : Circle} {C F G : Point} (hF : Centre F α)
    (hG : Centre G β) (hCα : OnCircle C α) (hCβ : OnCircle C β) (h : Between F G C) :
    TouchesInternally α β C := by
  refine ⟨hCα, hCβ, ?_, fun P hP hout => ?_⟩
  · /- The straight line from G to a point B off FG meets `β` at X, off FG (System E,
       Intersections 5); FX is less than FG, GX [I. 20], that is FG, GC, which make FC. -/
    have hFG : F ≠ G := ne_of_between h
    obtain ⟨L, hF_L, hG_L⟩ := Postulate1 F G hFG
    obtain ⟨B, hB, -⟩ := exists_off_line hFG []
    have hB_L : ¬ OnLine B L := hB.off_line hF_L hG_L
    have hGB : G ≠ B := fun e => hB_L (e ▸ hG_L)
    obtain ⟨M, hG_M, hB_M⟩ := Postulate1 G B hGB
    obtain ⟨X, hXβ, hX_M, -⟩ := line_circle_beyond (centre_inside hG) hG_M hB_M hGB.symm
    have hX_L : ¬ OnLine X L := fun hX_L =>
      hB_L (line_unique (ne_of_centre_of_on hG hXβ) hX_M hG_M hX_L hG_L ▸ hB_M)
    have h20 : ‖F X‖ < ‖F G‖ + ‖G X‖ :=
      (BookI.Prop20 (Triangle.of_line hF_L hG_L hFG hX_L).bac).1
    rw [Definition15 hG hXβ hCβ, len_add_of_between h] at h20
    exact ⟨X, hXβ, inside_of_len_lt hF hCα h20⟩
  have hlt : ‖F G‖ + ‖G P‖ < ‖F P‖ := by
    rw [Definition15 hG hP hCβ, len_add_of_between h]
    exact Touching.len_lt_of_outside hF hCα hout
  exact lt_irrefl _ (len_lt_of_add_lt hlt)

/-- **Contact without, from the line of the centres.** If a common point C lies between the
centres F and G, no point P is within both circles: FP, PG together would be less than FC,
CG, which make FG, and so FG less than itself [I. 20]. -/
theorem Touching.externally_of_between {α β : Circle} {C F G : Point} (hF : Centre F α)
    (hG : Centre G β) (hCα : OnCircle C α) (hCβ : OnCircle C β) (h : Between F C G) :
    TouchesExternally α β C := by
  refine ⟨hCα, hCβ, fun P hPα hPβ => ?_⟩
  have h₁ : ‖F P‖ < ‖F C‖ := len_lt_of_inside hF hCα hPα
  have h₂ : ‖P G‖ < ‖C G‖ := by
    rw [len_symm P G, len_symm C G]; exact len_lt_of_inside hG hCβ hPβ
  have hlt : ‖F P‖ + ‖P G‖ < ‖F G‖ := by
    rw [← len_add_of_between h]
    refine lt_trans (add_lt_add_right _ h₁) ?_
    rw [add_comm ‖F C‖, add_comm ‖F C‖]
    exact add_lt_add_right _ h₂
  exact lt_irrefl _ (len_lt_of_add_lt hlt)

/-! ### The agreement, in the form Book III uses

Every circle has a centre (`Tacit.exists_centre`), and Book III states its propositions
without one where the setting-out does not name it (III.2). So the two readings are one for
every circle, and every statement of Book III that speaks of circles touching may be read
either way. -/

/-- **The two readings of contact within agree**, for any two circles. -/
theorem Prop13.touchesInternally_iff {α β : Circle} {C : Point} :
    TouchesInternally α β C ↔ TouchesInternallyAt α β C := by
  constructor
  · /- From the whole circles to the point: what holds of every point of `β` holds of those
       near C, and the circles are two, for the point Q of `β` within `α` is not on `α`
       (System E, Generalities 4). -/
    intro h
    obtain ⟨hCα, hCβ, ⟨Q, hQβ, hQα⟩, hall⟩ := h
    have hαβ : α ≠ β := fun e => inside_not_on hQα (e ▸ hQβ)
    obtain ⟨γ, hγ⟩ := exists_circle_about C
    exact ⟨hCα, hCβ, hαβ, γ, hγ, fun P _ => hall P⟩
  · /- From the point to the whole circles, the centres taken by the rule that every circle
       has one: the point lies on the straight line through the centres, beyond the inner
       centre, and then no point of the inner circle is outside the outer, and some point
       of it is within. -/
    intro h
    obtain ⟨F, hF⟩ := exists_centre α
    obtain ⟨G, hG⟩ := exists_centre β
    exact Touching.internally_of_between hF hG h.1 h.2.1 (TouchesInternallyAt.between hF hG h)

/-- **The two readings of contact without agree**, for any two circles. -/
theorem Prop13.touchesExternally_iff {α β : Circle} {C : Point} :
    TouchesExternally α β C ↔ TouchesExternallyAt α β C := by
  constructor
  · /- From the whole circles to the point: what holds of every point holds of those near
       C. -/
    intro h
    obtain ⟨hCα, hCβ, hall⟩ := h
    obtain ⟨γ, hγ⟩ := exists_circle_about C
    exact ⟨hCα, hCβ, γ, hγ, fun P _ => hall P⟩
  · /- From the point to the whole circles, the centres taken by the rule: the point lies
       between the centres, and then no point is within both. -/
    intro h
    obtain ⟨F, hF⟩ := exists_centre α
    obtain ⟨G, hG⟩ := exists_centre β
    exact Touching.externally_of_between hF hG h.1 h.2.1 (TouchesExternallyAt.between hF hG h)

/-- **The two readings of Definition III.3 agree**, for any two circles: the circles touch at
C, read of the whole circles, exactly when they touch at C, read at the point. -/
theorem Prop13.circlesTouch_iff {α β : Circle} {C : Point} :
    CirclesTouch α β C ↔ CirclesTouchAt α β C := by
  have h₁ := Prop13.touchesInternally_iff (α := α) (β := β) (C := C)
  have h₂ := Prop13.touchesInternally_iff (α := β) (β := α) (C := C)
  have h₃ := Prop13.touchesExternally_iff (α := α) (β := β) (C := C)
  exact or_congr h₁ (or_congr h₂ h₃)

/-! ### Each way of the agreement

Each way of each agreement, as a theorem of its own. Each is cited from the agreement, which
proves it. -/

/-- Contact within, read of the whole circles, is contact within at the point: what holds of
every point of `β` holds of those near C. -/
theorem TouchesInternallyAt.of_whole {α β : Circle} {C : Point}
    (h : TouchesInternally α β C) : TouchesInternallyAt α β C :=
  Prop13.touchesInternally_iff.mp h

/-- Contact without, read of the whole circles, is contact without at the point. -/
theorem TouchesExternallyAt.of_whole {α β : Circle} {C : Point}
    (h : TouchesExternally α β C) : TouchesExternallyAt α β C :=
  Prop13.touchesExternally_iff.mp h

/-- **Contact within at a point is contact within of the whole circles**, the centres taken
by the rule that every circle has one (`Tacit.exists_centre`): the point lies on the straight
line through the centres, beyond the inner centre (`TouchesInternallyAt.between`), and then no
point of the inner circle is outside the outer, and some point of it is within
(`Touching.internally_of_between`). This is what Heath says Euclid "does practically assume"
in III.11 to III.13, proved. -/
theorem TouchesInternallyAt.whole {α β : Circle} {C : Point} (h : TouchesInternallyAt α β C) :
    TouchesInternally α β C :=
  Prop13.touchesInternally_iff.mpr h

/-- **Contact without at a point is contact without of the whole circles**, the centres taken
by the rule that every circle has one (`Tacit.exists_centre`): the point lies between the
centres (`TouchesExternallyAt.between`), and then no point is within both
(`Touching.externally_of_between`). -/
theorem TouchesExternallyAt.whole {α β : Circle} {C : Point} (h : TouchesExternallyAt α β C) :
    TouchesExternally α β C :=
  Prop13.touchesExternally_iff.mpr h

end Elements.BookIII
