import Elements

/-!
# Staging: Book III without `∃ O, Centre O α`

Brief 0008. The rule `exists_centre` is available, and the early restatements have moved
home. This file keeps the late targets: III.23 onwards and the circumference helpers.
Each statement drops only its existence hypothesis, except that III.34 takes its circle
explicitly and III.33 drops the conclusion's bare existence clause.

Each statement carries `sorry` and two checks: the existing statement gives the new one
when supplied with the rule's content, and the new one gives the existing statement. These
checks establish the interfaces only; they do not prove the staged statements. A statement
whose named centre occurs elsewhere in its geometry keeps that centre.

The names sit in `Elements.BookIII.Staging.Centre`, apart from brief 0006's staged
III.24 and III.25. Each declaration and its checks leave when its restatement moves home.
III.1's entry point, III.13's projection lemmas and Book Zero's `Centre.every` are now in
their home modules.

-/

namespace Elements.BookIII.Staging.Centre

open Tacit

/-! ## The propositions -/

/-- On the same straight line there cannot be constructed two similar and unequal segments of
circles on the same side. -/
theorem Prop23 {A B C D : Point} {ACB ADB : Circle} (hA₁ : OnCircle A ACB)
    (hB₁ : OnCircle B ACB) (hC : OnCircle C ACB) (hA₂ : OnCircle A ADB)
    (hB₂ : OnCircle B ADB) (hD : OnCircle D ADB) (hCD : SameSideOf C D A B)
    (hsim : ∠ A C B = ∠ A D B) :
    ACB = ADB := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop23 :=
  Elements.BookIII.Prop23 (exists_centre _) (exists_centre _)
example : type_of% @Elements.BookIII.Prop23 := fun _ _ => Centre.Prop23

/-- Similar segments of circles on equal straight lines are equal to one another.

III.24's statement before stage 3. Brief 0006 restates III.24 (its stage 3) and keeps
this statement as the companion `Prop24.equalCircles`, against which it is checked here;
the hypotheses `∃ O, Centre O AEB` and `∃ O, Centre O CFD` go from both
(`Brief0006.lean`). -/
theorem Prop24 {A B C D E F : Point} {AEB CFD : Circle} (hA : OnCircle A AEB)
    (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD) (hD : OnCircle D CFD)
    (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E) (hF_CD : ¬ Collinear C D F)
    (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop24 :=
  Elements.BookIII.Prop24.equalCircles (exists_centre _) (exists_centre _)
example : type_of% @Elements.BookIII.Prop24.equalCircles := fun _ _ => Centre.Prop24

/-- Given a segment of a circle, to describe the complete circle of which it is a segment.

III.25's statement before stage 4, still handed the whole circle: dropping its centre does
not give it the segment alone. Brief 0006 restates III.25 (its stage 4) and keeps this
statement as the companion `Prop25.of_circle`, against which it is checked here
(`Brief0006.lean`). -/
theorem Prop25 {A C : Point} {ABC : Circle} (hA : OnCircle A ABC) (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop25 :=
  Elements.BookIII.Prop25.of_circle (exists_centre _)
example : type_of% @Elements.BookIII.Prop25.of_circle := fun _ => Centre.Prop25

/-- To bisect a given circumference. -/
theorem Prop30 {A B : Point} {ADB : Circle} (hA : OnCircle A ADB) (hB : OnCircle B ADB) :
    ∀ P : Point, ¬ Collinear A B P → ∃ D : Point, OnCircle D ADB ∧ SameSideOf D P A B ∧
      standing ADB A B D = standing ADB D A B := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop30 :=
  Elements.BookIII.Prop30 (exists_centre _)
example : type_of% @Elements.BookIII.Prop30 := fun _ => Centre.Prop30

/-- If a straight line touch a circle, and from the point of contact there be drawn across, in
the circle, a straight line cutting the circle, the angles which it makes with the tangent
will be equal to the angles in the alternate segments of the circle. -/
theorem Prop32 {B D E F : Point} {ABCD : Circle} (hB : OnCircle B ABCD)
    (hD : OnCircle D ABCD) (hBD : B ≠ D) (hEF : Touches E F ABCD) (hEBF : Between E B F) :
    (∀ A : Point, OnCircle A ABCD → OppositeSidesOf A F B D → ∠ F B D = ∠ B A D) ∧
    (∀ C : Point, OnCircle C ABCD → SameSideOf C F B D → ∠ E B D = ∠ D C B) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop32 :=
  Elements.BookIII.Prop32 (exists_centre _)
example : type_of% @Elements.BookIII.Prop32 := fun _ => Centre.Prop32

/-- From a given circle to cut off a segment admitting an angle equal to a given rectilineal
angle.

The circle is now explicit: today the hypothesis `∃ O, Centre O ABC` names it, and without
that hypothesis nothing else would. -/
theorem Prop34 {D₁ D D₂ : Point} (ABC : Circle) (hD : Triangle D₁ D D₂) :
    ∃ A B C : Point, OnCircle A ABC ∧ OnCircle B ABC ∧ OnCircle C ABC ∧ Triangle B A C ∧
      ∠ B A C = ∠ D₁ D D₂ := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop34 :=
  fun ABC => Elements.BookIII.Prop34 (exists_centre ABC)
example : type_of% @Elements.BookIII.Prop34 := fun {_ _ _ ABC} _ => Centre.Prop34 ABC

/-- If in a circle two straight lines cut one another, the rectangle contained by the segments
of the one is equal to the rectangle contained by the segments of the other. -/
theorem Prop35 {A B C D E : Point} {ABCD : Circle} (hA : OnCircle A ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hD : OnCircle D ABCD)
    (hAEC : Between A E C) (hBED : Between B E D) :
    rect A E E C = rect D E E B := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop35 :=
  Elements.BookIII.Prop35 (exists_centre _)
example : type_of% @Elements.BookIII.Prop35 := fun _ => Centre.Prop35

/-- If a point be taken outside a circle and from it there fall on the circle two straight
lines, and if one of them cut the circle and the other touch it, the rectangle contained by
the whole of the straight line which cuts the circle and the straight line intercepted on it
outside between the point and the convex circumference will be equal to the square on the
tangent. -/
theorem Prop36 {A B C D : Point} {ABC : Circle} (hD : OutsideCircle D ABC)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hDCA : Between D C A)
    (hDB : Touches D B ABC) :
    rect A D D C = sq D B := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop36 :=
  Elements.BookIII.Prop36 (exists_centre _)
example : type_of% @Elements.BookIII.Prop36 := fun _ => Centre.Prop36

/-- If a point be taken outside a circle and from the point there fall on the circle two
straight lines, if one of them cut the circle, and the other fall on it, and if further the
rectangle contained by the whole of the straight line which cuts the circle and the straight
line intercepted on it outside between the point and the convex circumference be equal to
the square on the straight line which falls on the circle, the straight line which falls on
it will touch the circle. -/
theorem Prop37 {A B C D : Point} {ABC : Circle} (hD : OutsideCircle D ABC)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hDCA : Between D C A)
    (h : rect A D D C = sq D B) :
    Touches D B ABC := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop37 :=
  Elements.BookIII.Prop37 (exists_centre _)
example : type_of% @Elements.BookIII.Prop37 := fun _ => Centre.Prop37

/-! ## A conclusion: III.33's circle, without "with a centre" -/

/-- On a given straight line to describe a segment of a circle admitting an angle equal to a
given rectilineal angle.

Today's conclusion says also that the circle described has a centre, `∃ O, Centre O AEB`, so
that a citer could hand it on to a statement asking for one. Once every circle has a centre
that clause adds nothing, and goes (question 4 of brief 0008, decided at the freeze). -/
theorem Prop33 {A B C₁ C C₂ : Point} (hAB : A ≠ B) (hC : Triangle C₁ C C₂) :
    ∃ (AEB : Circle) (E : Point), OnCircle A AEB ∧ OnCircle B AEB ∧ OnCircle E AEB ∧
      ¬ Collinear A B E ∧ ∠ A E B = ∠ C₁ C C₂ := by
  sorry

/-- Here the directions turn round: today's III.33 gives the new one at once, and the new one
gives today's given the rule. -/
example : type_of% @Centre.Prop33 := fun hAB hC =>
  let ⟨AEB, E, _, h⟩ := Elements.BookIII.Prop33 hAB hC
  ⟨AEB, E, h⟩
example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Elements.BookIII.Prop33 := fun hAB hC =>
  let ⟨AEB, E, h⟩ := Centre.Prop33 hAB hC
  ⟨AEB, E, exists_centre AEB, h⟩

/-! ## Book III's shared steps on circumferences (`Circumferences.lean`) -/

variable {A B C K : Point} {α : Circle}

/-- **A circumference is measured at any point of the other segment.** The circumference
BKC is twice the angle BAC, for every point A of the circle on the other side of BC.
[III. 21] -/
theorem Circumference.eq (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hAK : OppositeSidesOf A K B C) :
    circumference α B K C = ∠ B A C + ∠ B A C := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Centre.Circumference.eq :=
  Elements.BookIII.Circumference.eq (exists_centre _)
example : type_of% @Elements.BookIII.Circumference.eq := fun _ => Centre.Circumference.eq

/-- **The circumference on which an angle stands.** For a point A of the circle off BC, the
circumference on which the angle BAC stands is twice that angle. [III. 21] -/
theorem Circumference.standing (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hBCA : Triangle B C A) :
    standing α B A C = ∠ B A C + ∠ B A C := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Centre.Circumference.standing :=
  Elements.BookIII.Circumference.standing (exists_centre _)
example : type_of% @Elements.BookIII.Circumference.standing :=
  fun _ => Centre.Circumference.standing

/-- **The whole circle.** A straight line BC cuts the circle into two circumferences, one on
each side, and together they are four right angles. [III. 21, III. 22] -/
theorem Circumference.whole (hB : OnCircle B α) (hC : OnCircle C α)
    (hAK : OppositeSidesOf A K B C) :
    circumference α B K C + circumference α B A C = ∟ + ∟ + (∟ + ∟) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Centre.Circumference.whole :=
  Elements.BookIII.Circumference.whole (exists_centre _)
example : type_of% @Elements.BookIII.Circumference.whole := fun _ => Centre.Circumference.whole

end Elements.BookIII.Staging.Centre
