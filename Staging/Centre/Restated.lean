import Elements.Figure.Circles
import Elements.Figure.CirclePoints
import Elements

/-!
# Staging: Book III without `∃ O, Centre O α`

Brief 0008. Once every circle has a centre (the rule `exists_centre`, which the owner
approved and which lands only in the coordinator's own pull request), a hypothesis that
only says that a circle has some centre says nothing. Each statement below is today's with
that hypothesis dropped, and nothing else changed, except that III.34 takes its circle
explicitly, since nothing else would name it. III.1 is in `Prop01.lean` beside this file.

Each statement carries `sorry` and two checks (checked by Lean):

* given the rule's content, taken as a hypothesis named `exists_centre`, today's statement
  gives the new one: so each new statement is provable once the rule lands, by today's
  proof with the centre taken from the rule;
* the new statement gives today's, which asks for more.

So, given the rule, each new statement says exactly what today's says. A statement that
names its centre and uses it (III.3, III.7, III.14 and nine more) is not here: it keeps
`Centre E α`, and does not change.

Three new lemmas for Lean users, approved at the freeze (question 11), are proved here:
III.13's two clauses, each with only the two circles it speaks of (`Prop13.internally`,
`Prop13.externally`), and `Centre.every`, which turns a fact about a named centre into the
condition said of every centre that III.4 and III.8 ask for. The names sit in
`Elements.BookIII.Staging.Centre` and `Elements.Staging.Centre`, apart from brief 0006's
staged III.24 and III.25. When the restated statements are proved they replace today's, and
this file is deleted.
-/

namespace Elements.BookIII.Staging.Centre

open Tacit

/-! ## The propositions -/

/-- If on the circumference of a circle two points be taken at random, the straight line joining
the points will fall within the circle. -/
theorem Prop2 {A B : Point} {ABC : Circle} (hA : OnCircle A ABC) (hB : OnCircle B ABC) :
    ∀ E : Point, Between A E B → InsideCircle E ABC := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop2 :=
  Elements.BookIII.Prop2 (exists_centre _)
example : type_of% @Elements.BookIII.Prop2 := fun _ => Centre.Prop2

/-- If in a circle two straight lines cut one another which are not through the centre, they do
not bisect one another. -/
theorem Prop4 {A B C D E : Point} {ABCD : Circle} (hA : OnCircle A ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hD : OnCircle D ABCD)
    (hAEC : Between A E C) (hBED : Between B E D) (hB_AC : ¬ Collinear A C B)
    (hAC : ∀ F : Point, Centre F ABCD → ¬ Collinear A C F)
    (hBD : ∀ F : Point, Centre F ABCD → ¬ Collinear B D F) :
    ¬ (‖A E‖ = ‖E C‖ ∧ ‖B E‖ = ‖E D‖) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop4 :=
  Elements.BookIII.Prop4 (exists_centre _)
example : type_of% @Elements.BookIII.Prop4 := fun _ => Centre.Prop4

/-- If a point be taken outside a circle and from the point straight lines be drawn through to
the circle, one of which is through the centre and the others are drawn at random, then, of
the straight lines which fall on the concave circumference, that through the centre is
greatest, while of the rest the nearer to that through the centre is always greater than the
more remote, but, of the straight lines falling on the convex circumference, that between the
point and the diameter is least, while of the rest the nearer to the least is always less
than the more remote, and only two equal straight lines will fall on the circle from the
point, one on each side of the least. -/
theorem Prop8 {A D G : Point} {ABC : Circle} (hD : OutsideCircle D ABC) (hA : OnCircle A ABC)
    (hG : OnCircle G ABC) (hDGA : Between D G A)
    (hGA : ∀ M : Point, Centre M ABC → Between G M A) :
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
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop8 :=
  Elements.BookIII.Prop8 (exists_centre _)
example : type_of% @Elements.BookIII.Prop8 := fun _ => Centre.Prop8

/-- If a point be taken within a circle, and more than two equal straight lines fall from the
point on the circle, the point taken is the centre of the circle. -/
theorem Prop9 {A B C D : Point} {ABC : Circle} (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hDA : ‖D A‖ = ‖D B‖) (hDB : ‖D B‖ = ‖D C‖) :
    Centre D ABC := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop9 :=
  Elements.BookIII.Prop9 (exists_centre _)
example : type_of% @Elements.BookIII.Prop9 := fun _ => Centre.Prop9

/-- A circle does not cut a circle at more points than two. -/
theorem Prop10 {B G H : Point} {ABC DEF : Circle} (hB₁ : OnCircle B ABC)
    (hB₂ : OnCircle B DEF) (hG₁ : OnCircle G ABC) (hG₂ : OnCircle G DEF)
    (hH₁ : OnCircle H ABC) (hH₂ : OnCircle H DEF) (hBG : B ≠ G) (hBH : B ≠ H)
    (hGH : G ≠ H) :
    ABC = DEF := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop10 :=
  Elements.BookIII.Prop10 (exists_centre _) (exists_centre _)
example : type_of% @Elements.BookIII.Prop10 := fun _ _ => Centre.Prop10

/-- A circle does not touch a circle at more points than one, whether it touch it internally or
externally. -/
theorem Prop13 {A B C D : Point} {ABDC EBFD ACK : Circle} :
    ((TouchesInternally ABDC EBFD D ∨ TouchesInternally EBFD ABDC D) →
      OnCircle B ABDC → OnCircle B EBFD → B = D) ∧
    (TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC → C = A) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop13 :=
  Elements.BookIII.Prop13 (exists_centre _) (exists_centre _) (exists_centre _)
example : type_of% @Elements.BookIII.Prop13 := fun _ _ _ => Centre.Prop13

/-- **III.13 for circles touching within**, with only the two circles it speaks of: circles
touching within, either inside the other, have no common point but the point of contact. A
lemma beside III.13, its first clause alone; it rests on whatever III.13 rests on. Without
it, a citer of that clause names III.13's third circle, which the clause never mentions. -/
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

/-- The check that the two lemmas give III.13 back (checked by Lean). -/
example : type_of% @Centre.Prop13 := fun {_ _ _ _ _ _ _} =>
  ⟨fun h hB₁ hB₂ => Prop13.internally h hB₁ hB₂, fun h hC₁ hC₂ => Prop13.externally h hC₁ hC₂⟩

/-- From a given point to draw a straight line touching a given circle. -/
theorem Prop17 {A : Point} {BCD : Circle} (hA : OutsideCircle A BCD) :
    ∃ B : Point, OnCircle B BCD ∧ Touches A B BCD := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop17 :=
  Elements.BookIII.Prop17 (exists_centre _)
example : type_of% @Elements.BookIII.Prop17 := fun _ => Centre.Prop17

/-- In a circle the angles in the same segment are equal to one another. -/
theorem Prop21 {A B D E : Point} {ABCD : Circle} (hA : OnCircle A ABCD)
    (hB : OnCircle B ABCD) (hD : OnCircle D ABCD) (hE : OnCircle E ABCD)
    (hAE : SameSideOf A E B D) :
    ∠ B A D = ∠ B E D := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop21 :=
  Elements.BookIII.Prop21 (exists_centre _)
example : type_of% @Elements.BookIII.Prop21 := fun _ => Centre.Prop21

/-- The opposite angles of quadrilaterals in circles are equal to two right angles. -/
theorem Prop22 {A B C D : Point} {ABCD : Circle} (hA : OnCircle A ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hD : OnCircle D ABCD)
    (hAC : OppositeSidesOf A C B D) :
    ∠ A B C + ∠ A D C = ∟ + ∟ ∧ ∠ B A D + ∠ D C B = ∟ + ∟ := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop22 :=
  Elements.BookIII.Prop22 (exists_centre _)
example : type_of% @Elements.BookIII.Prop22 := fun _ => Centre.Prop22

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

Today's statement of III.25, still handed the whole circle: dropping its centre does not
give it the segment alone. Brief 0006 restates III.25 (its stage 4), and keeps this
statement as the companion `Prop25.of_circle` (`Brief0006.lean`). -/
theorem Prop25 {A C : Point} {ABC : Circle} (hA : OnCircle A ABC) (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) : type_of% @Centre.Prop25 :=
  Elements.BookIII.Prop25 (exists_centre _)
example : type_of% @Elements.BookIII.Prop25 := fun _ => Centre.Prop25

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

namespace Elements.Staging.Centre

open Tacit

/-! ## Book Zero: a circle is equal to itself (`OnCircles.lean`) -/

/-- A circle is equal to itself. Heath remarks that III.26–III.29, said of equal circles, are
"equally true if the same circle is taken" (vol. 2, p. 61); this is how a proof says so.

Today it asks for a centre G and a point P of the circle, which name nothing in its
conclusion; the rule gives the one and Points 7 the other. -/
theorem EqualCircles.refl (α : Circle) : EqualCircles α α := by
  sorry

example (exists_centre : ∀ α : Circle, ∃ O : Point, Centre O α) :
    type_of% @Centre.EqualCircles.refl := fun α =>
  let ⟨_, hG⟩ := exists_centre α
  let ⟨_, hP, _⟩ := exists_point_on_circle α []
  Elements.EqualCircles.refl hG hP
example : type_of% @Elements.EqualCircles.refl := fun _ _ => Centre.EqualCircles.refl _

/-! ## Book Zero: what holds of one centre holds of every centre -/

/-- What is true of one centre of a circle is true of every centre, since a circle has only
one (`centre_unique`, proved in `Elements.Figure.Circles`). For a condition said of every centre, as III.4's
"not through the centre" and III.8's "through the centre" are: a citer who has named the
centre O passes `hO.every h`, with `h` the condition at O. -/
theorem _root_.Elements.Centre.every {O : Point} {α : Circle} {p : Point → Prop}
    (hO : Centre O α) (h : p O) : ∀ F : Point, Centre F α → p F :=
  fun _ hF => centre_unique hO hF ▸ h

/-- The check that it serves III.4 as stated, for a citer holding a named centre O (checked
by Lean). -/
example {A B C D E O : Point} {ABCD : Circle} (hO : Centre O ABCD) (hA : OnCircle A ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hD : OnCircle D ABCD)
    (hAEC : Between A E C) (hBED : Between B E D) (hB_AC : ¬ Collinear A C B)
    (hAC : ¬ Collinear A C O) (hBD : ¬ Collinear B D O) :
    ¬ (‖A E‖ = ‖E C‖ ∧ ‖B E‖ = ‖E D‖) :=
  BookIII.Staging.Centre.Prop4 hA hB hC hD hAEC hBED hB_AC (hO.every hAC) (hO.every hBD)

end Elements.Staging.Centre
