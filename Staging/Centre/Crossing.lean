import Elements.BookIII.Prop05
import Elements.BookIII.Prop06

/-!
# Staging: III.5 and III.6, cutting and touching as Definition III.3 reads them

Brief 0008, section 7. Today's III.5 reads "cut" as meeting at two points (`CirclesMeet`),
with the circles two (`ABC ≠ CDG`), and a circle drawn twice over, as two circles with one
centre and one radius, satisfies that, as it satisfies today's contact within. So any proof
of today's III.5 and III.6 must use Diagram-segment 2 (`circle_eq`), on which they rest, or
Circle 4, the two rules that tell two circles apart (the overlap catalogue, under III.5 and
III.6). Definition III.3 sets cutting against
touching: "Circles are said to touch one another which, meeting one another, do not cut one
another." Read so, circles that cut one another cross, each passing within the other, and
circles touching within have the inner circle passing within the outer, as Heath says the
definition must imply. Then III.5 and III.6 follow by Euclid's own argument, with neither
rule. The rules still give the restated statements in a line or two, so the overlap
catalogue keeps its rows: the proofs avoid the rules, which still contain the propositions
(brief 0008, section 7, after Astra's challenge).

Here, with proofs (the coordinator directed them; brief 0008, question 13, asks the freeze
to approve them as staged facts resting on no stub):

* `CirclesCut`, the new word, and contact within with a point of the inner circle within
  the outer, the definition that section 7 recommends (question 16), with `CirclesTouch`
  over it.
  They sit in `Elements.Staging.Centre`, since `Elements.TouchesInternally` and
  `Elements.CirclesTouch` are still declared;
* III.5 and III.6 restated, each proved by Euclid's argument: the straight line he draws
  "at random" is drawn through the point where the one circle passes within the other,
  and the order of the points on it gives "the less to the greater";
* checks (checked by Lean): cutting is symmetric; today's III.5 and III.6 give the restated
  ones, which ask more (no check here runs the converse); III.6 written as question 16's
  alternative, with the point in its statement and today's definition, is the same theorem;
  and the only lines of III.11 and III.13 that read the definition of contact within go
  through as they are written today;
* at the end, the axioms Lean reports for the restated III.5 and III.6, pinned with
  `#guard_msgs` as `Audit/Overlaps.lean` pins its lemmas: neither `circle_eq` nor Circle 4
  is among them, nor an admitted proof, and the build fails if one enters.

When the brief is frozen and the restatements land, the definitions go to
`Elements/Foundations/DefinitionsIII.lean`, the proofs to `Elements/BookIII/Prop05.lean` and
`Prop06.lean`, and this file is deleted.
-/

namespace Elements.Staging.Centre

open Tacit

/-- **Definition III.3**, circles that cut one another. The circles `α` and `β` cut one
another: they meet at two points, and each passes within the other, for a point of `α` is
within `β`, and a point of `β` within `α`. Definition III.3 sets cutting against touching,
and touching circles cross nowhere (`TouchesInternally`, `TouchesExternally`); cutting
circles cross. In the plane, two different circles that meet at two points cross so,
each within the other (brief 0008, section 7). III.5's argument uses one common point and
the point of `α` within `β`, which makes the circles two; the rest says which figure is
meant, as Euclid's setting-out names both points. -/
def CirclesCut (α β : Circle) : Prop :=
  CirclesMeet α β ∧ (∃ P : Point, OnCircle P α ∧ InsideCircle P β) ∧
    ∃ P : Point, OnCircle P β ∧ InsideCircle P α

/-- **Definition III.3**, contact within, as brief 0008 proposes it. The circles `α` and `β`
touch one another internally at `C`, `β` within `α`: they meet at `C`, `β` has passed
within `α`, for a point of `β` is within `α`, and `β` does not cut `α`, for no point of `β`
falls outside `α`. Heath says the definition "must be taken to imply" that "a circle
touching another internally must, immediately before 'meeting' it, have passed through
points *within* the circle that it touches" (vol. 2, p. 3); the definition in this form is
ours. The point within takes the place of today's clause that the circles are two, which
it implies. The last clause stays the whole-circle reading of brief 0004: Heath prefers to
read Definition III.3 locally, the circles not cutting at the point of contact, and the
point within does not make ours his. -/
def TouchesInternally (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ (∃ P : Point, OnCircle P β ∧ InsideCircle P α) ∧
    ∀ P : Point, OnCircle P β → ¬ OutsideCircle P α

/-- **Definition III.3.** The circles `α` and `β` touch one another at `C`, internally, one
within the other, or externally: today's `CirclesTouch`, over contact within as proposed
above. Contact without does not change. -/
def CirclesTouch (α β : Circle) (C : Point) : Prop :=
  TouchesInternally α β C ∨ TouchesInternally β α C ∨ TouchesExternally α β C

/-- Cutting is symmetric, as "cut one another" is (checked by Lean): the definition asks
the same of each circle. -/
example {α β : Circle} (h : CirclesCut α β) : CirclesCut β α := by
  obtain ⟨⟨A, B, hAB, hAα, hAβ, hBα, hBβ⟩, hαβ, hβα⟩ := h
  exact ⟨⟨A, B, hAB, hAβ, hAα, hBβ, hBα⟩, hβα, hαβ⟩

/-- Circles that cut one another are two circles that meet at two points, as today's III.5
asks (checked by Lean): the point of `α` within `β` is not on `β` (Generalities 4). -/
example {α β : Circle} (h : CirclesCut α β) : α ≠ β ∧ CirclesMeet α β := by
  refine ⟨?_, h.1⟩
  rintro rfl
  obtain ⟨-, ⟨P, hP, hP_in⟩, -⟩ := h
  exact inside_not_on hP_in hP

/-- Contact within, as proposed, is today's contact within with a point of the inner circle
within the outer, and that point makes the circles two (checked by Lean). -/
example {α β : Circle} {C : Point} :
    TouchesInternally α β C ↔
      Elements.TouchesInternally α β C ∧ ∃ P : Point, OnCircle P β ∧ InsideCircle P α := by
  constructor
  · rintro ⟨hCα, hCβ, ⟨P, hP, hP_in⟩, hnot⟩
    refine ⟨⟨hCα, hCβ, ?_, hnot⟩, P, hP, hP_in⟩
    rintro rfl
    exact inside_not_on hP_in hP
  · rintro ⟨⟨hCα, hCβ, -, hnot⟩, hpoint⟩
    exact ⟨hCα, hCβ, hpoint, hnot⟩

end Elements.Staging.Centre

namespace Elements.BookIII.Staging.Centre

open Tacit

/-- If two circles cut one another, they will not have the same centre. -/
theorem Prop5 {E : Point} {ABC CDG : Circle} (hcut : Staging.Centre.CirclesCut ABC CDG) :
    ¬ (Centre E ABC ∧ Centre E CDG) := by
  -- For let the circles ABC, CDG cut one another at the points B, C;
  obtain ⟨⟨B, C, -, -, -, hC_ABC, hC_CDG⟩, ⟨F, hF_ABC, hF_in⟩, -⟩ := hcut
  -- I say that they will not have the same centre.
  -- For, if possible, let it be E; let EC be joined, and let EFG be drawn through at random.
  rintro ⟨hE_ABC, hE_CDG⟩
  /- EC is drawn for the eye; our proof uses only its ends. EFG is drawn through F, a point
     of ABC within CDG, where the circles cut one another; produced beyond F, it meets CDG
     at G. One straight line from E meeting the circles at two points is all the argument
     needs, as Heath says under III.6. -/
  have hFE : F ≠ E := ne_of_centre_of_on hE_ABC hF_ABC
  obtain ⟨EFG, hE_EFG, hF_EFG⟩ := Postulate1 E F hFE.symm
  obtain ⟨G, hG_CDG, -, hGFE⟩ := line_circle_beyond hF_in hF_EFG hE_EFG hFE.symm
  -- Then, since the point E is the centre of the circle ABC,
  -- EC is equal to EF. [I. Def. 15]
  have hECF : ‖E C‖ = ‖E F‖ := Definition15 hE_ABC hC_ABC hF_ABC
  -- Again, since the point E is the centre of the circle CDG,
  -- EC is equal to EG.
  have hECG : ‖E C‖ = ‖E G‖ := Definition15 hE_CDG hC_CDG hG_CDG
  -- But EC was proved equal to EF also;
  -- therefore EF is also equal to EG, the less to the greater: which is impossible.
  have hEFG : ‖E F‖ = ‖E G‖ := hECF.symm.trans hECG
  /- F lies between E and G, so EF is the less, as in Euclid's figure. -/
  have hlt : ‖E F‖ < ‖E G‖ := len_lt_of_between (between_symm hGFE)
  rw [hEFG] at hlt
  exact lt_irrefl _ hlt
  -- Therefore the point E is not the centre of the circles ABC, CDG.
  -- Therefore etc.
  -- Q. E. D.

/-- If two circles touch one another, they will not have the same centre. -/
theorem Prop6 {C F : Point} {ABC CDE : Circle}
    (htouch : Staging.Centre.CirclesTouch ABC CDE C) :
    ¬ (Centre F ABC ∧ Centre F CDE) := by
  -- For let the two circles ABC, CDE touch one another at the point C;
  have hC : OnCircle C ABC ∧ OnCircle C CDE := by
    rcases htouch with ⟨h₁, h₂, -⟩ | ⟨h₂, h₁, -⟩ | ⟨h₁, h₂, -⟩ <;> exact ⟨h₁, h₂⟩
  -- I say that they will not have the same centre.
  -- For, if possible, let it be F; let FC be joined, and let FEB be drawn through at random.
  rintro ⟨hF₁, hF₂⟩
  /- Contact without, which Euclid leaves to the reader, ends here: F would be within
     each circle, as a centre is (`centre_inside`), and circles touching without have no
     point within both. So the circles touch within, whichever is the inner, and the inner
     has passed within the outer, at a point the definition gives. FC is drawn for the eye;
     our proof uses only its ends. FEB is drawn through that point and produced beyond it to
     the outer circle, so that E is on CDE and B on ABC, and the nearer F of the two is the
     point of the inner circle: one straight line meeting the circles at two points, as
     Heath answers Camerer. -/
  obtain ⟨E, B, hE, hB, hnear⟩ : ∃ E B : Point, OnCircle E CDE ∧ OnCircle B ABC ∧
      (Between F E B ∨ Between F B E) := by
    rcases htouch with ⟨-, -, ⟨E, hE, hE_in⟩, -⟩ | ⟨-, -, ⟨B, hB, hB_in⟩, -⟩ | ⟨-, -, hout⟩
    · have hEF : E ≠ F := ne_of_centre_of_on hF₂ hE
      obtain ⟨L, hF_L, hE_L⟩ := Postulate1 F E hEF.symm
      obtain ⟨B, hB, -, hBEF⟩ := line_circle_beyond hE_in hE_L hF_L hEF.symm
      exact ⟨E, B, hE, hB, Or.inl (between_symm hBEF)⟩
    · have hBF : B ≠ F := ne_of_centre_of_on hF₁ hB
      obtain ⟨L, hF_L, hB_L⟩ := Postulate1 F B hBF.symm
      obtain ⟨E, hE, -, hEBF⟩ := line_circle_beyond hB_in hB_L hF_L hBF.symm
      exact ⟨E, B, hE, hB, Or.inr (between_symm hEBF)⟩
    · exact absurd (centre_inside hF₂) (hout F (centre_inside hF₁))
  -- Then, since the point F is the centre of the circle ABC,
  -- FC is equal to FB.
  have hFB : ‖F C‖ = ‖F B‖ := Definition15 hF₁ hC.1 hB
  -- Again, since the point F is the centre of the circle CDE,
  -- FC is equal to FE.
  have hFE : ‖F C‖ = ‖F E‖ := Definition15 hF₂ hC.2 hE
  -- But FC was proved equal to FB;
  -- therefore FE is also equal to FB, the less to the greater: which is impossible.
  have hEB : ‖F E‖ = ‖F B‖ := hFE.symm.trans hFB
  /- Whichever of E and B is the nearer F is the less; in Euclid's figure, CDE is the inner
     circle, and E the nearer. -/
  rcases hnear with h | h
  · have hlt : ‖F E‖ < ‖F B‖ := len_lt_of_between h
    rw [hEB] at hlt
    exact lt_irrefl _ hlt
  · have hlt : ‖F B‖ < ‖F E‖ := len_lt_of_between h
    rw [← hEB] at hlt
    exact lt_irrefl _ hlt
  -- Therefore F is not the centre of the circles ABC, CDE.
  -- Therefore etc.
  -- Q. E. D.

/-- Today's III.5 gives the restated one, which asks more: circles that cut one another are
two, and meet at two points (checked by Lean). So the restated III.5 claims nothing that
today's does not. The check runs one way only. In the plane the two hypotheses agree (brief
0008, section 7); where the two rules that tell circles apart are dropped, a circle drawn
twice over meets today's and not the restated one, which shows that they differ there, not
every way in which they could. -/
example : type_of% @Centre.Prop5 := by
  intro E ABC CDG hcut
  refine Elements.BookIII.Prop5 ?_ hcut.1
  rintro rfl
  obtain ⟨-, ⟨P, hP, hP_in⟩, -⟩ := hcut
  exact inside_not_on hP_in hP

/-- Today's III.6 gives the restated one, whose contact within asks more (checked by
Lean). It too runs one way only. -/
example : type_of% @Centre.Prop6 := by
  intro C F ABC CDE htouch
  have within : ∀ {α β : Circle}, Staging.Centre.TouchesInternally α β C →
      TouchesInternally α β C := by
    rintro α β ⟨hCα, hCβ, ⟨P, hP, hP_in⟩, hnot⟩
    refine ⟨hCα, hCβ, ?_, hnot⟩
    rintro rfl
    exact inside_not_on hP_in hP
  refine Elements.BookIII.Prop6 (C := C) ?_
  rcases htouch with h | h | h
  · exact Or.inl (within h)
  · exact Or.inr (Or.inl (within h))
  · exact Or.inr (Or.inr h)

/-- III.6 the other way, the alternative of question 16: today's definition of contact
within kept, and the point of the inner circle within the outer written into III.6's
statement alone. It is the same theorem (checked by Lean, from the restated III.6). -/
example {C F : Point} {ABC CDE : Circle}
    (htouch : (TouchesInternally ABC CDE C ∧ ∃ P : Point, OnCircle P CDE ∧ InsideCircle P ABC) ∨
      (TouchesInternally CDE ABC C ∧ ∃ P : Point, OnCircle P ABC ∧ InsideCircle P CDE) ∨
      TouchesExternally ABC CDE C) :
    ¬ (Centre F ABC ∧ Centre F CDE) := by
  refine Centre.Prop6 (C := C) ?_
  rcases htouch with ⟨⟨hC₁, hC₂, -, hnot⟩, hpoint⟩ | ⟨⟨hC₂, hC₁, -, hnot⟩, hpoint⟩ | h
  · exact Or.inl ⟨hC₁, hC₂, hpoint, hnot⟩
  · exact Or.inr (Or.inl ⟨hC₂, hC₁, hpoint, hnot⟩)
  · exact Or.inr (Or.inr h)

/-- III.11 reads the definition of contact within in two lines, which go through against
the proposed definition as they are written today (checked by Lean): "by III.6 the centres
differ", and the destructuring that keeps the clause that no point of the inner circle is
outside the outer. -/
example {A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)
    (htouch : Staging.Centre.TouchesInternally ABC ADE A) :
    F ≠ G ∧ OnCircle A ABC ∧ OnCircle A ADE ∧
      ∀ P : Point, OnCircle P ADE → ¬ OutsideCircle P ABC := by
  have hFG : F ≠ G := fun e => Centre.Prop6 (Or.inl htouch) ⟨hF, e ▸ hG⟩
  obtain ⟨hA₁, hA₂, -, hwithin⟩ := htouch
  exact ⟨hFG, hA₁, hA₂, hwithin⟩

/-- III.13 touches the third clause in one line, which carries it unread to a second point
of contact B, and elsewhere reads only the first two; the line goes through as it is written
today (checked by Lean). -/
example {B D : Point} {α β : Circle} (ht : Staging.Centre.TouchesInternally α β D)
    (hBα : OnCircle B α) (hBβ : OnCircle B β) :
    Staging.Centre.TouchesInternally α β B ∧ OnCircle D α ∧ OnCircle D β :=
  ⟨⟨hBα, hBβ, ht.2.2.1, ht.2.2.2⟩, ht.1, ht.2.1⟩

/-- III.10's last step, as section 7 plans it (checked by Lean): with the one centre P and
the common point B, Diagram-segment 2 makes ABC and DEF one circle, which they were supposed
not to be. The restated III.5 cannot serve here, for circles about one centre do not cross. -/
example {B P : Point} {ABC DEF : Circle} (hne : ¬ ABC = DEF) (hP : Centre P ABC)
    (hP' : Centre P DEF) (hB₁ : OnCircle B ABC) (hB₂ : OnCircle B DEF) : False :=
  hne (circle_eq hP hP' hB₁ hB₂ rfl)

end Elements.BookIII.Staging.Centre

/-! ## What the restated III.5 and III.6 rest on

Neither rule that tells two circles apart, Diagram-segment 2 (`circle_eq`) and Circle 4
(`not_same_side_of_circles_meet`), nor an admitted proof: Definition I.15, Postulate 1 and
thirteen tacit rules, the same for each (checked by Lean, as `lake build Staging` builds
the file; the default `lake build` does not). The pins check the names of these two
declarations' axioms and nothing more: not the reading of the statements, nor the
statements of the axioms, nor the other declarations here, nor whether a shorter proof
from other rules exists. Shorter proofs do exist, from Diagram-segment 2 among others, as
the overlap catalogue will record (brief 0008, section 7). -/

/--
info: 'Elements.BookIII.Staging.Centre.Prop5' depends on axioms: [Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.inside_not_on,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.not_lt_zero]
-/
#guard_msgs in
#print axioms Elements.BookIII.Staging.Centre.Prop5

/--
info: 'Elements.BookIII.Staging.Centre.Prop6' depends on axioms: [Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.inside_not_on,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.not_lt_zero]
-/
#guard_msgs in
#print axioms Elements.BookIII.Staging.Centre.Prop6
