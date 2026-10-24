import Elements.Figure.Angles
import Elements.Figure.Incidence
import Elements.Figure.RuleBase
import Elements.Figure.Circles
import Elements.Foundations.DefinitionsIII

/-!
# Book Zero: straight lines in a circle

Book III draws straight lines in circles, and reads off its figures where their ends and the
points of the circle lie. These are the facts it takes for granted that need no proposition:
a circumference may be named from either side of the straight line that cuts it off; what
is true of one centre of a circle is true of every centre; equal circles have equal radii;
and a straight line that touches a circle meets it at a point of contact and has no point
within it. They follow from Definition 15, System E's rules for circles, and the definitions
of Book III.

Two more such facts need III.2, and follow it in its file: three points of a circle are not
on one straight line (`BookIII.Prop2.triangle`), and a straight line in a circle has points
of the circle on each side of it (`BookIII.Prop2.oppositeSide` and `BookIII.Prop2.sameSide`).
Book Zero proved them here for any circle from Circle 2 until 24 October 2026, when
Circle 2 and Circle 3 were proved from III.2, after it, and the copies here, which nothing
used, were taken out.

Nothing in Book Zero cites a proposition of the *Elements*, and nothing in it is an
axiom.
-/

namespace Elements

open Tacit

variable {A B C D K P Q : Point} {α β : Circle}

/-! ## A circumference named from either side -/

/-- The circumference BKC is the circumference BK'C for any K' on the same side of
BC as K: the points A that measure them, on the other side, are the same points. -/
theorem circumference_congr {K' : Point} (hK : SameSideOf K K' B C) :
    circumference α B K C = circumference α B K' C := by
  unfold circumference
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨A, hA, hAK, rfl⟩
    exact ⟨A, hA, (hK.symm.trans_opposite hAK.symm).symm, rfl⟩
  · rintro ⟨A, hA, hAK', rfl⟩
    exact ⟨A, hA, (hK.trans_opposite hAK'.symm).symm, rfl⟩

/-- The circumference on which the angle BAC stands (Definition III.9) is the
circumference BKC, for any K on the other side of BC from A: a point of the
circle is on A's side exactly when it is on the other side from K. -/
theorem standing_eq_circumference (hAK : OppositeSidesOf A K B C) :
    standing α B A C = circumference α B K C := by
  unfold standing circumference
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨X, hX, hXA, rfl⟩
    exact ⟨X, hX, hXA.trans_opposite hAK, rfl⟩
  · rintro ⟨X, hX, hXK, rfl⟩
    exact ⟨X, hX, OppositeSidesOf.sameSideOf hXK.symm hAK.symm, rfl⟩

/-- The circumference on which the angle BAC stands is the one on which BA'C stands,
for any A' on the same side of BC as A. -/
theorem standing_congr {A' : Point} (hA : SameSideOf A A' B C) :
    standing α B A C = standing α B A' C := by
  unfold standing
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨X, hX, hXA, rfl⟩
    exact ⟨X, hX, hXA.trans hA, rfl⟩
  · rintro ⟨X, hX, hXA', rfl⟩
    exact ⟨X, hX, hXA'.trans hA.symm, rfl⟩

/-- What is true of one centre of a circle is true of every centre, since a circle has only
one (`centre_unique`, proved in `Elements.Figure.Circles`). For III.4's and III.8's
conditions on every centre, `Centre.every` carries the condition from a known centre O to
any other centre. -/
theorem Centre.every {O : Point} {α : Circle} {p : Point → Prop}
    (hO : Centre O α) (h : p O) : ∀ F : Point, Centre F α → p F :=
  fun _ hF => centre_unique hO hF ▸ h

/-! ## Equal circles -/

/-- In equal circles the radii are equal: any radius GP of the one is equal to any
radius HQ of the other. A circle has only one centre
(`centre_unique`, proved in `Elements.Figure.Circles`), and its radii are equal to one
another (Definition I.15). -/
theorem EqualCircles.radii {G H : Point} (h : EqualCircles α β) (hG : Centre G α)
    (hH : Centre H β) (hP : OnCircle P α) (hQ : OnCircle Q β) : ‖G P‖ = ‖H Q‖ := by
  obtain ⟨G', H', P', Q', hG', hH', hP', hQ', hr⟩ := h
  obtain rfl := centre_unique hG' hG
  obtain rfl := centre_unique hH' hH
  rw [Definition15 hG' hP hP', hr, Definition15 hH' hQ' hQ]

/-- Equal circles, the other way round. -/
theorem EqualCircles.symm (h : EqualCircles α β) : EqualCircles β α := by
  obtain ⟨G, H, P, Q, hG, hH, hP, hQ, hr⟩ := h
  exact ⟨H, G, Q, P, hH, hG, hQ, hP, hr.symm⟩

/-- Circles that cut one another each pass within the other, in either order. -/
theorem CirclesCut.symm {α β : Circle} (h : CirclesCut α β) : CirclesCut β α := by
  obtain ⟨⟨A, B, hAB, hAα, hAβ, hBα, hBβ⟩, hαβ, hβα⟩ := h
  exact ⟨⟨A, B, hAB, hAβ, hAα, hBβ, hBα⟩, hβα, hαβ⟩

/-- A circle is equal to itself. Heath remarks that III.26–III.29, said of equal circles,
are "equally true if the same circle is taken" (vol. 2, p. 61); this is how a proof says
so. -/
theorem EqualCircles.refl (α : Circle) : EqualCircles α α := by
  obtain ⟨G, hG⟩ := exists_centre α
  obtain ⟨P, hP, -⟩ := exists_point_on_circle α []
  exact ⟨G, G, P, P, hG, hG, hP, hP, rfl⟩

/-! ## A straight line touching a circle -/

/-- No point of a straight line that touches a circle lies within it: a straight line
through a point within a circle cuts it (System E, Intersection 3). -/
theorem Touches.not_inside (h : Touches A B α) (hP : Collinear A B P) :
    ¬ InsideCircle P α := by
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B h.1
  obtain ⟨M, hA_M, hB_M, hP_M⟩ := hP
  have hP_L : OnLine P L := (line_unique h.1 hA_M hB_M hA_L hB_L) ▸ hP_M
  exact fun hin => (h.2 L hA_L hB_L).2 (line_meets_circle_of_inside hin hP_L)

/-- The point of contact of a straight line touching a circle. If the straight line AX
touches the circle α, some point B of α is on it; B may be A or X. Definition III.2 holds
the point inside `Touches`, behind a straight line named by A and X, and this reads it off
in one step, for a citer of III.17's companion `Prop17.general`. -/
theorem Touches.contact {A X : Point} {α : Circle} (h : Touches A X α) :
    ∃ B : Point, OnCircle B α ∧ Collinear A X B := by
  /- Name the straight line AX. Definition III.2 gives a point of the circle on it. -/
  obtain ⟨L, hA_L, hX_L⟩ := Postulate1 A X h.1
  obtain ⟨B, hB_L, hB⟩ := (h.2 L hA_L hX_L).1
  exact ⟨B, hB, ⟨L, hA_L, hX_L, hB_L⟩⟩

/-- A straight line that touches a circle, named by any two of its points. -/
theorem Touches.of_collinear (h : Touches A B α) (hC : Collinear A B C) (hD : Collinear A B D)
    (hCD : C ≠ D) : Touches C D α := by
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B h.1
  have on : ∀ {X : Point}, Collinear A B X → OnLine X L := fun ⟨M, hA_M, hB_M, hX_M⟩ =>
    (line_unique h.1 hA_M hB_M hA_L hB_L) ▸ hX_M
  refine ⟨hCD, fun M hC_M hD_M => ?_⟩
  have hLM : L = M := line_unique hCD (on hC) (on hD) hC_M hD_M
  subst hLM
  exact h.2 L hA_L hB_L

end Elements
