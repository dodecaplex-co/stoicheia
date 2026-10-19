import Elements.Figure.Angles
import Elements.Figure.Circles
import Elements.Foundations.DefinitionsIII

/-!
# Book Zero: straight lines in a circle

Book III draws straight lines in circles, and reads off its figures where their ends and the
points of the circle lie. These are the facts it takes for granted that need no proposition:
three points of a circle are not on one straight line; a straight line in a circle has points
of the circle on each side of it; a circumference may be named from either side of the
straight line that cuts it off; equal circles have equal radii; and a straight line that
touches a circle meets it at a point of contact and has no point within it. They follow
from Definition 15, System E's rules for circles, and the definitions of Book III.

The first two, proved here for any circle, rest on System E's Circle 2, which contains
III.2. The propositions take them from III.2 instead
(`BookIII.Prop2.triangle`, `BookIII.Prop2.oppositeSide`, `BookIII.Prop2.sameSide`), and so
rest on neither Circle 2 nor Circle 3.

Nothing in Book Zero cites a proposition of the *Elements*, and nothing in it is an
axiom.
-/

namespace Elements

open Tacit

variable {A B C D K P Q : Point} {α β : Circle}

/-! ## Points of a circle -/

/-- Three points of a circle are not on one straight line. Were they, one would lie
between the other two, and so within the circle (System E, Circle 2), not on it. For any
circle, `BookIII.Prop2.triangle` gives the same by III.2. -/
theorem Triangle.of_onCircle (hA : OnCircle A α) (hB : OnCircle B α) (hC : OnCircle C α)
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) : Triangle A B C := by
  rintro ⟨L, hA_L, hB_L, hC_L⟩
  rcases between_cases hAB hBC hAC hA_L hB_L hC_L with h | h | h
  · exact inside_not_on (inside_of_between (Or.inr hA) (Or.inr hC) h) hB
  · exact inside_not_on (inside_of_between (Or.inr hB) (Or.inr hC) h) hA
  · exact inside_not_on (inside_of_between (Or.inr hA) (Or.inr hB) h) hC

/-- A straight line `BC` in a circle has a point of the circle on the other side of it
from any point `K` off it. Take `M` between `B` and `C`; it is within the circle (System
E, Circle 2), so the straight line `KM`, produced beyond `M`, meets the circle
(Intersections 5), on the other side of `BC` from `K` (Pasch 3). For any circle,
`BookIII.Prop2.oppositeSide` gives the same by III.2. -/
theorem exists_onCircle_oppositeSidesOf (hB : OnCircle B α) (hC : OnCircle C α)
    (hK : Triangle B C K) : ∃ A : Point, OnCircle A α ∧ OppositeSidesOf A K B C := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hK.ne₁₂
  obtain ⟨M, hM_L, hBMC, -⟩ := exists_point_between hB_L hC_L hK.ne₁₂ []
  have hM_in : InsideCircle M α := inside_of_between (Or.inr hB) (Or.inr hC) hBMC
  have hK_L : ¬ OnLine K L := hK.off_line hB_L hC_L
  have hKM : K ≠ M := fun e => hK_L (e ▸ hM_L)
  obtain ⟨N, hK_N, hM_N⟩ := Postulate1 K M hKM
  obtain ⟨A, hA_α, hA_N, hAMK⟩ := line_circle_beyond hM_in hM_N hK_N hKM
  /- `A` is off `BC`: the straight lines `KM` and `BC` meet only at `M`, and `A` is on
     the circle, not within it. -/
  have hAM : A ≠ M := fun e => inside_not_on hM_in (e ▸ hA_α)
  have hA_L : ¬ OnLine A L := fun hA_L =>
    hK_L ((line_unique hAM hA_N hM_N hA_L hM_L) ▸ hK_N)
  exact ⟨A, hA_α, OppositeSidesOf.of_line hK.ne₁₂ hB_L hC_L
    ⟨hA_L, hK_L, pasch3 hAMK hM_L⟩⟩

/-- A straight line `BC` in a circle has a point of the circle on the same side of it as
any point `K` off it: take a point on the other side from `K`, and a point of the circle
on the other side from that (`exists_onCircle_oppositeSidesOf`). For any circle,
`BookIII.Prop2.sameSide` gives the same by III.2. -/
theorem exists_onCircle_sameSideOf (hB : OnCircle B α) (hC : OnCircle C α)
    (hK : Triangle B C K) : ∃ A : Point, OnCircle A α ∧ SameSideOf A K B C := by
  obtain ⟨Q, hQ, -⟩ := exists_oppositeSidesOf hK []
  obtain ⟨A, hA_α, hAQ⟩ := exists_onCircle_oppositeSidesOf hB hC hQ.triangle
  exact ⟨A, hA_α, OppositeSidesOf.sameSideOf hAQ.symm hQ⟩

/-! ## A circumference named from either side -/

/-- The circumference `BKC` is the circumference `BK'C` for any `K'` on the same side of
`BC` as `K`: the points `A` that measure them, on the other side, are the same points. -/
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

/-- The circumference on which the angle `BAC` stands (Definition III.9) is the
circumference `BKC`, for any `K` on the other side of `BC` from `A`: a point of the
circle is on `A`'s side exactly when it is on the other side from `K`. -/
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

/-- The circumference on which the angle `BAC` stands is the one on which `BA'C` stands,
for any `A'` on the same side of `BC` as `A`. -/
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
one (`centre_unique`, Generalities 2). For a condition said of every centre, as III.4's
"not through the centre" and III.8's "through the centre" are: a citer who has named the
centre O passes `hO.every h`, with `h` the condition at O. -/
theorem Centre.every {O : Point} {α : Circle} {p : Point → Prop}
    (hO : Centre O α) (h : p O) : ∀ F : Point, Centre F α → p F :=
  fun _ hF => centre_unique hO hF ▸ h

/-! ## Equal circles -/

/-- In equal circles the radii are equal: any radius `GP` of the one is equal to any
radius `HQ` of the other. A circle has only one centre (System E, Generalities 2), and
its radii are equal to one another (Definition 15). -/
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
