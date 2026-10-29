module

public import Model.Laws

/-!
# Translated by hand

**This file is written by hand.** It holds the laws first proved in the plane, translated
by hand before the generator existed, and `exists_centre`, translated by hand and proved in
the plane before it joined the library. Each law here is the library's, word for word, with
`S.Point` for `Elements.Point`, `S.OnCircle` for `Elements.OnCircle`, and so on, and the
printed original is quoted above it, from `Certificate/axioms.lock` for a retained axiom, or
its unchanged theorem type for a retired rule. The defined words the laws use
(`S.CirclesMeet`, `S.OppositeSides`, `S.OutsideCircle`) are the generated ones, from
`Model/Laws.lean`.

These laws are kept as the independent check they were written to be. `Check/Hand.lean`
puts the library's own words in for `S` and asks Lean whether each result is the original
declaration. For each retained axiom it asks too whether this is the law the generator
writes, the field of `Laws` it stands for; `Check/RoundTrip.lean` compares these with the
generated laws by syntax, binder kinds and names included. The retired rules are compared
directly with their theorem types by `comparePlanted`, including binder kinds. The build
fails if any of these fails. The plane proofs use the hand translations, and
`Model/Assembly.lean` gathers those of the retained axioms into their fields of `Laws`.
The other laws are stated the same way,
with the hand translations of `Model/Laws/`, each checked against its generated law in
`Check/`, or directly against its library declaration for a retired axiom. The retired
rules keep their concrete plane proofs and audits as derived facts, with no generated
assumption fields. A proof may instead be stated with the generated law itself,
`Law.Tacit.line_unique plane`, and then needs no hand translation.

The laws here are the circle-intersection rules: Intersection 5, the step Euclid takes for
granted in I.1; Intersection 4, in the corrected form we owe to LeanEuclid (Logan Murphy,
Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si), with our thanks; and
Intersections 8 and 9, which say on which side of the line of centres a crossing point
lies. With them are the eight magnitude laws, which test the translation of the instances
and of the kinds of magnitude, and the rule that every circle has a centre.

Intersection 4 and Intersections 9 are now proved in `Elements/Figure/Incidence.lean`:
the former from Intersection 5 and `line_circle_between`, with the first circle's centre
taken by the rule that every circle has one, and without Circle 1; the latter by choosing
a point on the opposite side and applying the retained Intersections 8 to it.
-/

@[expose] public section

namespace Model

namespace Hand

variable (S : Signature)

/-- `Elements.Tacit.circles_meet` (Intersection 5), by hand. The lock prints it as
`∀ {A B : Elements.Point} {α β : Elements.Circle}, Elements.OnCircle A α →
Elements.InsideCircle B α → Elements.InsideCircle A β → Elements.OnCircle B β →
Elements.CirclesMeet α β`. -/
def circles_meet : Prop :=
  ∀ {A B : S.Point} {α β : S.Circle}, S.OnCircle A α → S.InsideCircle B α →
    S.InsideCircle A β → S.OnCircle B β → S.CirclesMeet α β

/-- `Elements.Tacit.circles_meet_of_on_inside_outside` (Intersection 4, corrected), by
hand. The theorem's unchanged type is `∀ {A B : Elements.Point} {α β : Elements.Circle},
Elements.OnCircle A α → Or (Elements.InsideCircle B α) (Elements.OnCircle B α) →
Elements.InsideCircle A β → Elements.OutsideCircle B β → Elements.CirclesMeet α β`. -/
def circles_meet_of_on_inside_outside : Prop :=
  ∀ {A B : S.Point} {α β : S.Circle}, S.OnCircle A α →
    S.InsideCircle B α ∨ S.OnCircle B α → S.InsideCircle A β → S.OutsideCircle B β →
    S.CirclesMeet α β

/-- `Elements.Tacit.circles_meet_same_side` (Intersections 8), by hand. The lock prints it
as `∀ {α β : Elements.Circle} {B C D : Elements.Point} {L : Elements.Line},
Elements.CirclesMeet α β → Elements.Centre C α → Elements.Centre D β → Elements.OnLine C L →
Elements.OnLine D L → Not (Elements.OnLine B L) → Exists fun (A : Elements.Point) => And
(Elements.OnCircle A α) (And (Elements.OnCircle A β) (Elements.SameSide A B L))`. -/
def circles_meet_same_side : Prop :=
  ∀ {α β : S.Circle} {B C D : S.Point} {L : S.Line}, S.CirclesMeet α β → S.Centre C α →
    S.Centre D β → S.OnLine C L → S.OnLine D L → ¬ S.OnLine B L →
    ∃ A : S.Point, S.OnCircle A α ∧ S.OnCircle A β ∧ S.SameSide A B L

/-- `Elements.Tacit.circles_meet_opposite_side` (Intersections 9), by hand. The theorem's unchanged type
is `∀ {α β : Elements.Circle} {B C D : Elements.Point} {L : Elements.Line},
Elements.CirclesMeet α β → Elements.Centre C α → Elements.Centre D β → Elements.OnLine C L →
Elements.OnLine D L → Not (Elements.OnLine B L) → Exists fun (A : Elements.Point) => And
(Elements.OnCircle A α) (And (Elements.OnCircle A β) (Elements.OppositeSides A B L))`. -/
def circles_meet_opposite_side : Prop :=
  ∀ {α β : S.Circle} {B C D : S.Point} {L : S.Line}, S.CirclesMeet α β → S.Centre C α →
    S.Centre D β → S.OnLine C L → S.OnLine D L → ¬ S.OnLine B L →
    ∃ A : S.Point, S.OnCircle A α ∧ S.OnCircle A β ∧ S.OppositeSides A B L

/-! ## How magnitudes add and compare

The eight magnitude laws quantify over the kind of magnitude. They are easy in the plane;
they are here because they test the translation where it is most delicate, through the
instances behind `+`, `0` and `<`, and through the two copies of `Kind`, whose round trip
in `Check/Hand.lean` is an equivalence proved kind by kind rather than `rfl`. -/

/-- `Elements.Tacit.add_assoc`, by hand. The lock prints it as `∀ {k : Elements.Kind}
(a b c : Elements.Magnitude k), Eq (HAdd.hAdd (HAdd.hAdd a b) c) (HAdd.hAdd a (HAdd.hAdd b
c))`. -/
def add_assoc : Prop :=
  ∀ {k : Kind} (a b c : S.Magnitude k), a + b + c = a + (b + c)

/-- `Elements.Tacit.add_comm`, by hand. The lock prints it as `∀ {k : Elements.Kind}
(a b : Elements.Magnitude k), Eq (HAdd.hAdd a b) (HAdd.hAdd b a)`. -/
def add_comm : Prop :=
  ∀ {k : Kind} (a b : S.Magnitude k), a + b = b + a

/-- `Elements.Tacit.add_lt_add_right`, by hand. The lock prints it as `∀ {k : Elements.Kind}
{a b : Elements.Magnitude k} (c : Elements.Magnitude k), LT.lt a b → LT.lt (HAdd.hAdd a c)
(HAdd.hAdd b c)`. -/
def add_lt_add_right : Prop :=
  ∀ {k : Kind} {a b : S.Magnitude k} (c : S.Magnitude k), a < b → a + c < b + c

/-- `Elements.Tacit.add_zero`, by hand. The lock prints it as `∀ {k : Elements.Kind}
(a : Elements.Magnitude k), Eq (HAdd.hAdd a 0) a`. -/
def add_zero : Prop :=
  ∀ {k : Kind} (a : S.Magnitude k), a + 0 = a

/-- `Elements.Tacit.lt_irrefl`, by hand. The lock prints it as `∀ {k : Elements.Kind}
(a : Elements.Magnitude k), Not (LT.lt a a)`. -/
def lt_irrefl : Prop :=
  ∀ {k : Kind} (a : S.Magnitude k), ¬ a < a

/-- `Elements.Tacit.lt_trans`, by hand. The lock prints it as `∀ {k : Elements.Kind}
{a b c : Elements.Magnitude k}, LT.lt a b → LT.lt b c → LT.lt a c`. -/
def lt_trans : Prop :=
  ∀ {k : Kind} {a b c : S.Magnitude k}, a < b → b < c → a < c

/-- `Elements.Tacit.lt_trichotomy`, by hand. The lock prints it as `∀ {k : Elements.Kind}
(a b : Elements.Magnitude k), Or (LT.lt a b) (Or (Eq a b) (LT.lt b a))`. -/
def lt_trichotomy : Prop :=
  ∀ {k : Kind} (a b : S.Magnitude k), a < b ∨ a = b ∨ b < a

/-- `Elements.Tacit.not_lt_zero`, by hand. The lock prints it as `∀ {k : Elements.Kind}
(a : Elements.Magnitude k), Not (LT.lt a 0)`. -/
def not_lt_zero : Prop :=
  ∀ {k : Kind} (a : S.Magnitude k), ¬ a < 0

/-! ## Every circle has a centre

A law proposed for the foundations is proved in the model before it lands, so that its
model obligation is met when the library first rests on it. This one was proposed in issue
#59, proved in the plane (`Model/Euclidean/Centre.lean`), and then declared in the
library. -/

/-- `Elements.Tacit.exists_centre`, by hand: every circle has a centre, the library's own
rule, from Euclid's Definitions I.15 and I.16. The lock prints it as
`∀ (α : Elements.Circle), Exists fun (O : Elements.Point) => Elements.Centre O α`. -/
def exists_centre : Prop :=
  ∀ (α : S.Circle), ∃ O : S.Point, S.Centre O α

end Hand

end Model
