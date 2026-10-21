import Elements.Foundations.Postulates
import Elements.Foundations.Definitions
import Elements.Foundations.Tacit.Metric
import Elements.Foundations.Tacit.Superposition

/-!
Small subjects for the certificate's construction rules and cited laws (#150, question 4).
The test compiles this file as the temporary package's `Elements` module, as it does the
C.N. 4 fixture, over the repository's compiled foundations, which an unmodified copy of
`Certificate/Facts.lean` then reads.

The axioms of `CitedFixture` are the cases of the definition of a construction rule
(docs/FORMALIZATION.md, section 9), declared here so that the test does not depend on
which rules the lock holds: existence asserted directly, through a definition, through an
instance's order, twice negated, in an `Iff` and in an `Or`; and existence negated, behind
an implication, assumed in a hypothesis, or absent. They are stand-ins for the check, not
laws of the plane, and nothing is proved from them but the fixture's own law of I.7.

The entries cite laws in two shapes: through one shared theorem that proves every law of a
list by cases (I.1), and law by law in their own proof, naming each law's proof (I.2). I.3
reaches a second proof of Metric 3 only through I.2, an entry, where the walk stops. I.6
names one proof of Metric 3 and reaches another, which draws, only through a lemma that is
not itself a proof of the law, so every proof it reaches is listed, with the rules beneath
them all.
-/

namespace Elements

def companions : List (Lean.Name × String) := []

namespace CitedFixture

/-- A planted order on points, given by an instance of this project. -/
instance : LE Point := ⟨fun A B => ∃ L : Line, OnLine A L ∧ OnLine B L⟩

/-- Existence behind an implication, inside a definition. -/
def Empty (L : Line) : Prop := (∃ A : Point, OnLine A L) → False

/- Construction rules. -/
axiom plain (A B : Point) : A ≠ B → ∃ C : Point, Between A C B
axiom circles (α β : Circle) : CirclesMeet α β
axiom line_circle (L : Line) (α : Circle) : LineMeetsCircle L α
axiom lines (L M : Line) : L ≠ M → LinesMeet L M
axiom by_instance (A B : Point) : A ≤ B
axiom twice_negated (L : Line) : ¬ ¬ ∃ A : Point, OnLine A L
axiom in_iff (A B C : Point) : Collinear A B C ↔ Collinear B A C
axiom in_or (A : Point) (L : Line) : OnLine A L ∨ ∃ B : Point, OnLine B L

/- Not construction rules. -/
axiom triangle (A B C : Point) : A ≠ B → Triangle A B C
axiom not_collinear (A B C : Point) : ¬ Collinear A B C
axiom empty (L : Line) : Empty L
axiom assumed (A : Point) (L : Line) : (∃ B : Point, OnLine B L) → OnLine A L
axiom equal (A B : Point) : ‖A B‖ = ‖B A‖

open Superposition

/-- The fixture's law of I.7, assumed: a stand-in for Euclid's proof. -/
axiom prop7_law : Cited.prop7.Holds primitives

/-- Metric 3's law, from `len_symm` alone. -/
theorem holds_lenSymm : Cited.lenSymm.Holds primitives :=
  fun v _ => Tacit.len_symm (v.pt .A) (v.pt .B)

/-- A second proof of Metric 3's law, through the first. -/
theorem holds_lenSymm' : Cited.lenSymm.Holds primitives := holds_lenSymm

/-- Metric 4's law, with a use of Postulate 1 planted in its proof. -/
theorem holds_angleSymm : Cited.angleSymm.Holds primitives := by
  have _drawn := @Postulate1
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  exact Tacit.angle_symm h.1 h.2.1

/-- Every law of a list, by cases: one shared theorem for the laws an entry cites. -/
theorem holds_listed : ∀ c ∈ [Cited.lenSymm, Cited.angleSymm], c.Holds primitives := by
  intro c hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl
  · exact holds_lenSymm
  · exact holds_angleSymm

/-- Metric 3's law once more, with a use of Postulate 2 planted in its proof. -/
theorem holds_lenSymm_drawn : Cited.lenSymm.Holds primitives := by
  have _drawn := @Postulate2
  exact holds_lenSymm

/-- Metric 3's law beside a truth: a lemma, not itself a proof of the law. -/
theorem lenSymm_and_true : Cited.lenSymm.Holds primitives ∧ True :=
  ⟨holds_lenSymm_drawn, trivial⟩

end CitedFixture

namespace BookI

open Superposition CitedFixture

/-- The laws I.1 cites. -/
abbrev Prop1.cites : List Cited := [.lenSymm, .angleSymm]

/-- Its laws through one shared theorem. -/
theorem Prop1 : ∀ c ∈ Prop1.cites, c.Holds primitives := holds_listed

/-- The laws I.2 cites, out of the type's order. -/
abbrev Prop2.cites : List Cited := [.prop7, .lenSymm]

/-- I.7's law, with a use of `Tacit.circles_meet` planted in its proof. -/
theorem Prop2.holds_prop7 : Cited.prop7.Holds primitives := by
  have _met := @Tacit.circles_meet
  exact prop7_law

/-- Its laws one by one. -/
theorem Prop2 : ∀ c ∈ Prop2.cites, c.Holds primitives := by
  intro c hc
  simp only [Prop2.cites, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl
  · exact Prop2.holds_prop7
  · exact holds_lenSymm'

/-- Metric 3's law, from its first proof, beside I.2, whose proof reaches the second. -/
theorem Prop3 : Cited.lenSymm.Holds primitives ∧ ∀ c ∈ Prop2.cites, c.Holds primitives :=
  ⟨holds_lenSymm, Prop2⟩

/-- No law. -/
theorem Prop4 : True := trivial

/-- Metric 3's law from its first proof, named, and from the drawn one, reached only through
a lemma. -/
theorem Prop6 : Cited.lenSymm.Holds primitives ∧ Cited.lenSymm.Holds primitives :=
  ⟨holds_lenSymm, lenSymm_and_true.1⟩

end BookI

end Elements
