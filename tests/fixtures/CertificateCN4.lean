import Elements.Foundations.CommonNotions

/-!
Small subjects for the certificate's C.N. 4 regression. The test compiles this file as
the temporary package's `Elements` module, which an unmodified copy of
`Certificate/Facts.lean` imports in preference to the repository's module.

The restricted calculus (brief 0009) lands separately. These are stand-ins with the exact
names of its constructors in `Elements/Foundations/Superposition/Syntax.lean`, not a model
of its rules. Import only the Common Notions, so the stand-ins also work once the real
calculus lands. No axiom is declared here.
-/

namespace Elements

def companions : List (Lean.Name × String) := []

namespace Superposition

inductive Derives : Prop where
  | given : Derives
  | len_congr : Derives
  | angle_congr : Derives
  | area_congr : Derives

end Superposition

namespace CertificateFixture

/- Every subject inherits one existing axiom through this helper and uses another
directly. This makes the axiom-field comparison non-empty on both sides of the split. -/
theorem add_nothing (a : Length) : a + 0 = a := Tacit.add_zero a

end CertificateFixture

namespace BookI

open Superposition CertificateFixture

variable (a b : Length)

/- Each constructor occurs directly in a separate declaration's value. -/
theorem Prop1 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.len_congr⟩

theorem Prop2 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.angle_congr⟩

theorem Prop3 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.area_congr⟩

/- The next three subjects reach a constructor only through a helper's value. -/
theorem Prop4.step : Derives := Derives.len_congr
theorem Prop4 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Prop4.step⟩

theorem Prop5.step : Derives := Derives.angle_congr
theorem Prop5 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Prop5.step⟩

theorem Prop6.step : Derives := Derives.area_congr
theorem Prop6 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Prop6.step⟩

/- The walk reaches the congruence constructors only through the inductive type's
constructor list. Neither value uses one as a proof step. -/
theorem Prop7 (d : Derives) : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, d⟩

theorem Prop8 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.given⟩

end BookI
end Elements
