import Elements.Foundations.CommonNotions

/-!
Small subjects for the certificate's C.N. 4 regression. The test compiles this file as
the temporary package's `Elements` module, which an unmodified copy of
`Certificate/Facts.lean` imports in preference to the repository's module.

The restricted calculus (brief 0009) lands separately. These are stand-ins with the exact
names of its marker and constructors, not a model
of its rules. Import only the Common Notions, so the stand-ins also work once the real
calculus lands. No axiom is declared here.
-/

namespace Elements

def companions : List (Lean.Name × String) := []

namespace Superposition

inductive Coincidence : Prop where
  | step : Coincidence

inductive Derives : Prop where
  | given : Derives
  | len_congr (cn4 : Coincidence) (d : Derives) : Derives
  | angle_congr (cn4 : Coincidence) (d : Derives) : Derives
  | area_congr (cn4 : Coincidence) (d : Derives) : Derives

/- Rebuilding names every congruence constructor, but supplies no coincidence step.
The marker is passed along as a bound variable in each branch. -/
def Derives.map : Derives → Derives
  | .given => .given
  | .len_congr cn4 d => .len_congr cn4 (map d)
  | .angle_congr cn4 d => .angle_congr cn4 (map d)
  | .area_congr cn4 d => .area_congr cn4 (map d)

/- Elimination inspects every constructor without introducing a step either. -/
theorem Derives.sound : Derives → True
  | .given => True.intro
  | .len_congr _ d => sound d
  | .angle_congr _ d => sound d
  | .area_congr _ d => sound d

/- A helper that introduces a step must count, even if the caller takes another branch:
the certificate records the constants named by proof terms, without evaluating them. -/
def Derives.with_step : Bool → Derives
  | true => .len_congr .step .given
  | false => .given

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
  ⟨Tacit.add_comm a b, add_nothing a, Derives.len_congr .step .given⟩

theorem Prop2 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.angle_congr ⟨⟩ .given⟩

theorem Prop3 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.area_congr Coincidence.step .given⟩

/- The next three subjects reach a constructor only through a helper's value. -/
theorem Prop4.step : Derives := Derives.len_congr ⟨⟩ .given
theorem Prop4 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Prop4.step⟩

theorem Prop5.step : Derives := Derives.angle_congr .step .given
theorem Prop5 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Prop5.step⟩

theorem Prop6.step : Derives := Derives.area_congr Coincidence.step .given
theorem Prop6 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Prop6.step⟩

/- The walk reaches the congruence constructors only through the inductive type's
constructor list. Neither value uses one as a proof step. -/
theorem Prop7 (d : Derives) : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, d⟩

theorem Prop8 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.given⟩

/- Neither transforming a given derivation nor eliminating it supplies a step. -/
theorem Prop9 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.map .given⟩

theorem Prop10 : a + b = b + a ∧ a + 0 = a ∧ True :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.sound (Derives.map .given)⟩

/- The same transformers must preserve reporting of every real step. -/
theorem Prop11 : a + b = b + a ∧ a + 0 = a ∧ True :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.sound (Derives.map Prop4.step)⟩

theorem Prop12 : a + b = b + a ∧ a + 0 = a ∧ True :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.sound (Derives.map Prop5.step)⟩

theorem Prop13 : a + b = b + a ∧ a + 0 = a ∧ True :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.sound (Derives.map Prop6.step)⟩

/- A bound marker names no step, even when supplied to a congruence constructor. -/
theorem Prop14 (cn4 : Coincidence) : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.map (.len_congr cn4 .given)⟩

theorem Prop15 : a + b = b + a ∧ a + 0 = a ∧ Derives :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.with_step false⟩

/- Soundness alone must also leave a given derivation free of C.N. 4. -/
theorem Prop16 : a + b = b + a ∧ a + 0 = a ∧ True :=
  ⟨Tacit.add_comm a b, add_nothing a, Derives.sound .given⟩

end BookI
end Elements
