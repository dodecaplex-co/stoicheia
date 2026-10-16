import Elements.Figure.Basics
import Elements.BookI.Prop05

/-!
# Book I: small steps that cite a proposition

Book Zero (`Elements/Figure/`) may not cite a proposition of the *Elements*. A few
small steps that several proofs share do cite one, so they live here instead,
beside the propositions. Each is named after the proposition it cites, and this
file imports only what they need. A step that cited a later proposition would
make the imports go round in a circle, so it would need a file of its own: the
steps about parallels that cite I.28, I.29 or I.30 are in `HelpersParallels.lean`.

The certificate walks through these steps as it walks through any helper, so a
proof that uses one is recorded as citing the proposition inside it.
-/

namespace Elements.BookI

open Tacit

/-- The angles at the base, and only those. Our I.5 is stated as Euclid states it,
with the equal sides produced and the angles under the base as well, so to cite it
Lean must produce `AB` and `AC` (Post. 2). When only the angles at the base are
wanted, as in I.7, I.9, I.18, I.19, I.20 and I.24, any points beyond `B` and `C`
will do, and this produces them once. [I. 5] -/
theorem Prop5.base {A B C : Point} (hABC : Triangle A B C) (h : ‖A B‖ = ‖A C‖) :
    ∠ A B C = ∠ A C B := by
  obtain ⟨D, hABD⟩ := produce hABC.ne₁₂
  obtain ⟨E, hACE⟩ := produce hABC.ne₁₃
  exact (Prop5 hABC h hABD hACE).1

end Elements.BookI
