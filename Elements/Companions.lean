/-!
# The companions

The theorems proved beside a proposition, each with its reference in the certificate: a
more general form of its statement, say, listed as
`(``Elements.BookI.Prop40.general, "I.40 general")`. Each is an entry of the certificate
in its own right, attached to its proposition, whose namespace it lives in. There are
none yet.

The stage's integrator adds a companion's entry once the companion is proved, in the
commit that moves it beside its proposition (`docs/WORKFLOW.md`, section 4, and
`docs/FORMALIZATION.md`, section 2). `Certificate/Facts.lean` checks every entry.
-/

/-- The companions, each with its reference in the certificate. Empty until the first
companion is proved. -/
def Elements.companions : List (Lean.Name × String) := []
