/-!
# The companions

The theorems proved beside a proposition, each with its reference in the certificate: a
more general form of its statement, say, listed as
`(``Elements.BookI.Prop40.general, "I.40 general")`. Each lives in its proposition's
namespace and is an entry of the certificate in its own right, attached to that
proposition. `Certificate/Facts.lean` checks every entry.
-/

/-- The companions, each with its reference in the certificate. -/
def Elements.companions : List (Lean.Name × String) := []
