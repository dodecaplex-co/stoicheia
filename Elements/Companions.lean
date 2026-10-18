/-!
# The companions

The theorems proved beside a proposition, each with its reference in the certificate: a
more general form of its statement, say, listed as
`(``Elements.BookI.Prop40.general, "I.40 general")`. Each is an entry of the certificate
in its own right, attached to its proposition, whose namespace it lives in; it stands in
its proposition's file, beside the unchanged `theorem PropN`.

An entry is added once its companion is proved, in the same commit that moves the
companion beside its proposition (`docs/templates/orders.md`, the third kind of orders),
so that the listing travels with the proof it lists and with the stamp of its
proposition's review record. This file then imports that proposition's file, since Lean
checks each double-backticked name as it reads it. There are none yet.

The certificate, `Certificate/Facts.lean`, checks every entry: the companion must be
declared, in the namespace of a proposition, and listed by the reference its name gives,
`"I.40 general"` for `Prop40.general`; and a porism, an entry of its own, is never listed
here.
-/

/-- The companions, each with its reference in the certificate, as the note above says.
Empty until the first companion is proved. -/
def Elements.companions : List (Lean.Name × String) := []
