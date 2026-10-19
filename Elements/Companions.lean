import Elements.BookI.Prop40
import Elements.BookI.Prop45
import Elements.BookII.Prop01
import Elements.BookII.Prop14
import Elements.BookIII.Prop16
import Elements.BookIII.Prop31

/-!
# The companions

The theorems proved beside a proposition, each with its reference in the certificate: a
more general form of its statement, say, listed as
`(``Elements.BookI.Prop40.general, "I.40 general")`. Each lives in its proposition's
namespace and is an entry of the certificate in its own right, attached to that
proposition. `Certificate/Facts.lean` checks every entry.

Each entry's proposition file is imported at the top of this file, so that its
double-backtick name resolves.
-/

/-- The companions, each with its reference in the certificate. -/
def Elements.companions : List (Lean.Name × String) := [
  (``Elements.BookI.Prop40.general, "I.40 general"),
  (``Elements.BookI.Prop40.join, "I.40 join"),
  (``Elements.BookI.Prop40.special, "I.40 special"),
  (``Elements.BookI.Prop45.append, "I.45 append"),
  (``Elements.BookI.Prop45.sum, "I.45 sum"),
  (``Elements.BookI.Prop45.apart, "I.45 apart"),
  (``Elements.BookI.Prop45.figure, "I.45 figure"),
  (``Elements.BookI.Prop45.fan, "I.45 fan"),
  (``Elements.BookII.Prop1.two, "II.1 two"),
  (``Elements.BookII.Prop1.general, "II.1 general"),
  (``Elements.BookII.Prop14.rectangle, "II.14 rectangle"),
  (``Elements.BookII.Prop14.sum, "II.14 sum"),
  (``Elements.BookII.Prop14.apart, "II.14 apart"),
  (``Elements.BookII.Prop14.figure, "II.14 figure"),
  (``Elements.BookII.Prop14.square, "II.14 square"),
  (``Elements.BookII.Prop14.fan, "II.14 fan"),
  (``Elements.BookIII.Prop16.semicircle, "III.16 semicircle"),
  (``Elements.BookIII.Prop16.remaining, "III.16 remaining"),
  (``Elements.BookIII.Prop16.acute, "III.16 acute"),
  (``Elements.BookIII.Prop31.greater, "III.31 greater"),
  (``Elements.BookIII.Prop31.less, "III.31 less")]
