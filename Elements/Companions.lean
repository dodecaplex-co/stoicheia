import Elements.BookI.Prop39
import Elements.BookI.Prop40
import Elements.BookI.Prop45
import Elements.BookI.Prop47
import Elements.BookII.Prop01
import Elements.BookII.Prop14
import Elements.BookIII.Prop01
import Elements.BookIII.Prop07
import Elements.BookIII.Prop08
import Elements.BookIII.Prop13
import Elements.BookIII.Prop14
import Elements.BookIII.Prop15
import Elements.BookIII.Prop16
import Elements.BookIII.Prop17
import Elements.BookIII.Prop18
import Elements.BookIII.Prop20
import Elements.BookIII.Prop23
import Elements.BookIII.Prop24
import Elements.BookIII.Prop25
import Elements.BookIII.Prop27
import Elements.BookIII.Prop29
import Elements.BookIII.Prop30
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
  (``Elements.BookI.Prop39.general, "I.39 general"),
  (``Elements.BookI.Prop40.general, "I.40 general"),
  (``Elements.BookI.Prop40.join, "I.40 join"),
  (``Elements.BookI.Prop40.special, "I.40 special"),
  (``Elements.BookI.Prop45.append, "I.45 append"),
  (``Elements.BookI.Prop45.sum, "I.45 sum"),
  (``Elements.BookI.Prop45.apart, "I.45 apart"),
  (``Elements.BookI.Prop45.figure, "I.45 figure"),
  (``Elements.BookI.Prop45.fan, "I.45 fan"),
  (``Elements.BookI.Prop45.outline, "I.45 outline"),
  (``Elements.BookI.Prop47.general, "I.47 general"),
  (``Elements.BookII.Prop1.two, "II.1 two"),
  (``Elements.BookII.Prop1.general, "II.1 general"),
  (``Elements.BookII.Prop14.rectangle, "II.14 rectangle"),
  (``Elements.BookII.Prop14.sum, "II.14 sum"),
  (``Elements.BookII.Prop14.apart, "II.14 apart"),
  (``Elements.BookII.Prop14.figure, "II.14 figure"),
  (``Elements.BookII.Prop14.square, "II.14 square"),
  (``Elements.BookII.Prop14.fan, "II.14 fan"),
  (``Elements.BookII.Prop14.outline, "II.14 outline"),
  (``Elements.BookII.Prop14.outline_side, "II.14 outline_side"),
  (``Elements.BookIII.Prop1.of_circle, "III.1 of_circle"),
  (``Elements.BookIII.Prop7.general, "III.7 general"),
  (``Elements.BookIII.Prop8.general, "III.8 general"),
  (``Elements.BookIII.Prop13.touchesInternally_iff, "III.13 touchesInternally_iff"),
  (``Elements.BookIII.Prop13.touchesExternally_iff, "III.13 touchesExternally_iff"),
  (``Elements.BookIII.Prop13.circlesTouch_iff, "III.13 circlesTouch_iff"),
  (``Elements.BookIII.Prop14.general, "III.14 general"),
  (``Elements.BookIII.Prop15.le_diameter, "III.15 le_diameter"),
  (``Elements.BookIII.Prop15.nearer, "III.15 nearer"),
  (``Elements.BookIII.Prop16.semicircle, "III.16 semicircle"),
  (``Elements.BookIII.Prop16.remaining, "III.16 remaining"),
  (``Elements.BookIII.Prop16.acute, "III.16 acute"),
  (``Elements.BookIII.Prop17.general, "III.17 general"),
  (``Elements.BookIII.Prop18.contact_locallyEqual, "III.18 contact_locallyEqual"),
  (``Elements.BookIII.Prop18.contact_lt, "III.18 contact_lt"),
  (``Elements.BookIII.Prop18.semicircle_gt, "III.18 semicircle_gt"),
  (``Elements.BookIII.Prop18.acute, "III.18 acute"),
  (``Elements.BookIII.Prop20.special, "III.20 special"),
  (``Elements.BookIII.Prop20.circumference, "III.20 circumference"),
  (``Elements.BookIII.Prop23.point, "III.23 point"),
  (``Elements.BookIII.Prop24.equalCircles, "III.24 equalCircles"),
  (``Elements.BookIII.Prop24.equalMeasure, "III.24 equalMeasure"),
  (``Elements.BookIII.Prop25.complete, "III.25 complete"),
  (``Elements.BookIII.Prop25.kind, "III.25 kind"),
  (``Elements.BookIII.Prop25.of_circle, "III.25 of_circle"),
  (``Elements.BookIII.Prop27.of_measure, "III.27 of_measure"),
  (``Elements.BookIII.Prop29.of_measure, "III.29 of_measure"),
  (``Elements.BookIII.Prop30.halves, "III.30 halves"),
  (``Elements.BookIII.Prop31.greater, "III.31 greater"),
  (``Elements.BookIII.Prop31.less, "III.31 less")]
