import Elements.Foundations.CommonNotions
import Elements.Foundations.Definitions
import Elements.Foundations.DefinitionsII
import Elements.Foundations.DefinitionsIII
import Elements.Foundations.Magnitudes
import Elements.Foundations.Phrases
import Elements.Foundations.Postulates
import Elements.Foundations.Tacit.Constructions
import Elements.Foundations.Tacit.Diagram
import Elements.Foundations.Tacit.Magnitudes
import Elements.Foundations.Tacit.Metric
import Elements.Foundations.Tacit.Superposition
import Elements.Foundations.Tacit.Transfer
import Elements.Foundations.Words
import Model.Laws
import Model.Hand
import Model.Laws.incidence
import Check.Original
import Check.Generator

/-!
# The round trip, by syntax

`Model/Laws.lean` is printed Lean, and Lean elaborates it again when the model is built. Here
each law and each word, as Lean elaborated it from that file, is translated back, each field
of the signature and each word over it replaced by the library's word, and compared with the
library's declaration expression for expression (`Check.Generator.checkRoundTrip`). A binder's
kind and type always count, and so does its name wherever the bound variable is used; the name
of an unused hypothesis does not, since Lean prints it as an arrow and it is no part of what a
law says. The one difference allowed is that the four carrier words of the magnitudes are
unfolded on both sides first, since the signature's fields write the carriers out
(`Check.Generator.unfoldCarriers`). Anything left over that does not translate back, a field of
the signature used other than as a word, or a word of the model with no counterpart in the
library, is an error.

This is stricter than the kernel's round trip (`Check/Laws.lean`): it sees a binder made
explicit where the library's is implicit, and a law that is right only after a word is
unfolded, neither of which changes the proposition. It also checks:

* the words written by hand in `Model/Signature.lean`, exactly, and the type of each field of
  the signature against the library's opaque word;
* that `Neutral` and `Laws` have exactly a field for each law of the lock, each of type
  `Law.… S`, and nothing else;
* each law of `Model/Hand.lean` against the law the generator wrote for it; and
* that `original`, which the kernel's round trips put back for the signature, gives each field
  the library's word.

The section after the check plants a fault of each kind in a copy of a law, and the build fails
unless the check refuses each with the message given there.
-/

run_cmd Check.Generator.checkRoundTrip

/-! ## The check refuses what it is meant to refuse

Each definition here is a law of `Model/Laws.lean` with one fault planted in it, and
`comparePlanted` runs on it the comparison that `checkRoundTrip` makes of every generated law;
`#guard_msgs` fails the build unless the comparison refuses it with exactly the message above.
The first and the fourth pass the kernel's `rfl`, which is why the comparison by syntax is
needed. The last two are statements in the library's words, and the translation must refuse a
constant it has no translation for. -/

namespace Check.Planted

open Model

/-- Intersection 5 with the point `A` made explicit, where the library's is implicit. The
kernel cannot see it: -/
def explicit (S : Signature) : Prop :=
  ∀ (A : S.Point) {B : S.Point} {α β : S.Circle}, S.OnCircle A α → S.InsideCircle B α →
    S.InsideCircle A β → S.OnCircle B β → S.CirclesMeet α β

example : explicit original = type_of% @Elements.Tacit.circles_meet := rfl

/-- Intersection 5 with its two points exchanged in the first hypothesis. -/
def exchanged (S : Signature) : Prop :=
  ∀ {A B : S.Point} {α β : S.Circle}, S.OnCircle B α → S.InsideCircle B α →
    S.InsideCircle A β → S.OnCircle B β → S.CirclesMeet α β

/-- Postulate 1 without its guard `A ≠ B`. -/
def unguarded (S : Signature) : Prop :=
  ∀ (A B : S.Point), ∃ L : S.Line, S.OnLine A L ∧ S.OnLine B L

/-- Intersection 4 with `S.OutsideCircle B β` written out. The kernel unfolds the word, and
cannot see it: -/
def unfolded (S : Signature) : Prop :=
  ∀ {A B : S.Point} {α β : S.Circle}, S.OnCircle A α → S.InsideCircle B α ∨ S.OnCircle B α →
    S.InsideCircle A β → ¬S.InsideCircle B β ∧ ¬S.OnCircle B β → S.CirclesMeet α β

example : unfolded original = type_of% @Elements.Tacit.circles_meet_of_on_inside_outside := rfl

/-- A statement about parallels, a word the laws do not reach. -/
def parallels : Prop := ∀ L M : Elements.Line, Elements.Parallel L M → L ≠ M

/-- A statement using the check's own copy of the kinds, neither the library's nor Lean's. -/
def foreign : Prop := ∀ k : Model.Kind, kind k = kind k

end Check.Planted

/-- error: `Check.Planted.explicit`: the binder `A` is explicit where the library's `A` is implicit -/
#guard_msgs in
run_cmd Check.Generator.comparePlanted ``Check.Planted.explicit ``Elements.Tacit.circles_meet

/-- error: `Check.Planted.exchanged`: `B` where the library has `A` -/
#guard_msgs in
run_cmd Check.Generator.comparePlanted ``Check.Planted.exchanged ``Elements.Tacit.circles_meet

/-- error: `Check.Planted.unguarded`: `Exists …` where the library has `Ne … → …` -/
#guard_msgs in
run_cmd Check.Generator.comparePlanted ``Check.Planted.unguarded ``Elements.Postulate1

/-- error: `Check.Planted.unfolded`: `And` where the library has `Elements.OutsideCircle` -/
#guard_msgs in
run_cmd (Check.Generator.comparePlanted ``Check.Planted.unfolded
  ``Elements.Tacit.circles_meet_of_on_inside_outside)

/--
error: `Check.Planted.parallels`: `Elements.Parallel` is a word of the project with no translation: neither a field of the signature, nor `Kind`, nor a defined word the generator translates
-/
#guard_msgs in
run_cmd Check.Generator.translatePlanted ``Check.Planted.parallels

/--
error: `Check.Planted.foreign`: `Model.Kind` is neither Lean's own (from `Init`) nor a word of the project; `Check.kind` is neither Lean's own (from `Init`) nor a word of the project
-/
#guard_msgs in
run_cmd Check.Generator.translatePlanted ``Check.Planted.foreign
