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
import Model.Laws.«areas-p5»
import Model.Laws.intersections
import Model.Laws.circles
import Model.Laws.sides
import Model.Laws.order
import Model.Laws.incidence
import Model.Laws.lengths
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

The law fixtures copy `Model/Laws.lean` with one fault planted in each; `comparePlanted`
applies the comparison that `checkRoundTrip` makes of every generated law. `#guard_msgs`
pins each exact refusal. The first and fourth pass the kernel's `rfl`, which is why the
comparison by syntax is needed. Two statements in the library's words test that translation
refuses constants it has no translation for. Two copies of collinearity exercise
`comparePlantedWord`: the matching copy passes, and the corrupted copy pins its refusal. -/

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

/-- A copy of the translated definition of collinearity, with no fault planted. -/
def collinear (S : Signature) (A B C : S.Point) : Prop :=
  ∃ L : S.Line, S.OnLine A L ∧ S.OnLine B L ∧ S.OnLine C L

/-- The same definition with the last two points exchanged in its value. -/
def collinearExchanged (S : Signature) (A B C : S.Point) : Prop :=
  ∃ L : S.Line, S.OnLine A L ∧ S.OnLine C L ∧ S.OnLine B L

end Check.Planted

#guard_msgs in
run_cmd Check.Generator.comparePlantedWord ``Check.Planted.collinear ``Elements.Collinear

/-- error: `Check.Planted.collinearExchanged`: `C` where the library has `B` -/
#guard_msgs in
run_cmd (Check.Generator.comparePlantedWord ``Check.Planted.collinearExchanged
  ``Elements.Collinear)

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

/-! ## Purity before the shared modules arrive

These cases use Init declarations, so they run before the restricted calculus exists.
The planted declarations are copies passed to a lookup, never installed in Lean's
environment. Some fixtures make the root reach a second definition, so the faults test
both direct and transitive dependencies through types and values. -/

/- Init definitions, inductives, recursors and all three permitted axioms pass unchanged. -/
#guard_msgs in
run_cmd (Check.Generator.checkPureFixture
  #[``id, ``List, ``Nat.rec, ``propext, ``Classical.choice, ``Quot.sound])

/- Planted declaring-module lookups exercise the core and sharing decisions without
installing a module or constructing an environment. -/
#guard_msgs in
run_cmd Check.Generator.checkModuleTrustFixture `Init.«/tmp/Elements/Foundations/Words»

#guard_msgs in
run_cmd Check.Generator.checkModuleTrustFixture `Model.«..».Check.Original

#guard_msgs in
run_cmd Check.Generator.checkModuleTrustFixture `Elements.«..».Check.Original

/-- error: shared calculus reaches `Elements.Point`, outside the four pure modules and `Init` -/
#guard_msgs in
run_cmd Check.Generator.pureDependency ``Elements.Point

/-- error: shared calculus reaches `Elements.Point`, outside the four pure modules and `Init` -/
#guard_msgs in
run_cmd Check.Generator.pureDependency ``Elements.Point true

/-- error: shared calculus reaches `sorryAx` -/
#guard_msgs in
run_cmd Check.Generator.pureDependency ``sorryAx

/-- error: shared calculus reaches `Elements.Point`, outside the four pure modules and `Init` -/
#guard_msgs in
run_cmd Check.Generator.plantPureDependency ``id ``Elements.Point

/-- error: shared calculus reaches `Elements.Point`, outside the four pure modules and `Init` -/
#guard_msgs in
run_cmd Check.Generator.plantPureDependency ``Not ``Elements.Point true

#guard_msgs in
run_cmd Check.Generator.plantPureDependency ``id ``Not

/-- error: shared calculus reaches unapproved axiom `Not` -/
#guard_msgs in
run_cmd Check.Generator.pureAxiom

/-- error: `Nat.rec` is not shared -/
#guard_msgs in
run_cmd Check.Generator.checkSharedIdentity ``Nat.rec

/- Stand-in modules extend the production boundary, so these fixtures also work after
the calculus arrives. They exercise successful identities before the calculus exists.
List.filterMap has two universe arguments; Model.Kind.rec also checks that a shared name
in the Model namespace survives the residual-name check in reverse translation. -/
#guard_msgs in
run_cmd (Check.Generator.checkSharedIdentityWith
  (Check.Generator.pureModules ++ #[`Init.Data.List.Basic]) ``List.filterMap)

#guard_msgs in
run_cmd (Check.Generator.checkSharedIdentityWith
  (Check.Generator.pureModules ++ #[`Model.Signature]) ``Model.Kind.rec)

#guard_msgs in
run_cmd (Check.Generator.checkPureModuleFixture
  (Check.Generator.pureModules ++ #[`Init.Data.List.Basic]) ``List.filterMap)

/- No explicit declaration root is supplied to the audit: module data must find this
word even though the library's laws do not use it. -/
/-- error: shared calculus reaches `Elements.Point`, outside the four pure modules and `Init` -/
#guard_msgs in
run_cmd (Check.Generator.checkPureModuleFixture
  (Check.Generator.pureModules ++ #[`Init.Data.List.Basic])
  ``List.filterMap (some ``Elements.Point))

#guard_msgs in
run_cmd Check.Generator.checkSharedImportHeader

/-- error: shared calculus reaches `Elements.Point`, outside the four pure modules and `Init` -/
#guard_msgs in
run_cmd Check.Generator.pureOpaqueDependency

/-- error: shared calculus reaches `Elements.Point`, outside the four pure modules and `Init` -/
#guard_msgs in
run_cmd Check.Generator.pureRecursorDependency

#guard_msgs in
run_cmd Check.Generator.checkModelDirPaths

/-! ## The imports respect the shared boundary

The real tree and planted headers use the same parser and decision. The permitted headers
exercise comments, blank lines, import modifiers and escaped identifiers. Text after the
first body command is not part of the header. -/

#guard_msgs in
run_cmd Check.Generator.checkModelImports

/-- error: model/Model/Uppercase.LEAN: non-canonical source extension (expected `.lean`) -/
#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture [
  "model/Model.lean", "model/Model/Uppercase.LEAN"])

/-- error: source paths differ only in case: `model/Model/A.lean` and `model/Model/a.lean` -/
#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture [
  "model/Model/A.lean", "model/Model/a.lean"])

#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture [
  "model/Model.lean", "model/Model/Laws/areas-p5.lean", "model/Model/notes.txt",
  "Elements/Foundations/Superposition/Syntax.lean"])

/-- error: model/Model/Mixed.LeAn: non-canonical source extension (expected `.lean`) -/
#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture ["model/Model/Mixed.LeAn"])

/--
error: Elements/Foundations/Superposition/Syntax.lEaN: non-canonical source extension (expected `.lean`)
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture [
  "Elements/Foundations/Superposition/Syntax.lEaN"])

/-- error: model/Model.LEAN: non-canonical source extension (expected `.lean`) -/
#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture ["model/Model.LEAN"])

/--
error: source paths differ only in case: `model/Model/A.lean` and `model/Model/A.LEAN`
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture [
  "model/Model/A.lean", "model/Model/A.LEAN"])

/--
error: source paths differ only in case: `model/Model/Sub/A.lean` and `model/Model/sub/A.lean`
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture [
  "model/Model/Sub/A.lean", "model/Model/sub/A.lean"])

/--
error: source paths differ only in case: `Elements/Foundations/Superposition/Syntax.lean` and `Elements/Foundations/Superposition/syntax.lean`
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture [
  "Elements/Foundations/Superposition/Syntax.lean",
  "Elements/Foundations/Superposition/syntax.lean"])

/--
error: Elements/Foundations/Superposition/syntax.lean: non-canonical pure source path (expected `Elements/Foundations/Superposition/Syntax.lean`)
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelSourceListingFixture [
  "Elements/Foundations/Superposition/syntax.lean"])

/-! The compiled graph is checked separately from source headers. The real closure is
required to pass; planted closures need no compiled fixture files. -/

#guard_msgs in
run_cmd Check.Generator.checkModelImportClosure

#guard_msgs in
run_cmd (Check.Generator.checkModelImportClosureFixture
  #[`Model, `Model.Signature, `Elements.Foundations.Superposition.Syntax,
    `Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible,
    `LeanSearchClient, `ImportGraph, `ProofWidgets, `Cli]
  #[`Model, `Model.Signature])

/-- error: Model compiled import closure reaches `Check.Original`, outside the approved import roots -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportClosureFixture #[`Model, `Check.Original])

/--
error: Model compiled import closure reaches `Elements.Foundations.Words`, outside the approved import roots
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportClosureFixture #[`Model, `Elements.Foundations.Words])

/-- error: Model compiled import closure: non-canonical module name `Model.«..».Check.Original` -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportClosureFixture #[`Model, `Model.«..».Check.Original])

/-- error: Model source `Model.Unused` is not in the compiled import closure of `Model` -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportClosureFixture #[`Model, `Init] #[`Model, `Model.Unused])

#guard_msgs in
run_cmd Check.Generator.checkCanonicalModuleNames

/-- error: model/Model.lean: import `Model.«..».Check.Original` has a non-canonical module name -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model.lean", "import Model.«..».Check.Original\n")])

/--
error: Elements/Foundations/Superposition/Syntax.lean: import `Init.«/tmp/Elements/Foundations/Words»` has a non-canonical module name
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("Elements/Foundations/Superposition/Syntax.lean",
    "import Init.«/tmp/Elements/Foundations/Words»\n")])

#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model.lean",
    "import Model.Signature\nimport Mathlib\nimport Init\nimport Std\nimport Lean\n\
    import Plausible\nimport LeanSearchClient\nimport ImportGraph\nimport ProofWidgets\n\
    import Aesop\nimport Qq\nimport Batteries\nimport Cli\n"),
  ("model/Model/Planted.lean",
    "/- import Elements.Point /- nested -/ -/\nmodule\n\n\
    public /- between tokens -/ import Elements.Foundations.Superposition.Syntax\n\
    -- import Elements.Point\n\
    public meta import Elements.Foundations.Superposition.Semantics\n\
    import all Elements.Foundations.Superposition.Soundness\n\
    public import Elements.Foundations.Superposition.Restriction\n\
    public import Model.Laws.«areas-p5»\n\
    def body := \"import Elements.Point\"\nimport Elements.Point"),
  ("Elements/Foundations/Superposition/Syntax.lean",
    "module\nprelude\npublic import Init\nimport Init.Data.List.Basic\n\
    public import Elements.Foundations.Superposition.Semantics\n"),
  ("Elements/Foundations/Superposition/Semantics.lean",
    "import Elements.Foundations.Superposition.Syntax\n"),
  ("Elements/Foundations/Superposition/Soundness.lean",
    "import Elements.Foundations.Superposition.Semantics\n"),
  ("Elements/Foundations/Superposition/Restriction.lean",
    "import Elements.Foundations.Superposition.Soundness\n")])

/-- error: model/Model/Planted.lean: Model imports `Elements.Point`, outside the four pure modules -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model/Planted.lean", "import Elements.Point\n")])

/--
error: model/Model/Planted.lean: Model imports `Elements.Foundations.Words`, outside the four pure modules
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model/Planted.lean",
    "module\n\n/- header /- nested -/ comment -/\n\
    public /- comment -/ import\n  Elements.Foundations.Words\n")])

/-- error: model/Model.lean: Model imports `Elements`, outside the four pure modules -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model.lean", "module\npublic import Elements\n")])

/--
error: model/Model/Planted.lean: Model imports `Elements.Foundations.Superposition.Syntax.Extra`, outside the four pure modules
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model/Planted.lean",
    "import Elements.Foundations.Superposition.Syntax.Extra\n")])

/--
error: Elements/Foundations/Superposition/Syntax.lean: pure module imports `Elements.Foundations.Words`, outside the four pure modules and `Init`
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("Elements/Foundations/Superposition/Syntax.lean",
    "module\npublic import Elements.Foundations.Words\n")])

/--
error: Elements/Foundations/Superposition/Restriction.lean: pure module imports `Mathlib`, outside the four pure modules and `Init`
-/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("Elements/Foundations/Superposition/Restriction.lean", "import Mathlib\n")])

/-- error: model/Model.lean: Model imports `Check.Original`, outside the approved import roots -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model.lean", "import Check.Original\n")])

/-- error: model/Model/Planted.lean: Model imports `Staging.X`, outside the approved import roots -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model/Planted.lean", "module\npublic import Staging.X\n")])

/-- error: model/Model/Planted.lean: Model imports `Unknown.X`, outside the approved import roots -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model/Planted.lean", "module\nimport Unknown.X\n")])

/-- error: model/Model/Planted.lean: Model imports `Audit.X`, outside the approved import roots -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model/Planted.lean", "import Audit.X\n")])

/-- error: model/Model.lean: Model imports `Certificate.Facts`, outside the approved import roots -/
#guard_msgs in
run_cmd (Check.Generator.checkModelImportFixture [
  ("model/Model.lean", "module\npublic import Certificate.Facts\n")])
