"""A mechanical screen for docs/reports/overlaps.md.

For every statement in facts.json, Lean's `grind` tries a proof from
  - no rule at all (the bare try),
  - each axiom alone,
  - each family of axioms together (the module that declares them),
  - each pair of the rules about circles, and
  - each pair of families,
with every definition unfolded that a statement or a rule reaches. Each attempt with rules
is two tries, each a theorem with a budget of its own (BEATS): `grind` with the rules as it
chooses to use them, and `grind` forward from their hypotheses. A failed try falls back to
`sorry`, and only the tries that close without it are reported. A try that runs out of
time is tried again with RETRY times the budget, and one that runs out again is listed as
not searched to the end. A try that stops on any other error is listed so at once. A
statement that the bare try closes holds by its definitions and logic alone, so its other
tries say nothing of a rule: the screen lists it apart from the statements a rule closes.

The rules `grind` refuses. Given a rule in which it finds nothing to match, `grind`
refuses the whole list, and the try fails with no search at all. So a pass before the
attempts gives `grind` each rule alone, in each of the two ways, and each try leaves out
the rules refused in its way; a try left with none is not made. Refused both ways are the
seven rules that only say that a point, a straight line or a circle exists (Postulates 1 to
3, the three `exists_point` rules the second axiom retirement leaves, and `exists_centre`,
which the pass's two cases, tried alone on 21 October 2026, found refused); refused forward
as well are thirteen with no hypothesis `grind` can start from (`len_symm`, `add_comm` and
the like), plus the restricted superposition rule, whose conclusion is the structure
`Superposition.Rule`. Such a rule gives
`grind` nothing to work with in any case (see below); but while it stayed in, as in the
families Postulates and Constructions and every pair with either, the try searched with
none of its other rules.

What is unfolded. Before the attempts, a pass over facts.json's statements and its axioms
lists every definition of the edition that their types reach, through the bodies of other
definitions (Triangle reaches Collinear; Rectangle reaches Parallelogram, AreParallel and
Parallel; Apart.area reaches Magnitude.sum), and the screen stops if one is in none of the
lists below. The definitions Lean makes for itself, to compile a definition by cases or by
recursion (`InOrder.match_1`, `segments._f`), and the fields of a structure
(`Apart.pieces`), are followed but not listed: the first are unfolded with the definition
they serve, and `grind` reads a field as it is. Each listed definition is given to `grind`
in one of three ways.
  - DEFS, the phrases (SameSideOf, Triangle, Collinear, Parallelogram, ...) and the words
    that say "any number" (the points in order of II.1, `InOrder`, with its `segments` and
    `endOf`; I.45's `triples`; the sum of a list, `Magnitude.sum`, and the areas of a figure
    given with its triangles, `Rectilineal.area` and `Apart.area`): unfolded to their
    bodies, those defined by cases or by recursion one case at a time, by the equations
    Lean proves for them. The restricted rule's `primitives` interpretation is unfolded
    here too: it assigns the edition's words to the pure calculus's fields.
  - CHOSEN, the magnitudes Lean chooses (`circumference`, `standing`, `rect`) and the
    order "not greater": by what the definition says of them and nothing more, as a lemma
    proved from Lean's choice alone (`Classical.epsilon_spec`), in the preamble of every
    file. Unfolded to `Classical.epsilon` alone, a chosen magnitude gives `grind` nothing to
    reason with. What the lemma leaves out stays unsearched: that two descriptions choose
    the same magnitude when they hold of the same things, and, for `circumference` and
    `standing`, that every point of the circle gives the same angle, which is III.21 (so a
    statement whose proof needs it, as the catalogue's near misses of the measure do, is
    not found here, and is not a rule's overlap).
  - CARRIERS, the kinds of magnitude and their sum, order and zero: the words the axioms
    are stated in, left as they are.
A word that names a new kind of thing, with rules of formation of its own, is not an
abbreviation to unfold, and the pass does not list it: the figure of triangles fitted
together (`Fitted`, defined by induction), and the figures given with their triangles
(`Rectilineal`, `Apart`, structures). `grind` takes them as they are: it does not reason by
induction on `Fitted`, and draws on a figure's fields only where a rule or the goal names
them. So a companion of I.45 or II.14 whose proof needs that is not found here.
The restricted superposition rule is also a structure, `Superposition.Rule`. Its field
requires a represented derivation; `grind` does not build that derivation or open the
field of itself. Unfolding `primitives` supplies its interpretation, not placement
witnesses or an existential substitute for the rule.
Every file of tries begins by proving a few goals that `grind` closes only so (CONTROLS),
so a screen that has stopped unfolding stops, and ends with a line that Lean prints (END),
so a Lean process that stopped early is not read as tries that closed.

It is a screen, not a proof search. `grind` instantiates rules among the terms already in
a goal; it does not draw a new circle or lay down a triangle. The former superposition
shortcuts for I.2, I.3 and I.23 are retired: the restricted rule returns no placement
witnesses. The former I.7 overlap used Circle 4, now a corollary of I.7 and no longer an
axiom in this screen; deriving I.7 through it is circular.

The statements are facts.json's entries: the propositions, the porisms and the companions.
At commit d040117, with only the phrases SameSideOf to LinesMeet unfolded, both tries in
one budget and no rule left out, 40,698 attempts over the 99 propositions and the three
porisms closed III.2, III.5 and III.6, and nothing else. Run again on the statements of
1caff82, with every definition unfolded, each try in its own budget and the refused rules
left out, they closed the same three. Run on the statements of 89c5da4, the 99
propositions, the three porisms and the 19 companions, with a bare try for each, the
48,400 attempts made 90,629 tries (6,050 were left with no rule) and closed the same
three, each by a rule; no statement closed bare. 175 tries ran out of time and were tried
again; 7 ran out again, all of them III.34 from Postulate 4, alone or with Postulate 5 and
at most one more family, as on 1caff82. III.34 asks for three points on its circle, and
the rules among those that put a point on a circle that has none need a straight line,
which III.34 does not give and none of those rules draws. III.2 closes by Circle 2 with
Generalities 4 (`inside_not_on`), and by the diagram rules together, but not by Circle 2
alone: `grind` tries Circle 2 only on points of which the goal asks whether they are
within the circle, and III.2 asks that only of E, until Generalities 4 brings in A and B.

On 19 October 2026 the screen was run on the centre restatements of brief 0008's step 6,
with fresh certificates at commit b260c826 and Tacit.exists_centre added to CIRCLE. It used
the screen as it then stood on that branch,
which gave both tries one budget, unfolded only the phrases, made no bare try and left no
rule out, over 88 axioms, 25 of them in CIRCLE: 135 statements (99 propositions, three
porisms and 33 companions), 424 attempts each, 57,240 in all. Eleven
attempts closed: seven for III.2, three for III.5 and one for III.6, with no other
statement closing. No pair containing Tacit.exists_centre closed; but `grind` refuses
that rule (above), so on that screen its single try and every pair with it searched with
none of their rules, and the result says nothing of the rule. Of the remaining
attempts, 57,196 fell back to sorry and 33 timed out at the 30,000-heartbeat limit.
docs/reports/overlaps.md lists every closing and its rules. III.5 from the Magnitudes and
Transfer families uses only Tacit.len_lt_of_inside, Tacit.lt_irrefl and Tacit.lt_trans,
besides Lean's logical axioms: an uncatalogued candidate route already found by an
earlier 51,600-attempt run, which also closed eleven attempts on these three
propositions. No catalogue row is added by the screen.

That run is no longer a true account of this screen. Axiom wave one (19 October 2026)
had not reached that branch: it made eight rules theorems, five of them rules about
circles, the second axiom retirement made 31 more, nine of them rules about circles, and
the third (24 October 2026) made Circle 3 (Tacit.outside_of_between) a theorem, proved
after III.2, and the fourth (26 October 2026) made Circle 1 (Tacit.between_of_inside_chord)
a theorem, proved after III.2 as well; all sixteen have left CIRCLE. The screen tries the
48 axioms of the certificate, 9 of them in CIRCLE with Tacit.exists_centre, and it
unfolds, budgets and leaves out rules as described above. III.2 closed by Circle 2 in the
runs on 89c5da4 and on 19 October, and Circle 2 is one of wave one's eight.

Run on the statements of 58018a3 (21 October 2026), the second axiom retirement's before
train C6a was merged into it, the 15,860 attempts over the 122 statements made 28,060 tries
(3,538 were left with no rule) and closed III.5 alone, by Diagram-segment 2 (`circle_eq`):
alone, paired with each other rule about circles, and in its family, Transfer, alone or
with any other family; no statement closed bare. 8 tries ran out of time again, all of
them III.34 from Postulate 4, as before. III.2 and III.6 no longer closed: the rules that
closed them, Circle 2 and Generalities 4 for III.2 and Generalities 3 for III.6, are
theorems now, with others of the diagram rules, and the screen tries only axioms. Their
rows in the catalogue rest on their audit lemmas, `Audit.III_2` and `Audit.III_6`. That
run read III.5 and III.6 as they were stated before brief 0008 restated them (cutting as
crossing, contact within with a point within).
On this revision, which holds the restated readings, Generalities 4 is a theorem, so the
screen, which tries axioms alone, no longer closes the restated III.5, which needs that
rule to finish: `circle_eq` makes the two circles one, and only Generalities 4
(`inside_not_on`) then contradicts F being both within that circle and on it. A scratch
run of III.2, III.5 and III.6, by a copy of the screen kept to them, closed none of 690
tries. The screen checks that the rows of KNOWN, below, still close by a rule, and says so
when one does not. KNOWN still names III.5, and is stale until a check change gives the
screen a new canary, tracked in issue #160. And, already on main, the screen cannot
run until DEFS takes the 18 words train C6a introduced, so the run on the restated
readings is still to be made: its pass over the definitions stops on them, for none of
the lists below names them (also in issue #160). They are `Arc.Congruent`,
`Arc.Drawn`, `Arc.measure`, `InSegment`, `LocallyLess`, `LocallyWithin`,
`MixedAngle.Exceeds`, `MixedAngle.FallsShort`, `MixedAngle.WellFormed`,
`MixedAngle.casesOn`, `MixedAngle.region`, `MixedAngle.vertex`, `NearVertexOpen`, `OnArc`,
`OnSideOrLine`, `Places`, `Surrounds` and `WithinAngle`.
No run of this screen on the restated statements is recorded here.

usage (from the repository root, after `lake build`):
    python3 -I Audit/screen.py OUTDIR [--jobs N] [--write]
    python3 -I Audit/screen.py --check-current

It writes its Lean files and logs to OUTDIR, which must be outside the repository. Each
job is one Lean process on one thread, so N jobs keep N cores busy. It takes about an hour
and a half of processor time: some eight minutes with twelve jobs on an idle machine.
Every try imports what `lake build` built, not the sources. So a run reads the commit and
its inputs, checks with `lake build --no-build Elements` that the build is current, and
reads them again before any Lean runs. Before --write records a completed run, it checks
the build again, after every try and retry, and reads the commit and the inputs again. It
stops if either build check fails, or if the commit or the inputs changed around one of
those checks, and a record names what it read first. Checks at the two ends of a run
cannot show that nothing changed and changed back in between.
Standard library only. Its cases, which need no Lean, are in tests/test_screen.py.

What a run read. With --write, a run that ends with every known row closed by a rule
records, in Audit/screen-run.toml (RECORD), the one file it writes in the repository, the
commit, the number of statements in facts.json, and a sha256 of each part of what decides
its result, and of them all. That is more than the statements and the rules: every file of
tries imports Elements, so the library's notation, in which SPECS and CONTROLS are
written, and its instances count too (`grind`'s AC solver looks for `Std.Associative` and
`Std.Commutative`, which Elements/Figure/Areas.lean gives the sum of magnitudes). So the
parts are facts.json's statements (name, reference, kind and statement), its rules
(modules and statements) and its words (`vocabulary`); every Lean file of the library; the
toolchain's files; and this file without this docstring, which records the run and so is
written after it, with any other Python module under Audit/, which a run without -I could
import in place of a standard one. An ignored file among the input files counts, and the
inputs are then not a commit's; ignored files outside the input paths and modules
under __pycache__ do not count. No input file or its directory may be a symbolic link,
since Git commits the link and the run would read its target. --write records only a run on
a commit's inputs as committed, and stops before the run otherwise. `--check-current`
refuses a record that does not name a commit's 40 hex digits in that state, computes the
parts again, without Lean, and exits 1 when the record is missing, the inputs differ,
matching inputs are not committed, or an input path is a symbolic link. It names each part
that changed. The run needs Lean and takes the time above, so this is a release step
(docs/WORKFLOW.md, section 10, step 10), not one of CI's checks. The record is written only
by a run, never by hand. `--check-current` reads the record, not the run: a record written
by hand, or by `write_record` with no run, passes it, and the record holds only hashes. The
run's closing lines, quoted in the release's pull request, are its evidence.
"""

import argparse
import ast
import datetime
import hashlib
import itertools
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# What a run read (see "What a run read" above): the record, and the files it pins beside
# facts.json and this file. Lake reads lakefile.lean in preference to lakefile.toml, so an
# absent toolchain file is recorded as absent. A module under Audit/, by these endings,
# could be imported in place of a standard one by a run without -I, so each is pinned too.
RECORD = ROOT / "Audit" / "screen-run.toml"
SCREEN = "Audit/screen.py"
LIBRARY = ("Elements.lean", "Elements")
TOOLCHAIN = ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json")
MODULES = (".py", ".pyc", ".pyd", ".so")
INPUTS = ("facts.json", *LIBRARY, *TOOLCHAIN, *[f"Audit/*{m}" for m in MODULES])   # for git
COMMITTED = "inputs as committed"   # the state of a record --check-current accepts
PARTS = {
    "statements": "the statements in facts.json",
    "rules": "the rules in facts.json (axiom_modules and axiom_types)",
    "words": "the words the statements and the rules reach (facts.json's vocabulary)",
    "library": "the library's Lean files (Elements.lean and Elements/), which the tries import",
    "toolchain": f"the toolchain's files ({', '.join(TOOLCHAIN)})",
    "screen": "Audit/screen.py, apart from its docstring, and any other Python module under "
              "Audit/",
}

# Rules that speak of circles: the pairs among these are screened against every statement.
CIRCLE = """Definition15 Postulate3 Tacit.exists_centre
Tacit.circles_meet Tacit.line_circle_between Tacit.line_circle_beyond
Tacit.circles_meet_same_side Tacit.exists_point_inside_circle Tacit.circle_eq""".split()

# The phrases, and the words for "any number", unfolded in every attempt.
DEFS = """SameSideOf OppositeSidesOf OppositeSides OutsideCircle CirclesMeet CirclesCut
LineMeetsCircle CirclesTouch TouchesInternally TouchesExternally Touches LinesMeet Collinear
Triangle OnRay InsideTriangle Equilateral IsRightAngle IsObtuse IsAcute Square Parallel
AreParallel Parallelogram Rectangle EqualCircles Contain quadArea sq InOrder segments endOf
triples Magnitude.sum Rectilineal.area Apart.area primitives""".split()

# The chosen magnitudes, and the order "not greater", each given by its lemma in SPECS.
CHOSEN = {"circumference": "Screen.circumference_spec", "standing": "Screen.standing_spec",
          "rect": "Screen.rect_spec", "instLEMagnitude": "Screen.le_iff"}

# The words the axioms are stated in, left as they are.
CARRIERS = """Magnitude Length Angle Area instAddMagnitude instLTMagnitude
instOfNatMagnitudeOfNatNat""".split()

# The rows of the catalogue the screen is to find, each by a rule: a screen that misses one
# reports itself broken. III.2 and III.6 left with the second axiom retirement, which made
# the rules that closed them theorems. III.5 is stale on this revision: the restated III.5
# needs Generalities 4, a theorem now, and the screen tries axioms alone, so it no longer
# closes. It stays until a check change gives the screen a new canary (issue #160).
KNOWN = ["BookIII.Prop5"]

# What each chosen definition says, proved from Lean's choice alone; nothing else.
SPECS = """namespace Screen
open Elements

/-- `circumference`: given a point of the circle on the other side of BC from K, the
measure is twice the angle BXC at some such point X. -/
theorem circumference_spec {α : Circle} {A B K C : Point} (hA : OnCircle A α)
    (h : OppositeSidesOf A K B C) :
    ∃ X, OnCircle X α ∧ OppositeSidesOf X K B C ∧ circumference α B K C = ∠ B X C + ∠ B X C :=
  Classical.epsilon_spec
    (p := fun x => ∃ X, OnCircle X α ∧ OppositeSidesOf X K B C ∧ x = ∠ B X C + ∠ B X C)
    ⟨_, A, hA, h, rfl⟩

/-- `standing`: given a point of the circle on A's side of BC, the measure is twice the
angle BYC at some such point Y. -/
theorem standing_spec {α : Circle} {X B A C : Point} (hX : OnCircle X α)
    (h : SameSideOf X A B C) :
    ∃ Y, OnCircle Y α ∧ SameSideOf Y A B C ∧ standing α B A C = ∠ B Y C + ∠ B Y C :=
  Classical.epsilon_spec
    (p := fun x => ∃ Y, OnCircle Y α ∧ SameSideOf Y A B C ∧ x = ∠ B Y C + ∠ B Y C)
    ⟨_, X, hX, h, rfl⟩

/-- `rect`: if AB and CD contain some area, the rectangle contained by them is one. -/
theorem rect_spec {A B C D : Point} {x : Area} (h : Contain ‖A B‖ ‖C D‖ x) :
    Contain ‖A B‖ ‖C D‖ (rect A B C D) :=
  Classical.epsilon_spec ⟨x, h⟩

/-- `≤`: "not greater". -/
theorem le_iff {k : Kind} {a b : Magnitude k} : a ≤ b ↔ ¬ b < a := Iff.rfl

end Screen

"""

# Each try's budget, in thousands of heartbeats; a try that runs out has RETRY times as much.
BEATS = 30000
RETRY = 4

# The two ways a try gives `grind` its rules: the end of the try's name, and the mark
# before each rule.
MODES = {"": "", "__forward": "→ "}

# The last line of every file the screen writes: Lean prints it only if it got that far.
END = "screen: end of file"

UNFOLD = ", ".join([f"Elements.{d}" for d in DEFS] + list(CHOSEN.values()))

# Goals that `grind` closes only with the definitions unfolded and the lemmas given: the
# preamble of every file proves them, so a screen that unfolds nothing stops.
CONTROLS = [
    "∀ {A B C : Point} {L : Line}, Triangle A B C → OnLine A L → OnLine B L → ¬ OnLine C L",
    "∀ {A B C : Point} {L : Line}, OnLine A L → OnLine B L → OnLine C L → Collinear A B C",
    "∀ {α : Circle} {A B K C E F G : Point}, OnCircle A α → OppositeSidesOf A K B C → "
    "(∀ X, OnCircle X α → OppositeSidesOf X K B C → ∠ B X C = ∠ E F G) → "
    "circumference α B K C = ∠ E F G + ∠ E F G",
    "∀ {α : Circle} {A B X C E F G : Point}, OnCircle X α → SameSideOf X A B C → "
    "(∀ Y, OnCircle Y α → SameSideOf Y A B C → ∠ B Y C = ∠ E F G) → "
    "standing α B A C = ∠ E F G + ∠ E F G",
    "∀ {A B : Point} {x : Area}, Contain ‖A B‖ ‖A B‖ x → Contain ‖A B‖ ‖A B‖ (sq A B)",
    "∀ {a b : Angle}, a < b → ¬ b ≤ a",
    "∀ {A B C : Point}, InOrder [A, B, C] → Between A B C",
    "∀ {A B C : Point}, segments [A, B, C] = [(A, B), (B, C)]",
    "∀ {A B C : Point}, endOf A [B, C] = C",
    "∀ {A B C : Point}, triples [A, B, C] = [(A, B, C)]",
    "∀ {a b : Length}, Magnitude.sum [a, b] = a + (b + 0)",
    "∀ {R : Rectilineal}, R.area = Magnitude.sum (R.pieces.map fun t => △ t.1 t.2.1 t.2.2)",
    "∀ {R : Apart}, R.area = Magnitude.sum (R.pieces.map fun t => △ t.1 t.2.1 t.2.2)",
]

HEAD = ("import Elements\nopen Elements Elements.Tacit\nset_option maxErrors 1000000\n\n"
        + SPECS
        + "".join(f"example : {g} := by\n  intros\n  grind [{UNFOLD}]\n\n" for g in CONTROLS))

# The pass before the attempts: every definition of the edition that the roots' types
# reach, through the bodies of definitions; and every listed name the edition lacks. The
# definitions Lean makes for itself (a name with a part that begins `_`, as `segments._f`;
# the matchers, as `InOrder.match_1`) and the fields of structures are followed, not listed.
REACH = """import Lean
import Elements
open Lean

run_cmd do
  let env ← getEnv
  let roots : Array Name := #[ROOTS]
  let listed : Array Name := #[LISTED]
  for n in roots ++ listed do
    if (env.find? n).isNone then Lean.logInfo m!"screen-unknown {n}"
  let mut todo : Array Name := #[]
  for n in roots do
    if let some ci := env.find? n then todo := todo ++ ci.type.getUsedConstants
  let mut seen : NameSet := {}
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some (ConstantInfo.defnInfo d) := env.find? n then
      if (`Elements).isPrefixOf n then
        unless n.isInternal || Meta.isMatcherCore env n || env.isProjectionFn n do
          Lean.logInfo m!"screen-def {n}"
        todo := todo ++ d.value.getUsedConstants ++ d.type.getUsedConstants

""" + f'#print "{END}"\n'


# The kinds of attempt, each the start of a try's name; the bare try has no rules.
KINDS = ("bare", "single", "family", "pair", "fampair")

# An error in Lean's log, after the file, line and column: Lean may name the kind of error
# after the word (`error(lean.unknownIdentifier): ...`), or not (`error: ...`). The message
# is the group.
ERROR = r"error(?:\([^)\s]*\))?: (.*)"


def ident(s: str) -> str:
    return re.sub(r"\W", "_", s)


def attempts(facts: dict) -> list[tuple[str, str, list[str]]]:
    """Each attempt: its name, the statement, and the rules. The bare attempt, with no rules,
    comes first for each statement."""
    decls = [e["name"] for e in facts["propositions"]]
    axioms = sorted(facts["axiom_modules"])
    missing = [c for c in CIRCLE if c not in facts["axiom_modules"]]
    if missing:
        sys.exit(f"screen: no such axioms in facts.json: {missing}")
    families: dict[str, list[str]] = {}
    for ax, module in facts["axiom_modules"].items():
        families.setdefault(module.split(".")[-1], []).append(ax)
    jobs = []
    for d in decls:
        jobs.append((f"bare__{ident(d)}", d, []))
        for ax in axioms:
            jobs.append((f"single__{ident(d)}__{ident(ax)}", d, [ax]))
        for fam in sorted(families):
            jobs.append((f"family__{ident(d)}__{fam}", d, sorted(families[fam])))
        for a, b in itertools.combinations(CIRCLE, 2):
            jobs.append((f"pair__{ident(d)}__{ident(a)}__{ident(b)}", d, [a, b]))
        for f, g in itertools.combinations(sorted(families), 2):
            jobs.append((f"fampair__{ident(d)}__{f}__{g}", d,
                         sorted(families[f] + families[g])))
    return jobs


def refusal_cases(axioms: list[str]) -> tuple[list[tuple[str, str]], str]:
    """The pass over the rules: each rule alone, in each way (MODES), for a goal `grind`
    closes at once, so that an error is a refusal; and the Lean file that tries them. Two
    lines of header, then three lines a case: the case k starts on line 3 + 3k."""
    cases = [(mode, ax) for ax in sorted(axioms) for mode in MODES]
    text = ("import Elements\n\n"
            + "".join(f"example (h : False) : False := by\n"
                      f"  grind [{MODES[mode]}Elements.{ax}]\n\n" for mode, ax in cases)
            + f'#print "{END}"\n')
    return cases, text


def refusals(cases: list[tuple[str, str]], name: str, log: str) -> dict[str, set[str]]:
    """Read the pass over the rules: for each way, the rules `grind` refused. Stop if Lean
    did not reach the end of the file, or if any error is not a refusal of the rule."""
    if END not in log:
        sys.exit("screen: the pass over the rules stopped early (see Refused.log)")
    found: dict[str, set[str]] = {mode: set() for mode in MODES}
    for m in re.finditer(rf"{re.escape(name)}:(\d+):\d+: {ERROR}", log):
        k = (int(m.group(1)) - 3) // 3
        if not 0 <= k < len(cases) or not re.search(
                r"invalid `grind`|failed to find patterns", m.group(2)):
            sys.exit(f"screen: the pass over the rules failed at line {m.group(1)}: "
                     f"{m.group(2)} (see Refused.log)")
        found[cases[k][0]].add(cases[k][1])
    return found


def refused(facts: dict, out: Path) -> dict[str, set[str]]:
    """The rules `grind` refuses, for each way of giving them (MODES)."""
    cases, text = refusal_cases(list(facts["axiom_modules"]))
    path = out / "Refused.lean"
    path.write_text(text)
    run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True,
                         text=True)
    log = run.stdout + run.stderr
    (out / "Refused.log").write_text(log)
    found = refusals(cases, path.name, log)
    for mode, way in (("", "as it chooses"), ("__forward", "forward")):
        print(f"grind refuses {len(found[mode])} rules given {way}, left out of those "
              f"tries: {', '.join(sorted(found[mode]))}")
    return found


def tries(jobs: list[tuple[str, str, list[str]]],
          refuse: dict[str, set[str]]) -> dict[str, tuple[str, str]]:
    """Each attempt with rules is two tries, each a theorem with a budget of its own:
    `grind` with the rules as it chooses to use them, and `grind` forward from their
    hypotheses, each without the rules `grind` refuses in its way; a try left with no rule
    is not made. The bare attempt is one try, with no rule. A try maps to its statement and
    what `grind` is given."""
    out = {}
    for name, decl, rules in jobs:
        if not rules:
            out[name] = (decl, "")
            continue
        for mode, mark in MODES.items():
            given = [r for r in rules if r not in refuse[mode]]
            if given:
                out[name + mode] = (decl, ", ".join(f"{mark}Elements.{r}" for r in given))
    return out


def theorem(name: str, decl: str, given: str, beats: int) -> str:
    rules = f"{given}, " if given else ""
    return (f"set_option maxHeartbeats {beats} in\n"
            f"theorem {name} : type_of% @Elements.{decl} := by\n"
            f"  intros\n"
            f"  first\n"
            f"  | grind [{rules}{UNFOLD}]\n"
            f"  | sorry\n\n")


def reach_file(facts: dict) -> str:
    """The pass over the definitions, for the statements and the rules."""
    roots = [e["name"] for e in facts["propositions"]] + sorted(facts["axiom_modules"])
    listed = DEFS + list(CHOSEN) + CARRIERS
    return (REACH.replace("ROOTS", ", ".join(f"`Elements.{n}" for n in roots))
                 .replace("LISTED", ", ".join(f"`Elements.{n}" for n in listed)))


def definitions(log: str, ok: bool) -> set[str]:
    """Read the pass over the definitions: the definitions reached. Stop if Lean did not
    reach the end of the file or failed, if a listed name or a root is not the edition's,
    if nothing was reached, or if a definition reached is in none of the lists."""
    if END not in log:
        sys.exit("screen: the pass over the definitions stopped early (see Reach.log)")
    unknown = re.findall(r"screen-unknown Elements\.(\S+)", log)
    found = set(re.findall(r"screen-def Elements\.(\S+)", log))
    if not ok or unknown or not found:
        sys.exit("screen: the pass over the definitions failed (see Reach.log)"
                 + (f"; not in the edition: {unknown}" if unknown else ""))
    unlisted = sorted(found - set(DEFS + list(CHOSEN) + CARRIERS))
    if unlisted:
        sys.exit(f"screen: a statement or a rule reaches {unlisted}, which the screen does "
                 "not unfold: add each to DEFS, or to CHOSEN with its lemma in SPECS")
    return found


def reached(facts: dict, out: Path) -> None:
    """Stop unless every definition the statements and the rules reach is in DEFS, CHOSEN
    or CARRIERS, and every name listed there is the edition's."""
    path = out / "Reach.lean"
    path.write_text(reach_file(facts))
    run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True,
                         text=True)
    log = run.stdout + run.stderr
    (out / "Reach.log").write_text(log)
    found = definitions(log, run.returncode == 0)
    print(f"{len(found)} definitions reached: {len(found & set(DEFS))} unfolded, "
          f"{len(found & set(CHOSEN))} given by their lemmas, "
          f"{len(found & set(CARRIERS))} left as they are")


def outcomes(name: str, text: str, log: str) -> tuple[int, list[str], list[str], list[str]]:
    """The tries in a file of tries (its name and text, and Lean's log of it): how many,
    those that closed, those that ran out of time, and those that stopped on any other
    error (the limit of recursion, the kernel refusing a proof). A try runs from its
    `set_option` line to the next try's; Lean reports its errors, and its `sorry`, at its
    `theorem` line or below."""
    lines = text.splitlines()
    starts = [(i + 1, m.group(1)) for i, line in enumerate(lines)
              if (m := re.match(rf"theorem ((?:{'|'.join(KINDS)})__\S+) :", line))]
    if END not in log:
        sys.exit(f"screen: Lean stopped before the end of {name} (see the log)")
    bad = {int(m.group(1)) for m in re.finditer(
        rf"{re.escape(name)}:(\d+):\d+: (error|warning: declaration uses)", log)}
    slow, stop = set(), set()
    for m in re.finditer(rf"{re.escape(name)}:(\d+):\d+: {ERROR}", log):
        timeout = re.match(r"\(deterministic\) timeout|\(kernel\) deterministic timeout",
                           m.group(2))
        (slow if timeout else stop).add(int(m.group(1)))
    first = starts[0][0] - 1 if starts else len(lines) + 1
    if any(b < first for b in bad):
        sys.exit(f"screen: the preamble of {name} does not compile: a lemma of SPECS, or a "
                 "goal of CONTROLS that the definitions unfolded should close (see the log)")
    closed, timed_out, stopped = [], [], []
    for k, (start, try_name) in enumerate(starts):
        begin = start - 1
        end = starts[k + 1][0] - 1 if k + 1 < len(starts) else len(lines) + 1
        if any(begin <= b < end for b in slow):
            timed_out.append(try_name)
        elif any(begin <= b < end for b in stop):
            stopped.append(try_name)
        elif not any(begin <= b < end for b in bad):
            closed.append(try_name)
    return len(starts), closed, timed_out, stopped


def run(todo: dict[str, tuple[str, str]], beats: int, out: Path, stem: str,
        jobs: int) -> tuple[int, list[str], list[str], list[str]]:
    """Run the tries `todo` with the budget `beats`, in `jobs` Lean processes of one thread
    each: how many were read back, and those that closed, ran out of time, or stopped on
    another error."""
    names = list(todo)
    files = []
    for k in range(min(jobs, len(names))):
        path = out / f"{stem}{k}.lean"
        path.write_text(HEAD + "".join(theorem(n, *todo[n], beats) for n in names[k::jobs])
                        + f'#print "{END}"\n')
        files.append(path)
    procs = [(f, subprocess.Popen(["lake", "env", "lean", "--threads=1", str(f)], cwd=ROOT,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True))
             for f in files]
    total, closed, timed_out, stopped = 0, [], [], []
    for f, p in procs:
        log, _ = p.communicate()
        (out / f"{f.stem}.log").write_text(log)
        n, ok, slow, stop = outcomes(f.name, f.read_text(), log)
        total += n
        closed += ok
        timed_out += slow
        stopped += stop
    return total, closed, timed_out, stopped


def statement_of(try_name: str) -> str:
    """The statement a try is about, as `ident` writes it: the part of its name after the
    kind."""
    return try_name.split("__")[1]


def refs(facts: dict, hit: set[str]) -> list[str]:
    """The references of the statements `hit`, as `ident` writes them, in facts.json's
    order."""
    return [e["ref"] for e in facts["propositions"] if ident(e["name"]) in hit]


def statements(facts: dict, names: list[str]) -> list[str]:
    """The references of the statements that the tries `names` are about."""
    return refs(facts, {statement_of(n) for n in names})


def by_rule(closed: list[str]) -> tuple[set[str], set[str]]:
    """The statements the bare try closes, and those that only a try with rules closes."""
    bare = {statement_of(n) for n in closed if n.startswith("bare__")}
    ruled = {statement_of(n) for n in closed if not n.startswith("bare__")} - bare
    return bare, ruled


def lost(closed: list[str]) -> list[str]:
    """The rows of KNOWN that no try with rules closed, or that the bare try closed."""
    _, ruled = by_rule(closed)
    return [d for d in KNOWN if ident(d) not in ruled]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value) -> bytes:
    """A value of facts.json as bytes that do not depend on the order of its keys."""
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode()


def files_digest(root: Path, paths: list[str], read=Path.read_bytes) -> str:
    """The sha256 of these files, each by its path and its bytes, or as absent."""
    h = hashlib.sha256()
    for rel in paths:
        p = root / rel
        data = read(p) if p.is_file() else None
        h.update(rel.encode() + b"\0"
                 + (b"absent" if data is None else str(len(data)).encode() + b"\0" + data)
                 + b"\0")
    return h.hexdigest()


def library_files(root: Path) -> list[str]:
    """Every Lean file that `import Elements` reads: the root and those under Elements/."""
    return [LIBRARY[0]] + sorted(p.relative_to(root).as_posix()
                                 for p in (root / LIBRARY[1]).rglob("*.lean"))


def screen_files(root: Path) -> list[str]:
    """This file, then every other Python module under Audit/, outside __pycache__."""
    return [SCREEN] + sorted(
        rel for p in (root / "Audit").rglob("*") if p.suffix in MODULES
        and "__pycache__" not in p.parts and (rel := p.relative_to(root).as_posix()) != SCREEN)


def without_docstring(text: str) -> str:
    """A Python file's text without its docstring, which the screen's run records, so it is
    written after the run. Code on the docstring's last line keeps the whole text."""
    body = ast.parse(text).body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) \
            and isinstance(body[0].value.value, str):
        if len(body) > 1 and body[1].lineno <= body[0].end_lineno:
            return text
        lines = text.splitlines(keepends=True)
        return "".join(lines[:body[0].lineno - 1] + lines[body[0].end_lineno:])
    return text


def inputs(root: Path, facts: dict) -> dict[str, str]:
    """What decides a run, part by part (PARTS), each as a sha256."""
    statements = sorted(({k: e.get(k) for k in ("name", "ref", "kind", "statement")}
                         for e in facts["propositions"]), key=lambda e: e["name"])
    screen = root / SCREEN
    return {
        "statements": sha(canonical(statements)),
        "rules": sha(canonical({"modules": facts["axiom_modules"],
                                "types": facts.get("axiom_types")})),
        "words": sha(canonical(facts.get("vocabulary"))),
        "library": files_digest(root, library_files(root)),
        "toolchain": files_digest(root, list(TOOLCHAIN)),
        "screen": files_digest(root, screen_files(root), lambda p: without_docstring(
            p.read_text(encoding="utf-8")).encode() if p == screen else p.read_bytes()),
    }


def total(parts: dict[str, str]) -> str:
    """The sha256 of all the parts together."""
    return sha(canonical(parts))


def git(*args: str, root: Path = ROOT) -> str | None:
    try:
        p = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True)
    except OSError:
        return None
    return p.stdout.strip() if p.returncode == 0 else None


def input_paths(root: Path) -> list[str]:
    """The file paths whose contents `inputs` reads when they exist."""
    return ["facts.json", *library_files(root), *TOOLCHAIN, *screen_files(root)]


def input_symlinks(root: Path) -> list[str]:
    """Symbolic links among input files or their directory components."""
    found = set()
    for rel in ("facts.json", LIBRARY[0], LIBRARY[1], *TOOLCHAIN, "Audit", SCREEN):
        path = root
        for part in Path(rel).parts:
            path /= part
            if path.is_symlink():
                found.add(path.relative_to(root).as_posix())
                break
    for rel, excluded, suffixes in ((LIBRARY[1], set(), {".lean"}),
                                    ("Audit", {"__pycache__"}, set(MODULES))):
        base = root / rel
        if base.is_symlink() or not base.is_dir():
            continue
        for directory, dirs, files in os.walk(base, followlinks=False):
            dirs[:] = [name for name in dirs if name not in excluded]
            for name in list(dirs):
                path = Path(directory) / name
                if path.is_symlink():
                    found.add(path.relative_to(root).as_posix())
                    dirs.remove(name)
            for name in files:
                path = Path(directory) / name
                if path.is_symlink() and (not path.exists() or path.suffix in suffixes):
                    found.add(path.relative_to(root).as_posix())
    return sorted(found)


def revision(root: Path) -> tuple[str, str]:
    """The commit checked out, and whether the inputs are as it has them (COMMITTED)."""
    commit = git("rev-parse", "HEAD", root=root) or "unknown"
    links = input_symlinks(root)
    if links:
        return commit, "input paths include symbolic links: " + ", ".join(links)
    status = git("status", "--porcelain", "--", *INPUTS, root=root)
    ignored = git("status", "--porcelain", "--ignored=matching", "--untracked-files=all",
                  "--", *input_paths(root), root=root)
    state = ("unknown" if status is None or ignored is None else
             "inputs differ from this commit" if status or ignored else COMMITTED)
    return commit, state


def record_text(parts: dict[str, str], commit: str, state: str, count: int) -> str:
    """The record of a run, as --write writes it."""
    return "\n".join([
        "# What Audit/screen.py last ran on: written by",
        "# `python3 -I Audit/screen.py OUTDIR --write` when a run ends with every known row",
        "# closed by a rule, never by hand. `python3 -I Audit/screen.py --check-current`",
        "# compares it with the inputs now (docs/WORKFLOW.md, section 10).",
        f'commit = "{commit}"',
        f'state = "{state}"',
        f"statements = {count}",
        f'date = "{datetime.date.today().isoformat()}"',
        f'inputs = "{total(parts)}"',
        "",
        "[parts]",
        *[f'{k} = "{v}"' for k, v in parts.items()],
    ]) + "\n"


def write_record(root: Path, read: dict[str, str], count: int, path: Path = RECORD, *,
                 at: tuple[str, str]) -> None:
    """Record what the run read, at the commit and state `revision` gave when it read them,
    unless its inputs or that commit changed while it ran, or they are not a commit's;
    through a new file renamed over the record, which is never a symbolic link."""
    if links := input_symlinks(root):
        sys.exit("screen: input paths include symbolic links, so nothing is recorded: "
                 + ", ".join(links))
    facts = json.loads((root / "facts.json").read_text(encoding="utf-8"))
    moved = [k for k, v in inputs(root, facts).items() if read[k] != v]
    if moved:
        sys.exit("screen: its inputs changed while it ran, so nothing is recorded: "
                 + "; ".join(PARTS[k] for k in moved))
    commit, state = at
    if revision(root) != at:
        sys.exit(f"screen: the commit checked out, or the state of its inputs, changed while "
                 f"it ran (it was {commit[:12]}, {state}, as it read them), so nothing is "
                 "recorded")
    if state != COMMITTED or not re.fullmatch(r"[0-9a-f]{40}", commit):
        sys.exit(f"screen: the inputs are not a commit's ({state}), so nothing is recorded")
    if path.is_symlink():
        sys.exit(f"screen: {path.relative_to(root)} is a symbolic link, so nothing is recorded")
    new = path.with_name(f".{path.name}.{os.getpid()}")
    with open(new, "x", encoding="utf-8") as f:
        f.write(record_text(read, commit, state, count))
    os.replace(new, path)
    print(f"recorded what this run read in {path.relative_to(root)}: commit {commit[:12]} "
          f"({state}), {count} statements")


def check_current(root: Path = ROOT, path: Path = RECORD) -> tuple[list[str], dict, list[str]]:
    """(the problems, the record as read, the parts changed since the run it records). The
    problems are a missing or unreadable record, or one no run on a commit's inputs wrote,
    and each part of the inputs that differs."""
    name = path.relative_to(root).as_posix() if root in path.parents else str(path)
    if path.is_symlink():
        return [f"{name} is a symbolic link: a run writes the record as a file"], {}, []
    if not path.is_file():
        return ([f"there is no record of a run at {name}: run `python3 -I Audit/screen.py "
                 "OUTDIR --write` on this revision"], {}, [])
    try:
        rec = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError, UnicodeDecodeError) as e:
        return [f"{name} does not read: {e}"], {}, []
    parts = rec.get("parts")
    if not isinstance(parts, dict) or set(parts) != set(PARTS) \
            or not isinstance(rec.get("statements"), int) or rec.get("inputs") != total(parts):
        return [f"{name} is not as a run writes it: its parts, its statements or its inputs "
                "hash do not agree"], rec, []
    if not re.fullmatch(r"[0-9a-f]{40}", str(rec.get("commit"))) \
            or rec.get("state") != COMMITTED:
        return [f"{name} records a run on inputs other than a commit's: --write records only "
                f'a commit\'s 40 hex digits, with the state "{COMMITTED}"'], rec, []
    if links := input_symlinks(root):
        return ["the inputs now include symbolic links: " + ", ".join(links)], rec, []
    try:
        facts = json.loads((root / "facts.json").read_text(encoding="utf-8"))
        now = inputs(root, facts)
        current_commit, current_state = revision(root)
    except (OSError, ValueError, KeyError, TypeError, SyntaxError) as e:
        return [f"the inputs do not read now: {e!r}"], rec, []
    if parts["statements"] == now["statements"] \
            and rec["statements"] != len(facts["propositions"]):
        return [f"{name} is not as a run writes it: it counts {rec['statements']} statements, "
                f"but the statements it pins are {len(facts['propositions'])}"], rec, []
    if total(now) == rec["inputs"]:
        if current_state != COMMITTED or not re.fullmatch(r"[0-9a-f]{40}", current_commit):
            return [f"the inputs now are not a commit's ({current_state}): matching hashes "
                    "are current only for committed inputs"], rec, []
        return [], rec, []
    changed = [k for k in PARTS if parts[k] != now[k]]
    problems = []
    for k in changed:
        detail = (f" ({rec['statements']} at the run, {len(facts['propositions'])} now)"
                  if k == "statements" else "")
        problems.append(f"changed since the run at {str(rec.get('commit'))[:12]}: {PARTS[k]}"
                        + detail)
    return problems, rec, changed


def since(rec: dict, changed: list[str]) -> list[str]:
    """What git can say of the parts changed, when it has the commit the record names and
    the run read that commit's files: the statements added, removed or restated, and the
    files changed."""
    commit = str(rec.get("commit", ""))
    if rec.get("state") != COMMITTED or not re.fullmatch(r"[0-9a-f]{40}", commit):
        return []
    notes = []
    if "statements" in changed and (then := git("show", f"{commit}:facts.json")) is not None:
        try:
            old = {e["name"]: e for e in json.loads(then)["propositions"]}
            now = json.loads((ROOT / "facts.json").read_text(encoding="utf-8"))
            new = {e["name"]: e for e in now["propositions"]}
        except (OSError, ValueError, KeyError, TypeError):
            old = new = {}
        for label, names in (("added", sorted(set(new) - set(old))),
                             ("removed", sorted(set(old) - set(new))),
                             ("restated", sorted(n for n in set(old) & set(new)
                                                 if any(old[n].get(k) != new[n].get(k)
                                                        for k in ("ref", "kind", "statement"))))):
            if names:
                notes.append(f"statements {label}: {', '.join(names)}")
    paths = {"library": list(LIBRARY), "toolchain": list(TOOLCHAIN),
             "screen": [f"Audit/*{m}" for m in MODULES]}
    files = [p for k in changed if k in paths
             for p in (git("diff", "--name-only", commit, "--", *paths[k]) or "").split()]
    if files:
        notes.append(f"files changed since {commit[:12]}: " + ", ".join(files[:12])
                     + (f" and {len(files) - 12} more" if len(files) > 12 else ""))
    return notes


def report_current() -> int:
    """--check-current: 0 when the record names what the screen would read now, else 1."""
    problems, rec, changed = check_current()
    if not problems:
        print(f"screen: current: {RECORD.relative_to(ROOT)} records a run at "
              f"{str(rec.get('commit'))[:12]} on {rec['statements']} statements, and what "
              "decides its result is unchanged")
        return 0
    print("screen: not current; run it again on this revision with --write "
          "(docs/WORKFLOW.md, section 10, step 10):")
    for p in problems + since(rec, changed):
        print("  " + p)
    return 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("outdir", type=Path, nargs="?")
    ap.add_argument("--jobs", type=int, default=12)
    ap.add_argument("--write", action="store_true",
                    help=f"record what a run read in {RECORD.relative_to(ROOT)}")
    ap.add_argument("--check-current", action="store_true",
                    help="compare that record with the inputs now, without Lean")
    args = ap.parse_args()
    if args.check_current:
        if args.outdir or args.write:
            ap.error("--check-current takes no OUTDIR and no --write")
        return report_current()
    if args.outdir is None:
        ap.error("OUTDIR is required")
    out = args.outdir.resolve()
    if out == ROOT or ROOT in out.parents:
        sys.exit("screen: OUTDIR must be outside the repository")
    at = revision(ROOT)
    if args.write and at[1] != COMMITTED:
        sys.exit(f"screen: --write records only a run on a commit's inputs as committed, and "
                 f"these are not ({at[1]}): commit them, or run without --write")
    facts = json.loads((ROOT / "facts.json").read_text(encoding="utf-8"))
    read = inputs(ROOT, facts)
    try:
        built = subprocess.run(["lake", "build", "--no-build", "Elements"], cwd=ROOT,
                               capture_output=True, text=True).returncode == 0
    except OSError:
        sys.exit("screen: there is no `lake` to run (export PATH=$HOME/.elan/bin:$PATH)")
    if not built:
        sys.exit("screen: the build of Elements is not current with its sources, and every try "
                 "imports the build: run `lake build` first")
    if revision(ROOT) != at or inputs(
            ROOT, json.loads((ROOT / "facts.json").read_text(encoding="utf-8"))) != read:
        sys.exit("screen: the commit or the inputs changed while the build was checked, so "
                 "the build checked may not be theirs: nothing is run")
    out.mkdir(parents=True, exist_ok=True)
    kinds: dict[str, int] = {}
    for e in facts["propositions"]:
        kinds[e["kind"]] = kinds.get(e["kind"], 0) + 1
    print(f"{len(facts['propositions'])} statements: "
          + ", ".join(f"{n} {k}" for k, n in sorted(kinds.items())))
    reached(facts, out)
    jobs = attempts(facts)
    todo = tries(jobs, refused(facts, out))
    total, closed, slow, stopped = run(todo, BEATS, out, "Screen", args.jobs)
    if total != len(todo):
        sys.exit(f"screen: {total} of {len(todo)} tries were read back from the logs")
    ruled_jobs = [j for j in jobs if j[2]]
    print(f"{len(jobs)} attempts, {len(jobs) - len(ruled_jobs)} of them bare; {total} tries "
          f"({2 * len(ruled_jobs) - (total - (len(jobs) - len(ruled_jobs)))} left with no "
          f"rule grind takes); {len(slow)} ran out of time at {BEATS} and were tried again "
          f"at {BEATS * RETRY}")
    if slow:
        _, more, slow, also = run({n: todo[n] for n in slow}, BEATS * RETRY, out, "Again",
                                  args.jobs)
        closed += more
        stopped += also
    print(f"{len(closed)} tries closed:")
    for name in sorted(closed):
        print("  " + name)
    bare, ruled = by_rule(closed)
    print(f"{len(bare)} statements closed with no rule, by their definitions and logic "
          f"alone: {', '.join(refs(facts, bare)) or 'none'}")
    print(f"{len(ruled)} statements closed by a rule: "
          f"{', '.join(refs(facts, ruled)) or 'none'}")
    if slow:
        print(f"{len(slow)} tries ran out of time again, not searched to the end, on "
              f"{', '.join(statements(facts, slow))}:")
        for name in sorted(slow):
            print("  " + name)
    if stopped:
        print(f"{len(stopped)} tries stopped on another error, not searched to the end, on "
              f"{', '.join(statements(facts, stopped))}:")
        for name in sorted(stopped):
            print("  " + name)
    missing = lost(closed)
    if missing:
        print(f"screen: the known rows {missing} did not close by a rule; the screen may be "
              "broken")
        return 1
    if args.write:
        try:
            built = subprocess.run(["lake", "build", "--no-build", "Elements"], cwd=ROOT,
                                   capture_output=True, text=True).returncode == 0
        except OSError:
            sys.exit("screen: there is no `lake` to run (export PATH=$HOME/.elan/bin:$PATH)")
        if not built:
            sys.exit("screen: the build of Elements changed while the screen ran and is not "
                     "current with its sources, so nothing is recorded: run `lake build` "
                     "and the screen again")
        write_record(ROOT, read, len(facts["propositions"]), RECORD, at=at)
    return 0


if __name__ == "__main__":
    sys.exit(main())
