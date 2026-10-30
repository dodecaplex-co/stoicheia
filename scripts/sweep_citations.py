"""List the candidates for dummy citations, artificial hypothesis uses and concealing helpers.

FORMALIZATION.md, section 5, asks that the Lean cite only what its argument uses, never
mention a hypothesis only to silence a warning, and never hide a whole conclusion behind
a helper; WORKFLOW.md, section 6, asks reviewers to hunt for all three; brief 0005's stage
5 promises a script that lists the candidates (#32). This is that script. It lists, for
the Lean under `Elements/` (and `Staging/` or `Audit/`, or single files, when named;
Lean's linter passes over any declaration with a `sorry` in it, even one that never runs,
so a statement staged before its proof gives no hit until the proof arrives, and outside
`Staging/` such a file is refused):

* **unused bindings in proofs**: a `have`, `let`, `obtain`, `rcases` or `intro` whose
  name nothing uses (kinds `unused-have`, `unused-let`, `unused-obtain` for one unused
  part of a result whose other parts are used, `unused-intro`, and `unused-binding` for
  the rest, such as a case split's names, `rcases h with hp | hq`);
* **discarded results** (`discarded`): an `obtain` or `rcases` whose whole result goes
  unused, as `obtain ⟨KF, -, -⟩ := Postulate1 …` when KF is never named again: a citation
  whose result is bound and never used. A case split is never one: it is used, whatever
  its names;
* **`_`-named citations** (`underscore`): `have _ := h…`, `let _x := …`, `obtain _ := …`,
  whose name Lean's linter never checks, used or not;
* **helpers that may conceal a whole conclusion** (`helper`): a proposition, porism or
  companion (the entries of facts.json, Certificate/FIELDS.md) whose proof, after its
  intros, comes down in every branch to one application of a helper that the proof's
  own steps do not feed; or that cites a helper whose statement is exactly its own.

How each is found:

1. **Lean's own judgement** for unused names. Each file is elaborated, in parallel, with
   Lean's unused-variables linter (Sebastian Ullrich's and Mario Carneiro's, in Lean
   itself) and its tactic analysis switched on, `-Dlinter.unusedVariables=true
   -Dlinter.unusedVariables.analyzeTactics=true`, which is off by default. With it the
   linter looks through every tactic state, so a hypothesis that `assumption`,
   `simp_all`, `omega` or `grind` uses without naming it counts as used. A file that
   sets one of the linter's options itself, as
   `set_option linter.unusedVariables false in`, or its `.analyzeTactics`, `.funArgs`
   or `.patternVars`, in any spelling or spacing (`set_option«linter».unusedVariables`),
   would silence it there; so would any `#guard_msgs` but a pin of `#print` (Audit's and
   Staging's pins of `#print axioms`), which swallows the linter's report with
   `(drop warning)`, `(drop all)` or a docstring that expects the warning; and so, outside
   `Staging/`, would a `sorry` or `admit`, even one that never runs, as
   `first | rfl | sorry`, since the linter passes over the whole declaration that holds
   one (it reads the syntax, not the proof). So the sweep refuses that file, exit 2,
   naming it and each such line. It reads the code as `check_fidelity.py` reads it,
   beginning every comment's body at its fourth character, as Lean does, so that neither a
   `/--/` nor a `/-/-` hides a line from it. The
   linter reads a copy of the file, outside the tree, in which two things are renamed,
   lines kept: each anonymous `have` is named `this`, which Lean then checks (it passes
   over the name Lean gives an anonymous `have`), and each `have`, `let` or `obtain`
   whose name begins with `_` is given a plain name, so Lean says whether anything uses
   it; one that the proof writes again, as `have _h := …` then `exact _h`, keeps its
   name, so the copy still elaborates, and is listed as used by name. A binder of the
   statement itself (an unused hypothesis) is not listed: FORMALIZATION, section 5,
   makes that a review prompt and a `redundant-hypothesis` tag, not a dummy citation;
   the statement ends at its `:=`, or at the first `|` of a proof by equations.
2. **A textual pass for exactly one shape the linter cannot see**: a name an `obtain` or
   `rcases` pattern keeps, whose other parts are all cleared (`-`) or found unused by
   Lean, and which is never written again in its declaration, as `obtain ⟨KF, -, -⟩`.
   Lean counts KF as used, because the facts it clears mention KF in the tactic states
   it reads. The pass stands aside when automation that can use a hypothesis without
   naming it (`assumption`, `simp_all`, `simpa`, `omega`, `grind`, `trivial`, `‹…›`, and
   their kind: AUTOMATION, below) follows in the declaration, and a `_` part counts as
   used, since automation may use it. A pattern is read with its alternatives, and an
   `rcases … with` over line breaks, as `check_fidelity.py` reads them. The `have`,
   `let` and `obtain` whose names begin with `_` are found by their text too (they are
   what they are, used or not), and Lean says whether each is used.
3. **Lean's proof terms** for helpers: one run of Lean, with `import Lean` and `import
   Elements`, reads each entry's proof term past its intros, its `have`, `let` and
   `obtain` steps, its case splits, a reductio's opening, a cast and the parts of an
   anonymous constructor; from a field of a structure, not a class's law (a part of a
   conjunction, `.1`, `.2`, either way of an iff, `.mp`, `.mpr`, or a field of a figure,
   `(fig h).line`, unless the proof's own step is what the field is applied to) or a
   fact turned round (`.symm`) to the term it is read from, so that
   `exact (Prop7.figure h).2` is read as `Prop7.figure h`; and from a step, or a part of
   a split of one term, that a branch returns as it is to the term the step is bound to
   or the term split, so that
   `have hw := Prop7.figure h` then `exact hw.2`, or `obtain ⟨-, hL⟩ := Prop7.figure h`
   then `exact hL`, is read the same way. Parts put together again by a constructor are
   a step of the proof's own, and are not read on. The names a split binds count as
   steps of the proof's own, so that a helper they feed is fed, when it takes apart a
   step, a citation or a field of one, as `obtain ⟨hne, -⟩ := (fig h).2`; those of a
   split of a hypothesis do not. A helper is a theorem or definition
   of the project's own, private or not, that is not an entry, nor a field of a
   structure (whatever gives the structure is the helper), nor from
   `Elements/Foundations/` (an axiom, a Common Notion or a proved rule, which the
   overlap catalogue and a record's `[overlap]` answer for), nor a declaration Lean made
   for another. Staging and Audit hold no entries, so this part reads only `Elements/`.

**What it does not see.** A binding cleared away (`clear h`), or handed to a function
that ignores it (`exact (fun _ => hKF) h`), counts as used, and so does a kept name that
automation such as `contradiction` or `simpa` follows in its declaration, where the
textual pass stands aside, and a name an `obtain` or `rcases` keeps that a later binding
writes again, which the textual pass counts as naming it; a `_` name inside a pattern
(`obtain ⟨L, hK, _hF⟩`) or after `intro` is not listed; a citation whose result feeds
only another idle step is listed by that step alone; and a helper fed by one trivial
step passes, unless its statement is the entry's own, and so does a part of a helper's
result returned from a `match` on two or more terms at once. Elements has no `clear`, no
`(fun _ => …)` applied and no `_` name in a pattern or after `intro` today; its two
entries that split several terms at once, `Prop45.sum` and `Prop14.sum`, split only
what their statements bind; and the sweep finds the same hits there with the
stand-aside off.

**Declared hits.** There is one rule. A hit is declared when the review record of its
proposition, `review/<book>/NN.toml`, has a `[[passage]]` whose `at` begins a sentence
of the run of `--` lines (Euclid's words) over the hit's line, and whose `unused` lists
the binding by the name the proof gives it (`hAB_FC`, `hDC_AB`, or `this` for an
anonymous `have`; every name, where the hit keeps several):

    [[passage]]
    at = "Therefore the base AB is equal to the base FC"
    kind = "carried"
    unused = ["hAB_FC"]

Nothing else declares a hit: not a passage's note, whose words a reader meets and which
says a hypothesis in words (STYLE, section 1, "Hypotheses in words"), nor a `#` comment
of the record. TOML does not read a comment, so neither does the records' `text` stamp
(#77), which hashes a record as TOML reads it: a declaration there could change with no
reader's knowledge. `unused` is a key of the record like any other, which
review/SCHEMA.md defines and which the records' `text` stamp covers, and
`check_fidelity.py` fails a name in it that the Lean beneath the passage's run does not
bind (`unbound_unused`), so a declaration cannot outlive its binding. A helper hit
is never declared: FORMALIZATION, section 5, has a helper supply one step, never a whole
conclusion, so one is fixed. Nor is a binding with no name of its own, `obtain -` or
`have _`.

The runs and sentences are read as `check_fidelity.py` reads them (`runs_beneath`,
`sentence_starts`), so the passage that `check_fidelity.py` places over a run declares
the hits beneath it here. Only a hit inside `theorem PropN` can be declared: no `--`
line stands over a helper's or a companion's proof. The coordinator's ruling of 28
October 2026 (#482), which replaces Tw2's on the joins (#32), is why an idle join is
deleted, not declared: a join under a sentence of Euclid's is written in the Lean only
where the formal proof uses the line it draws; Heath's sentence stays as its `--` line,
and the record says the join is drawn in the text and not needed by the formal proof.
FORMALIZATION, section 5, allows a checked intermediate fact tied to a real sentence of
Euclid's, which is declared as above.

Each hit is printed as `file:line: kind: name: why`, a declared one followed by
`(declared in review/…)`, then a summary for each book. Exits 0 after listing;
`--fail-on-undeclared` exits 1 when any undeclared hit remains (the release gate,
docs/WORKFLOW.md, section 10); 2 when the sweep cannot run (no Lean, an unbuilt library,
a run of Lean that prints a panic, a file that does not elaborate, that sets the linter's
options itself, that captures its messages with `#guard_msgs` or that, outside `Staging/`,
has a `sorry` or `admit`, a facts.json that does not match Lean).

    python3 scripts/sweep_citations.py                       Elements/
    python3 scripts/sweep_citations.py Elements Staging Audit  these trees (or files)
    python3 scripts/sweep_citations.py --fail-on-undeclared  the release gate
    python3 scripts/sweep_citations.py --self-test           plants and controls

`--self-test` writes planted Lean outside the tree, each plant of which must be
reported: each kind of hit; a `_` name the proof writes again, as used by name; an
`rcases … with` whose pattern, or whose `with`, is on the next line; a case split's
names, never `discarded`; a `suffices`; a `have` in a proof by equations; one named
`killed`; one under `warningAsError`, which Lean reports as an error; and a helper
behind a whole proof: after a step that feeds it nothing, as a private theorem, in each
branch of a case split (of a hypothesis, or by excluded middle), behind a reductio's
opening, a cast (`rw`), a `show` or metadata, through `.1`, `.2` (as Lean's primitive
projection too), `.symm`, `.mp` and `.mpr`, applied or not, as a field of a figure,
through a step bound to its result, or a part of it or of one of its parts taken apart,
or of it through `id`, fed only by a part of a hypothesis taken apart, and, cited by a
reductio, stated exactly.
Its controls must not be reported: a binding used later, one used by
`assumption` or `simp_all`, a pattern's `_` part, an unused hypothesis of the statement,
a helper that supplies one step, a helper's parts put together again, a part of a
helper's result taken apart and its part fed to another helper, an entry that
cites another, an iff applied to the proof's own step, a case split of that step, a
field of a figure the statement gives, a match on two terms, an `if` whose other branch
is a rule of the foundations, a proved rule of the foundations, a class's law; and a
declared join, reported as declared. Its record is read as TOML, and in it only a name
in `unused` over its own run declares, and only with every name the hit keeps: one in a
note or a `#` comment does not, nor one in `unused` over another run, which
`check_fidelity.unbound_unused` must report; and no helper hit is declared. The sweep
must refuse, exit 2, a file that silences the linter (eleven lines: seven settings of
its options, one behind a `/--/` and one behind a `/-/-`, three `#guard_msgs` and a
`sorry` that never runs, each line named), but not a remark that quotes them nor a
`#guard_msgs` around `#print`; a file that does not elaborate; a run of Lean that fails
with no error at a line (a file that is not there); and a run that ends in a signal or an
exit but 0 or 1, or exits 1 with anything but the linter's reports, one promoted to an
error, even a panic after them; and a run that prints a line beginning `PANIC at `,
`PANIC: ` or `INTERNAL PANIC`, on either stream, whatever its exit, 0 among them, naming
the line (#236), but not a message that quotes the words within a line. Read without
Lean, a file with an `admit` must be refused, naming its line, but not in `Staging/`; and
the reader must begin every comment's body at its fourth character, as Lean does. It exits 1
naming any plant missed, control reported, binding misread or file not refused. Both it
and the sweep need the library built by `lake build`
and the Lean tools on PATH (`export PATH=$HOME/.elan/bin:$PATH`); the sweep also reads
facts.json (`lake env lean Certificate/Facts.lean`). Standard library only; Python 3.11
or later, for the review records.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import functools
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest.mock
from pathlib import Path
from typing import Callable, NamedTuple

import check_fidelity
import heath

ROOT = heath.ROOT
FACTS = ROOT / "facts.json"
LINT = ["-Dlinter.unusedVariables=true", "-Dlinter.unusedVariables.analyzeTactics=true"]
# A file's own setting of one of the linter's options (`linter.unusedVariables`, and its
# `.funArgs`, `.patternVars` and `.analyzeTactics`), in any spelling or spacing, as
# `set_option«linter».unusedVariables`: it would silence what LINT switches on, so it is
# refused.
SILENCING = re.compile(r"(?<![\w'.])set_option\s*«?linter»?\s*\.\s*«?unusedVariables")
# Every `#guard_msgs` but a pin of `#print` (the axiom pins of Audit and Staging), in any
# spacing: with `(drop warning)`, `(drop all)`, or a docstring that expects the warning, it
# swallows the linter's report.
GUARDED = re.compile(r"(?<![\w'.])#guard_msgs\b(?!(?:\s*\([^)]*\))?\s*in\b\s*#print\b)")
# A `sorry` or `admit`, even one that never runs: Lean's linter passes over the whole
# declaration that holds one (`hasSorry` reads the syntax). Staging's statements await theirs.
UNLINTED = re.compile(r"(?<![\w'.])(?:sorry|admit)(?![\w'!?])")
TREES = ("Elements", "Staging", "Audit")

# The kinds of hit, in the order the summary counts them.
KINDS = ("discarded", "unused-have", "unused-let", "unused-obtain", "unused-intro",
         "unused-binding", "underscore", "helper")

# Tactics and notations that can use a hypothesis without naming it. Lean's linter sees
# their uses; the textual pass (2, above) does not, so it stands aside where one follows.
AUTOMATION = re.compile(
    r"(?<![\w'.])(?:assumption|assumption_mod_cast|simp_all|simp_arith|simpa|omega|grind|"
    r"aesop|tauto|trivial|contradiction|solve_by_elim|linarith|nlinarith|subst_vars|cc|"
    r"exists|exact\?|apply\?)(?![\w'!])|‹|\[\s*\*\s*\]|\bat\s+\*")

# Lean's identifiers, as far as this script needs them.
IDENT = re.compile(r"[^\W\d][\w'!?₀-₉]*(?:\.[^\W\d][\w'!?₀-₉]*)*")
# The linter's report, a warning, or an error where a file sets `warningAsError` (as
# Audit/Overlaps.lean does).
WARNING = re.compile(r"^(?P<file>.+?):(?P<line>\d+):(?P<col>\d+): "
                     r"(?P<severity>warning|error): "
                     r"(?:Variable name|unused variable) `(?P<name>[^`]+)`", re.M)
# The lines that follow the first line of each of the linter's reports, as Lean 4.35
# prints them (Lean/Linter/UnusedVariables.lean): blank lines, its hint, the name it
# suggests, and its note.
LINT_TAIL = re.compile(
    r"|Hint: The binding can be removed \(if unused\) or named `_` \(if used implicitly\)\. "
    r"Alternatively, prefix the name with `_` to silence this warning:"
    r"|  \[apply\] _\S.*"
    r"|Note: This linter can be disabled with `set_option linter\.unusedVariables false`")
ERROR = re.compile(r"^.+?:\d+:\d+: error\b(?!: (?:Variable name|unused variable) `).*$", re.M)
# A line where Lean reports a panic (#236): `PANIC at …`, which Lean can print and still
# exit 0, `PANIC: …`, as a dropped promise prints it, or `INTERNAL PANIC`, which ends Lean
# with exit 1.
PANIC = re.compile(r"^(?:PANIC(?: at |: )|INTERNAL PANIC).*$", re.M)
# An anonymous `have`, which Lean names `this` without checking it.
ANONYMOUS = re.compile(r"(?<![\w'.])have(?![\w'!?])(?=[ \t]*:)")
# A binding whose name begins with `_`, which Lean's linter never checks.
UNDERSCORE = re.compile(r"(?<![\w'.])(?P<kw>have|let|obtain)[ \t]+(?P<name>_[\w']*)"
                        r"(?![\w'!?])(?=[ \t]*(?::|$|\n))")
RENAMED = "sweep_underscore"   # the prefix a `_`-named binding is given in the copy
PATTERN_KEYWORD = re.compile(r"(?<![\w'.])(obtain|rcases)(?![\w'!?])")
# The keyword that introduces a binding, found by reading back from its name.
BINDERS = {
    "have": "unused-have", "haveI": "unused-have", "have'": "unused-have",
    "let": "unused-let", "letI": "unused-let", "set": "unused-let",
    "obtain": "unused-obtain", "rcases": "unused-obtain",
    "intro": "unused-intro", "intros": "unused-intro", "rintro": "unused-intro",
    "fun": "unused-intro", "λ": "unused-intro",
    "cases": "unused-binding", "induction": "unused-binding", "match": "unused-binding",
    "by_cases": "unused-binding", "by_contra": "unused-binding", "next": "unused-binding",
    "case": "unused-binding", "if": "unused-binding", "generalize": "unused-binding",
    "choose": "unused-binding", "suffices": "unused-binding", "∀": "unused-binding",
    "∃": "unused-binding",
}
TOKEN = re.compile(r"[^\W\d][\w'!?₀-₉]*|λ|∀|∃")


class SweepError(Exception):
    """The sweep cannot run, or could not read what Lean said (exit 2)."""


class Hit(NamedTuple):
    path: str          # the file, from the repository's root (or a self-test file)
    line: int
    kind: str
    name: str
    why: str
    declared: str | None = None   # the record that declares it


class Proposition(NamedTuple):
    """What declares a file's hits: theorem PropN's number, its record's passages, and
    the record's name."""
    n: int
    passages: list
    record: str


# ---------------------------------------------------------------------------------------
# Reading the Lean.

def code_of(src: str) -> str:
    """The Lean with its comments and literals blanked, offsets kept (check_fidelity)."""
    return check_fidelity.read_lean(src)[0]


def line_starts(text: str) -> list[int]:
    starts = [0]
    for m in re.finditer("\n", text):
        starts.append(m.end())
    return starts


def line_at(starts: list[int], offset: int) -> int:
    """The 1-based line of `offset`."""
    lo, hi = 0, len(starts) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if starts[mid] <= offset:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


class Declarations:
    """The top-level items of a file's code text (a line that begins at its first
    column begins one), each with the end of its signature: the first `:=` outside
    brackets, or, for a proof by equations, the first line outside brackets that begins
    with `|`, so that a binder of the statement is told from one of the proof."""

    OPEN, CLOSE = "([{⟨", ")]}⟩"

    def __init__(self, code: str):
        self.code = code
        self.items: list[tuple[int, int, int]] = []    # (start, signature end, end)
        starts = [m.start() for m in re.finditer(r"(?m)^\S", code)] + [len(code)]
        for a, b in zip(starts, starts[1:]):
            self.items.append((a, self._signature_end(a, b), b))

    def _signature_end(self, a: int, b: int) -> int:
        depth = 0
        for i in range(a, b):
            c = self.code[i]
            if c in self.OPEN:
                depth += 1
            elif c in self.CLOSE:
                depth = max(depth - 1, 0)
            elif c == ":" and depth == 0 and self.code.startswith(":=", i):
                return i
            elif (c == "|" and depth == 0 and self.code[i + 1:i + 2] not in ("|", ">")
                  and not self.code[self.code.rfind("\n", a, i) + 1:i].strip()):
                return i                  # `| 0 => …`: the first equation of the proof
        return b

    def at(self, offset: int) -> tuple[int, int, int]:
        for item in self.items:
            if item[0] <= offset < item[2]:
                return item
        return (0, 0, len(self.code))


def value_after(code: str, offset: int, end: int) -> str:
    """What a binding at `offset` binds: the first name after its `:=`, in backticks, or
    a plain description."""
    m = re.compile(r":=").search(code, offset, min(end, offset + 300))
    if not m:
        return "a stated fact"
    rest = code[m.end():end].lstrip()
    if re.match(r"by\b", rest):
        return "a `by` proof"
    rest = rest.lstrip("(@ ")
    name = IDENT.match(rest)
    if not name or name.group(0) in ("fun", "show", "match", "if"):
        return "a term"
    return f"`{name.group(0)}`"


def mentioned(code: str, start: int, end: int, name: str) -> bool:
    return re.search(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'!?])",
                     code[start:end]) is not None


def binder_keyword(code: str, start: int, offset: int) -> str | None:
    """The nearest binding keyword before `offset`, within its declaration."""
    found = None
    for m in TOKEN.finditer(code, max(start, offset - 2000), offset):
        if m.group(0) in BINDERS:
            found = m.group(0)
    return found


class Pattern(NamedTuple):
    keyword: str       # obtain or rcases
    offset: int        # the keyword's
    leaves: list       # check_fidelity.Leaf: a name, `-` or `_` (or `rfl`), and its offset
    end: int           # the end of the pattern
    value: str         # what the pattern takes apart, described
    split: bool        # a case split: an alternative after a `|`, at any depth


# The leaves of an rcases pattern and its alternatives, and where an `rcases` pattern
# begins, read as check_fidelity.py reads them for a passage's `unused`, so the two agree
# on what a pattern binds.
read_alternatives = check_fidelity.read_alternatives
rcases_pattern = check_fidelity.rcases_pattern
BAR = re.compile(r"(?<!\|)\|(?![|>])")


def patterns(code: str) -> list[Pattern]:
    """Every `obtain` and `rcases` pattern in the code text, with its alternatives."""
    out = []
    for m in PATTERN_KEYWORD.finditer(code):
        start = m.end() if m.group(1) == "obtain" else rcases_pattern(code, m.end())
        if start is None:
            continue
        leaves, end = read_alternatives(code, start)
        if m.group(1) == "obtain":
            value = value_after(code, end, len(code))
        else:
            value = _described(code[m.end():start])
        if leaves:
            out.append(Pattern(m.group(1), m.start(), leaves, end, value,
                               BAR.search(code, start, end) is not None))
    return out


def _described(text: str) -> str:
    text = text.strip().lstrip("(@ ")
    name = IDENT.match(text)
    return f"`{name.group(0)}`" if name else "a term"


# ---------------------------------------------------------------------------------------
# Running Lean.

def lean_tools() -> None:
    if shutil.which("lake") is None:
        raise SweepError("lake is not on PATH: export PATH=$HOME/.elan/bin:$PATH, and run "
                         "`lake build` first")


def run_lean(path: Path, options: list[str], what: str) -> str:
    """`lake env lean <options> <path>` from the repository's root; its output. A Lean
    error is the sweep's failure, never a quiet pass."""
    r = subprocess.run(["lake", "env", "lean", *options, str(path)], cwd=ROOT,
                       capture_output=True, text=True)
    # A panic is Lean's failure whatever its exit: Lean can print one and still exit 0, with
    # no error line (#236).
    for stream, text in (("standard output", r.stdout), ("standard error", r.stderr)):
        panic = PANIC.search(text)
        if panic:
            raise SweepError(f"Lean panicked while elaborating {what} (exit {r.returncode}), "
                             f"on its {stream}:\n{panic.group(0)}")
    out = r.stdout + r.stderr
    errors = ERROR.findall(out)
    if (r.returncode == 0 and not errors
            or r.returncode == 1 and not r.stderr.strip() and only_lint(r.stdout)):
        return out
    shown = "\n".join(errors[:5]) or out.strip()[-2000:]
    raise SweepError(f"Lean could not elaborate {what} (exit {r.returncode}); is the "
                     f"library built (`lake build`)?\n{shown}")


def only_lint(out: str) -> bool:
    """Whether `out` is the linter's reports and nothing else, one of them an error, as
    `warningAsError` makes it: the one failure the sweep reads, since the linter's reading
    is then whole."""
    promoted = False
    reading = False
    for line in out.splitlines():
        m = WARNING.match(line)
        if m:
            promoted = promoted or m["severity"] == "error"
            reading = True
        elif not (reading and LINT_TAIL.fullmatch(line)):
            return False
    return promoted


class Copy(NamedTuple):
    """The copy of a file that the linter reads, with what was renamed in it."""
    text: str
    anonymous: set          # lines on which an anonymous `have` was named `this`
    underscore: dict        # copy name -> (line, keyword, original name)
    named: list             # (line, keyword, name): a `_` name the proof writes again


def prepare(src: str, rel: str) -> Copy:
    """Name each anonymous `have` `this`, and give each `_`-named binding a plain name,
    so that the linter judges them; every line keeps its number. A `_` name that the
    proof writes again in its declaration, as `have _h := …` then `exact _h`, keeps its
    name, so the copy still elaborates: it is used, by name. A file that sets one of the
    linter's options itself (SILENCING), captures its messages with `#guard_msgs`
    (GUARDED), or, outside Staging, has a `sorry` or `admit` (UNLINTED), is refused, by
    its name and lines."""
    code = code_of(src)
    starts = line_starts(code)
    silencing = sorted(line_at(starts, m.start()) for p in (SILENCING, GUARDED)
                       + (() if rel.startswith("Staging/") else (UNLINTED,))
                       for m in p.finditer(code))
    if silencing:
        lines = src.split("\n")
        shown = "\n".join(f"{rel}:{n}: {lines[n - 1].strip()}" for n in silencing)
        raise SweepError("a file sets an option of Lean's unused-variables linter, or captures "
                         "its messages with `#guard_msgs` around anything but `#print`, or has "
                         "a `sorry` or `admit`, even one that never runs, which would silence "
                         f"the sweep there; remove it:\n{shown}")
    if RENAMED in src:
        raise SweepError(f"{rel}: the file already uses the name {RENAMED}, which the sweep "
                         "needs")
    edits, anonymous, underscore, named = [], set(), {}, []
    decls = Declarations(code)
    for m in ANONYMOUS.finditer(code):
        edits.append((m.end(), m.end(), " this"))
        anonymous.add(line_at(starts, m.start()))
    for k, m in enumerate(UNDERSCORE.finditer(code)):
        line, kw, name = line_at(starts, m.start()), m.group("kw"), m.group("name")
        if name != "_" and mentioned(code, m.end("name"), decls.at(m.start())[2], name):
            named.append((line, kw, name))
            continue
        new = f"{RENAMED}{k}{name}"
        edits.append((m.start("name"), m.end("name"), new))
        underscore[new] = (line, kw, name)
    text = src
    for a, b, new in sorted(edits, reverse=True):
        text = text[:a] + new + text[b:]
    return Copy(text, anonymous, underscore, named)


def lint(path: Path, rel: str, workdir: Path) -> tuple[Copy, list]:
    """The linter's warnings for `path`, read from its copy: (line, column, name)."""
    src = path.read_text()
    copy = prepare(src, rel)
    target = workdir / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(copy.text)
    out = run_lean(target, LINT, f"the sweep's copy of {rel}")
    warnings = [(int(m["line"]), int(m["col"]), m["name"]) for m in WARNING.finditer(out)
                if Path(m["file"]).name == target.name]
    return copy, warnings


# ---------------------------------------------------------------------------------------
# The hits of one file.

def file_hits(rel: str, copy: Copy, warnings: list) -> list[Hit]:
    """The hits of one file, from its copy's text and the linter's warnings."""
    code = code_of(copy.text)
    starts = line_starts(code)
    decls = Declarations(code)
    hits: list[Hit] = []
    # Each warning, by the offset of its name, outside any statement's signature.
    reported = {}
    for line, col, name in warnings:
        offset = starts[line - 1] + col
        _, signature, _ = decls.at(offset)
        if offset < signature:
            continue                      # an unused hypothesis of the statement itself
        reported[(line, name)] = offset
    consumed = set()

    # The `_`-named bindings: listed whatever the linter says, and named back.
    underscores = [(line, kw, original, new) for new, (line, kw, original)
                   in copy.underscore.items()]
    underscores += [(line, kw, original, None) for line, kw, original in copy.named]
    for line, kw, original, new in underscores:
        unused = any(n == new for (_, n) in reported)
        for key in [k for k in reported if k[1] == new]:
            consumed.add(key)
        offset = starts[line - 1]
        _, _, end = decls.at(offset)
        value = value_after(code, offset, end)
        verdict = ("the proof names it again, so it is used" if new is None
                   else "Lean finds it unused" if unused
                   else "Lean finds it used, without its name")
        hits.append(Hit(rel, line, "underscore", original,
                        f"`{kw} {original}` binds {value}; a name that begins with `_` keeps "
                        f"Lean's linter quiet, and here {verdict}"))

    # The patterns of `obtain` and `rcases`.
    for p in patterns(code):
        if any(leaf.name.startswith(RENAMED) for leaf in p.leaves):
            continue
        if p.split:
            # A case split is used whatever its names: only Lean's warnings are hits.
            for leaf in p.leaves:
                key = (line_at(starts, leaf.offset), leaf.name)
                if key in reported and key not in consumed:
                    consumed.add(key)
                    hits.append(Hit(rel, key[0], "unused-binding", leaf.name,
                                    f"`{p.keyword}` of {p.value}, a case split: Lean finds "
                                    f"{leaf.name} unused in its case"))
            continue
        _, _, end = decls.at(p.offset)
        rest_used = AUTOMATION.search(code, p.end, end) is not None
        found, cleared, unseen, used = [], 0, [], False
        for leaf in p.leaves:
            key = (line_at(starts, leaf.offset), leaf.name)
            if leaf.name == "-":
                cleared += 1
            elif leaf.name in ("_", "rfl"):
                used = True
            elif key in reported:
                found.append((key, leaf))
            elif mentioned(code, p.end, end, leaf.name):
                used = True
            else:
                unseen.append(leaf)
        line = line_at(starts, p.offset)
        if not used and not (unseen and rest_used) and (unseen or found or cleared):
            # The whole result goes unused: one hit, named by what it keeps.
            consumed.update(key for key, _ in found)
            names = ([leaf.name for leaf in unseen] or [leaf.name for _, leaf in found]
                     or ["(cleared)"])
            parts = []
            if unseen:
                parts.append(f"{', '.join(leaf.name for leaf in unseen)} never named again")
            if found:
                parts.append(f"Lean finds {', '.join(leaf.name for _, leaf in found)} unused")
            if cleared:
                parts.append("the rest cleared with `-`" if unseen or found
                             else "every part cleared with `-`")
            hits.append(Hit(rel, line, "discarded", ", ".join(names),
                            f"`{p.keyword}` of {p.value}: the whole result goes unused "
                            f"({'; '.join(parts)})"))
        else:
            for key, leaf in found:
                consumed.add(key)
                hits.append(Hit(rel, key[0], "unused-obtain", leaf.name,
                                f"`{p.keyword}` of {p.value}: Lean finds this part unused, "
                                "while the result is used"))

    # Every other warning, by the keyword that binds it.
    for (line, name), offset in sorted(reported.items()):
        if (line, name) in consumed:
            continue
        start, _, end = decls.at(offset)
        kw = binder_keyword(code, start, offset)
        kind = BINDERS.get(kw, "unused-binding")
        if name == "this" and line in copy.anonymous:
            hits.append(Hit(rel, line, "unused-have", "this",
                            f"anonymous `have` of {value_after(code, offset, end)}: "
                            "Lean finds `this` unused"))
        elif kind in ("unused-have", "unused-let"):
            hits.append(Hit(rel, line, kind, name,
                            f"`{kw} {name}` binds {value_after(code, offset, end)}; "
                            "Lean finds it unused"))
        else:
            binds = f"`{kw}` binds {name}" if kw else f"{name} is bound here"
            hits.append(Hit(rel, line, kind, name, f"{binds}, which Lean finds unused"))
    return hits


# ---------------------------------------------------------------------------------------
# Helpers that may conceal a whole conclusion: Lean reads the proof terms.

HELPERS_LEAN = r"""import Lean
@IMPORTS@

@PLANTS@

open Lean Meta

namespace SweepCitations

/-- The module that declares `c`, or "" for this file. -/
def moduleOf (env : Environment) (c : Name) : String :=
  match env.getModuleIdxFor? c with
  | some idx => env.header.moduleNames[idx.toNat]!.toString
  | none => ""

/-- Is `c` the project's own: declared in a module under `Elements`, or in this file? -/
def isOurs (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx => (`Elements).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => true

/-- A helper: a theorem or definition of the project's own that is not an entry, not of
the foundations (an axiom, a Common Notion, a proved rule), not a field of a structure
(whatever gives the structure is the helper), and not a matcher or a declaration Lean
made for another. A private one is judged by the name it is written with, since Lean
marks every private name an internal detail. -/
def isHelper (entries : NameSet) (c : Name) : MetaM Bool := do
  let env ← getEnv
  if entries.contains c || !isOurs env c || (privateToUserName c).isInternalDetail then
    return false
  if (moduleOf env c).startsWith "Elements.Foundations" then return false
  if (← isMatcher c) || (← isProjectionFn c) then return false
  match env.find? c with
  | some (.thmInfo _) | some (.defnInfo _) | some (.opaqueInfo _) => return true
  | _ => return false

partial def strip : Expr → Expr
  | .mdata _ b => strip b
  | e => e

/-- Does the split `e` take apart something the proof obtained: a step, or a citation, or a
field of one (`(fig h).2`)? -/
partial def obtained (steps : Array Expr) (e : Expr) : MetaM Bool := do
  if steps.any (fun s => e.containsFVar s.fvarId!) then return true
  let e := strip e
  if let .proj _ _ s := e then return (← obtained steps s)
  match e.getAppFn with
  | .const c _ =>
    if let some info ← getProjectionFnInfo? c then
      if !info.fromClass && e.getAppNumArgs > info.numParams then
        return (← obtained steps e.getAppArgs[info.numParams]!)
    return isOurs (← getEnv) c
  | _ => return false

/-- Each term that finishes a branch of the proof `e`, with the steps before it. The proof
is followed past its intros, its `have`, `let` and `obtain` steps, its case splits, a
reductio's opening, a cast and the parts of an anonymous constructor; from a field of a
structure, not a class's law (`.1`, `.2`, `.mp`, `.mpr`, `(fig h).line`, unless a step of
the proof is what the field is applied to) or a fact turned round (`.symm`) to the term it
is read from; and from a step, or a part of a split of one term, that a branch returns as
it is, to the term the step is bound to or the term split, so that
`have hw := pair h; exact hw.2` and `obtain ⟨-, hL⟩ := pair h; exact hL` are each read as
`pair h`. `parts` holds each split around `e`: the names it binds, and the term split. -/
partial def ends (steps : Array Expr) (parts : Array (Array Expr × Expr)) (e : Expr) :
    MetaM (Array (Array Expr × Expr)) := do
  let e := strip e
  match e with
  | .lam .. => lambdaTelescope e fun _ b => ends steps parts b
  | .letE n t v b _ =>
    withLetDecl n t v fun x => ends (steps.push x) parts (b.instantiate1 x)
  | .proj _ _ s => ends steps parts s
  | .fvar x =>
    if let some v ← x.getValue? then
      return (← ends (steps.filter (· != e)) parts v)
    if let some (xs, d) := parts.find? (·.1.contains e) then
      return (← ends (steps.filter (fun s => !xs.contains s)) parts d)
    return #[(steps, e)]
  | _ =>
    if e.isAppOfArity ``Classical.byContradiction 2 || e.isAppOfArity ``Eq.mpr 4 ||
        e.isAppOfArity ``id 2 || e.isAppOfArity ``Iff.symm 3 || e.isAppOfArity ``Eq.symm 4 ||
        e.isAppOfArity ``Ne.symm 4 then
      return (← ends steps parts e.appArg!)
    if let .const c _ := e.getAppFn then
      if let some info ← getProjectionFnInfo? c then
        let args := e.getAppArgs
        if !info.fromClass && args.size > info.numParams then
          if (args.extract (info.numParams + 1) args.size).any
              (fun a => steps.any (fun s => a.containsFVar s.fvarId!)) then
            return #[(steps, e)]
          return (← ends steps parts args[info.numParams]!)
    -- Parts put together by a constructor are no longer returned as they are.
    if e.isAppOfArity ``Exists.intro 4 then
      return (← ends steps #[] e.appArg!)
    if e.isAppOfArity ``And.intro 4 || e.isAppOfArity ``Iff.intro 4 then
      return (← ends steps #[] e.appFn!.appArg!) ++ (← ends steps #[] e.appArg!)
    if e.isAppOfArity ``dite 5 then
      return (← ends steps parts e.appFn!.appArg!) ++ (← ends steps parts e.appArg!)
    if let some app ← matchMatcherApp? e (alsoCasesOn := true) then
      let fromSteps ← app.discrs.anyM (obtained steps)
      let mut out := #[]
      for alt in app.alts do
        out := out ++ (← lambdaTelescope (strip alt) fun xs b =>
          ends (if fromSteps then steps ++ xs else steps)
            (if app.discrs.size == 1 then parts.push (xs, app.discrs[0]!) else parts) b)
      return out
    return #[(steps, e)]

def report (entry helper : Name) (shape : String) : MetaM Unit := do
  let env ← getEnv
  let (a, b) ← match ← findDeclarationRanges? entry with
    | some r => pure (r.range.pos.line, r.range.endPos.line)
    | none => pure (0, 0)
  let h ← match ← findDeclarationRanges? helper with
    | some r => pure r.range.pos.line
    | none => pure 0
  let st := (toString (← ppExpr (← getConstInfo helper).type)).replace "\n" " "
  IO.println s!"HIT\t{entry}\t{privateToUserName helper}\t{shape}\t{moduleOf env entry}\t{a}\t{b}\t{moduleOf env helper}\t{h}\t{st}"

def judge (entries : NameSet) (n : Name) : MetaM Unit := do
  let env ← getEnv
  let some ci := env.find? n | IO.println s!"MISSING\t{n}"
  let some v := ci.value? (allowOpaque := true) | IO.println s!"MISSING\t{n}"
  let leaves ← ends #[] #[] v
  let mut helpers : Array Name := #[]
  let mut concealed := !leaves.isEmpty
  let mut anySteps := false
  for (steps, b) in leaves do
    anySteps := anySteps || !steps.isEmpty
    let b := strip b
    let fed := b.getAppArgs.any (fun a => steps.any (fun s => a.containsFVar s.fvarId!))
    match b.getAppFn with
    | .const c _ =>
      if (← isHelper entries c) && !fed then
        unless helpers.contains c do helpers := helpers.push c
      else concealed := false
    | _ => concealed := false
  if concealed then
    for c in helpers do report n c (if anySteps then "unfed" else "whole")
  for c in v.getUsedConstants do
    if (← isHelper entries c) && !(concealed && helpers.contains c) then
      if (← getConstInfo c).type == ci.type then report n c "restates"

def entries : Array Name := #[@ENTRIES@]

#eval show MetaM Unit from do
  let set := entries.foldl (·.insert ·) ({} : NameSet)
  for n in entries do judge set n
  IO.println s!"CHECKED\t{entries.size}"
"""

SHAPES = {
    "whole": "its whole proof, after its intros, comes down to one application of",
    "unfed": "its proof ends in one application, fed by none of its own steps, of",
    "restates": "it cites a helper whose statement is exactly its own,",
}


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def helper_hits(entries: list[str], imports: list[str], plants: str, workdir: Path,
                here: str) -> list[Hit]:
    """The helper hits for the entries named (full Lean names), from one run of Lean.
    `plants` is Lean put before the analysis (the self-test's); a hit in it is reported
    at `here`, the analysis file's name."""
    if not entries:
        return []
    source = (HELPERS_LEAN.replace("@IMPORTS@", "\n".join(f"import {m}" for m in imports))
              .replace("@PLANTS@", plants)
              .replace("@ENTRIES@", ", ".join(f"`{e}" for e in entries)))
    target = workdir / "SweepHelpers.lean"
    target.write_text(source)
    out = run_lean(target, [], "the helper analysis")
    missing = re.findall(r"^MISSING\t(.+)$", out, re.M)
    if missing:
        raise SweepError(f"Lean knows no proof for {', '.join(missing)}: is facts.json "
                         "current? (lake env lean Certificate/Facts.lean)")
    checked = re.search(r"^CHECKED\t(\d+)$", out, re.M)
    if not checked or int(checked.group(1)) != len(entries):
        raise SweepError(f"the helper analysis did not finish:\n{out.strip()[-2000:]}")
    hits = []
    for row in re.findall(r"^HIT\t(.+)$", out, re.M):
        entry, helper, shape, emod, a, b, hmod, hline, statement = row.split("\t", 8)
        path = module_path(emod) if emod else here
        short = helper.removeprefix("Elements.")
        text = target.read_text() if not emod else (ROOT / path).read_text()
        line = application_line(code_of(text), int(a), int(b), short) or int(a)
        where = f"{module_path(hmod)}:{hline}" if hmod else f"{here}:{hline}"
        statement = " ".join(statement.split()).replace("Elements.", "")
        hits.append(Hit(path, line, "helper", short,
                        f"{entry.removeprefix('Elements.')}: {SHAPES[shape]} `{short}` "
                        f"({where}), whose statement is: {statement}"))
    return hits


def application_line(code: str, a: int, b: int, helper: str) -> int | None:
    """The last line from `a` to `b` that names `helper` (or the end of its name)."""
    lines = code.split("\n")
    parts = helper.split(".")
    tails = [".".join(parts[i:]) for i in range(len(parts))]
    for ln in range(min(b, len(lines)), max(a, 1) - 1, -1):
        for tail in tails:
            if re.search(r"(?<![\w'])" + re.escape(tail) + r"(?![\w'!?])", lines[ln - 1]):
                return ln
    return None


# ---------------------------------------------------------------------------------------
# Declared hits.

def declaring(hit: Hit, src: str, prop: Proposition) -> str | None:
    """The record that declares `hit`, or None: one with a passage whose `at` begins a
    sentence of the run of `--` lines over the hit's line (the run the line stands
    beneath, `check_fidelity.runs_beneath`), and whose `unused` lists every name the hit
    keeps. The one rule: neither a note nor a `#` comment declares anything, and a helper
    hit is never declared."""
    if hit.kind == "helper":
        return None
    rows = check_fidelity.proof_lines(src, prop.n)
    over = [run for run in check_fidelity.runs_beneath(rows) if hit.line in run.lean]
    if not over:
        return None
    run = set(over[0].words)
    starts = check_fidelity.sentence_starts(rows)
    names = [name.strip() for name in hit.name.split(",")]
    for p in prop.passages:
        at = check_fidelity._plain(p["at"])
        if (any(ln in run and words.startswith(at) for ln, words in starts)
                and all(name in p.get("unused", []) for name in names)):
            return prop.record
    return None


@functools.lru_cache(maxsize=None)
def record_for(rel: str) -> Proposition | None:
    """The proposition whose Lean file `rel` is, with its record's passages."""
    m = re.fullmatch(r"Elements/Book([IVX]+)/Prop(\d\d)\.lean", rel)
    if not m or m.group(1) not in heath.BOOKS:
        return None
    book, n = m.group(1), int(m.group(2))
    try:
        record = heath.load_review(book, n, require_stamp=False)
    except (heath.ReviewError, RuntimeError, FileNotFoundError) as e:
        print(f"note: {rel}: its record could not be read, so nothing in it is declared: {e}")
        return None
    path = heath.review_path(book, n)
    return Proposition(n, record.get("passage", []), path.relative_to(ROOT).as_posix())


# ---------------------------------------------------------------------------------------
# The sweep.

def sweep(files: list[tuple[Path, str]], records: Callable[[str], Proposition | None],
          entries: list[str], imports: list[str], plants: str = "",
          jobs: int | None = None) -> list[Hit]:
    """Every hit in `files` ((path, name to report it by)), and the helper hits of
    `entries`, each marked declared where its record declares it."""
    lean_tools()
    hits: list[Hit] = []
    with tempfile.TemporaryDirectory(prefix="sweep-citations-") as tmp:
        work = Path(tmp)
        (work / "helpers").mkdir()
        with concurrent.futures.ThreadPoolExecutor(jobs or os.cpu_count() or 2) as pool:
            helper = pool.submit(helper_hits, entries, imports, plants, work / "helpers",
                                 "SweepHelpers.lean") if entries else None
            linted = {rel: pool.submit(lint, path, rel, work / "copies")
                      for path, rel in files}
            for rel, future in linted.items():
                copy, warnings = future.result()
                hits += file_hits(rel, copy, warnings)
            if helper is not None:
                hits += helper.result()
    sources = {rel: path.read_text() for path, rel in files}
    out = []
    for hit in hits:
        prop = records(hit.path)
        src = sources.get(hit.path)
        declared = declaring(hit, src, prop) if prop and src is not None else None
        out.append(hit._replace(declared=declared))
    return sorted(set(out), key=lambda h: (group_order(h.path), h.path, h.line, h.kind, h.name))


def group(path: str) -> str:
    m = re.match(r"Elements/Book([IVX]+)/", path)
    if m:
        return f"Book {m.group(1)}"
    for prefix, name in (("Elements/Figure/", "Book Zero (Elements/Figure)"),
                         ("Elements/Foundations/", "Foundations"),
                         ("Elements/", "Elements"), ("Staging/", "Staging"),
                         ("Audit/", "Audit")):
        if path.startswith(prefix):
            return name
    return "self-test"


def group_order(path: str) -> int:
    g = group(path)
    books = list(heath.BOOKS)
    if g.startswith("Book ") and g[5:] in books:
        return 2 + books.index(g[5:])
    return {"Foundations": 0, "Book Zero (Elements/Figure)": 1}.get(g, 50)


def print_hits(hits: list[Hit]) -> None:
    for h in hits:
        tail = f" (declared in {h.declared})" if h.declared else ""
        print(f"{h.path}:{h.line}: {h.kind}: {h.name}: {h.why}{tail}")


def summary(hits: list[Hit], groups: list[str]) -> None:
    print("\nSummary, by book:")
    for g in groups:
        mine = [h for h in hits if group(h.path) == g]
        declared = sum(1 for h in mine if h.declared)
        kinds = ", ".join(f"{k} {n}" for k in KINDS
                          if (n := sum(1 for h in mine if h.kind == k)))
        print(f"  {g}: {len(mine)} hit{'s' * (len(mine) != 1)}, {declared} declared, "
              f"{len(mine) - declared} undeclared" + (f" ({kinds})" if kinds else ""))
    declared = sum(1 for h in hits if h.declared)
    print(f"  In all: {len(hits)} hits, {declared} declared, {len(hits) - declared} undeclared")


def exit_code(hits: list[Hit], fail_on_undeclared: bool) -> int:
    return 1 if fail_on_undeclared and any(not h.declared for h in hits) else 0


def selected(paths: list[str]) -> list[tuple[Path, str]]:
    """The .lean files under the named trees or files, from the repository's root."""
    out = []
    for name in paths:
        p = (ROOT / name).resolve()
        try:
            rel = p.relative_to(ROOT)
        except ValueError:
            raise SweepError(f"{name} is not in the repository") from None
        if not rel.parts or rel.parts[0] not in TREES:
            raise SweepError(f"{name}: the sweep reads Lean under {', '.join(TREES)}")
        if p.is_dir():
            out += [(f, f.relative_to(ROOT).as_posix()) for f in sorted(p.rglob("*.lean"))
                    if not f.is_symlink()]
        elif p.suffix == ".lean" and p.is_file():
            out.append((p, rel.as_posix()))
        else:
            raise SweepError(f"{name}: no such tree or Lean file")
    return sorted(set(out), key=lambda x: x[1])


def entries_in(files: list[tuple[Path, str]]) -> list[str]:
    """The entries of facts.json declared in `files`, by their full Lean names."""
    if not FACTS.exists():
        raise SweepError("facts.json is missing: run `lake env lean Certificate/Facts.lean`")
    facts = json.loads(FACTS.read_text())
    wanted = {rel for _, rel in files}
    out = []
    for e in facts["propositions"]:
        book, n, _, _ = heath.parse_ref(e["ref"])
        if heath.lean_path(book, n).relative_to(ROOT).as_posix() in wanted:
            out.append("Elements." + e["name"])
    return out


# ---------------------------------------------------------------------------------------
# The self-test: plants that must be reported, controls that must not.

PLANTS_LEAN = """import Elements.Foundations.Postulates

namespace SweepSelfTest

open Elements

/-- The self-test's proposition: its `--` lines stand for Euclid's. -/
theorem Prop1 {K F G : Point} (hKF : K ≠ F) (hKG : K ≠ G) (hidle : G ≠ F) : K ≠ F := by
  -- Let KF be joined;
  obtain ⟨KF, -, -⟩ := Postulate1 K F hKF
  -- and let KG be joined.
  obtain ⟨KG, -, -⟩ := Postulate1 K G hKG
  -- Therefore K is not F.
  have hstated : K ≠ F := hKF
  obtain ⟨hpair, hpair2⟩ := And.intro hKF hKG
  -- Then the rest follows.
  have hjoin := Postulate1 K F hKF
  obtain - := Postulate1 K G hKG
  have _ := hKG
  have := Postulate1 K G hKG
  let n := (2 : Nat)
  obtain ⟨L, hK, hF⟩ := Postulate1 K F hKF
  have : OnLine K L := hK
  have hline : OnLine K L := this
  have hused : K ≠ F := hKF
  exact (fun _ : OnLine K L => hused) hline

theorem control_assumption {K F : Point} (h : K ≠ F) : K ≠ F := by
  have hauto : K ≠ F := h
  assumption

theorem control_simp_all (a b : Nat) (h : a = b) : b = a := by
  have hsimp : a = b := h
  simp_all

theorem plant_intro : ∀ m : Nat, (0 : Nat) = 0 := by
  intro m
  rfl

theorem control_automation {K F : Point} (h : K ≠ F) : ∃ L : Line, OnLine K L := by
  obtain ⟨L, hK, -⟩ := Postulate1 K F h
  exact ⟨_, by assumption⟩

theorem control_underscore_part {K F : Point} (hKF : K ≠ F) : K ≠ F := by
  obtain ⟨L2, _, -⟩ := Postulate1 K F hKF
  exact hKF

theorem plant_suffices (a : Nat) : a = a := by
  suffices hsuf : a + 0 = a by rfl
  rfl

theorem plant_named {K F : Point} (hKF : K ≠ F) : K ≠ F := by
  have _hnamed : K ≠ F := hKF
  exact _hnamed

theorem plant_rcases {K F : Point} (hKF : K ≠ F) : K ≠ F := by
  rcases Postulate1 K F hKF with
    ⟨KM, -, -⟩
  exact hKF

theorem plant_rcases_with {K F : Point} (hKF : K ≠ F) : K ≠ F := by
  rcases Postulate1 K F
      hKF with ⟨KN, -, -⟩
  exact hKF

theorem plant_split (p q : Prop) (hpq : p ∨ q) (hq : q) : q := by
  rcases hpq with hp | hq2
  · exact hq
  · exact hq

theorem plant_equations : ∀ m : Nat, m + 0 = m
  | 0 => by
    have heqn : (0 : Nat) = 0 := rfl
    rfl
  | _ + 1 => rfl

theorem plant_killed (a : Nat) : a = a := by
  have killed : a + 0 = a := rfl
  rfl

/- A remark that quotes Lean's hint, `set_option linter.unusedVariables false in`, or a
`#guard_msgs (drop warning) in`, is not refused: only code is read. Nor is a `#guard_msgs`
around `#print`, as Audit pins its axioms. -/
/-- info: 'SweepSelfTest.plant_intro' does not depend on any axioms -/
#guard_msgs in
#print axioms plant_intro

/- Under `warningAsError`, as Audit/Overlaps.lean sets it, the linter reports an error. -/
set_option warningAsError true

theorem plant_error (a : Nat) : a = a := by
  have herror : a + 0 = a := rfl
  rfl

end SweepSelfTest
"""

# The self-test's record of Prop1, read by tomllib as heath.load_review reads a record,
# so its `#` comments are lost as a real record's are. KF is declared by the `unused` of
# the passage over its run. KG is named in its passage's note and `#` comments, never in
# `unused`, and so is not. hstated is declared; hjoin, listed with it, stands under
# another run, and so is not, and check_fidelity.unbound_unused reports it. hpair is
# listed there too, but the result it is part of keeps hpair2 as well, which is not, so
# that result is not declared. `this` is named in a comment only, and n in a note only.
PLANT_RECORD = """\
[statement]
scope = "full"

[route]
kind = "euclid"

[[passage]]
at = "Let KF be joined;"
kind = "carried"
note = "The Lean joins KF by Postulate 1, as Euclid asks."
unused = ["KF"]

[[passage]]
at = "and let KG be joined."
kind = "carried"
note = "The Lean joins KG by Postulate 1, and does not use KG again."
# unused = ["KG"]
# KG: joined as Euclid asks, and not used again

[[passage]]
at = "Therefore K is not F."
kind = "carried"
note = "The Lean states that K is not F, as Euclid does; nothing after uses it."
unused = ["hstated", "hjoin", "hpair"]

[[passage]]
at = "Then the rest follows."
kind = "carried"
note = "The Lean carries this sentence; n is only a number."
# this: stated as Euclid states it, and not used again

[review]
stage = "exceptions"
reviewer = "the sweep's self-test"
"""
# What check_fidelity.unbound_unused must report of it: hjoin, under the wrong run.
PLANT_UNBOUND = [(3, "Therefore K is not F.", ["hjoin"])]
# Shapes of binding that check_fidelity.bound_names must read, and the names each binds.
BOUND_CASES = [
    ("obtain ⟨KF, -, -⟩ := Postulate1 K F hKF", {"KF"}),
    ("obtain ⟨L, (hK : OnLine K L), _⟩ := x", {"L", "hK"}),
    ("have hstated : K ≠ F := hKF", {"hstated"}),
    ("have : OnLine K L := hK", {"this"}),
    ("have := Postulate1 K G hKG", {"this"}),
    ("let n := (2 : Nat)", {"n"}),
    ("rcases h with ⟨x, rfl⟩ | hy", {"x", "hy"}),
    ("rcases Postulate1 K F hKF with\n    ⟨KM, -, -⟩", {"KM"}),
    ("  rcases between_cases a b\n      c with h | ⟨x, hx⟩", {"h", "x", "hx"}),
    ("  rcases h\n  exact { h with left := hp }", set()),   # a later tactic's `with`
    ("intro a ⟨b, -⟩ c", {"a", "b", "c"}),
    ("exact (fun (h : K ≠ F) => hused) hline", {"h"}),
    ("exact hstated.symm", set()),
]

HELPER_PLANTS = """namespace SweepSelfTest

open Elements

/-- A helper. -/
theorem Prop2.figure {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L :=
  Postulate1 A B h

/-- Plant: the whole conclusion behind a helper. -/
theorem Prop2 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  exact Prop2.figure h

/-- Control: the helper supplies one step, which the proof goes on from. -/
theorem Prop3 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine B L ∧ OnLine A L := by
  obtain ⟨L, hA, hB⟩ := Prop2.figure h
  exact ⟨L, hB, hA⟩

/-- Control: an entry that cites another entry. -/
theorem Prop4 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := Prop2 h

/-- Plant: a step that feeds nothing, then the helper. -/
theorem Prop5 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  have hBA : B ≠ A := h.symm
  exact Prop2.figure h

/-- A helper that takes a step the proof supplies. -/
theorem Prop6.flip {A B : Point} (h : B ≠ A) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  obtain ⟨L, hB, hA⟩ := Postulate1 B A h
  exact ⟨L, hA, hB⟩

/-- Control: the proof's own step feeds the helper that finishes it. -/
theorem Prop6 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  have hBA : B ≠ A := h.symm
  exact Prop6.flip hBA

/-- Plant: a step that is the helper's statement exactly, and nothing after it. -/
theorem Prop7 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  have hw := Prop2.figure h
  exact hw

/-- A helper, private to this file. -/
private theorem Prop8.hidden {A B : Point} (h : A ≠ B) :
    ∃ L : Line, OnLine A L ∧ OnLine B L :=
  Postulate1 A B h

/-- Plant: the whole conclusion behind a private helper. -/
theorem Prop8 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  exact Prop8.hidden h

/-- A helper that gives the figure, two facts at once. -/
theorem Prop9.figure {A B : Point} (h : A ≠ B) :
    B ≠ A ∧ ∃ L : Line, OnLine A L ∧ OnLine B L :=
  ⟨h.symm, Postulate1 A B h⟩

/-- Plant: the whole conclusion, one part of a helper's. -/
theorem Prop9 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  exact (Prop9.figure h).2

/-- A helper. -/
theorem Prop10.ne {A B : Point} (h : A ≠ B) : B ≠ A := h.symm

/-- Plant: the whole conclusion, a helper's turned round. -/
theorem Prop10 {A B : Point} (h : A ≠ B) : A ≠ B := by
  exact (Prop10.ne h).symm

/-- A helper: an iff. -/
theorem Prop11.iff {A B : Point} : A ≠ B ↔ B ≠ A := ⟨Ne.symm, Ne.symm⟩

/-- Plant: the whole conclusion, one way of a helper's iff. -/
theorem Prop11 {A B : Point} (h : A ≠ B) : B ≠ A := Prop11.iff.mp h

/-- Control: the helper's iff is applied to the proof's own step. -/
theorem Prop12 {A B : Point} (h : A ≠ B) : A ≠ B := by
  have hBA : B ≠ A := h.symm
  exact Prop11.iff.mp hBA

-- Plant: Prop9's proof with its `.2` as Lean's primitive projection, which the
-- elaborator writes as `And.right` but a tactic may leave in a proof term. It has no
-- place in this file, so its hit is reported at line 0.
open Lean Meta in
run_meta do
  let ci ← getConstInfo ``Prop9
  let v ← forallTelescope ci.type fun xs _ =>
    mkLambdaFVars xs (.proj ``And 1 (mkAppN (.const ``Prop9.figure []) xs))
  addDecl (.thmDecl { name := `SweepSelfTest.Prop13, levelParams := [], type := ci.type,
                      value := v })

/-- Plant: a case split of a hypothesis, each branch the helper, fed by nothing. -/
theorem Prop14 {A B : Point} (h : A ≠ B) (p : Prop) (hp : p ∨ ¬p) :
    ∃ L : Line, OnLine A L ∧ OnLine B L := by
  rcases hp with h1 | h2
  · exact Prop2.figure h
  · exact Prop2.figure h

/-- Control: a case split of the proof's own step, each branch feeding the helper. -/
theorem Prop15 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  have hor : B ≠ A ∨ B ≠ A := Or.inl h.symm
  rcases hor with h1 | h2
  · exact Prop6.flip h1
  · exact Prop6.flip h2

/-- A helper: an equality turned round. -/
theorem Prop16.eq {A B : Point} (h : A = B) : B = A := h.symm

/-- Plant: the whole conclusion, a helper's equality turned round. -/
theorem Prop16 {A B : Point} (h : A = B) : A = B := (Prop16.eq h).symm

/-- Plant: the whole conclusion, one way of a helper's iff, not applied. -/
theorem Prop17 {A B : Point} : A ≠ B → B ≠ A := Prop11.iff.mp

/-- Plant: the whole conclusion, the other way of a helper's iff. -/
theorem Prop18 {A B : Point} (h : B ≠ A) : A ≠ B := Prop11.iff.mpr h

/-- Plant: the whole conclusion, the first part of a helper's. -/
theorem Prop19 {A B : Point} (h : A ≠ B) : B ≠ A := (Prop9.figure h).1

/-- Plant: the whole conclusion, a helper's iff turned round. -/
theorem Prop20 {A B : Point} : B ≠ A ↔ A ≠ B := Prop11.iff.symm

/-- Plant: a step bound to a helper's result, one part of which is returned. -/
theorem Prop21 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  have hw := Prop9.figure h
  exact hw.2

/-- Plant: a helper's result taken apart, and one part returned as it is. -/
theorem Prop22 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  obtain ⟨-, hL⟩ := Prop9.figure h
  exact hL

/-- A figure of the self-test's own, and a helper that gives it. -/
structure Prop23.Fig (A B : Point) : Prop where
  ne : B ≠ A
  line : ∃ L : Line, OnLine A L ∧ OnLine B L

theorem Prop23.fig {A B : Point} (h : A ≠ B) : Prop23.Fig A B := ⟨h.symm, Postulate1 A B h⟩

/-- Plant: the whole conclusion, a field of a helper's figure; the helper is `Prop23.fig`,
not the field. -/
theorem Prop23 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L :=
  (Prop23.fig h).line

/-- Control: a field of a figure that the statement gives, not a helper. -/
theorem Prop24 {A B : Point} (hf : Prop23.Fig A B) : ∃ L : Line, OnLine A L ∧ OnLine B L :=
  hf.line

/-- Plant: a reductio whose contradiction is a helper stating exactly the entry's
statement. -/
theorem Prop25 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L :=
  Classical.byContradiction fun hn => hn (Prop2.figure h)

/-- Control: a part of the helper's result, put together with the line it gives. -/
theorem Prop26 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L := by
  obtain ⟨L, hA, -⟩ := Prop2.figure h
  exact ⟨L, hA⟩

/-- Control: a match on two terms that returns a part of the second, a hypothesis. -/
theorem Prop27 {A B : Point} (h : A ≠ B) (hp : B ≠ A ∧ ∃ L : Line, OnLine A L ∧ OnLine B L) :
    ∃ L : Line, OnLine A L ∧ OnLine B L :=
  match Prop9.figure h, hp with
  | _, ⟨_, hL⟩ => hL

/-- Control: the parts of a helper's result, put together the other way round. -/
theorem Prop28 {A B : Point} (h : A ≠ B) :
    (∃ L : Line, OnLine A L ∧ OnLine B L) ∧ B ≠ A := by
  obtain ⟨hne, hL⟩ := Prop9.figure h
  exact ⟨hL, hne⟩

/-- A helper that does the whole reductio. -/
theorem Prop29.contra {A B : Point} (h : A ≠ B) (hn : ¬∃ L : Line, OnLine A L ∧ OnLine B L) :
    False :=
  hn (Postulate1 A B h)

/-- Plant: a reductio whose contradiction is all the helper's. -/
theorem Prop29 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L :=
  Classical.byContradiction fun hn => Prop29.contra h hn

/-- Plant: the goal rewritten, a cast, then the helper. -/
theorem Prop30 {A B : Point} (h : A ≠ B) :
    (fun X => ∃ L : Line, OnLine X L ∧ OnLine B L) A := by
  rw [show ((fun X => ∃ L : Line, OnLine X L ∧ OnLine B L) A) =
      (∃ L : Line, OnLine A L ∧ OnLine B L) from rfl]
  exact Prop2.figure h

/-- Plant: the goal shown in another form, then the helper. -/
theorem Prop31 {A B : Point} (h : A ≠ B) :
    (fun X => ∃ L : Line, OnLine X L ∧ OnLine B L) A := by
  show ∃ L : Line, OnLine A L ∧ OnLine B L
  exact Prop2.figure h

/-- Control: an `if`, one branch the helper, the other a rule of the foundations. -/
theorem Prop32 {A B : Point} (h : A ≠ B) (p : Prop) [Decidable p] :
    ∃ L : Line, OnLine A L ∧ OnLine B L :=
  if hp : p then Prop2.figure h else Postulate1 A B h

/-- Control: the whole proof one proved rule of the foundations, Common Notion 1. -/
theorem Prop33 {a b c : Nat} (h₁ : a = c) (h₂ : b = c) : a = b := CommonNotion1 h₁ h₂

/-- A class of the self-test's own, and an instance of it. -/
class Prop34.Turn (α : Type) : Prop where
  turn : ∀ a b : α, a ≠ b → b ≠ a

instance Prop34.inst : Prop34.Turn Point := ⟨fun _ _ h => h.symm⟩

/-- Control: a class's law, which is no field of a figure: its instance is no helper. -/
theorem Prop34 {A B : Point} (h : A ≠ B) : B ≠ A := Prop34.Turn.turn A B h

/-- Plant: a case split by excluded middle, no step of the proof's, each branch the
helper. -/
theorem Prop35 {A B : Point} (h : A ≠ B) (p : Prop) : ∃ L : Line, OnLine A L ∧ OnLine B L :=
  match Classical.em p with
  | .inl _ => Prop2.figure h
  | .inr _ => Prop2.figure h

/-- A helper that gives three facts at once. -/
theorem Prop36.figure {A B : Point} (h : A ≠ B) :
    A ≠ B ∧ B ≠ A ∧ ∃ L : Line, OnLine A L ∧ OnLine B L :=
  ⟨h, h.symm, Postulate1 A B h⟩

/-- Plant: a part of a helper's result taken apart, and one part of that returned as it
is. -/
theorem Prop36 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  obtain ⟨-, hL⟩ := (Prop36.figure h).2
  exact hL

-- Plant: Prop2's proof with the helper's application wrapped in metadata, which a tactic
-- may leave in a proof term. It has no place in this file, so its hit is reported at
-- line 0.
open Lean Meta in
run_meta do
  let ci ← getConstInfo ``Prop2
  let v ← forallTelescope ci.type fun xs _ =>
    mkLambdaFVars xs (.mdata {} (mkAppN (.const ``Prop2.figure []) xs))
  addDecl (.thmDecl { name := `SweepSelfTest.Prop37, levelParams := [], type := ci.type,
                      value := v })

/-- Control: a part of a helper's result taken apart, and its part fed to another helper. -/
theorem Prop38 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  obtain ⟨hne, -⟩ := (Prop36.figure h).2
  exact Prop6.flip hne

/-- Plant: a helper's result through `id` taken apart, and one part returned as it is: a
split's parts are read on whether or not the proof counts the split as its own step. -/
theorem Prop39 {A B : Point} (h : A ≠ B) : ∃ L : Line, OnLine A L ∧ OnLine B L := by
  obtain ⟨-, hL⟩ := id (Prop9.figure h)
  exact hL

/-- Plant: a part of a hypothesis taken apart, and its part fed to a helper that gives the
whole conclusion: a field of what the proof did not obtain is not a step of its own. -/
theorem Prop40 {A B : Point} (hp : A ≠ B ∧ B ≠ A ∧ B ≠ A) :
    ∃ L : Line, OnLine A L ∧ OnLine B L := by
  obtain ⟨hne, -⟩ := hp.2
  exact Prop6.flip hne

end SweepSelfTest
"""
# The shape (SHAPES) each planted entry's helper must be reported with; the controls'
# helpers must not be reported. Prop7's step, the helper's result returned whole, is read
# as the helper itself. Read wrongly, Prop31 and Prop37 would still be reported, but as
# `restates`, and Prop35 as `unfed`: their shapes are what is checked.
HELPER_SHAPES = {"Prop2": "whole", "Prop5": "unfed", "Prop7": "whole", "Prop8": "whole",
                 "Prop9": "whole", "Prop10": "whole", "Prop11": "whole", "Prop13": "whole",
                 "Prop14": "whole", "Prop16": "whole", "Prop17": "whole", "Prop18": "whole",
                 "Prop19": "whole", "Prop20": "whole", "Prop21": "whole", "Prop22": "whole",
                 "Prop23": "whole", "Prop25": "restates", "Prop29": "whole",
                 "Prop30": "whole", "Prop31": "whole", "Prop35": "whole", "Prop36": "whole",
                 "Prop37": "whole", "Prop39": "whole", "Prop40": "whole"}
HELPER_CONTROLS = ["Prop3", "Prop4", "Prop6", "Prop12", "Prop15", "Prop24", "Prop26",
                   "Prop27", "Prop28", "Prop32", "Prop33", "Prop34", "Prop38"]
HELPER_ENTRIES = [f"SweepSelfTest.{e}" for e in
                  sorted([*HELPER_SHAPES, *HELPER_CONTROLS], key=lambda e: int(e[4:]))]

# (kind, name, declared?) that must be reported; names that must not be, as any hit.
EXPECTED = [
    ("discarded", "KF", True),        # the declared join: in `unused` over its run
    ("discarded", "KG", False),       # named in its passage's note and `#` comments only
    ("unused-have", "hstated", True), # a stated fact, in `unused` over its run
    ("unused-have", "hjoin", False),  # a citation never used, in `unused` over another run
    ("discarded", "hpair, hpair2", False),  # two names kept, one in `unused` over its run
    ("discarded", "(cleared)", False),  # obtain - := …, every part cleared
    ("underscore", "_", False),       # have _ := hKG
    ("unused-have", "this", False),   # an anonymous have, named in a `#` comment only
    ("unused-let", "n", False),       # named in a note only
    ("unused-obtain", "hF", False),   # one part of a result whose other parts are used
    ("unused-intro", "m", False),
    ("underscore", "_hnamed", False), # a `_` name the proof writes again: used, by name
    ("discarded", "KM", False),       # rcases … with, the pattern on the next line
    ("discarded", "KN", False),       # rcases … with, the `with` on the next line
    ("unused-binding", "hp", False),  # a case split's names: never `discarded`
    ("unused-binding", "hq2", False),
    ("unused-binding", "hsuf", False),  # `suffices` binds it
    ("unused-have", "heqn", False),   # in a proof by equations
    ("unused-have", "killed", False), # a crash's word as a name: never a refusal
    ("unused-have", "herror", False), # under `warningAsError`, reported as an error
    ("helper", "SweepSelfTest.Prop2.figure", False),   # Prop2, 5, 7, 14, 25, 30, 31, 35, 37
    ("helper", "SweepSelfTest.Prop29.contra", False),  # behind a reductio's opening
    ("helper", "SweepSelfTest.Prop36.figure", False),  # a part of a part, taken apart
    ("helper", "SweepSelfTest.Prop8.hidden", False),   # private, named as written
    ("helper", "SweepSelfTest.Prop9.figure", False),   # `.2`, `.1`, a step's, `id`: 9, 13, 19, 21, 22, 39
    ("helper", "SweepSelfTest.Prop6.flip", False),     # fed by a part of a hypothesis alone: 40
    ("helper", "SweepSelfTest.Prop10.ne", False),      # its `.symm`
    ("helper", "SweepSelfTest.Prop11.iff", False),     # `.mp`, `.mpr`, `.symm`: 11, 17, 18, 20
    ("helper", "SweepSelfTest.Prop16.eq", False),      # an equality's `.symm`
    ("helper", "SweepSelfTest.Prop23.fig", False),     # a field of its figure, never the field
]
# hline is handed to a function that ignores it, `(fun _ => …) hline`: a shape the sweep
# does not see, which README names; it stays a control so that a change there shows. L2
# is kept by a pattern whose `_` part counts as used.
CONTROLS = ["hused", "hline", "hauto", "hsimp", "hidle", "L", "hK", "h", "a", "b", "hpq",
            "hq", "L2"]

# Files the sweep must refuse (SweepError, exit 2). One sets the linter's options itself,
# in several spellings and spacings, one behind a `/--/` and one behind a `/-/-` (every
# comment's body begins at its fourth character, as Lean reads it), captures its messages
# with `#guard_msgs`, or has a `sorry` that never runs, on the lines SILENCED_AT names; it
# elaborates, so that only the refusal stands between it and a quiet pass. The other does
# not elaborate, and Lean would drop the hits of what fails while it reports the rest, as
# hok.
SILENCED_LEAN = """\
set_option linter.unusedVariables false in
theorem silenced (a : Nat) : a = a := by
  have hsilenced : a + 0 = a := rfl
  rfl

set_option «linter».unusedVariables.analyzeTactics false in
theorem unanalysed (a b : Nat) (h : a = b) : b = a := by
  have hunanalysed : a = b := h
  simp_all

theorem inner (a : Nat) : a = a := by
  set_option linter.«unusedVariables».patternVars false in
  have hinner : a + 0 = a := rfl
  rfl

#guard_msgs (drop warning) in
theorem guarded (a : Nat) : a = a := by
  have hguarded : a + 0 = a := rfl
  rfl

/-- warning: Variable name `hexpected` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly).
Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hexpected

Note: This linter can be disabled with `set_option linter.unusedVariables false` -/
#guard_msgs in
theorem expected (a : Nat) : a = a := by
  have hexpected : a + 0 = a := rfl
  rfl

set_option«linter».unusedVariables false in
theorem nospace (a : Nat) : a = a := by
  have hnospace : a + 0 = a := rfl
  rfl

#guard_msgs (drop warning)in
theorem guardednospace (a : Nat) : a = a := by
  have hguardednospace : a + 0 = a := rfl
  rfl

/--/ " -/
theorem desynced : True := trivial

set_option linter.unusedVariables false in
theorem hidden (a : Nat) : a = a := by
  have hhidden : a + 0 = a := rfl
  rfl
-- "

theorem deadsorry (a : Nat) : a = a := by
  have hdead : a + 0 = a := rfl
  first | rfl | sorry

/-/- -/
set_option linter.unusedVariables false in
theorem plainhidden (a : Nat) : a = a := by
  have hplainhidden : a + 0 = a := rfl
  rfl
-- -/

set_option
  linter.unusedVariables.funArgs false
"""
SILENCED_AT = [1, 6, 12, 16, 28, 33, 38, 46, 54, 57, 63]
UNELABORATED_LEAN = """\
theorem elaborated (a : Nat) : a = a := by
  have hok : a + 0 = a := rfl
  rfl

theorem unelaborated : (0 : Nat) = 1 := rfl
"""
# A staged statement and an `admit` that never runs (the fourth review's probe Q7 shows
# that Lean's linter passes over its declaration): refused outside Staging, naming lines 1
# and 5, of which the self-test checks the `admit`'s.
ADMITTED_LEAN = """\
theorem staged : (0 : Nat) = 0 := sorry

theorem admitted (a : Nat) : a = a := by
  rfl
  all_goals admit
"""


def refusal(text: str, path: Path) -> str | None:
    """What the sweep says as it refuses the Lean `text`, written at `path`; None if it
    runs."""
    path.write_text(text)
    try:
        sweep([(path, path.name)], lambda rel: None, [], [])
    except SweepError as e:
        return str(e)
    return None


# Panics as Lean prints them, for the self-test's runs of Lean (#236): the first line of each
# is the line a refusal must name.
PANIC_AT = ("PANIC at Lean.Elab.Term.elabTermEnsuringType Lean.Elab.Term:1712:14: "
            "unreachable code has been reached")
PANIC_TRACE = ("\nbacktrace:\n/home/lean/.elan/toolchains/lean4/bin/lean(lean_panic_fn+0x8f)"
               " [0x5581f2c3a1bf]\n")
INTERNAL_PANIC = "INTERNAL PANIC: out of memory"
DROPPED_PROMISE = ("PANIC: Promise.result!: promise has been dropped without ever being "
                   "resolved")


def self_test() -> int:
    """Plant each kind of hit, and the controls, outside the tree; 1 on any miss."""
    problems = []
    record = heath._toml().loads(PLANT_RECORD)
    problems += [f"the self-test's record breaks review/SCHEMA.md: {p}"
                 for p in heath._shape(record, require_stamp=False)]
    with tempfile.TemporaryDirectory(prefix="sweep-citations-self-test-") as tmp:
        plant = Path(tmp) / "SweepPlants.lean"
        plant.write_text(PLANTS_LEAN)
        prop = Proposition(1, record["passage"], "the self-test's record")
        hits = sweep([(plant, "SweepPlants.lean")],
                     lambda rel: prop if rel == "SweepPlants.lean" else None,
                     HELPER_ENTRIES, ["Elements.Foundations.Postulates",
                                      "Elements.Foundations.CommonNotions"], HELPER_PLANTS)
        silenced = refusal(SILENCED_LEAN, Path(tmp) / "SweepSilenced.lean")
        unelaborated = refusal(UNELABORATED_LEAN, Path(tmp) / "SweepUnelaborated.lean")
        # Lean exits 1 with no error at a line of a file: only the exit code shows it.
        try:
            run_lean(Path(tmp) / "SweepMissing.lean", LINT, "a file that is not there")
            missing = None
        except SweepError as e:
            missing = str(e)
        warning = (f"{plant}:1:1: warning: Variable name `hwarning` is not explicitly "
                   "referenced.\n")
        promoted = warning.replace("warning:", "error:")
        killed = (f"{plant}:2:7: warning: Variable name `killed` is not explicitly "
                  "referenced.\n\nHint: The binding can be removed (if unused) or named `_` "
                  "(if used implicitly). Alternatively, prefix the name with `_` to silence "
                  "this warning:\n  [apply] _killed\n\nNote: This linter can be disabled "
                  "with `set_option linter.unusedVariables false`\n")
        # (what Lean did, its exit, its output, its standard error, whether it is read)
        runs = [
            ("a warning, then a signal", -9, warning, "", False),
            ("a warning, then an abort", 134, warning, "", False),
            ("a warning, then exit 1", 1, warning, "", False),
            ("a promoted warning, then a signal", -6, promoted, "", False),
            ("a promoted warning, then an abort", 134, promoted, "", False),
            ("a promoted warning, then exit 2", 2, promoted, "", False),
            ("a promoted warning, then a panic", 1,
             promoted + "PANIC at Lean.Elab.Command\n", "", False),
            ("a promoted warning, then a failed process", 1,
             promoted + "process exited with code 134\n", "", False),
            ("a failed process, then a promoted warning", 1,
             "process exited with code 134\n" + promoted, "", False),
            ("a promoted warning, and a stack overflow", 1, promoted,
             "Stack overflow detected. Aborting.\n", False),
            ("a promoted warning", 1, promoted, "", True),
            ("a promoted warning, in full", 1,
             killed.replace("warning:", "error:", 1), "", True),
            ("an unused binding named killed", 0, killed, "", True),
            # Panics on exit 0, with no error line (#236), and a message that only quotes one.
            ("a panic and its backtrace, then exit 0", 0, PANIC_AT + PANIC_TRACE, "", False),
            ("a warning, then an internal panic, then exit 0", 0,
             killed + INTERNAL_PANIC + "\n", "", False),
            ("a warning, and a panic on standard error, then exit 0", 0, killed,
             PANIC_AT + "\n", False),
            ("Lean's dropped promise, then exit 0", 0, DROPPED_PROMISE + "\n", "", False),
            ("a warning that quotes a panic within its line", 0,
             f"{plant}:3:2: warning: a note that says PANIC at Lean.Elab.Command\n", "", True),
        ]
        # Each run refused for a panic, and the line its refusal must name.
        panics = {"a promoted warning, then a panic": "PANIC at Lean.Elab.Command",
                  "a panic and its backtrace, then exit 0": PANIC_AT,
                  "a warning, then an internal panic, then exit 0": INTERNAL_PANIC,
                  "a warning, and a panic on standard error, then exit 0": PANIC_AT,
                  "Lean's dropped promise, then exit 0": DROPPED_PROMISE}
        outcomes = {}
        for what, returncode, output, stderr, _ in runs:
            with unittest.mock.patch.object(
                    subprocess, "run",
                    return_value=subprocess.CompletedProcess([], returncode, output, stderr)):
                try:
                    run_lean(plant, LINT, f"the self-test's run of {what}")
                    outcomes[what] = None
                except SweepError as e:
                    outcomes[what] = str(e)
    print_hits(hits)
    for kind, name, declared in EXPECTED:
        found = [h for h in hits if h.kind == kind and h.name == name]
        if not found:
            problems.append(f"plant missed: {kind} {name}")
        elif any(bool(h.declared) != declared for h in found):
            problems.append(f"plant {kind} {name} reported as "
                            f"{'declared' if found[0].declared else 'undeclared'}")
    if not any(h.name == "_hnamed" and "names it again" in h.why for h in hits):
        problems.append("plant misread: `_hnamed`, which the proof names again, is not "
                        "reported as used by name")
    if not any(h.name == "hsuf" and "`suffices` binds hsuf" in h.why for h in hits):
        problems.append("plant misread: hsuf is not reported as bound by `suffices`")
    # A helper hit is never declared, even by a name in `unused` over its run.
    kf = next((h for h in hits if h.name == "KF"), None)
    if kf and declaring(kf._replace(kind="helper"), PLANTS_LEAN, prop) is not None:
        problems.append("a helper hit is declared by a name in `unused`")
    if silenced is None or any(f"SweepSilenced.lean:{n}: " not in silenced
                               for n in SILENCED_AT):
        problems.append(f"a file that sets the linter's options or captures its messages is "
                        f"not refused, naming each of its lines {SILENCED_AT}: {silenced!r}")
    if unelaborated is None or "could not elaborate" not in unelaborated:
        problems.append(f"a file that does not elaborate is not refused: {unelaborated!r}")
    if missing is None or "could not elaborate" not in missing:
        problems.append(f"a run of Lean that fails with no error at a line is not refused: "
                        f"{missing!r}")
    for what, _, _, _, read in runs:
        if read and outcomes[what] is not None:
            problems.append(f"a Lean run of {what} is refused: {outcomes[what]!r}")
        elif not read and outcomes[what] is None:
            problems.append(f"a Lean run of {what} is accepted")
    for what, line in panics.items():
        said = outcomes[what]
        if said is None or "Lean panicked" not in said or not said.endswith("\n" + line):
            problems.append(f"a Lean run of {what} is refused without naming its panic "
                            f"{line!r}: {outcomes[what]!r}")
    helpers = [h for h in hits if h.kind == "helper"]
    for entry, shape in HELPER_SHAPES.items():
        mine = [h for h in helpers if h.why.startswith(f"SweepSelfTest.{entry}:")]
        if not any(SHAPES[shape] in h.why for h in mine):
            problems.append(f"plant missed: the helper behind SweepSelfTest.{entry}, as "
                            f"`{shape}`")
    for entry in HELPER_CONTROLS:
        if any(h.why.startswith(f"SweepSelfTest.{entry}:") for h in helpers):
            problems.append(f"control reported: SweepSelfTest.{entry}'s helper")
    for name in CONTROLS:
        if any(name in (n.strip() for n in h.name.split(",")) for h in hits):
            problems.append(f"control reported: {name}")
    expected = {(k, n) for k, n, _ in EXPECTED}
    for h in hits:
        if (h.kind, h.name) not in expected:
            problems.append(f"unexpected hit: {h.path}:{h.line}: {h.kind}: {h.name}")
    if exit_code(hits, True) != 1 or exit_code([h for h in hits if h.declared], True) != 0:
        problems.append("--fail-on-undeclared does not exit 1 on undeclared hits alone")
    # check_fidelity's half: a name in `unused` that the Lean beneath does not bind.
    unbound = check_fidelity.unbound_unused(PLANTS_LEAN, 1, record["passage"])
    if unbound != PLANT_UNBOUND:
        problems.append(f"check_fidelity.unbound_unused reports {unbound}, not {PLANT_UNBOUND}")
    for code, want in BOUND_CASES:
        got = check_fidelity.bound_names(code)
        if got != want:
            problems.append(f"check_fidelity.bound_names({code!r}) is {sorted(got)}, "
                            f"not {sorted(want)}")
    # Read without Lean: `admit` is refused as `sorry` is, but not in Staging, whose
    # statements await their proofs; and the reader shared with check_fidelity begins
    # every comment's body at its fourth character, as Lean does, so that `/--/ x -/` and
    # `/- /- -/ x -/` are each one comment, and `/-/- -/` is one too.
    for rel, refused in (("SweepAdmit.lean", True), ("Staging/SweepAdmit.lean", False)):
        try:
            prepare(ADMITTED_LEAN, rel)
            said = None
        except SweepError as e:
            said = str(e)
        if refused and (said is None or f"{rel}:5: " not in said):
            problems.append(f"a file with `admit` is not refused, naming its line 5: {said!r}")
        if not refused and said is not None:
            problems.append(f"a staged file with `sorry` and `admit` is refused: {said!r}")
    for text, seen in (("/--/ x -/ y", "y"), ("/-/- -/ x", "x"), ("/- /- -/ x -/ y", "y")):
        if code_of(text).split() != [seen]:
            problems.append(f"the reader does not read {text!r} as Lean does, leaving {seen!r}")
    if problems:
        print(f"\nself-test: {len(problems)} problem(s):")
        for p in problems:
            print(f"  ✗ {p}")
        return 1
    print(f"\n✓ self-test: {len(EXPECTED)} plants reported (only those in `unused` over "
          f"their run as declared), {len(HELPER_SHAPES)} entries with their helper's shape, "
          f"{len(CONTROLS) + len(HELPER_CONTROLS)} controls passed, a file that silences the "
          f"linter ({len(SILENCED_AT)} ways), one that does not elaborate and a run of Lean "
          f"that fails with no error at a line refused, "
          f"{sum(not r[4] for r in runs)} failed runs of Lean refused and "
          f"{sum(r[4] for r in runs)} read, `admit` refused outside Staging, "
          f"and check_fidelity reads three comments as Lean does, {len(BOUND_CASES)} shapes "
          f"of binding and the stale `unused` name")
    return 0


# ---------------------------------------------------------------------------------------

def at_least_one(text: str) -> int:
    """`--jobs`: a whole number, 1 or more."""
    try:
        n = int(text)
    except ValueError:
        n = 0
    if n < 1:
        raise argparse.ArgumentTypeError(f"{text!r} is not a whole number of 1 or more")
    return n


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("paths", nargs="*", default=["Elements"],
                        help="trees or Lean files to sweep (default: Elements)")
    parser.add_argument("--fail-on-undeclared", action="store_true",
                        help="exit 1 when any hit is not declared in its record")
    parser.add_argument("--self-test", action="store_true",
                        help="plant each kind of hit outside the tree, and check the sweep")
    parser.add_argument("--jobs", type=at_least_one, default=None,
                        help="files linted at once, 1 or more (default: the number of "
                        "processors)")
    args = parser.parse_args(argv)
    try:
        if args.self_test:
            return self_test()
        began = time.monotonic()
        files = selected(args.paths)
        hits = sweep(files, record_for, entries_in(files), ["Elements"], jobs=args.jobs)
    except SweepError as e:
        print(f"sweep_citations: {e}", file=sys.stderr)
        return 2
    print_hits(hits)
    groups = sorted({group(rel) for _, rel in files}, key=lambda g: group_order(
        next(rel for _, rel in files if group(rel) == g)))
    summary(hits, groups)
    print(f"Swept {len(files)} files in {time.monotonic() - began:.0f} s.")
    return exit_code(hits, args.fail_on_undeclared)


if __name__ == "__main__":
    sys.exit(main())
