"""List the candidates for dummy citations, artificial hypothesis uses and concealing helpers.

FORMALIZATION.md, section 5, asks that the Lean cite only what its argument uses, never
mention a hypothesis only to silence a warning, and never hide a whole conclusion behind
a helper; WORKFLOW.md, section 6, asks reviewers to hunt for all three; brief 0005's stage
5 promises a script that lists the candidates (#32). This is that script. It lists, for
the Lean under `Elements/` (and `Staging/` or `Audit/`, or single files, when named):

* **unused bindings in proofs**: a `have`, `let`, `obtain`, `rcases` or `intro` whose
  name nothing uses (kinds `unused-have`, `unused-let`, `unused-obtain` for one unused
  part of a result whose other parts are used, `unused-intro`, and `unused-binding` for
  the rest, such as a case split's names);
* **discarded results** (`discarded`): an `obtain` or `rcases` whose whole result goes
  unused, as `obtain ⟨KF, -, -⟩ := Postulate1 …` when KF is never named again: a citation
  whose result is bound and never used;
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
   `simp_all`, `omega` or `grind` uses without naming it counts as used. The linter reads
   a copy of the file, outside the tree, in which two things are renamed, lines kept:
   each anonymous `have` is named `this`, which Lean then checks (it passes over the
   name Lean gives an anonymous `have`), and each `_`-named binding is given a plain
   name, so Lean says whether anything uses it. A binder of the statement itself (an
   unused hypothesis) is not listed: FORMALIZATION, section 5, makes that a review prompt
   and a `redundant-hypothesis` tag, not a dummy citation.
2. **A textual pass for exactly one shape the linter cannot see**: a name an `obtain` or
   `rcases` pattern keeps, whose other parts are all cleared (`-`) or found unused by
   Lean, and which is never written again in its declaration, as `obtain ⟨KF, -, -⟩`.
   Lean counts KF as used, because the facts it clears mention KF in the tactic states
   it reads. The pass stands aside when automation that can use a hypothesis without
   naming it (`assumption`, `simp_all`, `simpa`, `omega`, `grind`, `trivial`, `‹…›`, and
   their kind: AUTOMATION, below) follows in the declaration, and a `_` part counts as
   used, since automation may use it. `_`-named bindings are found by their text too
   (they are what they are, used or not), and Lean says whether each is used.
3. **Lean's proof terms** for helpers: one run of Lean, with `import Lean` and `import
   Elements`, reads each entry's proof term past its intros, its `have`, `let` and
   `obtain` steps, its case splits, a reductio's opening, a cast and the parts of an
   anonymous constructor. A helper is a theorem or definition of the project's own that
   is not an entry, nor from `Elements/Foundations/` (an axiom, a Common Notion or a
   proved rule, which the overlap catalogue and a record's `[overlap]` answer for), nor a
   declaration Lean made for another. Staging and Audit hold no entries, so this part
   reads only `Elements/`.

**Declared hits.** A hit is declared when the review record of its proposition,
`review/<book>/NN.toml`, has a `[[passage]]` whose `at` begins a sentence of the run of
`--` lines (Euclid's words) under which the hit's line stands, and which names the
binding, as a whole word:

* a point or a straight line, in Euclid's letters (FC, KF, N), in the passage's `note`,
  as train Tw2 declares the Postulate 1 joins of I.5 and I.11: "The Lean joins FC and GB
  by Postulate 1, as Euclid asks"; or in a `#` comment of the passage's table;
* a hypothesis, or `this` for an anonymous `have`, in a `#` comment of the passage's
  table alone, between its `[[passage]]` line and the next table: a note says a
  hypothesis in words, never by its local name, and a record's `#` comments, which no
  page shows, may name it as the Lean does (STYLE, section 1, "Hypotheses in words");
* a helper, as the passage's `helper`, or in its note or a comment.

The runs and sentences are read as `check_fidelity.py` reads them (`proof_lines`,
`sentence_starts`), so a passage that declares a run there declares the hits beneath it
here. Only a hit inside `theorem PropN` can be declared: no `--` line stands over a
helper's or a companion's proof. The decisions page's ruling of 20 October 2026 is why a
join stays: it stays wherever a sentence of Euclid's stands over it, and is then
declared, not deleted; and FORMALIZATION, section 5, allows a checked intermediate fact
tied to a real sentence of Euclid's, which is declared in the same way.

Each hit is printed as `file:line: kind: name: why`, a declared one followed by
`(declared in review/…)`, then a summary for each book. Exits 0 after listing;
`--fail-on-undeclared` exits 1 when any undeclared hit remains (the release gate,
docs/WORKFLOW.md, section 10); 2 when the sweep cannot run (no Lean, an unbuilt library,
a file that does not elaborate, a facts.json that does not match Lean).

    python3 scripts/sweep_citations.py                       Elements/
    python3 scripts/sweep_citations.py Elements Staging Audit  these trees (or files)
    python3 scripts/sweep_citations.py --fail-on-undeclared  the release gate
    python3 scripts/sweep_citations.py --self-test           plants and controls

`--self-test` writes planted Lean outside the tree (each kind of hit, each of which must
be reported, and controls that must not be: a binding used later, one used by
`assumption` or `simp_all`, an unused hypothesis of the statement, a declared join, a
helper that supplies one step, an entry that cites another) and exits 1 naming any plant
missed or control reported. Both it and the sweep need the library built by `lake build`
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
from pathlib import Path
from typing import Callable, NamedTuple

import check_fidelity
import heath

ROOT = heath.ROOT
FACTS = ROOT / "facts.json"
LINT = ["-Dlinter.unusedVariables=true", "-Dlinter.unusedVariables.analyzeTactics=true"]
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
WARNING = re.compile(r"^(?P<file>.+?):(?P<line>\d+):(?P<col>\d+): (?:warning|error): "
                     r"(?:Variable name|unused variable) `(?P<name>[^`]+)`", re.M)
ERROR = re.compile(r"^.+?:\d+:\d+: error\b(?!: (?:Variable name|unused variable) `).*$", re.M)
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
    "choose": "unused-binding", "∀": "unused-binding", "∃": "unused-binding",
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
    brackets, so that a binder of the statement is told from one of the proof."""

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


class Leaf(NamedTuple):
    name: str          # a name, `-` or `_` (or `rfl`)
    offset: int


class Pattern(NamedTuple):
    keyword: str       # obtain or rcases
    offset: int        # the keyword's
    leaves: list
    end: int           # the end of the pattern
    value: str         # what the pattern takes apart, described


def read_pattern(code: str, i: int) -> tuple[list, int]:
    """The leaves of the rcases pattern at `i`, and where it ends. A type ascription in
    brackets, `(h : T)`, gives its name only."""
    while i < len(code) and code[i] in " \t":
        i += 1
    if i >= len(code):
        return [], i
    if code[i] != "⟨":
        m = re.compile(r"-|[^\W\d][\w'!?₀-₉]*").match(code, i)
        return ([Leaf(m.group(0), i)], m.end()) if m else ([], i)
    leaves, depth, j, skip = [], 0, i, None
    while j < len(code):
        c = code[j]
        if c in "⟨(":
            depth += 1
        elif c in "⟩)":
            if skip is not None and depth == skip:
                skip = None
            depth -= 1
            if depth == 0:
                return leaves, j + 1
        elif skip is None and c == ":" and code[j - 1] != ":" and not code.startswith(":=", j):
            skip = depth                     # a type ascription: skip to its bracket's end
        elif skip is None:
            m = re.compile(r"-|[^\W\d][\w'!?₀-₉]*").match(code, j)
            if m and (j == 0 or not (code[j - 1].isalnum() or code[j - 1] in "_'")):
                leaves.append(Leaf(m.group(0), j))
                j = m.end()
                continue
        j += 1
    return leaves, j


def patterns(code: str) -> list[Pattern]:
    """Every `obtain` and `rcases` pattern in the code text."""
    out = []
    for m in PATTERN_KEYWORD.finditer(code):
        if m.group(1) == "obtain":
            leaves, end = read_pattern(code, m.end())
            value = value_after(code, end, len(code))
        else:
            w = re.compile(r"(?<![\w'.])with(?![\w'!?])").search(code, m.end(), m.end() + 600)
            if not w:
                continue
            leaves, end = read_pattern(code, w.end())
            value = _described(code[m.end():w.start()])
        if leaves:
            out.append(Pattern(m.group(1), m.start(), leaves, end, value))
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
    out = r.stdout + r.stderr
    errors = ERROR.findall(out)
    if errors or (r.returncode != 0 and not WARNING.search(out)):
        shown = "\n".join(errors[:5]) or out.strip()[-2000:]
        raise SweepError(f"Lean could not elaborate {what} (exit {r.returncode}); is the "
                         f"library built (`lake build`)?\n{shown}")
    return out


class Copy(NamedTuple):
    """The copy of a file that the linter reads, with what was renamed in it."""
    text: str
    anonymous: set          # lines on which an anonymous `have` was named `this`
    underscore: dict        # copy name -> (line, keyword, original name)


def prepare(src: str) -> Copy:
    """Name each anonymous `have` `this`, and give each `_`-named binding a plain name,
    so that the linter judges them; every line keeps its number."""
    code = code_of(src)
    if RENAMED in src:
        raise SweepError(f"the file already uses the name {RENAMED}, which the sweep needs")
    edits, anonymous, underscore = [], set(), {}
    starts = line_starts(code)
    for m in ANONYMOUS.finditer(code):
        edits.append((m.end(), m.end(), " this"))
        anonymous.add(line_at(starts, m.start()))
    for k, m in enumerate(UNDERSCORE.finditer(code)):
        new = f"{RENAMED}{k}{m.group('name')}"
        edits.append((m.start("name"), m.end("name"), new))
        underscore[new] = (line_at(starts, m.start()), m.group("kw"), m.group("name"))
    text = src
    for a, b, new in sorted(edits, reverse=True):
        text = text[:a] + new + text[b:]
    return Copy(text, anonymous, underscore)


def lint(path: Path, rel: str, workdir: Path) -> tuple[Copy, list]:
    """The linter's warnings for `path`, read from its copy: (line, column, name)."""
    src = path.read_text()
    copy = prepare(src)
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
    for new, (line, kw, original) in copy.underscore.items():
        unused = any(n == new for (_, n) in reported)
        for key in [k for k in reported if k[1] == new]:
            consumed.add(key)
        offset = starts[line - 1]
        _, _, end = decls.at(offset)
        value = value_after(code, offset, end)
        verdict = "Lean finds it unused" if unused else "Lean finds it used, without its name"
        hits.append(Hit(rel, line, "underscore", original,
                        f"`{kw} {original}` binds {value}; a name that begins with `_` keeps "
                        f"Lean's linter quiet, and here {verdict}"))

    # The patterns of `obtain` and `rcases`.
    for p in patterns(code):
        if any(leaf.name.startswith(RENAMED) for leaf in p.leaves):
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
        kw = binder_keyword(code, start, offset) or "a binder"
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
            hits.append(Hit(rel, line, kind, name,
                            f"`{kw}` binds {name}, which Lean finds unused"))
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
the foundations (an axiom, a Common Notion, a proved rule), and not a matcher or a
declaration Lean made for another. -/
def isHelper (entries : NameSet) (c : Name) : MetaM Bool := do
  let env ← getEnv
  if entries.contains c || !isOurs env c || c.isInternalDetail then return false
  if (moduleOf env c).startsWith "Elements.Foundations" then return false
  if ← isMatcher c then return false
  match env.find? c with
  | some (.thmInfo _) | some (.defnInfo _) | some (.opaqueInfo _) => return true
  | _ => return false

partial def strip : Expr → Expr
  | .mdata _ b => strip b
  | e => e

/-- Does the split `e` take apart something the proof obtained: a step, or a citation? -/
def obtained (steps : Array Expr) (e : Expr) : MetaM Bool := do
  if steps.any (fun s => e.containsFVar s.fvarId!) then return true
  match (strip e).getAppFn with
  | .const c _ => return isOurs (← getEnv) c
  | _ => return false

/-- Each term that finishes a branch of the proof `e`, with the steps before it. The proof
is followed past its intros, its `have`, `let` and `obtain` steps, its case splits, a
reductio's opening, a cast and the parts of an anonymous constructor. -/
partial def ends (steps : Array Expr) (e : Expr) : MetaM (Array (Array Expr × Expr)) := do
  let e := strip e
  match e with
  | .lam .. => lambdaTelescope e fun _ b => ends steps b
  | .letE n t v b _ => withLetDecl n t v fun x => ends (steps.push x) (b.instantiate1 x)
  | _ =>
    if e.isAppOfArity ``Classical.byContradiction 2 || e.isAppOfArity ``Eq.mpr 4 ||
        e.isAppOfArity ``id 2 || e.isAppOfArity ``Exists.intro 4 then
      return (← ends steps e.appArg!)
    if e.isAppOfArity ``And.intro 4 || e.isAppOfArity ``Iff.intro 4 ||
        e.isAppOfArity ``dite 5 then
      return (← ends steps e.appFn!.appArg!) ++ (← ends steps e.appArg!)
    if let some app ← matchMatcherApp? e (alsoCasesOn := true) then
      let fromSteps ← app.discrs.anyM (obtained steps)
      let mut out := #[]
      for alt in app.alts do
        out := out ++ (← lambdaTelescope (strip alt) fun xs b =>
          ends (if fromSteps then steps ++ xs else steps) b)
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
  IO.println s!"HIT\t{entry}\t{helper}\t{shape}\t{moduleOf env entry}\t{a}\t{b}\t{moduleOf env helper}\t{h}\t{st}"

def judge (entries : NameSet) (n : Name) : MetaM Unit := do
  let env ← getEnv
  let some ci := env.find? n | IO.println s!"MISSING\t{n}"
  let some v := ci.value? (allowOpaque := true) | IO.println s!"MISSING\t{n}"
  let leaves ← ends #[] v
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
    "whole": "its whole proof, after its intros, is one application of",
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

def runs(src: str, n: int) -> list[list[int]]:
    """The runs of `--` lines in theorem PropN, as check_fidelity reads them: a run is
    ended by a line of Lean or a `/- … -/` remark, not by a blank line."""
    out, current = [], None
    for ln, kind, _ in check_fidelity.proof_lines(src, n):
        if kind == "words":
            if current is None:
                current = []
                out.append(current)
            current.append(ln)
        elif kind in ("lean", "remark"):
            current = None
    return out


def names_in(text: str, name: str) -> bool:
    return re.search(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'!?])", text) is not None


# A name in Euclid's letters: a point or a straight line, as FC, KF or N.
LETTERS = re.compile(r"[A-Z][A-Z'′₀-₉]*")


def declaring(hit: Hit, src: str, prop: Proposition) -> str | None:
    """The record that declares `hit`, or None: a passage that begins a sentence of the
    run of `--` lines above the hit, and names the binding: a point or straight line in
    its note or in a `#` comment of its table; a hypothesis, or `this`, in a comment only,
    since a note says a hypothesis in words (STYLE, section 1, "Hypotheses in words");
    and a helper as its `helper`, or in its note or a comment."""
    rows = check_fidelity.proof_lines(src, prop.n)
    if not rows or not rows[0][0] <= hit.line <= rows[-1][0]:
        return None
    above = [run for run in runs(src, prop.n) if run[-1] < hit.line]
    if not above:
        return None
    run = set(above[-1])
    starts = check_fidelity.sentence_starts(rows)
    names = [name.strip() for name in hit.name.split(",")]
    for p in prop.passages:
        at = check_fidelity._plain(p["at"])
        if not any(ln in run and words.startswith(at) for ln, words in starts):
            continue
        note, comments = p.get("note", ""), "\n".join(p.get("comments", []))
        if hit.kind == "helper":
            parts = hit.name.split(".")
            tails = [".".join(parts[i:]) for i in range(len(parts) - 1)] or [hit.name]
            if p.get("helper") in tails or any(names_in(note + "\n" + comments, t)
                                               for t in tails):
                return prop.record
        elif all(names_in(comments, name)
                 or (LETTERS.fullmatch(name) and names_in(note, name)) for name in names):
            return prop.record
    return None


def passage_comments(text: str) -> list[list[str]]:
    """The full-line `#` comments of each `[[passage]]` table of a record's text, in
    order: those between its header and the next table's."""
    out, current = [], None
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("["):
            current = [] if s == "[[passage]]" else None
            if current is not None:
                out.append(current)
        elif current is not None and s.startswith("#"):
            current.append(s)
    return out


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
    passages = record.get("passage", [])
    comments = passage_comments(path.read_text())
    if len(comments) != len(passages):
        raise SweepError(f"{path.relative_to(ROOT)}: {len(passages)} passages, but "
                         f"{len(comments)} `[[passage]]` lines")
    return Proposition(n, [dict(p, comments=c) for p, c in zip(passages, comments)],
                       path.relative_to(ROOT).as_posix())


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
        if rel.parts[0] not in TREES:
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

end SweepSelfTest
"""

# The declared join: a passage over KF's run that names KF, as Tw2's records do (and KG,
# which stands under another run, and so is not declared by it); one over KG's that does
# not name it, and so declares nothing; a stated fact whose passage names its hypothesis
# in a `#` comment; and a passage over the plants' run whose note says "n" and "this" in
# prose, which declares neither.
PLANT_PASSAGES = [
    {"at": "Let KF be joined;", "kind": "carried",
     "note": "The Lean joins KF by Postulate 1, as Euclid asks; KG follows.",
     "comments": []},
    {"at": "and let KG be joined.", "kind": "carried",
     "note": "The Lean joins the second straight line by Postulate 1.", "comments": []},
    {"at": "Therefore K is not F.", "kind": "carried",
     "note": "The Lean states that K is not F, as Euclid does; nothing after uses it.",
     "comments": ["# hstated: stated as Euclid states it, and not used again"]},
    {"at": "Then the rest follows.", "kind": "carried",
     "note": "The Lean carries this sentence; n is only a number.",
     "comments": ["# nothing here is declared"]},
]
SAMPLE_RECORD = """[statement]
scope = "full"

[[passage]]
at = "Let KF be joined;"
kind = "carried"
note = "The Lean joins KF by Postulate 1."
# KF: joined as Euclid asks

[[passage]]
at = "and let KG be joined."
kind = "given"
note = "Given."

[review]
# not a passage's
stage = "full"
"""

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

end SweepSelfTest
"""
HELPER_ENTRIES = [f"SweepSelfTest.Prop{n}" for n in (2, 3, 4, 5, 6)]

# (kind, name, declared?) that must be reported; names that must not be, as any hit.
EXPECTED = [
    ("discarded", "KF", True),        # the declared join: reported, as declared
    ("discarded", "KG", False),       # obtain ⟨KG, -, -⟩, KG never named again
    ("unused-have", "hstated", True), # a stated fact under its own carried passage
    ("unused-have", "hjoin", False),  # a citation bound and never used
    ("discarded", "(cleared)", False),  # obtain - := …, every part cleared
    ("underscore", "_", False),       # have _ := hKG
    ("unused-have", "this", False),   # an anonymous have, never used
    ("unused-let", "n", False),
    ("unused-obtain", "hF", False),   # one part of a result whose other parts are used
    ("unused-intro", "m", False),
    ("helper", "SweepSelfTest.Prop2.figure", False),   # Prop2, and Prop5 after a step
]
CONTROLS = ["hused", "hline", "hauto", "hsimp", "hidle", "L", "hK", "h", "a", "b"]


def self_test() -> int:
    """Plant each kind of hit, and the controls, outside the tree; 1 on any miss."""
    with tempfile.TemporaryDirectory(prefix="sweep-citations-self-test-") as tmp:
        plant = Path(tmp) / "SweepPlants.lean"
        plant.write_text(PLANTS_LEAN)
        prop = Proposition(1, PLANT_PASSAGES, "the self-test's record")
        hits = sweep([(plant, "SweepPlants.lean")],
                     lambda rel: prop if rel == "SweepPlants.lean" else None,
                     HELPER_ENTRIES, ["Elements.Foundations.Postulates"], HELPER_PLANTS)
    print_hits(hits)
    problems = []
    for kind, name, declared in EXPECTED:
        found = [h for h in hits if h.kind == kind and h.name == name]
        if not found:
            problems.append(f"plant missed: {kind} {name}")
        elif any(bool(h.declared) != declared for h in found):
            problems.append(f"plant {kind} {name} reported as "
                            f"{'declared' if found[0].declared else 'undeclared'}")
    helpers = [h for h in hits if h.kind == "helper"]
    for entry in ("Prop2:", "Prop5:"):
        if not any(entry in h.why for h in helpers):
            problems.append(f"plant missed: the helper behind SweepSelfTest.{entry[:-1]}")
    for entry in ("Prop3:", "Prop4:", "Prop6:"):
        if any(entry in h.why for h in helpers):
            problems.append(f"control reported: SweepSelfTest.{entry[:-1]}'s helper")
    for name in CONTROLS:
        if any(name in (n.strip() for n in h.name.split(",")) for h in hits):
            problems.append(f"control reported: {name}")
    expected = {(k, n) for k, n, _ in EXPECTED}
    for h in hits:
        if (h.kind, h.name) not in expected:
            problems.append(f"unexpected hit: {h.path}:{h.line}: {h.kind}: {h.name}")
    if exit_code(hits, True) != 1 or exit_code([h for h in hits if h.declared], True) != 0:
        problems.append("--fail-on-undeclared does not exit 1 on undeclared hits alone")
    if passage_comments(SAMPLE_RECORD) != [["# KF: joined as Euclid asks"], []]:
        problems.append("a passage's `#` comments are misread: "
                        f"{passage_comments(SAMPLE_RECORD)}")
    if problems:
        print(f"\nself-test: {len(problems)} problem(s):")
        for p in problems:
            print(f"  ✗ {p}")
        return 1
    print(f"\n✓ self-test: {len(EXPECTED)} planted kinds reported (the declared ones as "
          f"declared), and {len(CONTROLS) + 3} controls passed")
    return 0


# ---------------------------------------------------------------------------------------

def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("paths", nargs="*", default=["Elements"],
                        help="trees or Lean files to sweep (default: Elements)")
    parser.add_argument("--fail-on-undeclared", action="store_true",
                        help="exit 1 when any hit is not declared in its record")
    parser.add_argument("--self-test", action="store_true",
                        help="plant each kind of hit outside the tree, and check the sweep")
    parser.add_argument("--jobs", type=int, default=None,
                        help="files linted at once (default: the number of processors)")
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
