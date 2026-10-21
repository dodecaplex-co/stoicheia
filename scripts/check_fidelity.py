"""Check that the Lean follows Euclid, and that the house rules hold.

1. Fidelity. For every proposition, the docstring of `theorem PropN` must be
   Heath's enunciation, and the full-line `--` comments inside its proof, read in
   order, must be exactly Heath's proof (whitespace aside). Euclid's words go in
   `--` comments; our own remarks go in `/- … -/` blocks.
2. Every `axiom` lives in `Elements/Foundations/`: a first look in the source here,
   which reads `Staging/`, `Audit/` and `model/` too, and the real check from Lean's own
   environment in 6.
3. Book Zero (`Elements/Figure/`) never imports a proposition.
4. None of the commands that `docs/FORMALIZATION.md`, section 7, forbids under
   `Elements/`, `Staging/`, `Audit/` or `model/` (LEAN_TREES), since they get round the kernel,
   bring in an axiom without the word, run a program when a file is built or imported,
   or stop Lean reading a file: `native_decide`, `bv_decide`, the word `native`,
   `(config := …)`, `set_option debug.…` and `set_option doc.…` (or `«debug».…` and
   `«doc».…`), `#eval`, `#exit`, `run_cmd`, `elab`, `macro`, `simproc` and its kin,
   `implemented_by`, `extern`, `unsafe`, the attributes it knows to register code (by a
   name ending in `elab`, `tactic`, `init`, `proc`, `parser`, `handler`, `unexpander` and
   others, or beginning `doc_`), and the rest of FORBIDDEN, below. The scan reads Lean's
   comments and its string and character literals as Lean does (`read_lean`), so a
   literal's text never opens a comment or ends an attribute's brackets, and is not read
   as code, while the code in an interpolated string's `{…}` holes is; a string whose
   braces Lean could read either way is refused. Each finding of 2, 3 and 4 names its
   file and line; symbolic links are refused by their paths and never followed.
   Under `model/`, the package's own `model/.lake` directory is never entered or read
   (a link there is refused like any other), while a `.lake` folder deeper in the model
   is read like any other; Mathlib imports are allowed. Only in `model/Check.lean` and `model/Check/`, `run_cmd` may be the first
   word on its line followed by `Check.Generator.<ident>` or
   `(Check.Generator.<ident>`, since those files run the generator. Every other command
   and attribute on the list is still refused there. The other half of #121, the model's
   compiled declarations replayed through Lean's kernel apart from the build, is
   `check_model_kernel.py`'s, in CI's `formal-model` job.
5. Placement, Euclid's application of one figure to another (brief 0006): outside its
   own files, `Elements/BookIII/Placement.lean` and `Elements/BookIII/Placement/`, no
   Lean under `Elements/` names `placement` or the `Placement` namespace but III.24's
   file and `Elements/BookIII/Arcs.lean`, read as 4 reads it (`read_lean`), each finding
   naming its file and line; and in 6, no entry but III.24 calls on one of them.
6. With `facts.json` present (run `lake env lean Certificate/Facts.lean` first; its
   fields are in `Certificate/FIELDS.md`):
   - every axiom an entry rests on, other than Lean's own `propext`,
     `Classical.choice` and `Quot.sound`, is declared under `Elements.Foundations`,
     and so is every axiom declared anywhere in `Elements`, as Lean itself reports;
   - the axiom lock: every axiom's statement, and every definition that the axioms'
     statements or the entries' statements reach, is exactly as
     `Certificate/axioms.lock` has it, in both directions. The number of Euclid's
     assumptions is the lock's, and the 17 primitive words of `Words.lean` and
     `Magnitudes.lean` are still `opaque`. Changing any of these is a decision,
     recorded in `docs/briefs/0002-decisions.md`; then
     `python3 scripts/check_fidelity.py --write-lock` writes the new lock;
   - the entries are the propositions of `heath.BOOKS`, a porism entry for each of
     Heath's porisms (`heath.heath_porisms`) and nothing else, and companions of
     those propositions, each tied to its proposition by `of` and `attached`;
   - for every entry, propositions, porisms and companions alike: none cites one that
     does not come before it; only I.4 and I.8 use superposition directly; none
     before I.29 rests on Postulate 5 or any Euclidean-only rule (a later book comes
     after I.29, and may); none rests on Circle 2 or Circle 3, each of which must be
     an axiom in the lock or a proved rule resting on another forbidden circle rule
     that remains an axiom in the lock; only III.24 has placement, or a lemma of the `Placement`
     namespace or of placement's files, among its shared steps;
   - every proposition of a completed book is proved, and so is everything attached
     to it, with both figures and a mishnah;
   - the facts pinned in `tests/certificate_expectations.json` still hold;
   - each name a review record's passage lists as `unused` is bound by the Lean beneath
     the run of `--` lines its `at` begins in (`unbound_unused`, read from the text by
     `bound_names`), so a declaration for the citation sweep cannot outlive its binding;
   - the review records (`review/SCHEMA.md`): every proposition has one, valid; its
     stamps match the statements in facts.json and its Lean file, so a record goes
     stale when either changes; its passages begin at Euclid's sentences and name
     helpers that exist; and every run of `--` lines with no Lean beneath it before
     the next run, a `/- … -/` remark ending a run and carrying none, is declared as a
     passage (`uncarried_runs`).
7. Inline count markers in tracked Markdown match the exact file-derived counts in
   generated_counts.py, and stand only where that module allows. Unknown and
   malformed markers are refused, as are unsafe paths and a missing or mismatched Git
   work tree.

`--facts PATH` checks another copy of facts.json (scripts/negative_tests.py uses it);
`--write-lock` writes `Certificate/axioms.lock` from facts.json and stops.

Exits non-zero on any failure. Standard library only; the review records need Python
3.11 or later (tomllib).
"""

import argparse
import functools
import json
import os
import re
import sys
from pathlib import Path
from typing import NamedTuple

import heath
import generated_counts

ROOT = heath.ROOT
BOOKS = heath.BOOKS
FACTS = ROOT / "facts.json"
LOCK = ROOT / "Certificate" / "axioms.lock"
EXPECTATIONS = ROOT / "tests" / "certificate_expectations.json"
# Books whose every proposition is proved: they must stay that way.
COMPLETE = {"I", "II", "III"}
SUPERPOSITION_ALLOWED = {"I.4", "I.8"}
EUCLIDEAN_ONLY = re.compile(r"^(Postulate5|Tacit\.Euclidean\..*)$")
# The first proposition of each book allowed to rest on Postulate 5. Euclid holds it
# back until I.29; Books II and III come after the whole of Book I, so they may use the
# postulate from their first proposition on, as II.10 does by name. A book missing here
# may use it throughout. A porism or companion goes with its proposition.
FIRST_EUCLIDEAN = {"I": 29, "II": 1, "III": 1}
# These rules contain III.2; no certificate entry may rest on either, even through a
# helper. Certificate names omit the leading `Elements.`.
FORBIDDEN_CIRCLE_RULES = {
    "Tacit.inside_of_between": "Circle 2",
    "Tacit.outside_of_between": "Circle 3",
}
# The words Euclid leaves undefined, and the magnitudes. Each must stay `opaque`: Lean
# then knows only what the axioms say of them, and the axioms stay true in the plane.
PRIMITIVES = {
    "Point", "Line", "Circle", "OnLine", "SameSide", "Between", "OnCircle", "InsideCircle",
    "Centre",                                                  # Words.lean
    "MagnitudeImpl", "Magnitude.zero", "Magnitude.add", "Magnitude.lt", "len", "ang", "area",
    "rightAngle",                                              # Magnitudes.lean
}
# Lean's own logical foundations, which every proof may use.
LEAN_FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}
# The Lean the edition builds, which the source scan (check_rules) reads: the library, the
# statements staged before their proofs, the audit lemmas, and model/, each folder with
# its root file (`Staging.lean`). The model allows Mathlib and skips its own model/.lake
# directory without entering it. Its Check files alone allow the generator calls named below.
# The checks' own Lean, `Certificate/Facts.lean`, is not among them.
LEAN_TREES = ("Elements", "Staging", "Audit", "model")
# Only model/Check.lean and model/Check/ may run the generator: run_cmd must be the first
# word on its source line, followed by Check.Generator.<ident> or (Check.Generator.<ident>.
# Match just that command, never exempt its arguments or another command on the line.
MODEL_CHECK_RUN_CMD = re.compile(
    r"^[ \t]*(?P<command>run_cmd)[ \t]+(?:\([ \t]*)?Check\.Generator\."
    r"[^\W\d][\w'!?]*(?=[ \t\r\n()]|$)", re.M)
# Commands that could get round the kernel (`native_decide` and the `debug.` options, among
# them `debug.skipKernelTC`, spelled `debug.` or `«debug».`), bring in an axiom without the
# keyword, run a program when the file is built or imported (`#eval`, `run_cmd` and their
# kin, `initialize`, the simproc commands and `set_library_suggestions`, whose code `simp`
# and the suggestion tactics run, and the `doc.` options, spelled `doc.` or `«doc».`: with
# `doc.verso` on, Lean runs the Lean in a docstring, which the scan takes out with the
# comments), give syntax a meaning in code (`elab`, `macro`), swap code in for a definition,
# or stop Lean reading the file (`#exit`). Matched as whole words, in the Lean as
# `read_lean` gives it; so is an attribute that registers code Lean runs while a file is
# built or printed, known by the end of its name (`command_elab`, `grind_tactic`, `init`,
# `sym_simproc`, `app_unexpander`, `term_parser`, `cpass`, `missing_docs_handler`,
# `simprocAttr` and the rest) or, for `builtin_doc` and the `doc_` attributes, its start,
# and named in full in the finding. The list holds the attributes found in Lean 4.35 to run
# code while a file is built; it may not be complete, and a later Lean may add more.
# FORMALIZATION.md, section 7, is their one home.
# Lean 4.35 evaluates natively, and admits the result as an axiom, for `native_decide`, the
# `bv_decide` family and `decide` with its `native` option, which `decide +zetaReduce
# +native`, `decide (native := Bool.true)` or a whole configuration, `(config := ⟨false,
# true, true, false⟩)`, also set: so the word `native` anywhere, and `(config := …)`, are
# refused as well.
FORBIDDEN = re.compile(
    r"\bnative_decide\b|\bdecide\s*\+\s*native\b|\bnative\s*:=\s*true\b|\bnative\b|"
    r"\(\s*«?config»?\s*:=|"
    r"\bset_option\s+«?(?:debug|doc)»?\.|#eval\b|#exit\b|"
    r"\b(bv_decide|bv_check|run_cmd|run_elab|run_meta|run_tac|by_elab|elab|elab_rules|"
    r"macro|macro_rules|command_elab|term_elab|initialize|builtin_initialize|"
    r"(?:builtin_)?(?:sym_|cbv_)?d?simproc(?:_decl|_pattern)?|set_library_suggestions|"
    r"implemented_by|extern|unsafe)\b|"
    r"(?:@|\battribute\s*)\[[^\]]*?\b(?P<attr>(?:builtin_)?doc(?:_\w+)?|\w*(?:elab|macro|"
    r"tactic|init|proc|discharger|unexpander|precheck|formatter|parenthesizer|control_info|"
    r"code_action|rpc_method|linter|parser|pass|suggestions?|check|handler|provider|fn|module|"
    r"hooks|Attr))\b")
# An axiom, declared anywhere in a line: Lean reads `example : True := trivial axiom
# planted : False` as two commands, the second an axiom.
AXIOM = re.compile(r"\baxiom\b")
# Placement (brief 0006, "Placement", the policy). `placement` carries the points on one
# side of a straight line, and the line, onto those on one side of an equal straight line,
# keeping every distance: Euclid's "let the segment AEB be applied to CFD" (III.24), with
# no motion assumed beyond I.4 and I.8. The lemmas of its namespace carry the same content,
# so the policy covers them all. Outside its own files, only III.24, which applies one
# segment to another, and the bridge theorems of Arcs.lean may cite them: the source of no
# other file under Elements/ names them, and no entry but III.24 calls on them.
PLACEMENT_HOME = ("Elements/BookIII/Placement.lean", "Elements/BookIII/Placement/")
PLACEMENT_CITERS = {"Elements/BookIII/Prop24.lean", "Elements/BookIII/Arcs.lean"}
PLACEMENT_ENTRIES = {"III.24"}
# `placement`, or the namespace `Placement`, as a whole name or a part of one
# (`BookIII.placement`, `Placement.dist`), in the Lean as `read_lean` gives it, its
# comments and literals taken out.
PLACEMENT_NAME = re.compile(r"\b(placement|Placement)\b")

errors: list[str] = []


def fail(msg: str) -> None:
    errors.append(msg)


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def theorem_block(src: str, n: int):
    """Return (docstring, proof_comment_text) for `theorem PropN`."""
    span = heath.theorem_span(src, n)
    if span is None:
        return None, None
    # Drop block comments (our remarks), keep full-line `--` comments (Euclid's words).
    body = re.sub(r"/-.*?-/", "", src[span.body:span.end], flags=re.S)
    words = [m.group(1) for m in re.finditer(r"^\s*--\s?(.*)$", body, re.M)]
    return span.doc, " ".join(words)


def first_difference(a: str, b: str) -> str:
    i = next((k for k in range(min(len(a), len(b))) if a[k] != b[k]), min(len(a), len(b)))
    return f"…{a[max(0, i - 40):i + 40]!r}\n      expected …{b[max(0, i - 40):i + 40]!r}"


def check_fidelity() -> None:
    for book, count in BOOKS.items():
        for n in range(1, count + 1):
            path = heath.lean_path(book, n)
            if not path.exists():
                fail(f"{book}.{n}: missing {path.relative_to(ROOT)}")
                continue
            doc, words = theorem_block(path.read_text(), n)
            if doc is None:
                fail(f"{book}.{n}: no documented `theorem Prop{n}` found")
                continue
            _, enunciation, proof = heath.read(book, n)
            if heath.normalize(doc) != heath.normalize(enunciation):
                fail(f"{book}.{n}: docstring is not Heath's enunciation:\n      "
                     + first_difference(heath.normalize(doc), heath.normalize(enunciation)))
            expected = heath.normalize(" ".join(proof))
            got = heath.normalize(words)
            if got != expected:
                fail(f"{book}.{n}: the `--` comments don't match Heath's proof:\n      "
                     + first_difference(got, expected))


# Lean's tokens, as its tokenizer starts them: an identifier begins with a letter or `_`,
# a raw string with `r`, any `#`s and `"`, a character literal with `'`; a number with a
# digit, so that the `'` after one begins a character literal. A string just after one of
# INTERPOLATED is read with its `{…}` holes, as Lean reads it.
IDENT = re.compile(r"[^\W\d][\w'!?.]*|\d[\w.]*")
RAW = re.compile(r'r(#*)"')
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\\n'])'")
INTERPOLATED = {"s!", "m!", "f!", "throwError"}


def read_lean(src: str) -> tuple[str, list[int]]:
    """The Lean as Lean's tokenizer reads it, with its comments (`--` to the end of the
    line, and `/- … -/` blocks, docstrings and nested ones among them), the text of its
    string and character literals, raw strings among them, and each `[` or `]` in a «…»
    name blanked; the code in an interpolated string's `{…}` holes is kept. Newlines stay,
    so lines keep their numbers. Also the offset of each string the scan cannot read for
    certain: one with a `{`, not after INTERPOLATED, whose two readings, plain and with
    holes, end in different places, since its braces may be text or holes of code."""
    marks: list[tuple[str, int, int]] = []
    _read_code(src, 0, marks)
    out, unsure = list(src), []
    for kind, i, j in marks:
        if kind == "unsure":
            unsure.append(i)
            continue
        for k in range(i, j):
            if out[k] != "\n" and (kind == "text" or out[k] in "[]"):
                out[k] = " "
    return "".join(out), unsure


def without_comments(src: str) -> str:
    """The Lean with its comments and the text of its string literals blanked, as
    `read_lean` reads it: what `scripts/render.py` searches for a declaration's uses, so a
    name in a comment, a docstring or a string is no use."""
    return read_lean(src)[0]


def _find(src: str, s: str, i: int) -> int:
    """The offset of `s` in `src` from `i` on, or the end of `src`."""
    k = src.find(s, i)
    return len(src) if k < 0 else k


def _read_code(src: str, i: int, marks: list, hole: bool = False) -> int:
    """Read Lean from `i` to the end or, in a hole, to the `}` that closes it, and return
    that offset. `marks` gains the text of each comment and literal ("text"), each «…»
    name ("name") and each string the scan cannot read for certain ("unsure")."""
    depth, previous = 0, ""
    while i < len(src):
        c, j = src[i], i + 1
        if src.startswith("--", i):
            j = _find(src, "\n", i)
            marks.append(("text", i, j))
        elif src.startswith("/-", i):
            # a comment's body begins at its fourth character, as Lean reads it: after
            # `/--` or `/-!`, and past the third character of any other `/-`, which Lean
            # passes over, so that `/-/- -/` is a whole comment
            j, nested = min(i + 3, len(src)), 1
            while j < len(src) and nested:
                pair = src[j:j + 2]
                nested += (pair == "/-") - (pair == "-/")
                j += 2 if pair in ("/-", "-/") else 1
            marks.append(("text", i, j))
        elif c == '"':
            j, previous = _read_string(src, i, marks, previous in INTERPOLATED), c
        elif m := RAW.match(src, i):
            close = '"' + m[1]
            k = _find(src, close, m.end())
            marks.append(("text", m.end(), k))
            j, previous = min(k + len(close), len(src)), c
        elif c == "«":
            j = min(_find(src, "»", i) + 1, len(src))
            marks.append(("name", i, j))
            previous = src[i:j]
        elif m := IDENT.match(src, i):
            j, previous = m.end(), m[0]
        elif c == "'" and src[j:j + 1] != "'" and (m := CHAR.match(src, i)):
            marks.append(("text", i + 1, m.end() - 1))
            j, previous = m.end(), c
        elif c == "}" and hole and not depth:
            return i
        elif not c.isspace():
            depth += (c == "{") - (c == "}")
            previous = c
        i = j
    return len(src)


def _read_string(src: str, i: int, marks: list, interpolated: bool) -> int:
    """Read the string at `i` and return the offset past it: with its holes, as an
    interpolated string, if it follows INTERPOLATED or both readings end in one place."""
    plain = i + 1
    while plain < len(src) and src[plain] != '"':
        plain += 2 if src[plain] == "\\" else 1
    plain = min(plain + 1, len(src))
    holes: list[tuple[str, int, int]] = []
    end = _read_interpolated(src, i, holes)
    if end == plain or (interpolated and end is not None):
        marks += holes
        return end
    marks.append(("text", i + 1, plain))
    if "{" in src[i:plain]:
        marks.append(("unsure", i, plain))
    return plain


def _read_interpolated(src: str, i: int, marks: list) -> int | None:
    """The offset past the string at `i` read as an interpolated string, with its text
    marked and its holes read as code; None if it does not close."""
    j = start = i + 1
    while j < len(src):
        if src[j] == "\\":
            j += 2
        elif src[j] == '"':
            marks.append(("text", start, j))
            return j + 1
        elif src[j] == "{":
            marks.append(("text", start, j))
            j = _read_code(src, j + 1, marks, hole=True)
            if j >= len(src):
                return None
            j = start = j + 1
        else:
            j += 1
    return None


def lean_sources() -> list[Path]:
    """Every `.lean` file and symbolic link of LEAN_TREES, excluding what lies inside the
    directory model/.lake: each folder's root file, then the folder in sorted order. A
    link is listed before anything is pruned, so a link at model/.lake is refused too."""
    paths = []
    for tree in LEAN_TREES:
        root = ROOT / f"{tree}.lean"
        paths += [root] if root.is_symlink() or root.exists() else []
        folder_root = ROOT / tree
        if folder_root.is_symlink():
            paths.append(folder_root)
            continue
        found = []
        for folder, dirs, files in os.walk(folder_root, followlinks=False):
            here = Path(folder)
            links = {name for name in dirs + files if (here / name).is_symlink()}
            dirs[:] = sorted(name for name in dirs if name not in links
                             and not (here == ROOT / "model" and name == ".lake"))
            found += sorted(here / name for name in links | set(files)
                            if name in links or name.endswith(".lean"))
        paths += sorted(found)
    return paths


def line_of(text: str, offset: int) -> int:
    return text[:offset].count("\n") + 1


def check_rules() -> None:
    for path in lean_sources():
        rel = path.relative_to(ROOT).as_posix()
        if path.is_symlink():
            fail(f"{rel}: a symbolic link, which the source scan does not follow; "
                 "use a regular file or directory (docs/FORMALIZATION.md, section 7)")
            continue
        src = path.read_text()
        code, unsure = read_lean(src)
        generator_calls = ({m.start("command") for m in MODEL_CHECK_RUN_CMD.finditer(src)}
                           if rel == "model/Check.lean" or rel.startswith("model/Check/")
                           else set())
        if not rel.startswith("Elements/Foundations/"):
            for m in AXIOM.finditer(code):
                fail(f"{rel}:{line_of(code, m.start())}: declares an axiom outside "
                     "Elements/Foundations/")
        for m in re.finditer("native_decide", src):
            fail(f"{rel}:{line_of(src, m.start())}: uses native_decide")
        for m in FORBIDDEN.finditer(code):
            if m.group(0) == "run_cmd" and m.start() in generator_calls:
                continue
            if m.group(0) != "native_decide":
                word = f"@[{m['attr']}]" if m["attr"] else " ".join(m.group(0).split())
                fail(f"{rel}:{line_of(code, m.start())}: uses `{word}`, which could get round "
                     "Lean's kernel, bring in an axiom unseen, run a program when the file is "
                     "built or imported, or stop Lean reading it (docs/FORMALIZATION.md, "
                     "section 7)")
        for offset in unsure:
            fail(f"{rel}:{line_of(src, offset)}: a string the scan cannot read for certain, "
                 "since Lean could read its braces as holes of code (docs/FORMALIZATION.md, "
                 "section 7)")
        if rel.startswith("Elements/Figure/"):
            for m in re.finditer(r"^import Elements\.Book", src, re.M):
                fail(f"{rel}:{line_of(src, m.start())}: Book Zero must not import a proposition")
        if (rel.startswith("Elements/") and not rel.startswith(PLACEMENT_HOME)
                and rel not in PLACEMENT_CITERS):
            for m in PLACEMENT_NAME.finditer(code):
                fail(f"{rel}:{line_of(code, m.start())}: names `{m.group(0)}`, but outside "
                     "placement's own files only III.24 and Elements/BookIII/Arcs.lean may cite "
                     "placement or a lemma of the `Placement` namespace (brief 0006)")


def placement_step(step: dict) -> bool:
    """Is this shared step (facts.json, `shared_steps`) placement, a lemma of the
    `Placement` namespace, or anything declared in placement's own files?"""
    name, file = step.get("name", ""), step.get("file", "")
    return (name == "BookIII.placement" or name.startswith(("BookIII.placement.",
                                                            "BookIII.Placement."))
            or file.startswith(PLACEMENT_HOME))


# The words retired from the reader-facing pages ("Euclid cites", "never need" and their
# kin) are checked by scripts/check_style.py, rule S5, whose home is docs/STYLE.md,
# section 8.


# The axiom lock, Certificate/axioms.lock.

LOCK_HEADER = """\
# Certificate/axioms.lock
#
# The exact statement of every assumption the propositions may rest on: Euclid's
# postulates, Definition 15 and the tacit rules, all declared in Elements/Foundations/.
# After them, every definition, instance, structure and opaque word of this project that
# those statements reach, or that the statement of a proposition, a porism or a
# companion reaches, so that neither an assumption nor a claim can change its meaning
# through a word it uses. Lean prints both, as Certificate/FIELDS.md says: full names,
# no notation, one line each.
#
# scripts/check_fidelity.py compares this file with facts.json in both directions, and
# takes the number of Euclid's assumptions from it. Change it only with a decision,
# recorded in docs/briefs/0002-decisions.md, and then only by running
#
#     python3 scripts/check_fidelity.py --write-lock
"""


def toml_string(s: str) -> str:
    """A TOML basic string. JSON's escapes (\\", \\\\, \\n, \\uXXXX …) are TOML's too."""
    return json.dumps(s, ensure_ascii=False)


def render_lock(axioms: dict, vocabulary: dict) -> str:
    lines = [LOCK_HEADER, f"[axioms]  # {len(axioms)}"]
    lines += [f"{toml_string(k)} = {toml_string(v)}" for k, v in sorted(axioms.items())]
    lines += ["", f"[vocabulary]  # {len(vocabulary)}"]
    lines += [f"{toml_string(k)} = {toml_string(v)}" for k, v in sorted(vocabulary.items())]
    return "\n".join(lines) + "\n"


def read_lock(path: Path = LOCK):
    """(axioms, vocabulary) from the lock, each {name: printed statement}; None if the
    file is missing. Raises ValueError if it cannot be read."""
    if not path.exists():
        return None
    tomllib = heath._toml()
    try:
        data = tomllib.loads(path.read_text())
    except tomllib.TOMLDecodeError as e:
        raise ValueError(f"{rel(path)}: not valid TOML: {e}") from None
    if set(data) != {"axioms", "vocabulary"} or not all(
            isinstance(data[k], dict) and all(isinstance(v, str) for v in data[k].values())
            for k in data):
        raise ValueError(f"{rel(path)}: expected an [axioms] and a [vocabulary] table of "
                         "strings, and nothing else")
    return data["axioms"], data["vocabulary"]


def foundations(module: str) -> bool:
    return module.startswith("Elements.Foundations.")


def check_lock(facts, path: Path = LOCK):
    """Compare the lock with facts.json's `axiom_types` and `vocabulary`, both ways.
    Returns the number of assumptions the lock holds, or None if it cannot be read."""
    try:
        lock = read_lock(path)
    except (ValueError, RuntimeError) as e:
        fail(str(e))
        return None
    if lock is None:
        fail(f"{rel(path)} is missing: with a decisions entry, write it with "
             "`python3 scripts/check_fidelity.py --write-lock`")
        return None
    proved = facts.get("proved_rules", {})
    for name, rule in FORBIDDEN_CIRCLE_RULES.items():
        if name in lock[0]:
            continue
        if name not in proved:
            fail(f"{name} ({rule}): not an axiom in {rel(path)} or a proved rule in "
                 "facts.json (if the rule was renamed, rename it in FORBIDDEN_CIRCLE_RULES too)")
        elif not any(other != name and other in lock[0] and other in proved[name]
                     for other in FORBIDDEN_CIRCLE_RULES):
            fail(f"{name} ({rule}): proved without another forbidden circle rule "
                 f"beneath it that is an axiom in {rel(path)}, so entries using it "
                 "cannot be refused by their axioms")
    types, vocabulary = facts.get("axiom_types"), facts.get("vocabulary")
    if types is None or vocabulary is None:
        fail("facts.json has no axiom_types or vocabulary: rerun `lake env lean Certificate/Facts.lean`")
        return len(lock[0])
    locked_axioms, locked_vocabulary = lock
    where = rel(path)
    for name in sorted(set(types) - set(locked_axioms)):
        fail(f"{name}: an assumption not in {where} (a new axiom is a decision: record it in "
             "docs/briefs/0002-decisions.md, then run `python3 scripts/check_fidelity.py --write-lock`)")
    for name in sorted(set(locked_axioms) - set(types)):
        fail(f"{name}: in the lock but no longer an axiom ({where}; removing one is a decision "
             "for docs/briefs/0002-decisions.md)")
    for name in sorted(set(types) & set(locked_axioms)):
        if types[name] != locked_axioms[name]:
            fail(f"{name}: its statement is not the one in {where}:\n      "
                 + first_difference(types[name], locked_axioms[name]))
    # The vocabulary: the words of the axioms' statements and of the entries'.
    for name in sorted(set(vocabulary) - set(locked_vocabulary)):
        fail(f"{name}: a word of the statements, the axioms' or the entries', not in "
             f"{where} (a new word is a decision: record it in docs/briefs/0002-decisions.md, "
             "then run `python3 scripts/check_fidelity.py --write-lock`)")
    for name in sorted(set(locked_vocabulary) - set(vocabulary)):
        fail(f"{name}: in the lock but no longer a word of any statement ({where})")
    for name in sorted(set(vocabulary) & set(locked_vocabulary)):
        if vocabulary[name] != locked_vocabulary[name]:
            fail(f"{name}: its definition is not the one in {where} (a changed word changes "
                 "what every statement using it says: a decision for "
                 "docs/briefs/0002-decisions.md):\n      "
                 + first_difference(vocabulary[name], locked_vocabulary[name]))
    return len(locked_axioms)


def write_lock(facts, path: Path = LOCK) -> int:
    """Write the lock from facts.json: the axioms declared in Elements/Foundations/, and
    the vocabulary. Prints what changed."""
    types, vocabulary = facts.get("axiom_types"), facts.get("vocabulary")
    modules = facts.get("axiom_modules", {})
    if types is None or vocabulary is None:
        print("facts.json has no axiom_types or vocabulary: rerun `lake env lean Certificate/Facts.lean`")
        return 1
    axioms = {n: s for n, s in types.items() if foundations(modules.get(n, ""))}
    for name in sorted(set(types) - set(axioms)):
        print(f"  not locked: {name}, declared in {modules.get(name) or 'an unknown module'}, "
              "outside Elements/Foundations/")
    try:
        old = read_lock(path)
    except ValueError:
        old = None
    text = render_lock(axioms, vocabulary)
    tomllib = heath._toml()
    if tomllib.loads(text) != {"axioms": axioms, "vocabulary": vocabulary}:
        print("internal error: the lock would not read back as written")
        return 1
    path.write_text(text)
    print(f"wrote {rel(path)}: {len(axioms)} axioms, {len(vocabulary)} words of vocabulary")
    if old is None:
        print("  (a new lock)")
        print("Record it in docs/briefs/0002-decisions.md.")
        return 0
    changes = []
    for new, before, label in ((axioms, old[0], "axiom"), (vocabulary, old[1], "vocabulary")):
        changes += [f"  + {label} {k}" for k in sorted(set(new) - set(before))]
        changes += [f"  - {label} {k}" for k in sorted(set(before) - set(new))]
        changes += [f"  ~ {label} {k}" for k in sorted(set(new) & set(before)) if new[k] != before[k]]
    print("\n".join(changes) if changes else "  (no change)")
    if changes:
        print("Record the decision in docs/briefs/0002-decisions.md, with the reason.")
    return 0


def check_axioms(facts, count) -> None:
    """Where the axioms live, read from Lean's environment by Certificate/Facts.lean.
    `count` is the number of assumptions the lock holds (None: no lock to compare)."""
    modules = facts.get("axiom_modules")
    if modules is None or "opaque" not in facts:
        fail("facts.json has no axiom_modules or opaque: rerun `lake env lean Certificate/Facts.lean`")
        return
    for name, module in sorted(modules.items()):
        if module.startswith("Elements") and not foundations(module):
            fail(f"{name}: an axiom declared in {module}, outside Elements/Foundations/")
    for p in facts["propositions"]:
        for a in p["axioms"]:
            if a in LEAN_FOUNDATIONS:
                continue
            if not foundations(modules.get(a, "")):
                fail(f"{p['ref']}: rests on {a}, which is not one of Euclid's assumptions in "
                     f"Elements/Foundations/ (declared in {modules.get(a) or 'an unknown module'})")
    declared = sum(1 for m in modules.values() if foundations(m))
    if count is not None and declared != count:
        fail(f"Elements/Foundations/ declares {declared} axioms, not {count}: a new or "
             "removed assumption is a decision for docs/briefs/0002-decisions.md, and then "
             "a new Certificate/axioms.lock (`--write-lock`)")
    for name in sorted(PRIMITIVES - set(facts["opaque"])):
        fail(f"{name}: no longer an opaque primitive; Lean must know only what the axioms say of it")


# The entries: propositions, porisms and companions.

def entries_by_ref(facts) -> dict:
    """{ref: (Ref, entry)} for every entry whose ref parses; faults are reported."""
    out = {}
    for p in facts["propositions"]:
        ref = p.get("ref", "")
        try:
            r = heath.parse_ref(ref)
        except ValueError as e:
            fail(f"facts.json: {e}")
            continue
        if str(r) != ref:
            fail(f"{ref}: facts.json writes it {ref!r}, not in its one form {str(r)!r}")
        if ref in out:
            fail(f"{ref}: two entries in facts.json")
        out[ref] = (r, p)
    return out


def check_entries(facts, by_ref) -> None:
    """Which entries there are, how they hang together, and the policies, for
    every entry."""
    if any("kind" not in p or "statement" not in p for p in facts["propositions"]):
        fail("facts.json predates Certificate/FIELDS.md (an entry has no `kind` or "
             "`statement`): rerun `lake env lean Certificate/Facts.lean`")
    props = {ref for ref, (r, _) in by_ref.items() if r.kind == "proposition"}
    want = {f"{book}.{n}" for book, count in BOOKS.items() for n in range(1, count + 1)}
    for ref in sorted(want - props, key=heath.prop_key):
        fail(f"{ref}: missing from facts.json (does Certificate/Facts.lean list Book {ref.split('.')[0]}?)")
    for ref in sorted(props - want, key=heath.prop_key):
        fail(f"{ref}: in facts.json but not in heath.BOOKS")

    # Porisms are exactly Heath's.
    porisms = {(r.book, r.n) for r, _ in by_ref.values() if r.kind == "porism"}
    heaths = heath.heath_porisms()
    for book, n in sorted(heaths - porisms, key=lambda p: heath.prop_key(f"{p[0]}.{p[1]}")):
        fail(f"{book}.{n}: Heath prints a porism, but facts.json has no entry "
             f"{book}.{n} Por. (is `Prop{n}.porism` declared?)")
    for book, n in sorted(porisms - heaths, key=lambda p: heath.prop_key(f"{p[0]}.{p[1]}")):
        fail(f"{book}.{n} Por.: a porism entry, but Heath prints no porism to {book}.{n}")

    # `of` and `attached` tie each porism and companion to its proposition.
    children: dict[str, list[str]] = {}
    for ref, (r, p) in by_ref.items():
        kind = p.get("kind", r.kind)
        if kind != r.kind:
            fail(f"{ref}: its kind is {kind!r}, but the reference names a {r.kind}")
        if r.kind == "proposition":
            if "of" in p:
                fail(f"{ref}: a proposition has no `of`")
            continue
        if r.parent not in props:
            fail(f"{ref}: its proposition {r.parent} has no entry in facts.json")
        if p.get("of", r.parent) != r.parent:
            fail(f"{ref}: `of` is {p['of']!r}, not {r.parent!r}")
        children.setdefault(r.parent, []).append(ref)
    for ref in sorted(props, key=heath.prop_key):
        p = by_ref[ref][1]
        expected = sorted(children.get(ref, []), key=lambda c: (heath.prop_key(c), c))
        if "kind" in p and p.get("attached", []) != expected:
            fail(f"{ref}: `attached` lists {p.get('attached', [])}, but its porism and "
                 f"companions are {expected}")

    # The policies, for every entry.
    for ref, (r, p) in sorted(by_ref.items(), key=lambda e: (heath.prop_key(e[1][0]), e[0])):
        key = heath.prop_key(r)
        # Euclid cites only what comes before: nothing after II.N, and Book I nothing of
        # Book II. A porism comes after its proposition, and a companion after both; two
        # companions of one proposition may cite one another.
        for c in p.get("cites", []):
            try:
                later = heath.prop_key(c) > key
            except ValueError as e:
                fail(f"{ref}: cites {c!r}: {e}")
                continue
            if later:
                fail(f"{ref}: cites {c}, which does not come before it")
        if "Tacit.superposition" in p.get("direct_axioms", []) and ref not in SUPERPOSITION_ALLOWED:
            fail(f"{ref}: uses superposition directly (only I.4 and I.8 may)")
        first = FIRST_EUCLIDEAN.get(r.book, 1)
        if r.n < first:
            bad = [a for a in p["axioms"] if EUCLIDEAN_ONLY.match(a)]
            if bad:
                fail(f"{ref}: rests on {', '.join(bad)} before {r.book}.{first}")
        for axiom, rule in FORBIDDEN_CIRCLE_RULES.items():
            if axiom in p["axioms"]:
                fail(f"{ref}: rests on {axiom} ({rule}), forbidden for every entry")
        if ref not in PLACEMENT_ENTRIES:
            for step in p.get("shared_steps", []):
                if placement_step(step):
                    fail(f"{ref}: calls on {step.get('name')} ({step.get('file')}), but only "
                         "III.24 may call on placement or a lemma of the `Placement` "
                         "namespace (brief 0006)")

    # A complete book stays complete: every proposition proved, with all it carries.
    for book in sorted(COMPLETE, key=heath.arabic):
        for n in range(1, BOOKS[book] + 1):
            ref = f"{book}.{n}"
            p = by_ref.get(ref, (None, {}))[1]
            if p.get("status") != "proved":
                fail(f"{ref}: Book {book} is complete, but {ref} is not proved")
            for a in p.get("attached", []):
                if by_ref.get(a, (None, {}))[1].get("status") != "proved":
                    fail(f"{a}: Book {book} is complete, but {a}, attached to {ref}, is not proved")
            for f in (f"figures/{book}/{n:02d}.svg", f"figures/{book}/{n:02d}-idea.svg",
                      f"mishnah/{book}/{n:02d}.md"):
                if not (ROOT / f).exists():
                    fail(f"{ref}: {f} is missing")


# Facts pinned by tests/certificate_expectations.json.

def check_expectations(by_ref, path: Path = EXPECTATIONS) -> None:
    """Each expectation names an entry (`ref`) and a list `field`, and asks that the
    list `includes` some names, `excludes` others, or holds exactly `count` names
    beginning with `prefix`; `equals` compares any field with a value. A field that is
    an object, as `inherited` is, is read by its keys: the axioms it names."""
    if not path.exists():
        fail(f"{rel(path)} is missing")
        return
    try:
        data = json.loads(path.read_text())
        expectations = data["expectations"]
    except (json.JSONDecodeError, KeyError, TypeError) as e:
        fail(f"{rel(path)}: expected a JSON object with a list `expectations` ({e})")
        return
    known = {"ref", "field", "includes", "excludes", "equals", "count", "why"}
    for i, x in enumerate(expectations, 1):
        label = f"{rel(path)}, expectation {i}"
        if not isinstance(x, dict) or not {"ref", "field", "why"} <= set(x) or set(x) - known:
            fail(f"{label}: needs `ref`, `field` and `why`, and one or more of `includes`, "
                 "`excludes`, `equals`, `count`")
            continue
        ref, field, why = x["ref"], x["field"], x["why"]
        if ref not in by_ref:
            fail(f"{ref}: pinned by {label}, but facts.json has no such entry")
            continue
        if field not in by_ref[ref][1]:
            # Read as empty, a missing field would let every `excludes` pass.
            fail(f"{ref}: pinned by {label}, but its entry has no field `{field}`")
            continue
        value = by_ref[ref][1].get(field)
        if "equals" in x and value != x["equals"]:
            fail(f"{ref}: its {field} is {value!r}, not {x['equals']!r} ({label}: {why})")
        listed = value if isinstance(value, list) else list(value) if isinstance(value, dict) \
            else []
        for name in x.get("includes", []):
            if name not in listed:
                fail(f"{ref}: its {field} should include {name} ({label}: {why})")
        for name in x.get("excludes", []):
            if name in listed:
                fail(f"{ref}: its {field} should not include {name} ({label}: {why})")
        if "count" in x:
            prefix, want = x["count"].get("prefix", ""), x["count"].get("is")
            got = sum(1 for v in listed if isinstance(v, str) and v.startswith(prefix))
            if got != want:
                fail(f"{ref}: its {field} has {got} names beginning {prefix!r}, not {want} "
                     f"({label}: {why})")


# How the `--` lines sit in the Lean, for the review records.

FORMULA = re.compile(
    r"\[?(?:(?:If\s+)?therefore\s+etc\.|Q\.\s*E\.\s*[DF]\.|"
    r"\(?Being\)?\s+what\s+it\s+was\s+required\s+to\s+(?:do|prove)\.)\]?|\]", re.I)
PORISM_LINE = re.compile(r"\[?PORISM\.")
SENTENCE_BREAK = re.compile(r"[.;:?!\]]\s+(?=\S)")


def _blank_remarks(text: str) -> str:
    """`text` with every `/- … -/` remark (nested ones too) made spaces, line breaks
    kept, and `--` line comments left as they are."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if not depth and text.startswith("--", i):
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out.append(text[i:j])
            i = j
        elif text.startswith("/-", i):
            depth, i = depth + 1, i + 2
            out.append("  ")
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
            out.append("  ")
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def proof_lines(src: str, n: int) -> list:
    """Each line of `theorem PropN`'s statement and proof in the Lean file's text `src`,
    as (line number, kind, text): kind "words" for a full-line `--` comment, its text
    Heath's words; "lean" for a line of Lean; "remark" for a line wholly within a
    `/- … -/` remark; "blank" for a blank line. [] if there is no such theorem."""
    span = heath.theorem_span(src, n)
    if span is None:
        return []
    first = src.count("\n", 0, span.body) + 1
    body = src[span.body:span.end]
    rows = []
    for i, (line, raw) in enumerate(zip(_blank_remarks(body).split("\n"), body.split("\n"),
                                        strict=True)):
        s = line.strip()
        if not s:
            rows.append((first + i, "remark" if raw.strip() else "blank", ""))
        elif s.startswith("--"):
            rows.append((first + i, "words", re.sub(r"^--\s?", "", s)))
        else:
            rows.append((first + i, "lean", s))
    return rows


def _plain(s: str) -> str:
    return heath.normalize(s.replace("*", ""))


def sentence_starts(rows) -> list:
    """Every place a sentence of Euclid's begins in the `--` lines of `rows`
    (`proof_lines`): the start of each line, after an opening bracket, and after . ; :
    ? ! or ] inside a line. Each is (line number, the words from there to the end)."""
    joined, spans = "", []
    for ln, kind, text in rows:
        if kind != "words":
            continue
        text = _plain(text)
        if joined and text:
            joined += " "
        spans.append((ln, len(joined), len(joined) + len(text)))
        joined += text
    starts = []
    for ln, start, end in spans:
        places = {start} | {start + m.end() for m in SENTENCE_BREAK.finditer(joined[start:end])}
        places |= {p + 1 for p in places if joined[p:p + 1] in ("[", "(")}
        starts += [(ln, joined[p:]) for p in sorted(places) if p < end]
    return starts


class Run(NamedTuple):
    """A run of `--` lines with no Lean beneath it: `line` is where its words begin,
    `text` its words (whitespace made single), `lines` the line numbers they are on.
    Formula lines and a porism paragraph are left out of both."""
    line: int
    text: str
    lines: frozenset


def uncarried_runs(src: str, n: int) -> list:
    """The runs of `--` lines in `theorem PropN` that no Lean carries. A run is a stretch
    of `--` lines that no line of Lean and no `/- … -/` remark interrupts; blank lines do
    not end it. A run is carried only by a line of Lean after it and before the next run
    (or the theorem's end). A remark ends a run without carrying it: the sentences on
    either side of a remark are two runs, and the Lean beneath the second does not carry
    the first. Lean after the remark, before the next run, still carries the run before
    it, so a remark may sit between a sentence and its Lean.

    Euclid's formulas, which no Lean need carry, are left out: "Q. E. D.", "Q. E. F.",
    "(Being) what it was required to do" (or "prove"), "[If] therefore etc.", a lone "]",
    and a porism paragraph, which is proved as a theorem of its own. A run left with no
    words is not returned.

    In Books I-III this finds runs of several kinds, among them the closing sentences of
    reductios (III.4, III.5, III.6, III.7, III.19), a "similarly" that one argument
    already covers (I.14), a sentence that the Lean above it carries (II.10,
    III.14), a setting-out or an "I say that" that the statement gives (I.13, I.21,
    I.23), a join that needs no object of its own (I.6), and III.16's last part: its
    conclusion, then the angle of the semicircle and the horn-like angle."""
    rows = proof_lines(src, n)
    text_of = {ln: text for ln, kind, text in rows if kind == "words"}
    found = []
    for run in runs_beneath(rows):
        if run.lean:
            continue
        words, porism = [], False
        for ln in run.words:
            text = text_of[ln]
            porism = porism or bool(PORISM_LINE.match(text))
            if porism or FORMULA.fullmatch(_plain(text)):
                continue
            words.append((ln, text))
        if words:
            found.append(Run(words[0][0], _plain(" ".join(t for _, t in words)),
                             frozenset(ln for ln, _ in words)))
    return found


class Beneath(NamedTuple):
    """A run of `--` lines and the Lean beneath it: `words`, the run's line numbers;
    `lean`, those of the lines of Lean after it and before the next run, or the theorem's
    end. A run is a stretch of `--` lines that no line of Lean and no `/- … -/` remark
    interrupts; Lean after a remark still stands beneath the run before the remark."""
    words: tuple
    lean: tuple


def runs_beneath(rows) -> list:
    """Every run of `--` lines in `rows` (`proof_lines`), with the Lean beneath it: how
    `uncarried_runs` reads the runs, and how a passage's `unused` and the citation sweep
    (scripts/sweep_citations.py) find the Lean under a sentence."""
    runs, current = [], None
    for ln, kind, _ in rows:
        if kind == "words":
            if current is None:
                current = ([], [])
                runs.append(current)
            current[0].append(ln)
        elif kind == "lean":
            if runs:
                runs[-1][1].append(ln)
            current = None
        elif kind == "remark":
            current = None
    return [Beneath(tuple(words), tuple(lean)) for words, lean in runs]


# The bindings a proof makes, read from its code text plainly, without Lean: what a
# passage's `unused` may name (review/SCHEMA.md). The keywords that bind, and of those,
# the ones that bind several names in a row.
BINDS = re.compile(r"(?<![\w'.])(?P<kw>have|haveI|let|letI|set|obtain|rcases|intro|intros|"
                   r"rintro|fun|λ|by_cases|by_contra)(?![\w'!?])")
SEVERAL = ("intro", "intros", "rintro", "fun", "λ")
WITH = re.compile(r"(?<![\w'.])with(?![\w'!?])")
PATTERN_LEAF = re.compile(r"-|[^\W\d][\w'!?₀-₉]*")
ALTERNATIVE = re.compile(r"[ \t]*\|(?![|>])\s*")    # the `|` before an alternative
INDENT = re.compile(r"\n([ \t]*)(?=\S)")


class Leaf(NamedTuple):
    """A part of an rcases pattern: a name, `-` or `_` (or `rfl`), and where it stands."""
    name: str
    offset: int


def read_pattern(code: str, i: int) -> tuple[list, int]:
    """The leaves of the rcases pattern at `i` in the code text `code` (`read_lean`), and
    where the pattern ends: one name, or every name in a pattern of ⟨…⟩ or (…), at any
    depth. A type ascription, `(h : T)`, gives its name only."""
    while i < len(code) and code[i] in " \t":
        i += 1
    if i >= len(code):
        return [], i
    if code[i] not in "⟨(":
        m = PATTERN_LEAF.match(code, i)
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
            m = PATTERN_LEAF.match(code, j)
            if m and (j == 0 or not (code[j - 1].isalnum() or code[j - 1] in "_'")):
                leaves.append(Leaf(m.group(0), j))
                j = m.end()
                continue
        j += 1
    return leaves, j


def read_alternatives(code: str, i: int) -> tuple[list, int]:
    """The leaves of the rcases pattern at `i` and of each alternative after a `|`, as
    `hp | hq` or `⟨x, hx⟩ | h`, and where the last alternative ends."""
    leaves, i = read_pattern(code, i)
    while leaves:
        bar = ALTERNATIVE.match(code, i)
        if not bar:
            break
        more, j = read_pattern(code, bar.end())
        if not more:
            break
        leaves, i = leaves + more, j
    return leaves, i


def rcases_pattern(code: str, i: int) -> int | None:
    """Where the pattern of the `rcases` whose keyword ends at `i` begins, or None when the
    tactic has no `with`: past its `with`, which may stand on a later line of the tactic
    (each indented further than the keyword), and past a line break after the `with`."""
    column = i - len("rcases") - (code.rfind("\n", 0, i) + 1)
    end = next((m.start() for m in INDENT.finditer(code, i) if len(m[1]) <= column),
               len(code))
    w = WITH.search(code, i, end)
    if not w:
        return None
    return re.compile(r"\s*").match(code, w.end()).end()


def bound_names(code: str) -> set:
    """The names the code text `code` (`read_lean`) binds, read plainly, without Lean: the
    name or pattern after `have`, `let`, `set`, `obtain`, `by_cases` or `by_contra`, or
    after `rcases … with` (`rcases_pattern`, over line breaks), with each alternative after
    a `|`; each name or pattern after `intro`, `intros`, `rintro`, `fun` or `λ`; and
    `this`, for a `have` that gives no name. Every name in a pattern counts, but `-`, `_`
    and `rfl`. A binding of another shape is not found, so a passage cannot name it in
    `unused`."""
    names = set()
    for m in BINDS.finditer(code):
        kw, i = m["kw"], m.end()
        if kw == "rcases":
            i = rcases_pattern(code, i)
            if i is None:
                continue
        if kw in ("have", "haveI") and re.compile(r"[ \t]*:").match(code, i):
            names.add("this")
            continue
        if kw in SEVERAL:
            while True:
                leaves, i = read_pattern(code, i)
                if not leaves:
                    break
                names.update(leaf.name for leaf in leaves if leaf.name not in ("-", "_", "rfl"))
        else:
            leaves, i = read_alternatives(code, i)
            names.update(leaf.name for leaf in leaves if leaf.name not in ("-", "_", "rfl"))
    return names


def unbound_unused(src: str, n: int, passages: list) -> list:
    """The names that passages of a record of PropN list as `unused` and the Lean beneath
    their run does not bind (`bound_names`), as (passage number, its `at`, the names): a
    declaration that has outlived its binding, or stands under the wrong sentence. A
    passage whose `at` begins no sentence is left to the check of `at`."""
    rows = proof_lines(src, n)
    starts = sentence_starts(rows)
    runs = runs_beneath(rows)
    code = read_lean(src)[0].split("\n")
    found = []
    for i, p in enumerate(passages, 1):
        if not p.get("unused"):
            continue
        at = _plain(p["at"])
        lines = {ln for ln, words in starts if words.startswith(at)}
        if not lines:
            continue
        lean = [ln for run in runs if lines & set(run.words) for ln in run.lean]
        bound = bound_names("\n".join(code[ln - 1] for ln in lean))
        missing = [x for x in p["unused"] if x not in bound]
        if missing:
            found.append((i, p["at"], missing))
    return found


@functools.lru_cache(maxsize=None)
def declared_names() -> frozenset:
    """Every declaration under Elements/, by its full name without `Elements.`, read
    from the source with its namespaces: what a passage's `helper` may name."""
    decl = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+"
        r"([^\s:({\[]+)")
    names = set()
    for path in (ROOT / "Elements").rglob("*.lean"):
        stack: list[list[str]] = []
        for line in read_lean(path.read_text())[0].splitlines():
            m = re.match(r"^\s*(namespace|section|end)\b\s*(\S*)", line)
            if m:
                word, name = m.groups()
                if word == "namespace":
                    stack.append(name.split("."))
                elif word == "section":
                    stack.append([])
                elif stack:
                    stack.pop()
                continue
            m = decl.match(line)
            if m:
                name = m.group(1)
                full = name[len("_root_."):] if name.startswith("_root_.") else \
                    ".".join([part for frame in stack for part in frame] + [name])
                names.add(full[len("Elements."):] if full.startswith("Elements.") else full)
    return frozenset(names)


def helper_exists(book: str, helper: str) -> bool:
    """Is `helper` declared: by its name under `Elements`, under the record's book, or
    as the end of exactly one declared name (as an `open` lets the Lean write it)?"""
    name = helper[len("Elements."):] if helper.startswith("Elements.") else helper
    names = declared_names()
    if name in names or f"Book{book}.{name}" in names:
        return True
    return sum(1 for d in names if d.endswith("." + name)) == 1


def check_reviews(facts, by_ref) -> None:
    """The review records against review/SCHEMA.md, the statements in facts.json (when
    `facts` is given) and the Lean files."""
    try:
        heath._toml()
    except RuntimeError as e:
        fail(f"review records: {e}")
        return
    for book, count in BOOKS.items():
        folder = heath.REVIEW / book
        for path in sorted(folder.glob("*.toml")) if folder.exists() else []:
            if not re.fullmatch(r"\d\d", path.stem) or not 1 <= int(path.stem) <= count:
                fail(f"{rel(path)}: not a proposition of Book {book}")
        for n in range(1, count + 1):
            check_review(facts, by_ref, book, n)


def check_review(facts, by_ref, book: str, n: int) -> None:
    ref = f"{book}.{n}"
    try:
        record = heath.load_review(book, n)
    except heath.ReviewError as e:
        fail(str(e))
        return
    where = rel(heath.review_path(book, n))
    st, route, rv = record["statement"], record["route"], record["review"]
    tags = record.get("representation", {}).get("tags", [])
    if not (st["scope"] == "full" and route["kind"] == "euclid" and not tags) and "note" not in st:
        fail(f"{where}: [statement] needs a `note`, shown beside the badge, since the "
             f"statement is {st['scope']}, the route {route['kind']}"
             + (f", and it carries {', '.join(tags)}" if tags else ""))
    for c in st["companions"]:
        if facts is not None and c not in by_ref:
            fail(f"{where}: companion {c} has no entry in facts.json")
    if facts is not None and "overlap" in record:
        for rule in [record["overlap"]["rule"]] + record["overlap"].get("also", []):
            if rule not in facts.get("axiom_modules", {}):
                fail(f"{where}: [overlap] rule {rule} is not one of the axioms in facts.json")

    # The stamps: what the reviewer read is what there is now. (A facts.json with no
    # statements has been reported once already, by check_entries.)
    if facts is not None and ref in by_ref and "statement" in by_ref[ref][1]:
        try:
            want = heath.review_fingerprint(facts, ref)
        except KeyError as e:
            fail(f"{ref}: {e.args[0] if e.args else e}")
        else:
            if st["fingerprint"] != want:
                fail(f"{ref}: its statement has changed since it was reviewed ({where} has "
                     f"{st['fingerprint']}, facts.json gives {want}): read the record "
                     "again, then stamp it with scripts/review_stamp.py --commit "
                     "(WORKFLOW.md, section 6)")
    lean = heath.lean_path(book, n)
    if not lean.exists():
        return
    want = heath.file_hash(lean)
    if rv["lean"] != want:
        fail(f"{ref}: its Lean file has changed since it was reviewed ({where} has "
             f"{rv['lean']}, {rel(lean)} is {want}): read the record again, then run "
             "scripts/review_stamp.py --commit (WORKFLOW.md, section 6)")

    # The passages begin at Euclid's sentences, and name helpers that exist.
    src = lean.read_text()
    starts = sentence_starts(proof_lines(src, n))
    for i, p in enumerate(record["passage"], 1):
        at = _plain(p["at"])
        if not any(words.startswith(at) for _, words in starts):
            fail(f"{where}: [[passage]] {i}: `at` {p['at']!r} does not begin a sentence of "
                 f"the `--` lines of theorem Prop{n}")
        if "helper" in p and not helper_exists(book, p["helper"]):
            fail(f"{where}: [[passage]] {i}: `helper` {p['helper']} is not declared under "
                 "Elements/")

    # What a passage lists as `unused` is bound by the Lean beneath its run, so that a
    # declaration cannot outlive its binding (review/SCHEMA.md).
    for i, at, missing in unbound_unused(src, n, record["passage"]):
        fail(f"{where}: [[passage]] {i}: `unused` names {', '.join(missing)}, which the "
             f"Lean beneath the `--` lines from {at!r} ({rel(lean)}) does not bind: name a "
             "binding that stands there, as the proof writes it, or `this` for a `have` "
             "that gives no name; or take the name out")

    # Every run of `--` lines with no Lean beneath it before the next run is declared: a
    # passage begins on one of its lines.
    for run in uncarried_runs(src, n):
        declared = any(ln in run.lines and words.startswith(_plain(p["at"]))
                       for p in record["passage"] for ln, words in starts)
        if not declared:
            first = " ".join(run.text.split()[:8])
            fail(f"{ref}: the `--` lines from {first!r} ({rel(lean)}:{run.line}) have no "
                 "Lean beneath them before the next `--` line (a `/- … -/` remark carries "
                 "none): move a remark that stands between them and the next sentence, put "
                 f"their Lean under them, or declare them in {where} with a [[passage]] "
                 "whose `at` quotes where they begin")


def check_facts(path: Path) -> None:
    if not path.exists():
        print(f"note: {rel(path)} not found; skipping certificate checks")
        check_reviews(None, {})
        return
    facts = json.loads(path.read_text())
    count = check_lock(facts)
    check_axioms(facts, count)
    by_ref = entries_by_ref(facts)
    check_entries(facts, by_ref)
    check_expectations(by_ref)
    check_reviews(facts, by_ref)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--facts", type=Path, default=FACTS,
                        help="the facts.json to check (default: the repository's)")
    parser.add_argument("--write-lock", action="store_true",
                        help="write Certificate/axioms.lock from facts.json, and stop")
    args = parser.parse_args(argv)
    if args.write_lock:
        return write_lock(json.loads(args.facts.read_text()))
    check_fidelity()
    check_rules()
    _, count_errors = generated_counts.updates(ROOT, check=True)
    for error in count_errors:
        fail(error)
    check_facts(args.facts)
    if errors:
        print(f"{len(errors)} problem(s):")
        for e in errors:
            print("  ✗ " + e)
        return 1
    total = sum(BOOKS.values())
    print(f"✓ fidelity: all {total} propositions quote Heath exactly; house rules, the "
          f"axiom lock, the policies for every entry and the {total} review records hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
