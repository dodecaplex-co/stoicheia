"""Check that the Lean follows Euclid, and that the house rules hold.

1. Fidelity. For every proposition, the docstring of `theorem PropN` must be
   Heath's enunciation, and the full-line `--` comments inside its proof, read in
   order, must be exactly Heath's proof (whitespace aside). Euclid's words go in
   `--` comments; our own remarks go in `/- … -/` blocks.
2. Every `axiom` lives in `Elements/Foundations/`: a first look in the source here,
   which reads `Staging/`, `Audit/` and `model/` too, and the real check from Lean's own
   environment in 6.
3. Book Zero (`Elements/Figure/`) never imports a proposition, directly or through
   another of the edition's files. Every `import` in its Lean, read as 4 reads it
   (`read_lean`), so that a comment never hides one and a string never makes one (save
   a string whose braces are kept as code, as `read_lean` reads them for 4, where an
   `import` is read too, failing closed), is read with the module it names, in each form
   of Lean 4.35's header (`public`, `meta` and `all` among them), whatever whitespace or
   comments stand between the words. An import is refused if its module, compared
   without regard to case, is under `Elements.Book`, if the module brings one in through
   the edition's own files, each read from its bytes as 4 reads the files it scans
   (`lean_text`), or if the scan cannot read it for certain, as when a part of the name
   in «…» is not a plain name.
4. None of the commands that `docs/FORMALIZATION.md`, section 7, forbids under
   `Elements/`, `Staging/`, `Audit/` or `model/` (LEAN_TREES), since they get round the kernel,
   bring in an axiom without the word, run a program when a file is built or imported,
   stop Lean reading a file, or hide an error from the build: `native_decide`,
   `bv_decide`, the word `native`, `(config := …)`, `set_option debug.…` and
   `set_option doc.…` (or `«debug».…` and `«doc».…`, with or without a space after
   `set_option`), `#eval`, `#exit`, `#guard_panic`, `#time`, `#with_exporting` and
   `#guard`, though not `#guard_msgs` or `#guard_expr` (with or without a space before the
   word after them), `run_cmd`, `elab`, `macro`, `simproc` and
   its kin, `implemented_by`, `extern`, `unsafe`, the attributes it knows to register code
   (by a name ending in `elab`, `tactic`, `init`, `proc`, `parser`, `handler`,
   `unexpander` and others, or beginning `doc_`), and the rest of FORBIDDEN, below;
   `#guard_msgs` with `drop` (GUARD_DROP) or `substring` (GUARD_SUBSTRING), in every file
   it reads, with no exception; `#guard_msgs` under a docstring that pins an error
   (`guard_docstring`), in every file it reads but the two of GUARD_ERROR_PINS; and a
   string literal found in the approximate span of `notation`, `infix`, `syntax` or
   another command of DECLARES_TOKENS, ending in a character a name may hold or `\\w`
   takes, as a letter, a digit, `_`, `'`, `!` or `?` (NAME_CHAR), in every file it reads,
   with no exception (`declared_tokens`, #234). The scan reads Lean's
   comments and its string and character literals as Lean does (`read_lean`), so a
   literal's text never opens a comment or ends an attribute's brackets, and is not read
   as code, while the code in an interpolated string's `{…}` holes is; a string whose
   braces Lean could read either way is refused, and so is a character literal or a raw
   string closed up to a name or token that Lean may read on through its first character
   (`closed_up`). It ends a name where Lean does, or sooner, before a character that `\\w`
   does not take, as `℃`, so a word closed up to `⁻¹` is seen to begin (#234). The
   scan reads each file's bytes
   decoded as UTF-8, with no newline translation (`lean_text`), so a `--` comment ends
   only at a line feed, as it does for Lean, not at a lone carriage return that Python's
   universal newlines would make one. Such a lone carriage return (a `\\r` not followed by
   `\\n`), which Lean refuses between tokens but accepts inside a comment or a literal, is
   refused in any scanned file, since a reader with universal newlines would end a comment
   at it and could miss the code after it. Each finding of 2, 3 and 4, and of a lone
   carriage return, names its file and line; symbolic links are refused by their paths and
   never followed.
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
     recorded in a decision entry of its own,
     `docs/decisions/<YYYY-MM-DD>-<slug>.md`; then
     `python3 scripts/check_fidelity.py --write-lock` writes the new lock;
   - the entries are the propositions of `heath.BOOKS`, a porism entry for each of
     Heath's porisms (`heath.heath_porisms`) and nothing else, and companions of
     those propositions, each tied to its proposition by `of` and `attached`;
   - for every entry, propositions, porisms and companions alike: none cites one that
     does not come before it; only I.4 and I.8 use superposition directly, and only I.4
     Common Notion 4 for figures (`Tacit.figures_coincide`, #517); none before I.29
     rests on Postulate 5 or any Euclidean-only rule (a later book comes after I.29, and
     may); none rests on Circle 2 or Circle 3, and each of those rules
     follows one of the allowed routes in docs/FORMALIZATION.md, section 7, "Circle 2 and
     Circle 3"; only III.24 has placement, or a lemma of the `Placement` namespace or of
     placement's files, among its shared steps;
   - every proposition of a completed book is proved, and so is everything attached
     to it, with both figures and a mishnah;
   - the facts pinned in `tests/certificate_expectations.json` still hold;
   - each name a review record's passage lists as `unused` is bound by the Lean beneath
     the run of `--` lines its `at` begins in (`unbound_unused`, read from the text by
     `bound_names`), so a declaration for the citation sweep cannot outlive its binding;
   - the review records (`review/SCHEMA.md`): every proposition has one, valid; its
     stamps match the statements in facts.json, its Lean file and its own text, so a
     record goes stale when any of them changes; its passages begin at Euclid's
     sentences and name helpers that exist; and every run of `--` lines with no Lean
     beneath it before the next run, a `/- … -/` remark ending a run and carrying none,
     is declared as a passage (`uncarried_runs`).
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
import unicodedata
from pathlib import Path
from typing import NamedTuple

import heath
# #206's reader, heath's since #349: see the note where it stood.
from heath import (CHAR, ESCAPE, FIELD, FIRST, IDENT, ID_FIRST, ID_REST, INTERPOLATED,
                   LETTER_LIKE, NAME_CHAR, NAME_RUN, NON_ASCII, NUMBER, RAW, REST,
                   SUBSCRIPT_ALNUM, read_lean, without_comments, lean_comments,
                   comment_end, _find, closed_up, _read_code, _read_string,
                   _read_interpolated, lean_string)
from heath import WORD_CHAR as WORD
import generated_counts

ROOT = heath.ROOT
BOOKS = heath.BOOKS
FACTS = ROOT / "facts.json"
LOCK = ROOT / "Certificate" / "axioms.lock"
# Where a new decision is recorded: a decision entry of its own (docs/WORKFLOW.md,
# section 10, "Decision entries"); docs/briefs/0002-decisions.md keeps the earlier ones
# as history.
DECISION_ENTRY = "a new decision entry, docs/decisions/<YYYY-MM-DD>-<slug>.md"
EXPECTATIONS = ROOT / "tests" / "certificate_expectations.json"
# Books whose every proposition is proved: they must stay that way.
COMPLETE = {"I", "II", "III"}
SUPERPOSITION_ALLOWED = {"I.4", "I.8"}
# Common Notion 4 for figures (`Tacit.figures_coincide`), which takes Metric 9's place in
# I.4's area clause (#517): only I.4 may have it among its direct axioms, so any other
# entry reaches it only through what it cites, as I.5 through I.4, or a Common Notion,
# which direct_axioms leaves out too. While it is no axiom, no entry names it and the rule
# holds of every entry.
FIGURES_COINCIDE_ALLOWED = {"I.4"}
EUCLIDEAN_ONLY = re.compile(r"^(Postulate5|Tacit\.Euclidean\..*)$")
# The first proposition of each book allowed to rest on Postulate 5. Euclid holds it
# back until I.29; Books II and III come after the whole of Book I, so they may use the
# postulate from their first proposition on, as II.10 does by name. A book missing here
# may use it throughout. A porism or companion goes with its proposition.
FIRST_EUCLIDEAN = {"I": 29, "II": 1, "III": 1}
# These rules contain III.2. No certificate entry may rest on either as an axiom, and none
# before III.2 may use either, even through a helper; a rule proved from III.2 may be used
# after III.2, and the use cites III.2. Certificate names omit the leading `Elements.`.
# Each stays an axiom in the lock, or is a theorem (`proved_rules`) proved in one of two
# ways. Proved from the other rule while that one is still a locked axiom, it brings that
# axiom into the axioms of every entry using it, which refuses the entry. Proved by a
# proof that cites III.2 (`proved_rule_cites`), with III.2 proved and resting on neither
# rule, it needs no axiom beneath it, and that is safe: an entry using such a rule cites
# III.2 through it, for Facts.lean's `directDeps`, the walk that finds an entry's
# citations, passes through the Tacit theorems. So the later-citation check refuses it in
# Books I and II and in III.1, porisms and companions included; III.2 cannot use it,
# since Lean admits no circular proof, and the route is refused if III.2's entry rests on
# either rule; after III.2 the use is an honest citation.
FORBIDDEN_CIRCLE_RULES = {
    "Tacit.inside_of_between": "Circle 2",
    "Tacit.outside_of_between": "Circle 3",
}
# The proposition that proves both, as a proved rule's `proved_rule_cites` gives it.
CIRCLE_SOURCE = "III.2"
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
# them `debug.skipKernelTC`, spelled `debug.` or `«debug».`, and with no space after
# `set_option` before a guillemet, as Lean reads `set_option«debug».skipKernelTC`, though
# not before a plain `debug`, since `set_optiondebug.skipKernelTC` is one name), bring
# in an axiom without the keyword, run a program when the file is built or imported
# (`#eval`, `run_cmd` and their kin, `initialize`, the simproc commands and
# `set_library_suggestions`, whose code `simp` and the suggestion tactics run, and the
# `doc.` options, spelled in the same ways: with
# `doc.verso` on, Lean runs the Lean in a docstring, which the scan takes out with the
# comments), give syntax a meaning in code (`elab`, `macro`), swap code in for a definition,
# stop Lean reading the file (`#exit`), take every message of the command it wraps out
# of the build, an error among them, once any one holds the word `PANIC` (`#guard_panic`),
# or wrap the command just after them, so that a word closed up to one, as in
# `#timeaxiom`, is a command that a reader of `#` and one name would miss (`#time`,
# `#with_exporting`: no file uses either, the decisions of 22 October 2026, #234).
# `#guard` runs compiled code when the file is built, as `#eval` does; Lean's other
# `#guard` tokens, `#guard_msgs` and `#guard_expr`, do not, and are not refused (no file
# uses `#guard`, the coordinator's second decision of 22 October 2026, #234).
# Matched as whole words, in the Lean as `read_lean` gives it, but for `#eval`,
# `#exit`, `#guard_panic`, `#time`, `#with_exporting` and `#guard`, which need no word
# boundary after them: Lean reads the longest command it knows, so `#evalx` is `#eval x`,
# `#exitx` stops it reading and `#guard_panicin` is `#guard_panic in` (#197), `#timeaxiom`
# is `#time axiom` and `#guard_x` is `#guard _x` (#234). An attribute that registers code
# Lean runs while a file is
# built or printed is matched too, known by the end of its name (`command_elab`,
# `grind_tactic`, `init`, `sym_simproc`, `app_unexpander`, `term_parser`, `cpass`,
# `missing_docs_handler`, `simprocAttr` and the rest) or, for `builtin_doc` and the `doc_`
# attributes, its start, and named in full in the finding. The list holds the attributes
# found in Lean 4.35 to run code while a file is built; it may not be complete, and a later
# Lean may add more. FORMALIZATION.md, section 7, is their one home.
# Lean 4.35 evaluates natively, and admits the result as an axiom, for `native_decide`, the
# `bv_decide` family and `decide` with its `native` option, which `decide +zetaReduce
# +native`, `decide (native := Bool.true)` or a whole configuration, `(config := ⟨false,
# true, true, false⟩)`, also set: so the word `native` anywhere, and `(config := …)`, are
# refused as well.
FORBIDDEN = re.compile(
    r"\bnative_decide\b|\bdecide\s*\+\s*native\b|\bnative\s*:=\s*true\b|\bnative\b|"
    r"\(\s*«?config»?\s*:=|"
    r"\bset_option(?:\s+«?|\s*«)(?:debug|doc)»?\.|"
    r"#eval|#exit|#guard_panic|#time|#with_exporting|#guard(?!_expr|_msgs)|"
    r"\b(bv_decide|bv_check|run_cmd|run_elab|run_meta|run_tac|by_elab|elab|elab_rules|"
    r"macro|macro_rules|command_elab|term_elab|initialize|builtin_initialize|"
    r"(?:builtin_)?(?:sym_|cbv_)?d?simproc(?:_decl|_pattern)?|set_library_suggestions|"
    r"implemented_by|extern|unsafe)\b|"
    r"(?:@|\battribute\s*)\[[^\]]*?\b(?P<attr>(?:builtin_)?doc(?:_\w+)?|\w*(?:elab|macro|"
    r"tactic|init|proc|discharger|unexpander|precheck|formatter|parenthesizer|control_info|"
    r"code_action|rpc_method|linter|parser|pass|suggestions?|check|handler|provider|fn|module|"
    r"hooks|Attr))\b")
# Why a finding of FORBIDDEN refuses these words, where the general reason would not say.
FORBIDDEN_WHY = {
    "#time": "which wraps the command after it, even one closed up to it (`#timeaxiom` is "
             "`#time` and `axiom`), and which no file uses, so it is refused wherever it "
             "stands",
    "#with_exporting": "which wraps the command after it, even one closed up to it "
                       "(`#with_exportingaxiom` is `#with_exporting` and `axiom`), and which "
                       "no file uses, so it is refused wherever it stands",
    "#guard": "which runs compiled code when the file is built, as `#eval` does",
}
# `#guard_msgs` with `drop` (#197): `(drop all)`, `(drop error)`, `(drop warning)`, `(drop
# info)`, `(warning, drop all)` and the rest take the messages they match out of the build.
# With `drop all` or `drop error` that is an error, so a theorem Lean refused still builds,
# resting on `sorryAx`; `drop warning` takes out the warning that a declaration uses
# `sorry`. Lean takes `drop` only as the plain word, never as `«drop»`, and needs no space
# before the brackets or inside them. Refused in every file the scan reads, with no
# exception: no file uses it (docs/briefs/0002-decisions.md, 21 October 2026), and a need
# for one is asked for in a change of its own. Matched in the Lean as `read_lean` gives it,
# so a remark inside the brackets hides nothing, and the words in a comment or a string
# are not refused.
GUARD_DROP = re.compile(r"#guard_msgs\s*\([^)]*\bdrop\b[^)]*\)")
# `#guard_msgs` with `substring` (#197): with `substring := true` the docstring need only
# appear somewhere in the messages, so one that is only part of them (`error`), an empty
# one, or none, matches an error, which leaves the build as with `drop`. Refused in any
# setting, `false` among them, with or without spaces, beside any filter or option, in
# every file the scan reads, with no exception: no file uses it (the decisions of 21
# October 2026). Matched as GUARD_DROP is.
GUARD_SUBSTRING = re.compile(r"#guard_msgs\s*\([^)]*\bsubstring\b[^)]*\)")
# `#guard_msgs` under a docstring that pins an error (#197). Lean writes each message it
# checks as its kind, `error:` for an error, and its text; a docstring that matches them
# takes them out of the build, so a theorem Lean refused still builds, resting on
# `sorryAx`. With `drop` and `substring` refused, a docstring pins an error only if it
# holds `error:`. Refused in every file the scan reads but these two, which pin errors on
# purpose: the model's round trip pins the generator's refusals, each over a `run_cmd`,
# and its audit pins one refusal of `#check`; neither wraps a declaration. The scan reads
# both, so without them here it would refuse their pins (the decisions of 21 October
# 2026).
GUARD_MSGS = re.compile(r"#guard_msgs")
GUARD_ERROR_PINS = {"model/Check/RoundTrip.lean", "model/Model/Audit.lean"}
# An axiom, declared anywhere in a line: Lean reads `example : True := trivial axiom
# planted : False` as two commands, the second an axiom.
AXIOM = re.compile(r"\baxiom\b")
# A lone carriage return: a `\r` not followed by `\n` (#207). Lean reads `\r\n` as `\n`,
# so CRLF files are allowed (no tracked .lean file has a `\r` today). It refuses a lone
# `\r` between tokens but accepts one inside a comment or a literal, and a `--` comment
# does not end at it, so, read as Lean reads the bytes, it can sit between a comment's
# words and a quote and hide the code after that quote; check_rules refuses it in every
# scanned file.
LONE_CR = re.compile(r"\r(?!\n)")
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
# Book Zero's imports (3). Lean 4.35's header (Lean/Parser/Module/Syntax.lean) is an
# optional `module`, an optional `prelude`, then any number of imports, each `[public]
# [meta] import [all] M` naming one module, two of them on one line if need be. Whitespace
# or comments, line, block or nested, may stand between the words, and nothing need stand
# before a «…» part or a comment. So every `import` in the Lean as `read_lean` gives it,
# outside a «…» name, is read with the name after it, each part plain or in «…»; one after
# a command, an error in Lean, is read all the same. Lean joins the parts into a path, and
# a disk that ignores case, as macOS's does, reads the Kelvin sign as `k` and the long s
# as `s`: so a part that is not a plain name once its «…» are off (`«Elements/BookI»`), or
# a name that does not end in whitespace, is refused as unread, and modules are compared
# in NFKC, case-folded.
IMPORT_WORD = re.compile(r"(?<![\w'!?.])import(?![\w'!?])")
MODULE_PART = r"«[^»]*»|[^\W\d][\w'!?]*"
IMPORTED = re.compile(rf"\s*(?:all(?![\w'!?.])\s*)?"
                      rf"(?P<name>(?:{MODULE_PART})(?:\.(?:{MODULE_PART}))*)(?=\s|\Z)")
PLAIN_PART = re.compile(r"[^\W\d][\w'!?]*")
QUOTED_NAME = re.compile(r"«[^»]*»")
PROPOSITIONS = "elements.book"

errors: list[str] = []


def fail(msg: str) -> None:
    errors.append(msg)


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def lean_text(path: Path) -> str:
    """A Lean source file's bytes, decoded as UTF-8, with no newline translation (#207).
    `Path.read_text()` uses Python's universal newlines, which turn a lone carriage return
    into a line feed; Lean does not. Lean reads `\\r\\n` as `\\n`,
    refuses a lone `\\r` between tokens but accepts one inside a comment or a literal, and
    a `--` comment ends only at a line feed, so a scan that let `read_text()` shorten
    `-- a remark\\r"` to a comment ending at the `\\r` would see a string open on the next
    line and swallow the code after it, hiding a forbidden command, an `axiom` included.
    Reading the bytes keeps the scan's view of comments, strings and lines exactly Lean's;
    check_rules then refuses any lone `\\r`."""
    return path.read_bytes().decode("utf-8")


def theorem_block(src: str, n: int):
    """Return (docstring, proof_comment_text) for `theorem PropN`."""
    span = heath.theorem_span(src, n)
    if span is None:
        return None, None
    # Blank block comments (our remarks), keep full-line `--` comments (Euclid's words).
    body = _blank_remarks(src[span.body:span.end])
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
            doc, words = theorem_block(lean_text(path), n)
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


# Lean's tokens, and #206's one reader of Lean's comments, strings, literals and
# names, are heath.py's: it travels with the landing tool's harness, so that the harness
# can read Lean with it too (#349; the coordinator's ruling of 22 October 23:50). They
# are imported at the top of this file under the names they had here, including the
# reader's WORD, imported from heath.py's WORD_CHAR so as not to shadow heath.WORD.

# An approximate token-declaration span (#234). Lean reads the longest token it knows, so after
# `infixl:65 " +x " => Nat.add` it reads `2 +x1set_option` as `2`, `+x`, `1` and
# `set_option`, where the scan, which does not read a file's tokens, reads `+` and the name
# `x1set_option`: `set_option«debug».byAsSorry true in theorem …` closed up so builds on
# `sorryAx`, unseen, and so does `2 +x'1set_option…` after `" +x' "`. So check_rules
# conservatively refuses every string literal it finds there that ends in a character a
# name may hold or Python's `\w` takes (NAME_CHAR), `'`, `!`, `?` and `℃` among them, in
# every file it reads: no tracked file declares such a token (the coordinator's decisions
# of 22 October 2026, the second widening the first from `\w`). `declared_tokens` reads
# literals from a command DECLARES_TOKENS names, Lean's own and Mathlib's `notation3`, from
# the command's word to the first `=>` outside brackets, which ends the tokens of a
# notation, a macro or an elaborator, or to the next command,
# whichever comes first (DECLARATION_END). A `syntax` command has no `=>` and may hold a
# literal after a spaced precedence (`syntax "a" term :max " +x " : term`), so it is read
# to the next command, known by a word of Lean's own that begins one, a keyword in every
# file, which no command's tokens can hold, or by `@[` or a `#` before a letter: a
# command whose first word is not among them, as Mathlib's `lemma`, is read as part of the
# `syntax` before it. Each literal is read, on any line of the command, as Lean reads it,
# its escapes and gaps resolved (`lean_string`), and a raw string as written; a `&"…"`,
# which declares no token, is read too. The command's word is read only as Lean reads one,
# not in a name (`Command.notation`, `«syntax»`).
DECLARES_TOKENS = re.compile(
    f"(?<![{ID_REST}.])(?:notation3?|infix[lr]?|prefix|postfix|syntax|macro|elab|"
    f"binder_predicate|declare_simp_like_tactic)(?![{ID_REST}])(?!\\.[{ID_FIRST}«])")
# The words of Lean 4.35's built-in tokens that begin a command (Lean.Parser's
# builtinTokenTable holds each).
COMMAND_WORDS = (
    "def theorem abbrev instance example structure class inductive coinductive axiom opaque "
    "namespace section end open export variable universe set_option attribute import "
    "noncomputable private protected partial nonrec unsafe mutual deriving notation infix "
    "infixl infixr prefix postfix syntax macro macro_rules elab elab_rules declare_syntax_cat "
    "binder_predicate initialize builtin_initialize omit include").split()
DECLARATION_END = re.compile(
    f"=>|@\\[|#[A-Za-z]|(?<![{ID_REST}.])(?:{'|'.join(COMMAND_WORDS)})"
    f"(?![{ID_REST}])(?!\\.[{ID_FIRST}«])")
NAME = re.compile(r"«[^»]*(?:»|\Z)")


def declared_tokens(code: str, strings: list) -> list[tuple[int, str, str]]:
    """Each string literal in an approximate token-declaration span (DECLARES_TOKENS), as
    its offset, the command's word and its text, in order: read in `code`, the Lean as
    `read_lean` gives it, with its «…» names blanked, from the word to the first
    DECLARATION_END outside brackets. The span can include a literal that declares no
    token, or one in a following library command that DECLARATION_END does not know.
    `strings` is what `read_lean` gave for the literals. A literal within two commands is
    given once, with the first. In time that grows with the length of `code`, however many
    commands there are (`_declaration_ends`)."""
    plain = NAME.sub(lambda m: re.sub(r"[^\n]", " ", m[0]), code)
    commands = [(m.end(), m[0]) for m in DECLARES_TOKENS.finditer(plain)]
    if not commands:
        return []
    ends = _declaration_ends(plain, [start for start, _ in commands])
    found, first, begun = [], 0, 0
    for offset, text in sorted(strings):
        while begun < len(commands) and commands[begun][0] <= offset:
            begun += 1
        # The first command begun at or before the literal whose end is past it: one that
        # ended before an earlier literal ended before this one too.
        while first < begun and ends[first] <= offset:
            first += 1
        if first < begun:
            found.append((offset, commands[first][1], text))
    return found


def _declaration_ends(plain: str, starts: list[int]) -> list[int]:
    """For each offset of `starts`, the first offset from it on where DECLARATION_END
    matches outside brackets, counted from that start as `declared_tokens` counts them, a
    `)`, `]` or `}` with none open counting for nothing; or the end of `plain`. With
    `height` the count of `(`, `[` and `{` less `)`, `]` and `}` before an offset, the
    brackets open there, counted from a start, are its height less the least height from
    the start to it, so none are open where the height is no greater than at any offset
    between: from each offset, `lower` gives the next such, and the ends are read from the
    last offset back."""
    height = [0] * (len(plain) + 1)
    for k, ch in enumerate(plain):
        height[k + 1] = height[k] + (ch in "([{") - (ch in ")]}")
    is_end = bytearray(len(plain) + 1)
    for m in re.finditer(f"(?=(?:{DECLARATION_END.pattern}))", plain):
        is_end[m.start()] = 1
    lower: list[int | None] = [None] * (len(plain) + 1)
    stack: list[int] = []
    for k in range(len(plain), -1, -1):
        while stack and height[stack[-1]] > height[k]:
            stack.pop()
        lower[k] = stack[-1] if stack else None
        stack.append(k)
    end = [len(plain)] * (len(plain) + 1)
    for k in range(len(plain), -1, -1):
        if is_end[k]:
            end[k] = k
        elif lower[k] is not None:
            end[k] = end[lower[k]]
    return [end[start] for start in starts]


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


def imports(code: str) -> list[tuple[int, str | None]]:
    """Each `import` in `code`, the Lean as `read_lean` gives it, outside a «…» name: its
    offset, and the module it names, plain parts joined by dots, or None if the scan cannot
    read the name for certain."""
    words = QUOTED_NAME.sub(lambda m: re.sub(r"[^\n]", " ", m[0]), code)
    found = []
    for word in IMPORT_WORD.finditer(words):
        m = IMPORTED.match(code, word.end())
        parts = [p.removeprefix("«").removesuffix("»")
                 for p in (re.findall(MODULE_PART, m["name"]) if m else ())]
        plain = bool(parts) and all(PLAIN_PART.fullmatch(p) for p in parts)
        found.append((word.start(), ".".join(parts) if plain else None))
    return found


def folded(module: str) -> str:
    """`module` as a disk that ignores case may read it: in NFKC, case-folded."""
    return unicodedata.normalize("NFKC", module).casefold()


def proposition(module: str) -> bool:
    """Is `module` under `Elements.Book`, to a Lean whose disk may ignore case?"""
    return folded(module).startswith(PROPOSITIONS)


def module_file(module: str) -> Path:
    """The edition's file for `module`, one folder for each part, as Lake finds it."""
    *folders, name = module.split(".")
    return ROOT.joinpath(*folders, name + ".lean")


def symlink_in(path: Path) -> Path | None:
    """The first symbolic-link component of `path` beneath `ROOT`, if any."""
    part = ROOT
    for name in path.relative_to(ROOT).parts:
        part /= name
        if part.is_symlink():
            return part
    return None


class FollowedImport(NamedTuple):
    path: str
    imported: str | None
    symlink: bool = False


def brought_in(module: str, read: dict) -> FollowedImport | None:
    """The first proposition that `module` imports through the edition's own Lean files,
    read breadth first, or the first symbolic link in a followed path. Each file is read
    from its bytes (`lean_text`), as Lean reads it, so a lone carriage return in a file the
    scan does not read for 4, as a root module may be, ends no `--` comment. Lean's own
    modules have no file here. `read` keeps each file's imports, so that each file is read
    once."""
    queue, seen = [module], {module}
    while queue:
        path = module_file(queue.pop(0))
        if link := symlink_in(path):
            return FollowedImport(link.relative_to(ROOT).as_posix(), None, True)
        if not path.is_file():
            continue
        if path not in read:
            read[path] = imports(read_lean(lean_text(path))[0])
        for _, imported in read[path]:
            if imported is None or proposition(imported):
                return FollowedImport(rel(path), imported)
            if imported not in seen:
                seen.add(imported)
                queue.append(imported)
    return None


def check_book_zero(file: str, code: str, read: dict) -> None:
    """Rule 3: refuse each import in the Book Zero file `file`, its Lean `code`, that brings
    in a proposition, directly or through the edition's own files, or that the scan cannot
    read for certain."""
    for offset, module in imports(code):
        where = f"{file}:{line_of(code, offset)}: Book Zero must not import a proposition"
        if module is None:
            fail(f"{where}, and the scan cannot read this import for certain: each part of "
                 "the module's name must be a plain name, in «…» or not, and whitespace "
                 "must follow it")
        elif proposition(module):
            fail(where)
        elif found := brought_in(module, read):
            if found.symlink:
                fail(f"{where}, and `{module}` reaches {found.path}, a symbolic link which "
                     "the import scan does not follow")
            else:
                fail(f"{where}, and `{module}` brings one in: {found.path} imports "
                     + (f"`{found.imported}`" if found.imported else
                        "a module the scan cannot read for certain"))


def guard_docstring(src: str, code: str, at: int) -> str:
    """The docstring of the `#guard_msgs` at offset `at`, with its `/--` and `-/`, or "" if
    it has none: the `/--` comment among the comments and whitespace just before it, read
    as `read_lean` reads them, which gave `code`. Lean takes no other docstring for it; a
    `--` or `/- … -/` comment there, a `/-!` one, or a docstring before other code, is not
    one."""
    start = at
    while start and code[start - 1].isspace():
        start -= 1
    marks: list[tuple[str, int, int]] = []
    _read_code(src[start:at], 0, marks)
    return "".join(src[start + i:start + j] for kind, i, j in marks
                   if kind == "text" and src.startswith("/--", start + i))


def check_rules() -> None:
    read: dict = {}           # each file's imports, for Book Zero's (check_book_zero)
    for path in lean_sources():
        rel = path.relative_to(ROOT).as_posix()
        if path.is_symlink():
            fail(f"{rel}: a symbolic link, which the source scan does not follow; "
                 "use a regular file or directory (docs/FORMALIZATION.md, section 7)")
            continue
        src = lean_text(path)
        strings: list[tuple[int, str]] = []
        code, unsure = read_lean(src, strings)
        for m in LONE_CR.finditer(src):
            fail(f"{rel}:{line_of(src, m.start())}: an isolated carriage return (a `\\r` not "
                 "followed by `\\n`), which Lean accepts inside a comment or a literal "
                 "and a `--` comment does not end at, so a reader with universal newlines "
                 "could miss the code after it (docs/FORMALIZATION.md, section 7)")
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
                why = FORBIDDEN_WHY.get(word, "which could get round Lean's kernel, bring in "
                                        "an axiom unseen, run a program when the file is "
                                        "built or imported, or stop Lean reading it")
                fail(f"{rel}:{line_of(code, m.start())}: uses `{word}`, {why} "
                     "(docs/FORMALIZATION.md, section 7)")
        for m in GUARD_DROP.finditer(code):
            fail(f"{rel}:{line_of(code, m.start())}: uses `{' '.join(m.group(0).split())}`, "
                 "whose `drop` takes the messages it matches out of the build, an error with "
                 "`drop all` or `drop error` (docs/FORMALIZATION.md, section 7)")
        for m in GUARD_SUBSTRING.finditer(code):
            fail(f"{rel}:{line_of(code, m.start())}: uses `{' '.join(m.group(0).split())}`, "
                 "whose `substring`, set true, lets a docstring that is only part of the "
                 "messages, an empty one, or none, match an error and take it out of the "
                 "build; it is refused in any setting (docs/FORMALIZATION.md, section 7)")
        for m in GUARD_MSGS.finditer(code) if rel not in GUARD_ERROR_PINS else ():
            if "error:" in guard_docstring(src, code, m.start()):
                fail(f"{rel}:{line_of(code, m.start())}: uses `#guard_msgs` under a docstring "
                     "holding `error:`, which pins an error and takes it out of the build; "
                     "only " + " and ".join(sorted(GUARD_ERROR_PINS)) + " may "
                     "(docs/FORMALIZATION.md, section 7)")
        for offset in unsure:
            if src[offset] in "'r":
                literal, example = (("a character literal", "`a℃'` or `⁻¹'`")
                                    if src[offset] == "'" else ("a raw string", "`a℃r\"`"))
                fail(f"{rel}:{line_of(src, offset)}: {literal} closed up to a name or token "
                     f"holding a character outside ASCII, as in {example}, through which "
                     "Lean may read on as one name or token, so the scan cannot read what "
                     "follows for certain (docs/FORMALIZATION.md, section 7)")
                continue
            fail(f"{rel}:{line_of(src, offset)}: a string the scan cannot read for certain, "
                 "since Lean could read its braces as holes of code (docs/FORMALIZATION.md, "
                 "section 7)")
        for offset, _, text in declared_tokens(code, strings):
            token = text.strip(" \t\r\n")
            if token and NAME_CHAR.match(token[-1]):
                fail(f"{rel}:{line_of(src, offset)}: finds a string literal whose trimmed "
                     f"text is `{token}` in an approximate token-declaration span; the scan "
                     "conservatively refuses such literals when their final character is "
                     "accepted by Lean's `isIdRest` or by Python's `\\w` "
                     "(docs/FORMALIZATION.md, section 7)")
        if rel.startswith("Elements/Figure/"):
            check_book_zero(rel, code, read)
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

# The lock's header, byte for byte as the committed lock has it: everything before its
# `[axioms]` line, except the last newline, which render_lock's join adds as the blank
# line. The header is part of the lock's bytes, which model/lock.sha256,
# tests/model/lock.sha256 and the model's generated files pin by the lock's sha256, so it
# changes only with the lock itself, as a lock change: with a decision entry, and the
# model's hashes renewed. tests/test_axiom_lock.py holds the two together: from the
# committed facts.json, `--write-lock` gives back the committed lock exactly (#260).
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
# recorded in a decision entry of its own, docs/decisions/<YYYY-MM-DD>-<slug>.md
# (docs/WORKFLOW.md, section 10, "Decision entries"), and then only by running
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


def circle_source_faults(facts) -> list[str]:
    """Why III.2's entry in facts.json cannot be the proof a forbidden circle rule is
    proved from: it is missing, it is not proved, or it rests on a forbidden circle rule
    itself, through its axioms, a shared step or a lemma it inherits an axiom through (the
    circular case). Empty when it can. For traversal, axioms must be a list, shared_steps
    a list of objects, and inherited an object of lists of objects; another outer shape is
    a fault, never a crash."""
    entries = facts.get("propositions")
    found = [p for p in entries if isinstance(p, dict) and p.get("ref") == CIRCLE_SOURCE] \
        if isinstance(entries, list) else []
    if not found:
        return [f"{CIRCLE_SOURCE} has no entry in facts.json"]
    faults = []
    for p in found:
        if p.get("status") != "proved":
            faults.append(f"{CIRCLE_SOURCE} is {p.get('status')!r}, not \"proved\"")
        axioms, steps, inherited = p.get("axioms"), p.get("shared_steps"), p.get("inherited")
        if not isinstance(axioms, list):
            faults.append(f"{CIRCLE_SOURCE}'s `axioms` is not a list")
            axioms = []
        if not isinstance(steps, list) or not all(isinstance(s, dict) for s in steps):
            faults.append(f"{CIRCLE_SOURCE}'s `shared_steps` is not a list of objects")
            steps = []
        if not isinstance(inherited, dict) or not all(
                isinstance(lems, list) and all(isinstance(lem, dict) for lem in lems)
                for lems in inherited.values()):
            faults.append(f"{CIRCLE_SOURCE}'s `inherited` is not an object of lists of objects")
            inherited = {}
        lemmas = [lem.get("name") for lems in inherited.values() for lem in lems]
        for name, rule in FORBIDDEN_CIRCLE_RULES.items():
            if name in axioms:
                faults.append(f"{CIRCLE_SOURCE} itself rests on {name} ({rule}) among its axioms")
            if any(s.get("name") == name for s in steps):
                faults.append(f"{CIRCLE_SOURCE} itself names {name} ({rule}) among its "
                              "shared steps")
            if name in lemmas:
                faults.append(f"{CIRCLE_SOURCE} itself names {name} ({rule}) among the "
                              "lemmas it inherits through")
    return list(dict.fromkeys(faults))


def check_lock(facts, path: Path = LOCK):
    """Compare the lock with facts.json's `axiom_types` and `vocabulary`, both ways.
    Returns the number of assumptions the lock holds, or None if it cannot be read."""
    try:
        lock = read_lock(path)
    except (ValueError, RuntimeError) as e:
        fail(str(e))
        return None
    if lock is None:
        fail(f"{rel(path)} is missing: with {DECISION_ENTRY}, write it with "
             "`python3 scripts/check_fidelity.py --write-lock`")
        return None
    proved = facts.get("proved_rules", {})
    # What each proved rule cites. A missing or non-object field, or a missing or non-list
    # value for the rule, supplies no citation; list contents receive no further validation.
    cites = facts.get("proved_rule_cites")
    cites = cites if isinstance(cites, dict) else {}
    for name, rule in FORBIDDEN_CIRCLE_RULES.items():
        if name in lock[0]:
            continue
        if name not in proved:
            fail(f"{name} ({rule}): not an axiom in {rel(path)} or a proved rule in "
                 "facts.json (if the rule was renamed, rename it in FORBIDDEN_CIRCLE_RULES too)")
        elif any(other != name and other in lock[0] and other in proved[name]
                 for other in FORBIDDEN_CIRCLE_RULES):
            continue
        elif not (isinstance(cites.get(name), list) and CIRCLE_SOURCE in cites[name]):
            fail(f"{name} ({rule}): proved without another forbidden circle rule "
                 f"beneath it that is an axiom in {rel(path)}, or a proof that cites "
                 f"{CIRCLE_SOURCE}, so entries using it cannot be refused by their axioms "
                 "or by their citations")
        else:
            for fault in circle_source_faults(facts):
                fail(f"{name} ({rule}): proved by a proof that cites {CIRCLE_SOURCE}, "
                     f"but {fault}, so the rule is not proved from a sound {CIRCLE_SOURCE}")
    types, vocabulary = facts.get("axiom_types"), facts.get("vocabulary")
    if types is None or vocabulary is None:
        fail("facts.json has no axiom_types or vocabulary: rerun `lake env lean Certificate/Facts.lean`")
        return len(lock[0])
    locked_axioms, locked_vocabulary = lock
    where = rel(path)
    for name in sorted(set(types) - set(locked_axioms)):
        fail(f"{name}: an assumption not in {where} (a new axiom is a decision: record it in "
             f"{DECISION_ENTRY}, then run `python3 scripts/check_fidelity.py --write-lock`)")
    for name in sorted(set(locked_axioms) - set(types)):
        fail(f"{name}: in the lock but no longer an axiom ({where}; removing one is a decision "
             f"for {DECISION_ENTRY})")
    for name in sorted(set(types) & set(locked_axioms)):
        if types[name] != locked_axioms[name]:
            fail(f"{name}: its statement is not the one in {where}:\n      "
                 + first_difference(types[name], locked_axioms[name]))
    # The vocabulary: the words of the axioms' statements and of the entries'.
    for name in sorted(set(vocabulary) - set(locked_vocabulary)):
        fail(f"{name}: a word of the statements, the axioms' or the entries', not in "
             f"{where} (a new word is a decision: record it in {DECISION_ENTRY}, "
             "then run `python3 scripts/check_fidelity.py --write-lock`)")
    for name in sorted(set(locked_vocabulary) - set(vocabulary)):
        fail(f"{name}: in the lock but no longer a word of any statement ({where})")
    for name in sorted(set(vocabulary) & set(locked_vocabulary)):
        if vocabulary[name] != locked_vocabulary[name]:
            fail(f"{name}: its definition is not the one in {where} (a changed word changes "
                 f"what every statement using it says: a decision for {DECISION_ENTRY}):"
                 "\n      "
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
        print(f"Record it in {DECISION_ENTRY}.")
        return 0
    changes = []
    for new, before, label in ((axioms, old[0], "axiom"), (vocabulary, old[1], "vocabulary")):
        changes += [f"  + {label} {k}" for k in sorted(set(new) - set(before))]
        changes += [f"  - {label} {k}" for k in sorted(set(before) - set(new))]
        changes += [f"  ~ {label} {k}" for k in sorted(set(new) & set(before)) if new[k] != before[k]]
    print("\n".join(changes) if changes else "  (no change)")
    if changes:
        print(f"Record the decision in {DECISION_ENTRY}, with the reason.")
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
             f"removed assumption is a decision for {DECISION_ENTRY}, and then "
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
        if "Tacit.figures_coincide" in p.get("direct_axioms", []) \
                and ref not in FIGURES_COINCIDE_ALLOWED:
            fail(f"{ref}: uses Common Notion 4 for figures directly (only I.4 may)")
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

def check_expectations(by_ref, path: Path = EXPECTATIONS, facts: dict | None = None) -> None:
    """Each expectation names a `field`, and usually an entry (`ref`), and asks that a
    supported field of names `includes` some names, `excludes` others, or holds exactly
    `count` names beginning with `prefix`; `equals` compares any field with a value. A
    field that is an object, as `inherited` is, is read by its keys: the axioms it names.
    `cited_laws` is a list of objects, read by each object's `law`, and fails unless every
    object has one; an expectation that also names a `law` reads that law's
    `construction_rules` instead, and fails when the entry cites no such law. `includes`,
    `excludes` and `count` read nothing else: on any other field, as `shared_steps` or a
    scalar is, they fail rather than read it as empty. An expectation with no `ref` reads
    a field of facts.json's top level, as `construction_rules` is, from `facts`. One with
    `"every": "entry"` and no `ref` reads its field in every entry of `by_ref` instead, and
    asks only that it `excludes` some names: there a list of objects, as `shared_steps`
    is, is read by each object's `name`, and fails unless every object has one, so that no
    entry's `shared_steps` can name Circle 3, say. An expectation that asks nothing fails:
    `includes` and `excludes` are effective only when nonempty lists of names, while
    `equals` and `count`, an object with an integer `is`, are effective whenever present."""
    if not path.exists():
        fail(f"{rel(path)} is missing")
        return
    try:
        data = json.loads(path.read_text())
        expectations = data["expectations"]
    except (json.JSONDecodeError, KeyError, TypeError) as e:
        fail(f"{rel(path)}: expected a JSON object with a list `expectations` ({e})")
        return
    known = {"ref", "field", "law", "includes", "excludes", "equals", "count", "why", "every"}
    for i, x in enumerate(expectations, 1):
        label = f"{rel(path)}, expectation {i}"
        reads_names = isinstance(x, dict) and (
            bool(x.get("includes")) or bool(x.get("excludes")) or "count" in x)
        effective = reads_names or (isinstance(x, dict) and "equals" in x)
        if (not isinstance(x, dict) or not {"field", "why"} <= set(x) or set(x) - known
                or not effective or ("law" in x and "ref" not in x)):
            fail(f"{label}: needs `field` and `why`, a `ref` unless it reads the top level "
                 "of facts.json (and always with a `law`), and an effective predicate: "
                 "nonempty `includes` or `excludes`, or present `equals` or `count`")
            continue
        count = x.get("count", {"is": 0})
        if not (all(isinstance(x.get(k, []), list)
                    and all(isinstance(n, str) for n in x.get(k, []))
                    for k in ("includes", "excludes"))
                and isinstance(count, dict) and set(count) <= {"prefix", "is"}
                and isinstance(count.get("is"), int)
                and isinstance(count.get("prefix", ""), str)):
            fail(f"{label}: `includes` and `excludes` must be lists of names, and `count` "
                 "an object with an integer `is` and, if it has one, a string `prefix`")
            continue
        if "every" in x and (x["every"] != "entry"
                             or set(x) - {"every", "field", "excludes", "why"}):
            fail(f"{label}: an expectation over every entry is `\"every\": \"entry\"`, with "
                 "a `field` and a nonempty `excludes`, and no `ref`, `law`, `includes`, "
                 "`equals` or `count`")
            continue
        field, why = x["field"], x["why"]
        if "every" in x:
            # With no entry to read, every `excludes` would pass.
            if not by_ref:
                fail(f"{label}: reads every entry, but facts.json has none")
            for ref, (_, p) in by_ref.items():
                if field not in p:
                    fail(f"{ref}: pinned by {label}, but its entry has no field `{field}`")
                    continue
                value = p[field]
                if isinstance(value, dict):
                    listed = list(value)
                elif isinstance(value, list) and all(isinstance(v, str) for v in value):
                    listed = value
                elif isinstance(value, list) and all(
                        isinstance(v, dict) and isinstance(v.get("name"), str) for v in value):
                    listed = [v["name"] for v in value]
                else:
                    fail(f"{ref}: its {field} is not a list of names, an object or a list of "
                         f"objects each with a `name`, so `excludes` cannot read it ({label}: "
                         f"{why})")
                    continue
                for name in x["excludes"]:
                    if name in listed:
                        fail(f"{ref}: its {field} should not include {name} ({label}: {why})")
            continue
        if "ref" in x:
            ref = x["ref"]
            if ref not in by_ref:
                fail(f"{ref}: pinned by {label}, but facts.json has no such entry")
                continue
            holder = by_ref[ref][1]
        else:
            ref = "facts.json"
            if facts is None:
                fail(f"{label}: reads the top level of facts.json, which was not given")
                continue
            holder = facts
        if field not in holder:
            # Read as empty, a missing field would let every `excludes` pass.
            where = "its entry" if "ref" in x else "its top level"
            fail(f"{ref}: pinned by {label}, but {where} has no field `{field}`")
            continue
        value, what = holder.get(field), field
        if field == "cited_laws" and ("law" in x or reads_names):
            laws = [v.get("law") if isinstance(v, dict) else None for v in value] \
                if isinstance(value, list) else [None]
            if not all(isinstance(n, str) and n for n in laws):
                fail(f"{ref}: pinned by {label}, but its cited_laws is not a list of objects "
                     "each with a `law` name")
                continue
        if "law" in x:
            law = x["law"]
            found = [v for v in value if isinstance(v, dict) and v.get("law") == law] \
                if isinstance(value, list) else []
            if len(found) != 1 or "construction_rules" not in found[0]:
                fail(f"{ref}: pinned by {label}, but its {field} has no law {law} with "
                     "construction_rules")
                continue
            value, what = found[0]["construction_rules"], \
                f"construction_rules for the cited law {law}"
        if "equals" in x and value != x["equals"]:
            fail(f"{ref}: its {what} is {value!r}, not {x['equals']!r} ({label}: {why})")
        if not reads_names:
            continue
        if isinstance(value, dict):
            listed = list(value)
        elif field == "cited_laws" and "law" not in x:
            listed = [v["law"] for v in value]
        elif isinstance(value, list) and all(isinstance(v, str) for v in value):
            listed = value
        else:
            fail(f"{ref}: its {what} is not a list of names, an object or cited_laws, so "
                 f"`includes`, `excludes` and `count` cannot read it ({label}: {why})")
            continue
        for name in x.get("includes", []):
            if name not in listed:
                fail(f"{ref}: its {what} should include {name} ({label}: {why})")
        for name in x.get("excludes", []):
            if name in listed:
                fail(f"{ref}: its {what} should not include {name} ({label}: {why})")
        if "count" in x:
            prefix, want = x["count"].get("prefix", ""), x["count"].get("is")
            got = sum(1 for v in listed if isinstance(v, str) and v.startswith(prefix))
            if got != want:
                fail(f"{ref}: its {what} has {got} names beginning {prefix!r}, not {want} "
                     f"({label}: {why})")


# How the `--` lines sit in the Lean, for the review records.

FORMULA = re.compile(
    r"\[?(?:(?:If\s+)?therefore\s+etc\.|Q\.\s*E\.\s*[DF]\.|"
    r"\(?Being\)?\s+what\s+it\s+was\s+required\s+to\s+(?:do|prove)\.)\]?|\]", re.I)
PORISM_LINE = re.compile(r"\[?PORISM\.")
SENTENCE_BREAK = re.compile(r"[.;:?!\]]\s+(?=\S)")


def _blank_remarks(text: str) -> str:
    """`text` with every `/- … -/` remark (nested ones too) made spaces, line breaks
    kept, and `--` line comments left as they are: the comments as `read_lean` reads
    them (`lean_comments`), so that a `--` within a remark goes with it, and a `/-`
    within a `--` comment or a string opens none."""
    out = list(text)
    for i, j in lean_comments(text):
        if text.startswith("/-", i):
            out[i:j] = ["\n" if ch == "\n" else " " for ch in text[i:j]]
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
        for line in read_lean(lean_text(path))[0].splitlines():
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
    own = heath.text_hash(heath.review_path(book, n).read_text())
    if rv["text"] != own:
        fail(f"{ref}: its record has changed since it was reviewed ({where} has `text` "
             f"{rv['text']}, its text now is {own}): read the record again, then stamp it "
             "with scripts/review_stamp.py --commit (WORKFLOW.md, section 6)")
    lean = heath.lean_path(book, n)
    if not lean.exists():
        return
    want = heath.file_hash(lean)
    if rv["lean"] != want:
        fail(f"{ref}: its Lean file has changed since it was reviewed ({where} has "
             f"{rv['lean']}, {rel(lean)} is {want}): read the record again, then run "
             "scripts/review_stamp.py --commit (WORKFLOW.md, section 6)")

    # The passages begin at Euclid's sentences, and name helpers that exist.
    src = lean_text(lean)
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
    check_expectations(by_ref, EXPECTATIONS, facts)
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
