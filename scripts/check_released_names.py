#!/usr/bin/env python3
"""Check that main keeps every name the last release tag declares, unless the tag deprecated it.

    python3 -I scripts/check_released_names.py               the check
    python3 -I scripts/check_released_names.py --self-test   planted cases first, then the check
    python3 -I scripts/check_released_names.py --list TAG    the list, printed at a release tag
    python3 -I tests/test_check_released_names.py            the rule's cases, which CI runs first

FORMALIZATION.md, section 2, "A released name stays, or is deprecated first": a released
name, one that a release tag's `Elements` declares, helpers and Book Zero included, is never
renamed or removed without a deprecated alias for one release, and a name deprecated in a
release may go in the release after. This script holds main to that against the last
release tag, whose names tests/released_names.txt lists (card #700).

The rule, for each name the list holds. A name the tag marked `deprecated` passes whether
main declares it or not: it may go in the release after the one that deprecated it. Any
other passes when main declares it, deprecated or not, and fails when main does not, with
"<name>: released in <tag>, missing on main with no deprecated alias (FORMALIZATION.md,
section 2)". A name new on main passes. So a renamed name passes only with its alias under
the old name, and a namespace renamed fails once for each name in it.

The probe. Names are read by a Lean file, `import Elements` and one `#eval` (PROBE_HEAD and
PROBE_EVAL below), written to a temporary folder outside the repository and run as
`lake env lean <file>` from the repository's root. It prints a row for each declaration:

* of a module under `Elements`, or of the probe's own file, which the self-test uses;
* that is neither an internal detail nor private (`_private`, `match_`, `proof_`, `eq_`);
* that is not a recursor Lean makes (`rec`, `casesOn`, `recOn`, `brecOn`, `noConfusion`);
* that is not a parser, a constant of type `Lean.ParserDescr` or `Lean.TrailingParserDescr`,
  as Lean makes for a `notation` or an infix and names from its symbols
  (`Elements.«term∠___»`): no citer writes such a name, and no deprecated alias can stand
  in for one, since a change to a notation is a change of how statements are written,
  which is outside this check. Instances stay: they are names Lean prints, and a user can
  cite them;
* that was written in the source, as its declaration range shows: the declarations without
  one are all Lean's own (`sizeOf_spec`, `injEq`, `inj`, `ctorIdx`, `below.*`, `eq_def`
  and the like).

A row is `name <n>`, or `deprecated <n>` for a declaration marked `@[deprecated]`, with
`<n>` as Lean prints the name, one word. Any other line of the probe's output, as a Lean
message would be, anything on its standard error, a failed run and an empty output each
stop the check (exit 2), never a pass. Measured on 29 October 2026, before parsers were
left out: book-III's build gave 502 rows and origin/main's at 511fb5fe5 gave 1,854, each
with the parsers of the four notations of Elements/Foundations/Magnitudes.lean among
them, so 498 and 1,850 without them; the names book-III has and main lacks are
`Elements.Triangle.of_onCircle`, `Elements.exists_onCircle_oppositeSidesOf` and
`Elements.exists_onCircle_sameSideOf`.

The probe reads the BUILT library, the .olean files that `lake build` writes, and not the
sources, and a stale build would give a stale answer. So before the probe, in each mode
that runs it, the script runs `lake build --no-build Elements` from the repository's
root, which builds nothing and fails when a module of `Elements` is not up to date with
its sources; when it fails, the script stops (exit 2) and prints its last lines. A stale
build is refused, not judged: run `lake build` first. In CI's `check` job the build runs
before this check, so there the refusal costs a check of Lake's traces and nothing more.

The list. tests/released_names.txt holds `#` comment lines, saying what it is and how it
is made; then one line `tag <tag> <commit>`, with the tag's full 40-hex commit; then the
probe's rows at the tag, sorted by code point, each name once. The tag begins with an ASCII
letter or digit, continues with ASCII letters, digits, `.`, `_`, `/` or `-`, and must make
a valid `refs/tags/<tag>` Git ref. Anything else is refused with its line (exit 2): a blank
line, a comment after the tag line, a row before it, a second tag line, a tag outside that
form, a commit that is not 40 lower-case hex digits, an unknown marker, a name listed
twice, a row out of order, or no rows at all. `--list TAG` prints the whole file, in a
built checkout whose HEAD is TAG's commit, and refuses a tag outside that form or any
other unmet condition (exit 2). Every tracked file except the list must be free of the
`assume-unchanged` and `skip-worktree` index flags:
either flag causes refusal even when the file's contents match HEAD, and must be cleared
before listing. No file that could change what the build declares may differ from the
commit: no tracked file may be modified, the list itself excepted, and there may be no
untracked or ignored Lean file, `lakefile.lean`, `lakefile.toml`, `lake-manifest.json` or
`lean-toolchain`. The list is excepted because the recipe's redirection empties it before
the script runs (`--list TAG > tests/released_names.txt`); the build never reads it. An
untracked copy of the script, which a tag made before the script needs, is allowed. At each
release, once the tag is made, the list is made with `--list <new tag>` at the tag's commit,
copied to a branch off main and
committed in the next pull request, the first after the release; until it lands, main is
compared with the release before, which is still correct for every name that release
declared. WORKFLOW.md, section 10's release step does not yet name this step: card #700's
handback proposes it. When the repository holds the list's tag and the tag points to
another commit, the list is not the tag's, and that is a finding. When the repository
does not hold it, as CI's `check` job does not, since it fetches no tags, or git cannot
say, one line says so and the check goes on. When the repository holds a later tag, one
whose history holds the list's commit, one line names it: the list may be out of date
(a note and not a finding, since between a tag and the list's pull request that is
expected).

The self-test writes the probe with a namespace of declarations, PLANTS, before its
`#eval`, and runs it once. Lean must read `kept`, `New.a`, `New.b`, `Old.b2` and the
instance `instPlant` as plain and `renamed`, `retired` and `Old.a` as deprecated, all in
`Elements.ReleasedNamesPlant`, and the structure `Shape`, its constructor and its field
plain; it must give no row for the private `hidden`, nor for the parsers of the notation
`⟪a⟫` and the infix `a ⊞ b`, one of each type left out, nor for nine names Lean makes for
`Shape` (its recursors, `noConfusion` and the names with no declaration range), nor for
any other name of the namespace; it must print no name outside `Elements`; and it must
read the real `Elements.BookI.Prop1` plain. Each name that must give no row is used by an
`example` in PLANTS, so a plant removed stops Lean rather than reading as absent. Then it
judges, on that output, lists made in memory (PLANT_CASES): a name removed fails; one
renamed with its alias passes, and so does one deprecated with nothing to replace it; of
two names, one with its alias and one aliased nowhere, only the second fails; a namespace
renamed fails once for each of its two names; a removed name that the tag marked
deprecated passes; and a list that names nothing new on main passes, though `New.a` and
`New.b` are there. Any surprise fails it (exit 1). Then the check runs on the same output,
with the planted namespace left out: one Lean file in all.

Exits 0 when no released name is missing and the list's tag, where the repository holds
it, points to the list's commit; 1 on any finding, printing each, then a summary of the
names released, those present on main, those of them deprecated there and those missing;
2 when it cannot judge: no `lake` on PATH, a build of `Elements` that is not current, the
probe fails or prints anything but rows, or the list is malformed; and 2 when `--list` is
refused. A temporary probe that cannot be created, resolved, written or removed also exits
2 without a traceback. Standard library only; Python 3.11 or later. A module planted
beside the script is never read in its place.
"""

import os
import sys

# Run as `python3 scripts/check_released_names.py`, Python puts the script's own folder
# first on sys.path, so a module planted there would stand in for the standard library's.
# sys is built in, and site has loaded os before any script runs, so neither is read from
# the folder; the folder is taken off before any other import. A script that imports this
# one, as its test does, keeps its own sys.path.
if __name__ == "__main__":
    sys.path[:] = [p for p in sys.path if os.path.realpath(p or os.curdir)
                   != os.path.dirname(os.path.realpath(__file__))]

import argparse  # noqa: E402
import re  # noqa: E402
import shutil  # noqa: E402
import subprocess  # noqa: E402
import tempfile  # noqa: E402
from pathlib import Path  # noqa: E402
from typing import NamedTuple  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
LIST = Path("tests/released_names.txt")
LIST_FILE = ROOT / LIST
RULE = "FORMALIZATION.md, section 2"

# The probe, in two parts, so that the self-test can put its plants between them.
PROBE_HEAD = """\
import Lean
import Elements

open Lean

"""
PROBE_EVAL = """\
#eval show CoreM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, info) in env.constants.toList do
    let own := match env.getModuleIdxFor? n with
      | some idx => (`Elements).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => true
    unless own do continue
    if n.isInternalDetail || isPrivateName n then continue
    if isAuxRecursor env n || isNoConfusion env n || isRecCore env n then continue
    if info.type.isConstOf ``Lean.ParserDescr then continue
    if info.type.isConstOf ``Lean.TrailingParserDescr then continue
    if (← findDeclarationRanges? n).isNone then continue
    rows := rows.push (if Linter.isDeprecated env n then s!"deprecated {n}" else s!"name {n}")
  for r in rows.qsort (· < ·) do IO.println r
"""

# The self-test's declarations, in a namespace of their own. Nothing uses a deprecated one,
# so Lean prints no warning for a use, and any message it printed would stop the self-test
# as output that is not a row. `retired` carries a message: Lean 4.35 warns at an attribute
# `@[deprecated (since := …)]` with neither a new name nor a message ("`[deprecated]`
# attribute should specify either a new name or a deprecation message"). The notation gives
# a parser of type `Lean.ParserDescr`, `«term⟪_⟫»`, and the infix one of type
# `Lean.TrailingParserDescr`, `«term_⊞_»`; each also gives definitions that are internal
# details and have a range, which only `isInternalDetail` leaves out. The structure `Shape`
# gives, in Lean 4.35, a name that only each of the other filters leaves out: `Shape.rec`
# the recursor filter's `isRecCore`, `Shape.recOn` and `Shape.casesOn` its
# `isAuxRecursor`, `Shape.mk.noConfusion` its `isNoConfusion`, and `Shape.ctorIdx`,
# `Shape.noConfusionType`, `Shape.mk.inj`, `Shape.mk.injEq` and `Shape.mk.sizeOf_spec` the
# range filter (each has no declaration range). The private `hidden` is an internal detail
# too, so `isInternalDetail` alone leaves it out, and `isPrivateName` is a second guard;
# with both gone, its private name, outside `Elements`, is a surprise. Every plant and
# generated name that must give no row is used by an `example` after the declarations, so
# that, were one gone, Lean would stop the self-test with an error, and not read it as
# absent. The recursor's two are noncomputable: Lean makes no code for a recursor.
PLANT_NAMESPACE = "Elements.ReleasedNamesPlant"
PLANTS = """\
namespace Elements.ReleasedNamesPlant
theorem kept : True := trivial
@[deprecated Elements.ReleasedNamesPlant.kept (since := "2026-10-29")]
theorem renamed : type_of% @kept := @kept
@[deprecated "nothing replaces it" (since := "2026-10-29")] theorem retired : True := trivial
theorem New.a : True := trivial
theorem New.b : True := trivial
@[deprecated Elements.ReleasedNamesPlant.New.a (since := "2026-10-29")]
theorem Old.a : type_of% @New.a := @New.a
theorem Old.b2 : True := trivial
private theorem hidden : True := trivial
notation "⟪" a "⟫" => id a
infixl:65 " ⊞ " => Nat.add
instance instPlant : Inhabited (Fin 1) := ⟨0⟩
structure Shape where
  side : Nat
example : True := hidden
example : Lean.ParserDescr := «term⟪_⟫»
example : Lean.TrailingParserDescr := «term_⊞_»
noncomputable example := @Shape.rec
noncomputable example := @Shape.recOn
example := @Shape.casesOn
example := @Shape.mk.noConfusion
example := @Shape.ctorIdx
example := @Shape.noConfusionType
example := @Shape.mk.inj
example := @Shape.mk.injEq
example := @Shape.mk.sizeOf_spec
end Elements.ReleasedNamesPlant

"""
# How Lean must read each plant; None for one that must give no row: `hidden`, private, the
# parsers of the notation and the infix, and the names `Shape` gives that a filter leaves
# out. Any other row of the planted namespace, an internal detail among them, is a surprise.
PLANTED = {"kept": "name", "New.a": "name", "New.b": "name", "Old.b2": "name",
           "instPlant": "name", "renamed": "deprecated", "retired": "deprecated",
           "Old.a": "deprecated", "Shape": "name", "Shape.mk": "name", "Shape.side": "name",
           "hidden": None, "«term⟪_⟫»": None, "«term_⊞_»": None, "Shape.rec": None,
           "Shape.recOn": None, "Shape.casesOn": None, "Shape.mk.noConfusion": None,
           "Shape.ctorIdx": None, "Shape.noConfusionType": None, "Shape.mk.inj": None,
           "Shape.mk.injEq": None, "Shape.mk.sizeOf_spec": None}
# A real declaration of the library, which the plants' run must read too, and plain.
REAL = "Elements.BookI.Prop1"
# The lists the self-test judges on the plants' output: what each shows, the released
# names with their markers at the tag, and the names that must fail, in order. A short name
# is in the planted namespace; `gone`, `Old.c`, `Old.x` and `Old.y` are declared nowhere.
PLANT_CASES = (
    ("a released name removed fails", {"gone": "name"}, ["gone"]),
    ("a renamed name with its deprecated alias passes", {"renamed": "name"}, []),
    ("a name deprecated with nothing to replace it passes", {"retired": "name"}, []),
    ("beside a name with its alias, a name aliased nowhere fails alone",
     {"Old.a": "name", "Old.c": "name"}, ["Old.c"]),
    ("a namespace renamed fails once for each name in it",
     {"Old.x": "name", "Old.y": "name"}, ["Old.x", "Old.y"]),
    ("a removed name the tag marked deprecated passes", {"gone": "deprecated"}, []),
    ("a list that names nothing new on main passes", {"kept": "name", REAL: "name"}, []),
)

MARKERS = ("name", "deprecated")
SHOWN = {"name": "plain", "deprecated": "deprecated", None: "absent"}
ROW = re.compile(r"(?P<marker>name|deprecated) (?P<name>\S+)")
TAG_LINE = re.compile(r"tag (?P<tag>\S+) (?P<commit>\S+)")
TAG = re.compile(r"[A-Za-z0-9][A-Za-z0-9._/-]*")
COMMIT = re.compile(r"[0-9a-f]{40}")

# What the list's comment lines say; `--list` prints them before the tag line.
LIST_HEADER = """\
# tests/released_names.txt: the names that release tag {tag}'s `Elements` declares, which
# scripts/check_released_names.py holds main to (FORMALIZATION.md, section 2, "A released
# name stays, or is deprecated first"). It is made by the script, never by hand, in a
# checkout of the tag's commit, after `lake build`, with no other file modified:
#     python3 -I scripts/check_released_names.py --list {tag} > tests/released_names.txt
# At each release, once the tag is made, it is made with `--list <new tag>` at the tag's
# commit, copied to a branch off main and committed in the next pull request, the first
# after the release; until it lands, main is compared with the release before, which is
# still correct for every name that release declared. After the tag line, each row is
# `name <n>`, or `deprecated <n>` for a name the tag marks deprecated, sorted by code
# point, each name once.
"""

# Builds nothing: fails when a module of `Elements` is not up to date with its sources (exit
# 3 in Lake 4.35), printing which, and on a current build prints nothing the probe reads. On
# a stale build Lake writes its diagnosis, a `.trace.nobuild` file, beside the trace of each
# module it finds out of date, and changes no .olean and no trace.
BUILD_CHECK = ("lake", "build", "--no-build", "Elements")
# How many of its last lines a refused build shows.
BUILD_LINES = 12


class Unreadable(Exception):
    """The list, probe or repository cannot be read or prepared, the build is not current,
    or `--list` is refused: the check cannot judge."""


class Listed(NamedTuple):
    """A list of released names: its tag, the tag's commit, the line of the tag line, and
    each name with its marker at the tag, in the list's order."""
    tag: str
    commit: str
    tag_line: int
    names: dict[str, str]


class TagTarget(NamedTuple):
    """The object a tag names after annotated tags are peeled, and its Git type."""
    oid: str
    kind: str


def printable(text: str) -> str:
    return text.encode("utf-8", "surrogateescape").decode("utf-8", "backslashreplace")


def shorten(line: str, width: int = 80) -> str:
    line = printable(line)
    return line if len(line) <= width else line[:width - 1] + "…"


def display(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        raise Unreadable(f"cannot read {display(path)}") from None


def lines_of(text: str) -> list[str]:
    """The lines of `text`, the empty one after its last line break left out."""
    lines = text.split("\n")
    if lines[-1] == "":
        lines.pop()
    return lines


def is_tag_name(tag: str) -> bool:
    """Whether `tag` has the restricted form here and makes a valid `refs/tags/` ref."""
    if not TAG.fullmatch(tag):
        return False
    ref = f"refs/tags/{tag}"
    parts = ref.split("/")
    return (".." not in ref and not ref.endswith(".")
            and all(part and not part.startswith(".") and not part.endswith(".lock")
                    for part in parts))


def parse_list(text: str, shown: str = str(LIST)) -> Listed:
    """The list `text`, as Listed; Unreadable, naming the line, when it breaks the form."""
    tag = commit = ""
    tag_line = 0
    names: dict[str, str] = {}
    first: dict[str, int] = {}
    previous: tuple[str, int] | None = None
    for number, line in enumerate(lines_of(text), 1):
        where = f"{shown}:{number}"
        if line.startswith("#"):
            if tag_line:
                raise Unreadable(f"{where}: a comment after the tag line; the comments "
                                 "stand before it")
            continue
        if not line.strip():
            raise Unreadable(f"{where}: a blank line; the list holds its comments, its tag "
                             "line and its rows, and nothing else")
        word = line.split(" ", 1)[0]
        if word == "tag":
            if tag_line:
                raise Unreadable(f"{where}: a second tag line (the first is line {tag_line})")
            found = TAG_LINE.fullmatch(line)
            if not found:
                raise Unreadable(f"{where}: `{shorten(line)}` is not a tag line, which is "
                                 "`tag <tag> <40-hex commit>`")
            if not is_tag_name(found["tag"]):
                raise Unreadable(f"{where}: `{shorten(found['tag'])}` is not a tag's name")
            if not COMMIT.fullmatch(found["commit"]):
                raise Unreadable(f"{where}: `{shorten(found['commit'])}` is not a full "
                                 "commit, 40 lower-case hex digits")
            tag, commit, tag_line = found["tag"], found["commit"], number
            continue
        if not tag_line:
            raise Unreadable(f"{where}: a row before the tag line, which comes first "
                             "(`tag <tag> <40-hex commit>`)")
        row = ROW.fullmatch(line)
        if not row:
            if word in MARKERS:
                raise Unreadable(f"{where}: `{shorten(line)}` is not a row, which is `name "
                                 "<n>` or `deprecated <n>`, one name of one word")
            raise Unreadable(f"{where}: `{shorten(word)}` is an unknown marker; a row is "
                             "`name <n>` or `deprecated <n>`")
        name = row["name"]
        if name in first:
            raise Unreadable(f"{where}: `{name}` is listed twice (first at line "
                             f"{first[name]})")
        if previous is not None and line < previous[0]:
            raise Unreadable(f"{where}: `{shorten(line)}` is out of order, after "
                             f"`{shorten(previous[0])}` (line {previous[1]}); the rows are "
                             "sorted by code point")
        names[name] = row["marker"]
        first[name] = number
        previous = (line, number)
    if not tag_line:
        raise Unreadable(f"{shown}: no tag line (`tag <tag> <40-hex commit>`)")
    if not names:
        raise Unreadable(f"{shown}:{tag_line}: no row follows the tag line, so the list "
                         "names nothing")
    return Listed(tag, commit, tag_line, names)


def render_list(tag: str, commit: str, rows: dict[str, str]) -> str:
    """The list file for `tag` at `commit`, with the probe's rows: what `--list` prints."""
    body = "".join(f"{row}\n" for row in sorted(f"{marker} {name}"
                                               for name, marker in rows.items()))
    return LIST_HEADER.format(tag=tag) + f"tag {tag} {commit}\n" + body


def read_probe(out: str) -> dict[str, str]:
    """The probe's rows, each name with its marker; Unreadable on an empty output, on a
    line that is not a row, as a Lean message is not, and on a name printed twice."""
    lines = lines_of(out)
    if not lines:
        raise Unreadable("the probe printed no names; is the library built (`lake build`)?")
    names: dict[str, str] = {}
    for number, line in enumerate(lines, 1):
        row = ROW.fullmatch(line)
        if not row:
            raise Unreadable(f"the probe's line {number} is not a row (`name <n>` or "
                             f"`deprecated <n>`), as a Lean message is not, so its output "
                             f"cannot be read: `{shorten(line)}`")
        if row["name"] in names:
            raise Unreadable(f"the probe printed `{row['name']}` twice, at line {number}")
        names[row["name"]] = row["marker"]
    return names


def probe(plants: str = "") -> str:
    """The probe's Lean, with `plants` before its `#eval`."""
    return PROBE_HEAD + plants + PROBE_EVAL


def require_current_build() -> None:
    """Refuse a stale build: Unreadable, with the last lines it printed, when BUILD_CHECK,
    run from the repository's root, fails."""
    try:
        done = subprocess.run(list(BUILD_CHECK), cwd=ROOT, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT)
    except OSError as error:
        raise Unreadable(f"lake cannot be run: {error}") from None
    if done.returncode != 0:
        said = done.stdout.decode("utf-8", "replace").strip().splitlines()[-BUILD_LINES:]
        raise Unreadable("\n".join(["the build of Elements is not current (lake build "
                                    "--no-build failed): run `lake build` first", *said]))


def run_lean(text: str) -> str:
    """Run the Lean file `text` as `lake env lean` from the repository's root, from a file
    in a temporary folder outside it, once the build is found current; what it printed.
    Unreadable when the temporary probe cannot be created, resolved, written or removed,
    or when Lean fails, writes to its standard error or prints what is not UTF-8. Another
    script that reads names the same way, as the release notes' generator does (#702),
    should call this and read_probe rather than copy them."""
    if shutil.which("lake") is None:
        raise Unreadable("lake is not on PATH: export PATH=$HOME/.elan/bin:$PATH, and run "
                         "`lake build` first")
    require_current_build()
    try:
        temporary = tempfile.TemporaryDirectory(prefix="released-names-")
    except OSError as error:
        raise Unreadable(f"cannot create a temporary folder for the probe: {error}") from None
    try:
        with temporary as tmp:
            try:
                folder = Path(tmp).resolve()
            except OSError as error:
                raise Unreadable(f"cannot resolve the temporary probe folder: {error}") \
                    from None
            if folder == ROOT or ROOT in folder.parents:
                raise Unreadable(f"the temporary folder {folder} is inside the repository; "
                                 "set TMPDIR to a folder outside it")
            path = folder / "Probe.lean"
            try:
                path.write_text(text, encoding="utf-8")
            except OSError as error:
                raise Unreadable(f"cannot write the temporary probe {path}: {error}") from None
            try:
                done = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                      capture_output=True)
            except OSError as error:
                raise Unreadable(f"lake cannot be run: {error}") from None
    except OSError as error:
        raise Unreadable(f"cannot remove the temporary probe folder: {error}") from None
    try:
        out, err = done.stdout.decode("utf-8"), done.stderr.decode("utf-8")
    except UnicodeDecodeError:
        raise Unreadable("the probe printed what is not UTF-8") from None
    if done.returncode != 0 or err.strip():
        shown = (out + err).strip()[-2000:]
        raise Unreadable(f"Lean could not run the probe (exit {done.returncode}), or wrote to "
                         f"its standard error; is the library built (`lake build`)?\n{shown}")
    return out


def run_probe(text: str) -> dict[str, str]:
    """The rows of the probe `text`, run by run_lean."""
    return read_probe(run_lean(text))


# The variables that point git at another repository, worktree, index, object store or
# configuration: scripts/safe_push.py's REPOSITORY_VARIABLES, git 2.50's list.
GIT_VARIABLES = frozenset({
    "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_COMMON_DIR", "GIT_CONFIG", "GIT_CONFIG_COUNT",
    "GIT_CONFIG_PARAMETERS", "GIT_DIR", "GIT_GRAFT_FILE", "GIT_IMPLICIT_WORK_TREE",
    "GIT_INDEX_FILE", "GIT_INTERNAL_SUPER_PREFIX", "GIT_NO_REPLACE_OBJECTS",
    "GIT_OBJECT_DIRECTORY", "GIT_PREFIX", "GIT_REPLACE_REF_BASE", "GIT_SHALLOW_FILE",
    "GIT_WORK_TREE"})


def git_env() -> dict[str, str]:
    """The environment of the script's git commands: none of GIT_VARIABLES, and
    replacement objects off, so that git reads this repository's own tags and HEAD."""
    env = {key: value for key, value in os.environ.items() if key not in GIT_VARIABLES}
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    return env


def git(*args: str) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(["git", *args], cwd=ROOT, env=git_env(), capture_output=True,
                              text=True, encoding="utf-8", errors="surrogateescape")
    except OSError as error:
        raise Unreadable(f"git cannot be run: {error}") from None


def object_of(revision: str) -> str | None:
    """The object `revision` names in this repository, or None when it names none."""
    done = git("rev-parse", "--verify", "--quiet", revision)
    if done.returncode == 1 and not done.stderr.strip():
        return None
    oid = done.stdout.strip()
    if done.returncode != 0 or not COMMIT.fullmatch(oid):
        raise Unreadable(f"git cannot say what {revision} is: "
                         f"{shorten(done.stderr.strip() or oid)}")
    return oid


def commit_of(revision: str) -> str | None:
    """The commit `revision` names in this repository, or None when it names none."""
    return object_of(f"{revision}^{{commit}}")


def tag_target(tag: str) -> TagTarget | None:
    """The peeled target of the repository's tag `tag`, or None when it holds no such tag."""
    oid = object_of(f"refs/tags/{tag}^{{}}")
    if oid is None:
        return None
    done = git("cat-file", "-t", oid)
    kind = done.stdout.strip()
    if done.returncode != 0 or kind not in {"blob", "commit", "tag", "tree"}:
        raise Unreadable(f"git cannot say what kind of object tag {tag} points to: "
                         f"{shorten(done.stderr.strip() or kind)}")
    return TagTarget(oid, kind)


def head_commit() -> str:
    commit = commit_of("HEAD")
    if commit is None:
        raise Unreadable("git cannot say what HEAD is")
    return commit


# Untracked files that could change what the build declares: a Lean file, Lake's
# configuration (Lake prefers a `lakefile.lean` to `lakefile.toml`, and runs it), its
# manifest and the toolchain, in any case of letters, since a case-insensitive file system
# opens `lakefile.LEAN` as `lakefile.lean`.
BUILD_INPUT = re.compile(r"(.*\.lean|(.*/)?lakefile\.(lean|toml)|(.*/)?lake-manifest\.json"
                         r"|(.*/)?lean-toolchain)", re.DOTALL | re.IGNORECASE)


def hidden_index_paths() -> list[str]:
    flagged: dict[str, list[str]] = {}
    for option, label in (("-v", "assume-unchanged"), ("-t", "skip-worktree")):
        done = git("--no-optional-locks", "ls-files", option, "-z")
        if done.returncode != 0:
            raise Unreadable(f"git cannot say which index flags are set: "
                             f"{shorten(done.stderr.strip())}")
        for record in done.stdout.split("\0"):
            if not record:
                continue
            if len(record) < 3 or record[1] != " ":
                raise Unreadable("git returned an index record that cannot be read")
            marker, path = record[0], record[2:]
            marked = marker.islower() if option == "-v" else marker == "S"
            if marked and path != LIST.as_posix():
                flagged.setdefault(path, []).append(label)
    return [f"{' and '.join(labels)}: {printable(path)}"
            for path, labels in flagged.items()]


def modified() -> list[str]:
    """The files and index flags that bar `--list`: Unreadable when any tracked file but
    the list has assume-unchanged or skip-worktree set, even if it matches HEAD; otherwise,
    each tracked file that differs from HEAD, staged or not, but the list itself, and each
    untracked or ignored BUILD_INPUT."""
    hidden = hidden_index_paths()
    if hidden:
        shown = ", ".join(hidden[:5]) + (", …" if len(hidden) > 5 else "")
        raise Unreadable(f"git index flags hide {len(hidden)} tracked files from status "
                         f"({shown}); clear the flags before --list")
    done = git("--no-optional-locks", "status", "--porcelain=v1", "-z",
               "--untracked-files=all", "--ignored=matching")
    if done.returncode != 0:
        raise Unreadable(f"git cannot say what is modified: {shorten(done.stderr.strip())}")
    found: list[str] = []
    seen: set[str] = set()

    def add(path: str) -> None:
        if path not in seen:
            found.append(printable(path))
            seen.add(path)

    records = done.stdout.split("\0")
    if records[-1] == "":
        records.pop()
    number = 0
    while number < len(records):
        record = records[number]
        number += 1
        if len(record) < 4 or record[2] != " ":
            raise Unreadable("git returned a status record that cannot be read")
        state, path = record[:2], record[3:]
        source = None
        if "R" in state or "C" in state:
            if number == len(records):
                raise Unreadable("git returned a rename status without its source path")
            source = records[number]
            number += 1
        if state in ("??", "!!"):
            if BUILD_INPUT.fullmatch(path):
                add(path)
        elif path != LIST.as_posix() or source is not None and source != LIST.as_posix():
            add(f"{source} -> {path}" if source is not None else path)

    ignored = git("--no-optional-locks", "ls-files", "--others", "--ignored",
                  "--exclude-standard", "-z", "--", ":(icase)*.lean",
                  ":(icase)lakefile.*", ":(glob,icase)**/lakefile.*",
                  ":(icase)lake-manifest.json", ":(glob,icase)**/lake-manifest.json",
                  ":(icase)lean-toolchain", ":(glob,icase)**/lean-toolchain")
    if ignored.returncode != 0:
        raise Unreadable(f"git cannot say what ignored build inputs exist: "
                         f"{shorten(ignored.stderr.strip())}")
    for path in ignored.stdout.split("\0"):
        if path and BUILD_INPUT.fullmatch(path):
            add(path)
    return found


def later_tags(listed: Listed) -> list[str]:
    """The repository's tags, but the list's own, whose history holds the list's commit,
    sorted; none when the repository does not hold that commit."""
    if commit_of(listed.commit) is None:
        return []
    done = git("tag", "--contains", listed.commit)
    if done.returncode != 0:
        raise Unreadable(f"git cannot list the tags after {listed.tag}: "
                         f"{shorten(done.stderr.strip())}")
    return sorted(tag for tag in done.stdout.split() if tag != listed.tag)


def finding(name: str, tag: str) -> str:
    return f"{name}: released in {tag}, missing on main with no deprecated alias ({RULE})"


def missing(listed: Listed, main: dict[str, str]) -> list[str]:
    """The rule: a finding for each name the list holds plain that main does not declare,
    in the list's order. A name the tag marked deprecated, and a name new on main, pass."""
    return [finding(name, listed.tag) for name, marker in listed.names.items()
            if marker == "name" and name not in main]


def tag_lines(listed: Listed, local: str | None, error: str | None = None,
              later: list[str] = ()) -> tuple[list[str], list[str]]:
    """The findings and the notes the list's tag gives, where `local` is the commit the
    repository's tag points to (None when it holds no such tag), `error` why git cannot
    say, and `later` the tags after it: a finding when the tag points elsewhere; a note
    when it is absent or unknown; and a note naming the later tags."""
    shown = f"{LIST}:{listed.tag_line}"
    found: list[str] = []
    notes: list[str] = []
    if error is not None:
        notes.append(f"{shown}: where tag {listed.tag} points cannot be read here ({error}), "
                     "so the list's commit is not compared with it")
    elif local is None:
        notes.append(f"{shown}: this repository holds no tag {listed.tag} (a checkout may "
                     "fetch no tags), so the list's commit is not compared with it")
    elif local != listed.commit:
        found.append(f"{shown}: the list gives {listed.tag} as {listed.commit}, but the tag in "
                     f"this repository points to {local}, so the list is not the tag's; make "
                     f"it with --list {listed.tag}")
    if later:
        notes.append(f"{shown}: tag {', '.join(later)} came after {listed.tag}, so the list "
                     "may be out of date; once a release is tagged, make the list with "
                     "--list <its tag> and commit it")
    return found, notes


def report(listed: Listed, main: dict[str, str], local: str | None,
           error: str | None = None, later: list[str] = ()) -> tuple[list[str], int]:
    """The lines the check prints, and its exit code, for the list and main's names."""
    found, notes = tag_lines(listed, local, error, later)
    gone = missing(listed, main)
    released = len(listed.names)
    present = sum(name in main for name in listed.names)
    deprecated = sum(main.get(name) == "deprecated" for name in listed.names)
    retired = released - present - len(gone)
    counts = (f"{released} names released in {listed.tag}: {present} present on main, "
              f"{deprecated} of them deprecated there; {len(gone)} missing with no "
              "deprecated alias")
    if retired:
        counts += f"; {retired} gone after the release that deprecated them"
    if gone or found:
        tail = "; and the list is not the tag's" if found else ""
        return notes + gone + found + [f"✗ {LIST}: {counts}{tail}"], 1
    return notes + [f"✓ {LIST}: {counts}"], 0


def full_name(name: str) -> str:
    """A name of PLANT_CASES in full: a short one is in the planted namespace."""
    return name if name.startswith("Elements.") else f"{PLANT_NAMESPACE}.{name}"


def self_test(rows: dict[str, str]) -> list[str]:
    """The surprises in the plants' output `rows`: a row that is not a name of `Elements`
    (one of Lean's own, or the private plant under its private name), a plant read
    otherwise than planted, the real declaration not read plain, and a planted list not
    judged as expected."""
    problems = []
    outside = sorted(name for name in rows if not name.startswith("Elements."))
    if outside:
        shown = ", ".join(f"`{shorten(name)}`" for name in outside[:3])
        more = f" and {len(outside) - 3} more" if len(outside) > 3 else ""
        names = "1 name" if len(outside) == 1 else f"{len(outside)} names"
        problems.append(f"the probe printed {names} outside `Elements`: {shown}{more}")
    prefix = f"{PLANT_NAMESPACE}."
    got = {name: marker for name, marker in rows.items() if name.startswith(prefix)}
    # A plant that must give no row is not among `want`: read at all, it is among `got`.
    want = {full_name(name): marker for name, marker in PLANTED.items() if marker}
    for name in sorted(got.keys() | want.keys()):
        if got.get(name) != want.get(name):
            problems.append(f"the probe read `{name}` as {SHOWN[got.get(name)]}, where it "
                            f"must be {SHOWN[want.get(name)]}")
    if rows.get(REAL) != "name":
        problems.append(f"the probe read `{REAL}` as {SHOWN[rows.get(REAL)]}, where it must "
                        "be plain")
    for what, released, failing in PLANT_CASES:
        listed = Listed("plant", "0" * 40, 1,
                        {full_name(name): marker for name, marker in released.items()})
        if what.startswith("a list that names nothing new"):
            new = [full_name(name) for name in ("New.a", "New.b")]
            if any(name not in rows or name in listed.names for name in new):
                problems.append(f"{what}: `New.a` and `New.b` must be on main and not "
                                "in the list")
        found = missing(listed, rows)
        expected = [finding(full_name(name), "plant") for name in failing]
        if found != expected:
            problems.append(f"{what}: expected {expected or 'no finding'}, found "
                            f"{found or 'no finding'}")
    return problems


def check_with(listed: Listed, rows: dict[str, str]) -> int:
    """Print the check's lines for the list and main's names; its exit code."""
    try:
        target = tag_target(listed.tag)
        local, error = target.oid if target is not None else None, None
    except Unreadable as e:
        local, error = None, str(e)
    try:
        later = later_tags(listed)
    except Unreadable:
        later = []
    lines, code = report(listed, rows, local, error, later)
    for line in lines:
        print(line)
    return code


def run_check() -> int:
    listed = parse_list(read(LIST_FILE), display(LIST_FILE))
    return check_with(listed, run_probe(probe()))


def run_self_test() -> int:
    # The list is read first, so that a malformed one stops the run before Lean.
    listed = parse_list(read(LIST_FILE), display(LIST_FILE))
    rows = run_probe(probe(PLANTS))
    problems = self_test(rows)
    for problem in problems:
        print(f"self-test: {problem}")
    if problems:
        surprises = "1 surprise" if len(problems) == 1 else f"{len(problems)} surprises"
        print(f"✗ self-test: {surprises}; the check is not run")
        return 1
    absent = sum(marker is None for marker in PLANTED.values())
    print(f"✓ self-test: the probe read the {len(PLANTED)} plants as planted, {absent} of them "
          f"absent (the private one, two parsers and nine names of a structure), no name "
          f"outside Elements, and {REAL} plain, and the "
          f"{len(PLANT_CASES)} planted lists were judged as expected")
    prefix = f"{PLANT_NAMESPACE}."
    return check_with(listed, {name: marker for name, marker in rows.items()
                               if not name.startswith(prefix)})


def make_list(tag: str) -> str:
    """The list file for `tag`, from the built checkout of the tag's commit; Unreadable
    when the tag's name is invalid, the tag is not in the repository, HEAD is another
    commit, any tracked file but the list has assume-unchanged or skip-worktree set, a file
    that could change the build differs from it (modified()), or the build is not current."""
    if not is_tag_name(tag):
        raise Unreadable(f"--list: `{shorten(tag)}` is not a tag's name")
    target = tag_target(tag)
    if target is None:
        raise Unreadable(f"--list {tag}: this repository holds no tag {tag}")
    if target.kind != "commit":
        raise Unreadable(f"--list {tag}: tag {tag} points to a {target.kind}, not a commit")
    commit = target.oid
    head = head_commit()
    if head != commit:
        raise Unreadable(f"--list {tag}: HEAD is {head}, not the tag's commit {commit}; check "
                         f"out the tag (git checkout --detach {tag}) and run `lake build` "
                         "first")
    changed = modified()
    if changed:
        shown = ", ".join(changed[:5]) + (", …" if len(changed) > 5 else "")
        raise Unreadable(f"--list {tag}: {len(changed)} files differ from the tag's commit "
                         f"({shown}); the list is made from the tag's commit as it stands")
    text = render_list(tag, commit, run_probe(probe()))
    parse_list(text, f"the list made at {tag}")
    return text


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--self-test", action="store_true",
                      help="planted cases first, then the check")
    mode.add_argument("--list", metavar="TAG",
                      help="print the list, in a built checkout of TAG's commit")
    args = parser.parse_args(argv)
    try:
        if args.list is not None:
            text = make_list(args.list)
            out = getattr(sys.stdout, "buffer", None)
            if out is None:
                sys.stdout.write(text)
            else:
                sys.stdout.flush()
                out.write(text.encode("utf-8"))
                out.flush()
            return 0
        return run_self_test() if args.self_test else run_check()
    except Unreadable as error:
        print(f"check_released_names: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
