#!/usr/bin/env python3
"""A change's risk class, determined from the files it changes, never declared. On 22
October 2026 the owner asked that every train's risk be tagged up front and clearly
determined.

One ordered table, RULES: each path takes the class of the first rule that matches it,
and a change takes the highest class among its paths. A path no rule matches takes R5, the
highest, so a new kind of file is never waved through a lighter lane. This file is the one
source of the classes (docs/decisions/2026-10-22-risk-lanes.md). CI's `risk` job runs
main's copy of it, never the change's own, and the jobs it gates read what that copy
writes to $GITHUB_OUTPUT (docs/WORKFLOW.md, section 8); a pull request that edits this file
is R5 by the table below.

The formal model in model/ imports some of the main package's Lean files, and so is
checked whenever one of them changes, whatever the change's class: model_inputs finds them
at a revision, from the model's own import lines, so the set follows the imports as they
change. It reads a header by a narrow grammar and fails closed: while a file among the
model's imports has a header it cannot read cleanly, or imports a module for which the
tree holds no file at the usual path unless its root is explicitly external, the formal
model is checked for every change. Thus a header Lean reads otherwise, or a main-package
source layout this narrow reader does not know, can only widen the set; and so it is while
the tree holds a .gitattributes anywhere, which can make the text Lean reads from the
checkout differ from the text Git holds, which this reads.

    python3 scripts/risk.py <worktree> [base]     the class of the worktree's HEAD against
                                                  base (origin/main), then each path's,
                                                  then whether the formal model must run
    python3 scripts/risk.py --diff BASE HEAD      the same for `git diff BASE...HEAD` in
                                                  the current repository; with
                                                  --github-output, also class=Rn and
                                                  formal_model=true|false appended to
                                                  $GITHUB_OUTPUT
    python3 scripts/risk.py --paths <file>...     the class of each path given (for cards,
                                                  up front)
    python3 scripts/risk.py --audit <worktree>    every tracked file's class; exit 1 if any
                                                  falls to the R5 default without a rule
    python3 scripts/risk.py --model-inputs REV    the main package's files the formal model
                                                  imports at REV, directly or through others,
                                                  then each file among them whose header or
                                                  imports it cannot read or resolve, and why

A rule matches a path whole, by fnmatch's rules, under which `*` matches `/` too, so
`scripts/*` holds `scripts/audit/jev.py`. Git gives the paths separated by NUL bytes
(`-z`), so a path with a space or a line break in it is one path; without rename
detection, so a file moved counts at the path it leaves as well as the path it takes; and
with every submodule's change shown, whatever .gitmodules says. A path is printed with each
character Python counts unprintable, a line break among them, written as an escape, so no
path can start a line of CI's log, as a workflow command would. An empty diff is R0. A Git
failure, or arguments that do not parse, exits 2 and prints no class. Standard library
only; tests/test_risk.py tests it.
"""

from __future__ import annotations

import fnmatch
import os
import posixpath
import re
import subprocess
import sys

CLASSES = {
    "R0": "Docs",
    "R1": "Text and records",
    "R2": "Proofs",
    "R3": "Checks",
    "R4": "Foundations",
    "R5": "Landing tool and CI",
}

# Ordered: the first match wins. Highest-risk rules first, so a specific file is never caught
# by a broader, lighter rule. scripts/risk.py is R5 because it decides which checks run.
# So are scripts/registry.py, whose copy at main decides the pre-flight's sequence of
# checks, and scripts/run_checks.py, which is CI's `check` job; the registry they read,
# checks/, is R3, so that adding a check stays a change to the checks (#229).
# scripts/shadow_policy.py is R5 too: it runs main's pre-flight in CI and gives its verdict
# (#574).
# lakefile.lean is R4 with the other build files, not R2 by `*.lean`: the repository has
# none, but Lake reads one in preference to lakefile.toml. scripts/check_model_kernel.py is
# R4, not R3 by `scripts/*`, because CI's formal-model job, which runs it, runs for R4 and R5.
RULES = [
    ("R5", ["scripts/safe_push.py", "scripts/test_safe_push.py", "scripts/git-safe-push*",
            "scripts/hooks/*", ".githooks/*", ".github/*", "tests/test_safe_push*",
            "scripts/risk.py", "scripts/registry.py", "scripts/run_checks.py",
            "scripts/shadow_policy.py"]),
    ("R4", ["Elements/Foundations/*", "Elements/Foundations.lean", "Certificate/axioms.lock",
            "model/*", "tests/model/*", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
            "Elements/Companions.lean", "lakefile.lean", "scripts/check_model_kernel.py"]),
    ("R3", ["scripts/*", "tests/*", "review/SCHEMA.md", "review/terms.toml", "Certificate/*",
            "docs/WORKFLOW.md", "Audit/screen.py",
            # The registry of checks, one file per check of CI's `check` job (#229): adding
            # or changing a check is a change to the checks, whatever else it touches.
            "checks/*",
            # ACCEPTANCE's table of the limitations allowed, which tests/test_acceptance_limits.py
            # ties to check_acceptance.py's ALLOWED_LIMITS: a check input (#249).
            "docs/ACCEPTANCE.md",
            # A rule of these can hide a file from the whole-worktree cleanliness check, or
            # change how Git reads one, so they are checks, not docs.
            ".gitignore", "*/.gitignore", ".gitattributes", "*/.gitattributes"]),
    ("R2", ["Elements/*", "Staging/*", "Audit/*", "Elements.lean", "Staging.lean", "Audit.lean",
            "*.lean"]),
    ("R1", ["heath/*", "mishnah/*", "review/*", "figures/*", "book/*", "facts.json",
            "CERTIFICATE.md", "GRAPH.md", "docs/reports/*", "docs/decisions/*", "docs/briefs/*",
            "docs/STYLE.md", "docs/FORMALIZATION.md", "docs/program.toml",
            "docs/PROGRAM.md", "reading/*"]),
    ("R0", ["docs/*", "README.md", "CONTRIBUTING.md", "AGENTS.md", "CLAUDE.md", "NOTICE",
            "CITATION.cff", "LICENSE*", "assets/*"]),
]

# The formal model's own inputs, which make its job run whatever the class (both are R4
# by the table in any case).
MODEL = "model/"
LOCK = "Certificate/axioms.lock"
EXTERNAL_ROOTS = ("Check", "Model", "Mathlib", "Lean", "Init", "Std")

USAGE = ("usage: risk.py <worktree> [base] | --diff BASE HEAD [--github-output] | "
         "--paths <file>... | --audit <worktree> | --model-inputs REV")


class GitFailure(Exception):
    """Git could not list the paths: no class may be printed."""


class Unread(Exception):
    """A Lean header or import the reader cannot read or resolve cleanly, and why: while a
    file among the formal model's imports has one, the model is checked for every change."""


def shown(text: str) -> str:
    """Text Git gave, a path say, as this script prints it: every character Python counts
    unprintable, a control character or a line break among them, written as an escape, as
    safe_push's printable_text writes a path."""
    return "".join(c if c.isprintable() else c.encode("unicode_escape").decode("ascii")
                   for c in text)


def classify(path: str) -> tuple[str, bool]:
    """The class of one path, and whether a rule named it (False: R5 by default)."""
    for cls, patterns in RULES:
        if any(fnmatch.fnmatchcase(path, pattern) for pattern in patterns):
            return cls, True
    return "R5", False


def change_class(paths) -> tuple[str, dict[str, tuple[str, bool]]]:
    """The highest class among the paths (R0 for none), and each path's."""
    per = {path: classify(path) for path in paths}
    return max((cls for cls, _ in per.values()), default="R0"), per


def git_bytes(args: list[str], cwd: str | None = None, data: bytes | None = None) -> bytes:
    """What a Git command prints, or GitFailure."""
    try:
        done = subprocess.run(["git", *args], cwd=cwd, input=data, capture_output=True)
    except OSError as error:
        raise GitFailure(f"git could not be run: {error}") from None
    if done.returncode != 0:
        message = done.stderr.decode(errors="replace").strip()
        raise GitFailure(f"git {' '.join(args)} exited {done.returncode}: {message}")
    return done.stdout


def git_paths(args: list[str], cwd: str | None = None) -> list[str]:
    """The NUL-separated paths a Git command prints, or GitFailure."""
    return [os.fsdecode(path) for path in git_bytes(args, cwd).split(b"\0") if path]


def revision(rev: str) -> str:
    """A revision given to Git, never one it could read as an option."""
    if not rev or rev.startswith("-"):
        raise GitFailure(f"not a revision: {rev!r}")
    return rev


def diff_paths(base: str, head: str, cwd: str | None = None) -> list[str]:
    """The paths `git diff base...head` changes: each side of a move, every submodule's
    change, and none relative."""
    return git_paths(["diff", "--name-only", "-z", "--no-renames", "--no-relative",
                      "--no-ext-diff", "--ignore-submodules=none",
                      f"{revision(base)}...{revision(head)}", "--"], cwd)


# A Lean file's header, read by a narrow grammar that fails closed rather than try to match
# Lean 4.35's, which reads more: a module part `«.»`, `«..»` or `«»`, and letters and
# symbols past ASCII. The reader knows `module`, `prelude`, the modifiers `public`,
# `private` and `meta`, and imports, each `import`, after an optional `all`, taking one
# module, several to a line if need be (`import A import B`); and between them spaces,
# tabs and line breaks, and comments as Lean reads them (comment_end, below): `--` to the
# line's end, and `/-` to its matching `-/`, nested, its body beginning past its third
# character, so that `/-/- -/` is one comment. A module's parts are plain, an ASCII
# letter or `_` then ASCII letters, digits and `_'!?`, or quoted, of ASCII letters, digits
# and `_'!?-`
# (`«areas-p5»`), joined by dots. The header ends at the first other word, or the first
# other ASCII character, where Lean's ends too: an `import` later in a file, in a string
# say, is no import. Anything else before the header ends is Unread: an `import` with no
# module after it; a word of the header that runs into anything but white space, a
# comment or the file's end (`Q.X℀`, or `Q.«.».A`); and any other character past ASCII,
# any other guillemet among them. Where the reader passes over what Lean refuses, or reads
# on where Lean's header ends, it can only widen the set: a tab, a lone carriage return, a
# doc comment, and `private import`, read as an import.
SPACE = " \t\r\n"
PART = r"(?:[A-Za-z_][A-Za-z0-9_'!?]*|«[A-Za-z0-9_'!?-]+»)"
NAME = re.compile(rf"{PART}(?:\.{PART})*")
HEADER_WORDS = ("module", "prelude", "public", "private", "meta", "import")
MODULE = re.compile(r"(?:«[^»]*»|[^.«»]+)(?:\.(?:«[^»]*»|[^.«»]+))*")
MODULE_PART = re.compile(r"«([^»]*)»|([^.«»]+)")


def named(char: str) -> str:
    """A character as a reason names it: '.' say, or U+2100."""
    return repr(char) if char.isascii() and char.isprintable() else f"U+{ord(char):04X}"


# The scripts' one reader of where a Lean comment ends is heath.py's `comment_end` (#206,
# #349). This file is run alone, from a temporary directory with -I, and can import
# nothing of the repository's, so it holds a copy of that one function, word for word;
# tests/test_risk.py holds the copy to heath's, by its source and by what it reads (the
# coordinator's ruling of 22 October 23:50).
def comment_end(src: str, i: int) -> int | None:
    """Where the comment that begins at `i`, with `--` or `/-`, ends, as Lean 4.35 reads
    it (`whitespace` and `finishCommentBlock` in Lean/Parser/Basic.lean): a `--` comment
    at the line feed that ends its line, or the end of `src`; a `/- … -/` block,
    docstrings and nested blocks among them, just past the `-/` that closes it, or None
    if none does. A block's body begins at its fourth character, after `/--` or `/-!`,
    and past the third of any other `/-`, which Lean passes over, so that `/-/- -/` is a
    whole comment and the `-/` of `/--/` closes nothing. `_read_code`, and so
    `read_lean` and `lean_comments`, and check_style's notes call this (#206). It uses
    nothing else of this file, so that a program that cannot import it holds a copy, word
    for word, which its tests hold to this one: the Jev generator, and risk.py from
    #349's second train."""
    if src.startswith("--", i):
        end = src.find("\n", i)
        return len(src) if end < 0 else end
    j, nested = i + 3, 1
    while j < len(src):
        pair = src[j:j + 2]
        nested += (pair == "/-") - (pair == "-/")
        j += 2 if pair in ("/-", "-/") else 1
        if not nested:
            return j
    return None


def past_space(text: str, pos: int) -> int:
    """Where the white space and comments that start at pos end: each comment as Lean
    reads it (comment_end), so that the `-/` of `/-/- -/` closes it, as Lean has it, and
    an import after it is read. A block no `-/` closes runs to the end of the text."""
    while pos < len(text):
        if text[pos] in SPACE:
            pos += 1
        elif text.startswith(("--", "/-"), pos):
            end = comment_end(text, pos)
            pos = len(text) if end is None else end
        else:
            break
    return pos


def imported_modules(text: str) -> list[str]:
    """The modules a Lean file's header imports, in order, as the file names them; Unread
    when the reader cannot read the header cleanly."""
    modules: list[str] = []
    pos, importing, whole = 0, False, False
    while True:
        pos = past_space(text, pos)
        match = NAME.match(text, pos)
        if not match:
            if importing:
                where = named(text[pos]) if pos < len(text) else "the file's end"
                raise Unread(f"an import with no module after it, at {where}")
            if pos < len(text) and not text[pos].isascii():
                raise Unread(f"{named(text[pos])} in the header")
            return modules
        word = match.group()
        if not importing and word not in HEADER_WORDS:
            return modules
        pos = match.end()
        if pos < len(text) and not (text[pos] in SPACE or text.startswith(("--", "/-"), pos)):
            raise Unread(f"{word} runs into {named(text[pos])}")
        if not importing:
            importing = word == "import"
        elif word == "all" and not whole:
            whole = True
        elif word in HEADER_WORDS or word == "all":
            raise Unread(f"an import with no module after it, at {word}")
        else:
            modules.append(word)
            importing, whole = False, False


def module_path(module: str) -> str:
    """The file in which Lake finds a module under its package's root: A.B.C at A/B/C.lean,
    and «areas-p5» at areas-p5.lean, normalised. Unread for a module with a part that is
    empty, `.` or `..`, or whose file would lie outside the tree."""
    if not MODULE.fullmatch(module):
        raise Unread(f"{module} is no module name")
    parts = [quoted or plain for quoted, plain in MODULE_PART.findall(module)]
    if any(part in ("", ".", "..") for part in parts):
        raise Unread(f"{module} has a part that is empty, . or ..")
    path = posixpath.normpath("/".join(parts) + ".lean")
    if path.startswith("/") or path == ".." or path.startswith("../"):
        raise Unread(f"{module} names a file outside the tree")
    return path


def tree_files(rev: str, cwd: str | None = None) -> dict[str, bytes]:
    """Every regular file Git holds at rev, by its path, with its object's name. A symbolic
    link is passed over: check_fidelity.py's source scan refuses any under Elements/,
    Staging/, Audit/ or model/ in CI's check job."""
    files = {}
    listing = git_bytes(["ls-tree", "-r", "-z", "--full-tree", revision(rev)], cwd)
    for record in listing.split(b"\0"):
        if not record:
            continue
        meta, _, path = record.partition(b"\t")
        mode, kind, name = meta.split(b" ")
        if kind == b"blob" and mode in (b"100644", b"100755"):
            files[os.fsdecode(path)] = name
    return files


def file_texts(names: list[bytes], cwd: str | None = None) -> list[str]:
    """The contents of Git's objects, by their names, read in one `git cat-file --batch`."""
    if not names:
        return []
    out = git_bytes(["cat-file", "--batch"], cwd, b"".join(name + b"\n" for name in names))
    texts, pos = [], 0
    for name in names:
        end = out.find(b"\n", pos)
        header = out[pos:end].split() if end >= 0 else []
        if (len(header) != 3 or header[0] != name or header[1] != b"blob"
                or not header[2].isdigit()):
            raise GitFailure(f"git cat-file could not read {name.decode()}")
        start = end + 1
        size = int(header[2])
        texts.append(out[start:start + size].decode("utf-8", errors="replace"))
        pos = start + size + 1
    return texts


def model_inputs(rev: str, cwd: str | None = None) -> tuple[set[str], dict[str, str]]:
    """The main package's Lean files the formal model imports at rev, directly or through
    one another: the modules each model/**/*.lean file's header imports whose file the main
    package holds at rev (module A.B.C at A/B/C.lean), then the same for each such file, to
    the end. An unresolved import is unread unless its root is Check, Model, Mathlib, Lean,
    Init or Std. Then each file read on the way, the model's own among them, whose header
    or imports the reader cannot read cleanly, with why: what it imports is unknown. A
    .gitattributes anywhere in the tree counts as unread too: the reader reads the text Git
    holds, Lean the text Git checks out, and an encoding or filter there makes the two
    differ (a `-/` that only the checkout holds can end a comment the blob leaves open)."""
    files = tree_files(rev, cwd)
    main = {path for path in files if not path.startswith(MODEL)}
    unread: dict[str, str] = {
        path: ("a .gitattributes can make the text Lean reads differ from the text Git "
               "holds, which the reader reads")
        for path in files if path.rsplit("/", 1)[-1] == ".gitattributes"}
    queue = sorted(path for path in files
                   if path.startswith(MODEL) and path.endswith(".lean"))
    found: set[str] = set()
    while queue:
        imported: set[str] = set()
        for path, text in zip(queue, file_texts([files[path] for path in queue], cwd)):
            try:
                modules = imported_modules(text)
            except Unread as why:
                unread[path] = str(why)
                continue
            for module in modules:
                try:
                    candidate = module_path(module)
                except Unread as why:
                    unread.setdefault(path, str(why))
                    continue
                if candidate in main:
                    imported.add(candidate)
                elif not any(module == root or module.startswith(root + ".")
                             for root in EXTERNAL_ROOTS):
                    unread.setdefault(path, f"{module} has no {candidate} in the tree")
        queue = sorted(imported - found)
        found.update(queue)
    return found, unread


def formal_model(top: str, paths, base: str, head: str,
                 cwd: str | None = None) -> tuple[bool, str]:
    """Whether CI's formal-model job must run in full for the change `git diff base...head`,
    and why: for R4 and R5, for a change under model/ or to the axiom lock, for every
    change while a file the model imports, at the diff's end or at its start, has a header
    or import the reader cannot read or resolve cleanly, and for a change to a file the
    model imports, at either end (at the start, a file the change deletes is still
    imported)."""
    if top >= "R4":
        return True, f"the class is {top}"
    for path in sorted(paths):
        if path.startswith(MODEL) or path == LOCK:
            return True, f"{shown(path)} changed"
    starts = git_bytes(["merge-base", "--all", revision(base), revision(head)], cwd)
    inputs, unread = model_inputs(head, cwd)
    for start in starts.decode().split():
        more_inputs, more_unread = model_inputs(start, cwd)
        inputs |= more_inputs
        unread = {**more_unread, **unread}
    if unread:
        first = sorted(unread)[0]
        files = (f"{shown(first)} and {len(unread) - 1} more of the formal model's imports "
                 "have headers" if len(unread) > 1
                 else f"{shown(first)}, in the formal model's imports, has a header")
        return True, (f"{files} the classifier cannot read ({shown(first)}: "
                      f"{shown(unread[first])}), so every change checks the model")
    imported = sorted(set(paths) & inputs)
    if imported:
        more = f", and {len(imported) - 1} more it imports" if len(imported) > 1 else ""
        return True, f"the formal model imports {shown(imported[0])}{more}"
    return False, ("the change touches nothing under model/, nor the axiom lock, nor a file "
                   "the formal model imports")


def show_change(top: str, per: dict[str, tuple[str, bool]],
                model: tuple[bool, str] | None = None) -> None:
    print(f"{top} {CLASSES[top]}")
    if not per:
        print("  (no file changed)")
    for path, (cls, ruled) in sorted(per.items(), key=lambda item: (item[1][0], item[0]),
                                     reverse=True):
        print(f"  {cls} {shown(path)}" + ("" if ruled else "  (no rule)"))
    if model is not None:
        full, why = model
        print(f"formal model: {'in full' if full else 'passes at once'}, since {why}")


def audit(worktree: str) -> int:
    counts: dict[str, int] = {}
    unruled = []
    for path in git_paths(["ls-files", "-z"], worktree):
        cls, ruled = classify(path)
        counts[cls] = counts.get(cls, 0) + 1
        if not ruled:
            unruled.append(path)
    for cls in sorted(counts):
        print(f"{cls} {CLASSES[cls]:<20} {counts[cls]} files")
    for path in unruled[:40]:
        print(f"  unruled (R5 by default): {shown(path)}")
    if len(unruled) > 40:
        print(f"  and {len(unruled) - 40} more")
    return 1 if unruled else 0


def judged(base: str, head: str, cwd: str | None = None):
    """The class of `git diff base...head`, each path's, and the formal model's lane."""
    paths = diff_paths(base, head, cwd)
    top, per = change_class(paths)
    return top, per, formal_model(top, paths, base, head, cwd)


def main(argv: list[str]) -> int:
    # A path Git gives that is not UTF-8 is printed with escapes, never as an error.
    reconfigure = getattr(sys.stdout, "reconfigure", None)
    if reconfigure is not None:
        reconfigure(errors="backslashreplace")
    args = list(argv)
    if not args:
        print(USAGE, file=sys.stderr)
        return 2
    if args[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    try:
        mode, rest = args[0], args[1:]
        if mode == "--paths":
            if not rest:
                print(USAGE, file=sys.stderr)
                return 2
            for path in rest:
                cls, ruled = classify(path)
                print(f"{cls} {shown(path)}" + ("" if ruled else "  (no rule: R5 by default)"))
            return 0
        if mode == "--audit":
            if len(rest) != 1:
                print(USAGE, file=sys.stderr)
                return 2
            return audit(rest[0])
        if mode == "--model-inputs":
            if len(rest) != 1:
                print(USAGE, file=sys.stderr)
                return 2
            inputs, unread = model_inputs(rest[0])
            for path in sorted(inputs):
                print(shown(path))
            for path in sorted(unread):
                print(f"unread: {shown(path)}: {shown(unread[path])}; while it is, every "
                      "change checks the formal model")
            return 0
        if mode == "--diff":
            github = "--github-output" in rest
            revs = [arg for arg in rest if arg != "--github-output"]
            if len(revs) != 2 or rest.count("--github-output") > 1:
                print(USAGE, file=sys.stderr)
                return 2
            output = os.environ.get("GITHUB_OUTPUT", "")
            if github and not output:
                print("--github-output: GITHUB_OUTPUT is not set", file=sys.stderr)
                return 2
            top, per, model = judged(*revs)
            if github:
                with open(output, "a", encoding="utf-8") as out:
                    out.write(f"class={top}\nformal_model={'true' if model[0] else 'false'}\n")
            show_change(top, per, model)
            return 0
        if mode.startswith("-") or len(args) > 2:
            print(USAGE, file=sys.stderr)
            return 2
        base = args[1] if len(args) > 1 else "origin/main"
        show_change(*judged(base, "HEAD", args[0]))
        return 0
    except GitFailure as error:
        print(f"risk.py: {shown(str(error))}; no class", file=sys.stderr)
        return 2
    except OSError as error:
        print(f"risk.py: {shown(str(error))}; no class", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
