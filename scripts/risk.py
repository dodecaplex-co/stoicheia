#!/usr/bin/env python3
"""A change's risk class, determined from the files it changes, never declared.

The owner, 22 October 2026: "we need to tag that risk up front. But clearly determine the
risk." One ordered table, RULES: each path takes the class of the first rule that matches
it, and a change takes the highest class among its paths. A path no rule matches takes R5,
the highest, so a new kind of file is never waved through a lighter lane. This file is the
one source of the classes: CI's `risk` job runs main's copy of it on each pull request, and
the jobs it gates read the class it prints (docs/WORKFLOW.md, section 8), so a pull request
that edits this file is judged by the copy it edits, and is R5 by the table below.

    python3 scripts/risk.py <worktree> [base]     the class of the worktree's HEAD against
                                                  base (origin/main), then each path's
    python3 scripts/risk.py --diff BASE HEAD      the class of `git diff BASE...HEAD` in the
                                                  current repository, on the first line,
                                                  then each path's; with --github-output,
                                                  also class=Rn appended to $GITHUB_OUTPUT
    python3 scripts/risk.py --paths <file>...     the class of each path given (for cards,
                                                  up front)
    python3 scripts/risk.py --audit <worktree>    every tracked file's class; exit 1 if any
                                                  falls to the R5 default without a rule

A rule matches a path whole, by fnmatch's rules, under which `*` matches `/` too, so
`scripts/*` holds `scripts/audit/jev.py`. Git gives the paths separated by NUL bytes
(`-z`), so a path with a space or a line break in it is one path, and without rename
detection, so a file moved counts at the path it leaves as well as the path it takes. An
empty diff is R0. A Git failure, or arguments that do not parse, exits 2 and prints no
class. Standard library only; tests/test_risk.py tests it.
"""

from __future__ import annotations

import fnmatch
import os
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
# lakefile.lean is R4 with the other build files, not R2 by `*.lean`: the repository has
# none, but Lake reads one in preference to lakefile.toml. scripts/check_model_kernel.py is
# R4, not R3 by `scripts/*`, because CI's formal-model job, which runs it, runs for R4 and R5.
RULES = [
    ("R5", ["scripts/safe_push.py", "scripts/test_safe_push.py", "scripts/git-safe-push*",
            "scripts/hooks/*", ".githooks/*", ".github/*", "tests/test_safe_push*",
            "scripts/risk.py"]),
    ("R4", ["Elements/Foundations/*", "Elements/Foundations.lean", "Certificate/axioms.lock",
            "model/*", "tests/model/*", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
            "Elements/Companions.lean", "lakefile.lean", "scripts/check_model_kernel.py"]),
    ("R3", ["scripts/*", "tests/*", "review/SCHEMA.md", "review/terms.toml", "Certificate/*",
            "docs/WORKFLOW.md", "Audit/screen.py",
            # A rule of these can hide a file from the whole-worktree cleanliness check, or
            # change how Git reads one, so they are checks, not docs.
            ".gitignore", "*/.gitignore", ".gitattributes", "*/.gitattributes"]),
    ("R2", ["Elements/*", "Staging/*", "Audit/*", "Elements.lean", "Staging.lean", "Audit.lean",
            "*.lean"]),
    ("R1", ["heath/*", "mishnah/*", "review/*", "figures/*", "book/*", "facts.json",
            "CERTIFICATE.md", "GRAPH.md", "docs/reports/*", "docs/decisions/*", "docs/briefs/*",
            "docs/ACCEPTANCE.md", "docs/STYLE.md", "docs/FORMALIZATION.md", "docs/program.toml",
            "docs/PROGRAM.md", "reading/*"]),
    ("R0", ["docs/*", "README.md", "CONTRIBUTING.md", "AGENTS.md", "CLAUDE.md", "NOTICE",
            "CITATION.cff", "LICENSE*", "assets/*"]),
]

USAGE = ("usage: risk.py <worktree> [base] | --diff BASE HEAD [--github-output] | "
         "--paths <file>... | --audit <worktree>")


class GitFailure(Exception):
    """Git could not list the paths: no class may be printed."""


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


def git_paths(args: list[str], cwd: str | None = None) -> list[str]:
    """The NUL-separated paths a Git command prints, or GitFailure."""
    try:
        done = subprocess.run(["git", *args], cwd=cwd, capture_output=True)
    except OSError as error:
        raise GitFailure(f"git could not be run: {error}") from None
    if done.returncode != 0:
        message = done.stderr.decode(errors="replace").strip()
        raise GitFailure(f"git {' '.join(args)} exited {done.returncode}: {message}")
    return [os.fsdecode(path) for path in done.stdout.split(b"\0") if path]


def diff_paths(base: str, head: str, cwd: str | None = None) -> list[str]:
    """The paths `git diff base...head` changes: each side of a move, and none relative."""
    for rev in (base, head):
        if not rev or rev.startswith("-"):
            raise GitFailure(f"not a revision: {rev!r}")
    return git_paths(["diff", "--name-only", "-z", "--no-renames", "--no-relative",
                      "--no-ext-diff", f"{base}...{head}", "--"], cwd)


def show_change(top: str, per: dict[str, tuple[str, bool]]) -> None:
    print(f"{top} {CLASSES[top]}")
    if not per:
        print("  (no file changed)")
    for path, (cls, ruled) in sorted(per.items(), key=lambda item: (item[1][0], item[0]),
                                     reverse=True):
        print(f"  {cls} {path}" + ("" if ruled else "  (no rule)"))


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
        print(f"  unruled (R5 by default): {path}")
    if len(unruled) > 40:
        print(f"  and {len(unruled) - 40} more")
    return 1 if unruled else 0


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
                print(f"{cls} {path}" + ("" if ruled else "  (no rule: R5 by default)"))
            return 0
        if mode == "--audit":
            if len(rest) != 1:
                print(USAGE, file=sys.stderr)
                return 2
            return audit(rest[0])
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
            top, per = change_class(diff_paths(*revs))
            if github:
                with open(output, "a", encoding="utf-8") as out:
                    out.write(f"class={top}\n")
            show_change(top, per)
            return 0
        if mode.startswith("-") or len(args) > 2:
            print(USAGE, file=sys.stderr)
            return 2
        base = args[1] if len(args) > 1 else "origin/main"
        show_change(*change_class(diff_paths(base, "HEAD", args[0])))
        return 0
    except GitFailure as error:
        print(f"risk.py: {error}; no class", file=sys.stderr)
        return 2
    except OSError as error:
        print(f"risk.py: {error}; no class", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
