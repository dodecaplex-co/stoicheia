#!/usr/bin/env python3
"""The registry of checks: one file per check in checks/, and this, its one reader (#229).

Three lists had to agree, safe_push.py's CHECKS, CI's steps and docs/WORKFLOW.md's section
8, and every train that added a check edited all three in the same places. Now each check
of CI's `check` job is a file of its own, `checks/<NN>-<slug>.toml`, and the three are
read from the registry: scripts/run_checks.py runs a job's entries, as CI's `check` job
does with the pull request's own registry; render.py writes section 8's first command block
from them; and the pre-flight (scripts/safe_push.py) runs origin/main's registry, read out
of Git by origin/main's copy of this file, never the commit's
(docs/decisions/2026-10-22-check-registry.md).

An entry holds these fields and no others:

    order     a number; the entries run in its order, so a check goes between two others
              by an order between theirs, with no file renamed
    name      the check's name, as the pre-flight reports it: the command's words joined
              by spaces, or "git status --porcelain is empty" for the entry below
    job       the CI job that runs it: "check", the only job the registry holds today
    command   the argv, a list of strings; "python3" as its first word stands for the
              interpreter that runs it
    empty     true in place of `command`: `git status --porcelain` must print nothing,
              over the whole worktree
    section8  the line section 8's first command block shows for it
    concurrent  true: the pre-flight may run the check beside the other concurrent checks
              next to it in order (#608; checks/README.md says what it promises)
    after     with `concurrent`: the names of earlier checks that must have ended before
              this one starts, as a check's own test runs before its verdict

`order`, `name`, `job` and `section8` are required, and exactly one of `command` and
`empty`; `concurrent` and `after` may be left out. The folder holds the entries, its
README.md (which this reader passes over) and nothing else but a Finder .DS_Store, which it
passes over too. A file of another name, a folder, a link, a file that is not UTF-8 TOML,
an unknown or missing field, a value of the wrong kind, an unknown job, `concurrent` other
than true or with `empty`, `after` without `concurrent` or naming anything but an earlier
check, two entries of one name or one order, or no entry at all is an error naming the
file: the registry is read whole or not at all.

    python3 scripts/registry.py [ROOT]                     each entry, in order
    python3 scripts/registry.py --json [ROOT]              the same, as JSON
    python3 scripts/registry.py --rev REV [--json] [ROOT]  the registry Git holds at REV,
                                                           in the repository at ROOT

ROOT is the repository's root, this file's parent's parent unless given. Exit 0 with the
entries, 1 when the registry fails, 2 for a usage error. Standard library and Git only;
scripts/test_safe_push.py tests it.

This file must stay self-contained, importing the standard library alone. The pre-flight
takes origin/main's copy out of Git and runs it on its own, with `python3 -I`, from a
temporary directory, where no module beside it can be found; and its step 3 runs the
commit's own copy the same way, refusing a commit whose copy fails so, since that copy
would judge every train after it once merged. render.py and run_checks.py import it from
scripts/, where a sibling module would load, so they cannot be what shows it works.
"""

from __future__ import annotations

import json
import math
import os
import re
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FOLDER = "checks"
README = "README.md"
PASSED_OVER = (README, ".DS_Store")
ENTRY = re.compile(r"[0-9]+-[a-z0-9]+(?:-[a-z0-9]+)*\.toml")
FIELDS = ("order", "name", "job", "command", "empty", "section8", "concurrent", "after")
REQUIRED = ("order", "name", "job", "section8")
JOBS = ("check",)
PYTHON = "python3"
EMPTY_COMMAND = ("git", "status", "--porcelain")
EMPTY_NAME = "git status --porcelain is empty"
# The line that opens section 8's first command block, which render.py writes from the
# registry between docs/WORKFLOW.md's checks markers (heath.REGIONS; this file imports
# nothing of the repository's, since safe_push.py runs origin/main's copy of it alone).
PATH_LINE = "export PATH=$HOME/.elan/bin:$PATH"
USAGE = "usage: registry.py [--rev REV] [--json] [ROOT]"


class RegistryError(Exception):
    """The registry cannot be read, or an entry breaks its rules: the message names the
    file."""


@dataclass(frozen=True)
class Entry:
    path: str                           # checks/<NN>-<slug>.toml
    order: int | float
    name: str
    job: str
    command: tuple[str, ...] | None     # None when `empty`
    empty: bool
    section8: str
    concurrent: bool = False
    after: tuple[str, ...] = ()         # earlier checks' names, with `concurrent` alone

    def argv(self, python: str = sys.executable) -> list[str]:
        """The command to run: `python` for a first word "python3", and for an `empty`
        entry, `git status --porcelain`."""
        words = list(EMPTY_COMMAND if self.empty else self.command)
        if words[0] == PYTHON:
            words[0] = python
        return words


def shown(text: str) -> str:
    """A name as an error prints it: every character Python counts unprintable written as
    an escape, so that no name can start a line of a log."""
    return "".join(c if c.isprintable() else c.encode("unicode_escape").decode("ascii")
                   for c in text)


def one_line(value) -> bool:
    return isinstance(value, str) and value.strip() == value and bool(value) \
        and value.isprintable()


def entry(path: str, data: bytes) -> Entry:
    """One file's entry, or RegistryError naming it."""
    try:
        fields = tomllib.loads(data.decode("utf-8"))
    except UnicodeDecodeError as error:
        raise RegistryError(f"{path}: not UTF-8 text (byte {error.start})") from None
    except tomllib.TOMLDecodeError as error:
        raise RegistryError(f"{path}: not TOML: {error}") from None
    unknown = sorted(set(fields) - set(FIELDS))
    if unknown:
        raise RegistryError(f"{path}: unknown field {', '.join(map(repr, unknown))}; an entry "
                            f"holds {', '.join(FIELDS)}")
    missing = [name for name in REQUIRED if name not in fields]
    if missing:
        raise RegistryError(f"{path}: missing field {', '.join(map(repr, missing))}")
    order = fields["order"]
    if isinstance(order, bool) or not isinstance(order, (int, float)) or not math.isfinite(order):
        raise RegistryError(f"{path}: order must be a number")
    if fields["job"] not in JOBS:
        raise RegistryError(f"{path}: unknown job {fields['job']!r}; the jobs are "
                            f"{', '.join(JOBS)}")
    for name in ("name", "section8"):
        if not one_line(fields[name]):
            raise RegistryError(f"{path}: {name} must be one line of printable text, with "
                                "no space at either end")
    if ("command" in fields) == ("empty" in fields):
        raise RegistryError(f"{path}: an entry holds exactly one of command and empty")
    command = fields.get("command")
    if "empty" in fields:
        if fields["empty"] is not True:
            raise RegistryError(f"{path}: empty is true, or absent with a command")
        expected = EMPTY_NAME
    else:
        if (not isinstance(command, list) or not command
                or not all(isinstance(word, str) and word and "\0" not in word
                           for word in command)):
            raise RegistryError(f"{path}: command must be a list of strings, none empty")
        command = tuple(command)
        expected = " ".join(command)
    if fields["name"] != expected:
        raise RegistryError(f"{path}: name must be {shown(expected)!r}, the "
                            + ("command's words joined by spaces" if command else
                               "name of the check that git status --porcelain prints nothing"))
    concurrent = "concurrent" in fields
    if concurrent and fields["concurrent"] is not True:
        raise RegistryError(f"{path}: concurrent is true, or absent for a check that runs "
                            "alone")
    if concurrent and "empty" in fields:
        raise RegistryError(f"{path}: the check with empty judges the whole worktree, and "
                            "runs alone: it is never concurrent")
    after = fields.get("after", [])
    if "after" in fields and not concurrent:
        raise RegistryError(f"{path}: after is for a concurrent check, which may otherwise "
                            "start beside those it names")
    if (not isinstance(after, list)
            or not all(one_line(name) for name in after) or len(set(after)) != len(after)):
        raise RegistryError(f"{path}: after must be a list of checks' names, each once")
    return Entry(path, order, fields["name"], fields["job"], command, "empty" in fields,
                 fields["section8"], concurrent, tuple(after))


def ordered(files: dict[str, bytes]) -> list[Entry]:
    """The entries of the files of checks/, by their names there, in order; RegistryError
    for a name the folder may not hold, a bad entry, two of one name or one order, or none."""
    entries = []
    for name in sorted(files):
        if name in PASSED_OVER:
            continue
        if not ENTRY.fullmatch(name):
            raise RegistryError(f"{FOLDER}/{shown(name)}: expected {README} or an entry named "
                                "<NN>-<slug>.toml, digits and then lower-case letters and "
                                "digits joined by hyphens")
        entries.append(entry(f"{FOLDER}/{name}", files[name]))
    if not entries:
        raise RegistryError(f"{FOLDER}/: no entry; the registry holds at least one check")
    for field in ("name", "order"):
        seen: dict = {}
        for e in entries:
            value = getattr(e, field)
            if value in seen:
                raise RegistryError(f"{e.path}: the {field} {shown(str(value))!r} is "
                                    f"{seen[value]}'s too")
            seen[value] = e.path
    entries.sort(key=lambda e: e.order)
    for at, e in enumerate(entries):
        earlier = {before.name for before in entries[:at]}
        for name in e.after:
            if name not in earlier:
                raise RegistryError(f"{e.path}: after names {shown(name)!r}, which is no "
                                    "earlier check's name")
    return entries


def folder_files(root: Path) -> dict[str, bytes]:
    """The files of root/checks/, by name; RegistryError for a folder, a link or anything
    that is not a regular file, and for no folder."""
    folder = root / FOLDER
    if folder.is_symlink() or not folder.is_dir():
        raise RegistryError(f"{FOLDER}/: no registry, a folder of checks, at {root}")
    files = {}
    for name in os.listdir(folder):
        path = folder / name
        if name == ".DS_Store":
            continue
        if path.is_symlink() or not path.is_file():
            raise RegistryError(f"{FOLDER}/{shown(name)}: expected a regular file")
        files[name] = path.read_bytes()
    return files


def git(root: Path, args: list[str], data: bytes | None = None) -> bytes:
    try:
        done = subprocess.run(["git", "-c", "core.useReplaceRefs=false", *args], cwd=root,
                              input=data, capture_output=True)
    except OSError as error:
        raise RegistryError(f"git could not be run: {error}") from None
    if done.returncode != 0:
        said = done.stderr.decode(errors="replace").strip()
        raise RegistryError(f"git {' '.join(args)} exited {done.returncode}: {shown(said)}")
    return done.stdout


def revision_files(root: Path, rev: str) -> dict[str, bytes]:
    """The files of checks/ Git holds at rev, by name, read with git's replacement objects
    off; RegistryError as folder_files gives it."""
    if not rev or rev.startswith("-"):
        raise RegistryError(f"not a revision: {shown(rev)!r}")
    top = git(root, ["ls-tree", "-z", "--full-tree", rev, "--", FOLDER])
    meta = top.split(b"\t", 1)[0].split()
    if len(meta) != 3 or meta[1] != b"tree":
        raise RegistryError(f"{FOLDER}/: no registry, a folder of checks, at {shown(rev)}")
    listing = git(root, ["ls-tree", "-z", meta[2].decode()])
    names, blobs = [], []
    for record in listing.split(b"\0"):
        if not record:
            continue
        meta, _, raw = record.partition(b"\t")
        mode, kind, oid = meta.split()
        name = os.fsdecode(raw)
        if name == ".DS_Store":
            continue
        if kind != b"blob" or mode not in (b"100644", b"100755"):
            raise RegistryError(f"{FOLDER}/{shown(name)}: expected a regular file")
        names.append(name)
        blobs.append(oid)
    out = git(root, ["cat-file", "--batch"], b"".join(oid + b"\n" for oid in blobs))
    files, pos = {}, 0
    for name, oid in zip(names, blobs):
        end = out.find(b"\n", pos)
        header = out[pos:end].split() if end >= 0 else []
        if len(header) != 3 or header[0] != oid or header[1] != b"blob" \
                or not header[2].isdigit():
            raise RegistryError(f"{FOLDER}/{shown(name)}: git cat-file could not read it")
        start = end + 1
        files[name] = out[start:start + int(header[2])]
        pos = start + int(header[2]) + 1
    return files


def load(root: Path | str = ROOT, rev: str | None = None) -> list[Entry]:
    """The registry's entries, in order: root/checks/ in the worktree, or, given rev, the
    folder Git holds at rev in the repository at root. RegistryError, naming the file, when
    it cannot be read or breaks a rule."""
    root = Path(root)
    return ordered(revision_files(root, rev) if rev is not None else folder_files(root))


def of_job(entries: list[Entry], job: str) -> list[Entry]:
    return [e for e in entries if e.job == job]


def section8_block(entries: list[Entry]) -> str:
    """Section 8's first command block, as render.py writes it between docs/WORKFLOW.md's
    checks markers (heath.REGIONS): the line that puts Lean's tools on the PATH, then each
    entry of the `check` job's line."""
    lines = [PATH_LINE, *(e.section8 for e in of_job(entries, "check"))]
    return "```sh\n" + "\n".join(lines) + "\n```\n"


def as_json(entries: list[Entry]) -> str:
    return json.dumps([{"name": e.name, "job": e.job, "order": e.order,
                        "command": list(e.command) if e.command else None,
                        "empty": e.empty, "concurrent": e.concurrent, "after": list(e.after),
                        "path": e.path} for e in entries], indent=1)


def main(argv: list[str]) -> int:
    args = list(argv)
    if args[:1] in (["-h"], ["--help"]):
        print(__doc__)
        return 0
    rev = None
    if "--rev" in args:
        at = args.index("--rev")
        if at + 1 >= len(args):
            print(USAGE, file=sys.stderr)
            return 2
        rev = args.pop(at + 1)
        args.pop(at)
    wanted_json = "--json" in args
    args = [a for a in args if a != "--json"]
    if len(args) > 1 or any(a.startswith("-") for a in args):
        print(USAGE, file=sys.stderr)
        return 2
    try:
        entries = load(Path(args[0]) if args else ROOT, rev)
    except (RegistryError, OSError) as error:
        print(f"registry.py: {error}", file=sys.stderr)
        return 1
    if wanted_json:
        print(as_json(entries))
    else:
        for e in entries:
            print(f"{e.order:>6} {e.job:<8} {e.name}  ({e.path})")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
