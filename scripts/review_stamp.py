"""Stamp the review records with what their reviewers read.

A review record, review/<book>/NN.toml (review/SCHEMA.md), carries three stamps:
`fingerprint` in [statement], a hash of the statements facts.json prints for the
proposition and everything attached to it (`heath.review_fingerprint`); `lean` in
[review], a hash of its Lean file (`heath.file_hash`); and `commit` in [review], the
commit whose files the record was last confirmed against. scripts/check_fidelity.py
fails when the first two no longer match, so a record is read again whenever a
statement or a Lean file changes.

This script writes the stamps, so that nobody computes a hash by hand. A stamp says the
record has been read against the statements and files as they are now: run it after
a review, never just to quiet the check.

    python3 scripts/review_stamp.py --commit 1a2b3c4 III.16 I.40  # these records
    python3 scripts/review_stamp.py --dry-run                     # say what would change

`commit` changes only when `--commit` names one: the commit whose files the reviewer
read. Commit the change first, then stamp with that commit. The script checks that the
record's Lean file at that commit is the file as it is now, so a record never names a
commit it was not read at. When a record's fingerprint or `lean` would change, or it
has no commit yet, `--commit` is required; otherwise an existing commit is kept. Each
stamp stays on a line of its own, `key = "value"`, and is rewritten in place or added at
the end of its section; nothing else in the file changes.

Run it after `lake env lean Certificate/Facts.lean`. Standard library only; reading
the records needs Python 3.11 or later (tomllib).
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

import heath

ROOT = heath.ROOT


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def set_stamp(text: str, section: str, key: str, value: str) -> str:
    """`text` with `key = "value"` in its [section]: the key's line rewritten if it is
    there, or a new line after the section's last line of content."""
    lines = text.split("\n")
    header = re.compile(r"^\s*\[\s*%s\s*\]\s*(#.*)?$" % re.escape(section))
    start = next((i for i, line in enumerate(lines) if header.match(line)), None)
    if start is None:
        raise ValueError(f"there is no [{section}] section")
    end = next((i for i in range(start + 1, len(lines)) if lines[i].lstrip().startswith("[")),
               len(lines))
    new = f'{key} = "{value}"'
    for i in range(start + 1, end):
        if re.match(r"^\s*%s\s*=" % re.escape(key), lines[i]):
            if not re.match(r'^\s*%s\s*=\s*"[^"\\]*"\s*(#.*)?$' % re.escape(key), lines[i]):
                raise ValueError(f'[{section}] `{key}` is not on a line of its own, as '
                                 f'{key} = "…"')
            lines[i] = new
            return "\n".join(lines)
    last = start
    for i in range(start + 1, end):
        if lines[i].strip() and not lines[i].lstrip().startswith("#"):
            last = i
    lines.insert(last + 1, new)
    return "\n".join(lines)


def hash_at(commit: str, path: Path) -> str | None:
    """`heath.file_hash` of the file at `path` as it stands in `commit`, or None when the
    commit or the file is not to be found there."""
    try:
        out = subprocess.run(["git", "show", f"{commit}:{rel(path)}"], cwd=ROOT,
                             capture_output=True, check=True)
    except (OSError, subprocess.CalledProcessError):
        return None
    return heath._sha(out.stdout)


def targets(refs: list[str]) -> list[tuple[str, int]]:
    if not refs:
        return [(book, n) for book, count in heath.BOOKS.items()
                for n in range(1, count + 1) if heath.review_path(book, n).exists()]
    out = []
    for ref in refs:
        r = heath.parse_ref(ref.replace("/", "."))
        if r.kind != "proposition" or r.book not in heath.BOOKS or r.n > heath.BOOKS[r.book]:
            raise ValueError(f"{ref}: a record is kept for each proposition of "
                             f"{', '.join(heath.BOOKS)}, as 'III.16'")
        out.append((r.book, r.n))
    return out


def stamp(facts: dict, book: str, n: int, commit: str | None, dry_run: bool) -> tuple[bool, str]:
    """Stamp one record. Returns (changed, what was done), or raises ValueError."""
    ref, path = f"{book}.{n}", heath.review_path(book, n)
    if not path.exists():
        raise ValueError(f"{ref}: there is no record {rel(path)}")
    try:
        record = heath.load_review(book, n, require_stamp=False)
    except heath.ReviewError as e:
        raise ValueError(f"not stamped: {e}") from None
    try:
        fingerprint = heath.review_fingerprint(facts, ref)
    except KeyError as e:
        raise ValueError(f"{ref}: {e.args[0] if e.args else e}") from None
    lean = heath.file_hash(heath.lean_path(book, n))
    old = path.read_text()
    text, changes = old, []
    st, rv = record["statement"], record["review"]
    if st.get("fingerprint") != fingerprint:
        text = set_stamp(text, "statement", "fingerprint", fingerprint)
        changes.append(f"fingerprint {st.get('fingerprint', '(none)')} → {fingerprint}")
    if rv.get("lean") != lean:
        text = set_stamp(text, "review", "lean", lean)
        changes.append(f"lean {rv.get('lean', '(none)')} → {lean}")
    if (changes or "commit" not in rv) and commit is None:
        raise ValueError(f"{ref}: its stamps change ({'; '.join(changes) or 'no commit yet'}): "
                         "name the commit whose files you read with --commit")
    if commit is not None and commit != rv.get("commit"):
        at = hash_at(commit, heath.lean_path(book, n))
        if at != lean:
            raise ValueError(f"{ref}: {rel(heath.lean_path(book, n))} at {commit} "
                             + ("is not to be found" if at is None else f"is {at}, not {lean}")
                             + ": commit the change first, then stamp with that commit")
        text = set_stamp(text, "review", "commit", commit)
        changes.append(f"commit {rv.get('commit', '(none)')} → {commit}")
    if not changes:
        return False, f"{ref}: current"
    if not dry_run:
        path.write_text(text)
        try:
            again = heath.load_review(book, n)
            if (again["statement"]["fingerprint"], again["review"]["lean"]) != (fingerprint, lean):
                raise heath.ReviewError(rel(path), ["the stamps did not read back as written"])
        except heath.ReviewError as e:
            path.write_text(old)
            raise ValueError(f"not stamped, and left as it was: {e}") from None
    return True, f"{ref}: " + "; ".join(changes)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description="Stamp the review records (review/SCHEMA.md).")
    parser.add_argument("refs", nargs="*", help="the propositions to stamp, as III.16 (default: every record)")
    parser.add_argument("--facts", type=Path, default=ROOT / "facts.json",
                        help="the facts.json to read the statements from")
    parser.add_argument("--commit", help="the commit whose files the reviewer read; required "
                        "when a stamp changes, and an existing commit is kept without it")
    parser.add_argument("--dry-run", action="store_true", help="say what would change; write nothing")
    args = parser.parse_args(argv)
    if args.commit and not heath.COMMIT.fullmatch(args.commit):
        parser.error("--commit is a git commit, 7 to 40 lower-case hex digits")
    facts = json.loads(args.facts.read_text())
    if any("statement" not in p for p in facts.get("propositions", [])):
        print(f"{args.facts}: an entry has no `statement` (Certificate/FIELDS.md): rerun "
              "`lake env lean Certificate/Facts.lean` first")
        return 1
    commit = args.commit
    try:
        todo = targets(args.refs)
    except ValueError as e:
        parser.error(str(e))
    changed = current = 0
    problems = []
    for book, n in todo:
        try:
            did, what = stamp(facts, book, n, commit, args.dry_run)
        except ValueError as e:
            problems.append(str(e))
            continue
        if did:
            changed += 1
            print(("  would stamp " if args.dry_run else "  stamped ") + what)
        else:
            current += 1
    for p in problems:
        print("  ✗ " + p)
    verb = "would stamp" if args.dry_run else "stamped"
    print(f"{verb} {changed} record(s); {current} already current; {len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
