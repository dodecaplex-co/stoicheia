"""Stamp the review records with what their reviewers read.

A review record, review/<book>/NN.toml (review/SCHEMA.md), carries four stamps:
`fingerprint` in [statement], a hash of the statements facts.json prints for the
proposition and everything attached to it (`heath.review_fingerprint`); `lean` in
[review], a hash of its Lean file (`heath.file_hash`); `text` in [review], a hash of the
record's own text, without its [review] table and fingerprint (`heath.text_hash`); and
`commit` in [review], the commit whose files the record was last confirmed against.
scripts/check_fidelity.py fails when a hash no longer matches, so a record is read again
whenever a statement, a Lean file or the record itself changes.

This script writes the stamps, so that nobody computes a hash by hand. A stamp says the
record has been read against the statements and files as they are now: run it after
a review, never just to quiet the check.

    python3 scripts/review_stamp.py --commit 1a2b3c4 III.16 I.40  # these records
    python3 scripts/review_stamp.py --dry-run                     # say what would change
    python3 scripts/review_stamp.py --migrate-text                # see below

`commit` changes only when `--commit` names one: the commit whose files the reviewer
read. Commit the change first, then stamp with that commit. The script checks that the
commit is in the history of HEAD, and that the record's Lean file and the record itself,
its [review] table and fingerprint aside, are at that commit as they are now, so a record
never names a commit it was not read at.
When a record's fingerprint, `lean` or `text` would change, or it has no commit yet,
`--commit` is required; otherwise an existing commit is kept. Each stamp stays on a line
of its own, `key = "value"`, and is rewritten in place or added at the end of its
section; nothing else in the file changes.

`--migrate-text` is for a record stamped before `text` was introduced, as one may be
on an older branch. It writes `text` alone, and only for a record whose own stamp
`commit` is in the history of HEAD and whose text at that commit is its text now: what
the reviewer read is then what the record says, so the stamp records no new reading. A
record whose text cannot be confirmed is listed as needing a reader. A stamp commit
absent from this clone or abbreviating more than one commit is instead a problem, and
so, for a record without `text`, is one not to be confirmed in the history of HEAD in a
shallow clone: fetch the missing history; or, for an ambiguous id, a reader identifies
the intended commit without guessing, reads the record and stamps it with --commit and
enough of the id to name that commit alone; then run the migration again. It changes
nothing it cannot confirm, and it can be run again at any time, as at landing, after
branches that change records.

Run it after `lake env lean Certificate/Facts.lean`. Standard library only; reading
the records needs Python 3.11 or later (tomllib).
"""

import argparse
import functools
import json
import os
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


NO_COMMIT = "is not a commit of this clone (a shallow clone, or a commit never fetched)"
AMBIGUOUS_COMMIT = "abbreviates more than one commit of this clone"
GIT = ("git", "--no-replace-objects", "-c", "advice.graftFileDeprecated=false")


def git_env() -> dict[str, str]:
    """The environment for every git command run here: this process's, with no graft file,
    since `--no-replace-objects` does not switch off a legacy .git/info/grafts."""
    return {**os.environ, "GIT_GRAFT_FILE": os.devnull}


@functools.lru_cache
def commit_objects(root: Path) -> tuple[str, ...]:
    """The full ids of all commit objects in the object store at `root`.

    Read once per process: a commit made later in the same process is not seen until
    `commit_objects.cache_clear()`."""
    try:
        out = subprocess.run(
            [*GIT, "cat-file", "--batch-all-objects",
             "--batch-check=%(objectname) %(objecttype)", "--unordered"],
            cwd=root, env=git_env(), capture_output=True, text=True, check=True)
    except (OSError, subprocess.CalledProcessError):
        return ()
    return tuple(line.split()[0] for line in out.stdout.splitlines()
                 if line.endswith(" commit") and len(line.split()) == 2)


def resolve(commit: str) -> tuple[str | None, str | None]:
    """Resolve a hexadecimal commit prefix independently of refs.

    Returns its one matching full commit id and no problem, or no id and a diagnostic
    when this clone has no matching commit object or has more than one.
    """
    matches = [full for full in commit_objects(ROOT) if full.startswith(commit)]
    if not matches:
        return None, NO_COMMIT
    if len(matches) != 1:
        return None, AMBIGUOUS_COMMIT
    return matches[0], None


def in_history(commit: str) -> bool:
    """Is `commit`, a full id, HEAD or an ancestor of HEAD?"""
    try:
        return subprocess.run([*GIT, "merge-base", "--is-ancestor", commit, "HEAD"],
                              cwd=ROOT, env=git_env(), capture_output=True).returncode == 0
    except OSError:
        return False


def is_shallow() -> bool:
    """Does Git report that this repository has a shallow history?"""
    try:
        out = subprocess.run([*GIT, "rev-parse", "--is-shallow-repository"], cwd=ROOT,
                             env=git_env(), capture_output=True, text=True)
    except OSError:
        return False
    return out.returncode == 0 and out.stdout.strip() == "true"


def show_at(commit: str, path: Path) -> bytes | None:
    """The file at `path` as it stands in `commit`, read by the commit's full id (resolve),
    or None when the commit or the file is not to be found there."""
    full, _ = resolve(commit)
    if full is None:
        return None
    try:
        out = subprocess.run([*GIT, "show", f"{full}:{rel(path)}"], cwd=ROOT,
                             env=git_env(), capture_output=True, check=True)
    except (OSError, subprocess.CalledProcessError):
        return None
    return out.stdout


def hash_at(commit: str, path: Path) -> str | None:
    """`heath.file_hash` of the file at `path` as it stands in `commit`, or None when the
    commit or the file is not to be found there."""
    data = show_at(commit, path)
    return None if data is None else heath._sha(data)


def text_at(commit: str, path: Path) -> str | None:
    """`heath.text_hash` of the record at `path` as it stands in `commit`, or None when
    the commit or the record is not to be found there, or is not valid TOML there."""
    data = show_at(commit, path)
    try:
        return None if data is None else heath.text_hash(data.decode())
    except (UnicodeDecodeError, ValueError):
        return None


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
    own = heath.text_hash(old)
    text, changes = old, []
    st, rv = record["statement"], record["review"]
    if st.get("fingerprint") != fingerprint:
        text = set_stamp(text, "statement", "fingerprint", fingerprint)
        changes.append(f"fingerprint {st.get('fingerprint', '(none)')} → {fingerprint}")
    if rv.get("lean") != lean:
        text = set_stamp(text, "review", "lean", lean)
        changes.append(f"lean {rv.get('lean', '(none)')} → {lean}")
    if rv.get("text") != own:
        text = set_stamp(text, "review", "text", own)
        changes.append(f"text {rv.get('text', '(none)')} → {own}")
    if (changes or "commit" not in rv) and commit is None:
        why = f"{ref}: its stamps change ({'; '.join(changes) or 'no commit yet'}): "
        ask = "name the commit whose files you read with --commit"
        full = None
        if "text" not in rv and "commit" in rv and len(changes) == 1:
            full, _ = resolve(rv["commit"])
        then = text_at(full, path) if full is not None and in_history(full) else None
        if then == own:
            raise ValueError(why + ask + "; or, as it was stamped before `text` was, write "
                             "`text` with --migrate-text")
        if then is not None:
            raise ValueError(why + f"the record was edited after its stamp commit "
                             f"{rv['commit']}, so it needs a reader, who reads it and stamps "
                             "it with --commit (docs/WORKFLOW.md, section 6)")
        raise ValueError(why + ask)
    if commit is not None:
        full, problem = resolve(commit)
        if full is None:
            recovery = ("fetch the missing history" if problem == NO_COMMIT else
                        "identify the intended commit without guessing and use enough of its "
                        "id to distinguish it")
            raise ValueError(f"{ref}: {commit} {problem}: {recovery}, then stamp with the "
                             "commit whose files you read, on this branch")
        if not in_history(full):
            why = ("cannot be confirmed in the incomplete history of this shallow clone: fetch "
                   "complete history, then stamp" if is_shallow() else
                   "is not in the history of HEAD: stamp")
            raise ValueError(f"{ref}: {commit} {why} with the commit whose files you read, "
                             "on this branch")
        at = hash_at(full, heath.lean_path(book, n))
        if at != lean:
            raise ValueError(f"{ref}: {rel(heath.lean_path(book, n))} at {commit} "
                             + ("is not to be found" if at is None else f"is {at}, not {lean}")
                             + ": commit the change first, then stamp with that commit")
        then = text_at(full, path)
        if then != own:
            raise ValueError(f"{ref}: {rel(path)} at {commit} "
                             + ("is not to be found, or does not read" if then is None
                                else "says something other than it says now, its [review] "
                                "table and fingerprint aside")
                             + ": commit the change first, then stamp with that commit")
        if commit != rv.get("commit"):
            text = set_stamp(text, "review", "commit", commit)
            changes.append(f"commit {rv.get('commit', '(none)')} → {commit}")
    if not changes:
        return False, f"{ref}: current"
    if not dry_run:
        write_checked(book, n, old, text, {("statement", "fingerprint"): fingerprint,
                                           ("review", "lean"): lean, ("review", "text"): own})
    return True, f"{ref}: " + "; ".join(changes)


def write_checked(book: str, n: int, old: str, new: str, want: dict) -> None:
    """Write the record's new text, and read it back: each (section, key) in `want` has
    its value, and the record's own text is what it was. Otherwise put the old text back
    and raise ValueError."""
    path = heath.review_path(book, n)
    path.write_text(new)
    try:
        again = heath.load_review(book, n)
        if (any(again[section].get(key) != value for (section, key), value in want.items())
                or heath.text_hash(new) != heath.text_hash(old)):
            raise heath.ReviewError(rel(path), ["the stamps did not read back as written"])
    except heath.ReviewError as e:
        path.write_text(old)
        raise ValueError(f"not stamped, and left as it was: {e}") from None


def migrate_text(book: str, n: int, dry_run: bool) -> tuple[str, str]:
    """Write the `text` stamp of a record stamped before it, when its own stamp commit is
    in the history of HEAD and its text at that commit is its text now. Returns (outcome,
    what was found): "written", "current", or "reader" for a record that needs a reader;
    raises ValueError when the record cannot be read, its commit is absent or ambiguous
    in this clone (resolve), or, for a record without `text`, shallow history prevents
    confirming its ancestry."""
    ref, path = f"{book}.{n}", heath.review_path(book, n)
    if not path.exists():
        raise ValueError(f"{ref}: there is no record {rel(path)}")
    try:
        rv = heath.load_review(book, n, require_stamp=False)["review"]
    except heath.ReviewError as e:
        raise ValueError(f"not migrated: {e}") from None
    old = path.read_text()
    own = heath.text_hash(old)
    full = None
    if "commit" in rv:
        commit = rv["commit"]
        full, problem = resolve(commit)
        if full is None:
            recovery = ("fetch the missing history, then run this again" if problem == NO_COMMIT
                        else "a reader identifies the intended commit without guessing and "
                             "stamps the record with --commit and enough of its id to name it "
                             "alone; then run this again")
            raise ValueError(f"{ref}: its stamp commit {commit} {problem}: {recovery}")
    if "text" in rv:
        if rv["text"] == own:
            return "current", f"{ref}: current"
        return "reader", f"{ref}: edited since its `text` stamp"
    if full is None:
        return "reader", f"{ref}: no stamp commit to compare it with"
    if not in_history(full):
        if is_shallow():
            raise ValueError(f"{ref}: its stamp commit {commit} cannot be confirmed in the "
                             "incomplete history of this shallow clone: fetch complete "
                             "history, then run this again")
        return "reader", f"{ref}: its stamp commit {commit} is not in the history of HEAD"
    then = text_at(full, path)
    if then is None:
        return "reader", f"{ref}: {rel(path)} is not to be found, or does not read, at {commit}"
    if then != own:
        return "reader", f"{ref}: edited since its stamp commit {commit}"
    if not dry_run:
        write_checked(book, n, old, set_stamp(old, "review", "text", own),
                      {("review", "text"): own})
    return "written", f"{ref}: text {own}, as at its stamp commit {commit}"


def migrate(todo: list[tuple[str, int]], dry_run: bool) -> int:
    found = {"written": [], "current": [], "reader": []}
    problems = []
    for book, n in todo:
        try:
            outcome, what = migrate_text(book, n, dry_run)
        except ValueError as e:
            problems.append(str(e))
            continue
        found[outcome].append(what)
    for what in found["written"]:
        print(("  would write " if dry_run else "  wrote ") + what)
    if found["reader"]:
        print("needs a reader, who reads the record and stamps it with --commit "
              "(docs/WORKFLOW.md, section 6):")
        for what in found["reader"]:
            print("  • " + what)
    for p in problems:
        print("  ✗ " + p)
    verb = "would write" if dry_run else "wrote"
    print(f"{verb} `text` in {len(found['written'])} record(s); {len(found['current'])} already "
          f"current; {len(found['reader'])} need(s) a reader; {len(problems)} problem(s)")
    return 1 if problems else 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description="Stamp the review records (review/SCHEMA.md).")
    parser.add_argument("refs", nargs="*", help="the propositions to stamp, as III.16 (default: every record)")
    parser.add_argument("--facts", type=Path, default=ROOT / "facts.json",
                        help="the facts.json to read the statements from")
    parser.add_argument("--commit", help="the commit whose files the reviewer read, in the "
                        "history of HEAD; required when a stamp changes, and an existing commit "
                        "is kept without it")
    parser.add_argument("--dry-run", action="store_true", help="say what would change; write nothing")
    parser.add_argument("--migrate-text", action="store_true",
                        help="write `text` alone, for each record whose text at its stamp commit, "
                        "in the history of HEAD, is its text now; list each record it cannot "
                        "confirm as needing a reader, and report a stamp commit that is absent "
                        "or ambiguous, or, for a record without `text`, not to be placed in "
                        "HEAD's history in a shallow clone, as a problem")
    args = parser.parse_args(argv)
    if args.commit and not heath.COMMIT.fullmatch(args.commit):
        parser.error("--commit is a git commit, 7 to 40 lower-case hex digits")
    if args.migrate_text:
        if args.commit:
            parser.error("--migrate-text records no new reading, so it takes no --commit")
        try:
            return migrate(targets(args.refs), args.dry_run)
        except ValueError as e:
            parser.error(str(e))
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
