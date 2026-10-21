#!/usr/bin/env python3
"""Check a train's members, merge trees, evidence and declared changes.

    python3 scripts/check_train.py --base <rev> --head <rev> --body-file <path>

Exit 0 means pass, 1 a refused train, and 2 an unreadable input. The check reads
committed trees; merge-tree writes temporary tree objects, never a checkout, and reads
merge attributes from the base, never from the checkout or the train, so a member's
.gitattributes cannot turn a resolved conflict into an automatic merge. Python 3.11 or
later, the standard library and Git 2.42 or later (merge-tree --write-tree came in 2.38,
--attr-source in 2.42); an older Git makes every train unreadable.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from safe_push import (
    CHECK_INPUTS, DECISIONS, GENERATED, GENERATED_REGIONS, SECTION, Refusal, changed_files,
    generated_parts, git,
    is_protected, judged_files, pinned, run, sections, shown, under, visible, written,
)

OID = re.compile(r"[0-9a-f]{40}")
HEAD = re.compile(r"[0-9a-f]{12,40}")
PASSED = re.compile(r"passed at ([0-9a-f]{12,40})(?:[ \t]+.*)?")
FIELDS = ("branch", "head", "code_review", "security_review", "no_mistakes")
# A review cell that is only a placeholder, as a whole, is no review's evidence; a finding
# that begins "To do so" or "Later commits" is not one. (/no-mistakes has its own two
# forms, "passed at" and "not run:", read below.)
PLACEHOLDER = re.compile(
    r"(?:pending|waiting|awaiting(?: (?:review|the review))?|(?:still )?to come|to ?do|"
    r"tbd|tbc|wip|queued|skipped|later|soon|in progress|n/?a|none|nothing|-+|\?+|"
    r"not (?:yet )?(?:run|done|started|reviewed)(?: yet)?|will run after (?:the )?merge)")
# A review cell names the commit it reviewed, by 7 to 40 lower-case hex digits; on
# /security-review, "Not required" stands instead, where no protected path changed.
COMMIT = re.compile(r"(?<![0-9A-Za-z])[0-9a-f]{7,40}(?![0-9A-Za-z])")
NOT_REQUIRED = re.compile(r"(?i)not required\b")
HEADINGS = ("Branch", "Head", "/code-review", "/security-review", "/no-mistakes")
CHECK_PATHS = ("scripts/", "tests/", ".github/")
FOUNDATION_PATHS = ("Elements/Foundations/", "Certificate/axioms.lock", "model/")
PROPOSITION_PATHS = (
    re.compile(r"Elements/Book([IVX]+)/Prop(\d+)\.lean"),
    re.compile(r"review/([IVX]+)/(\d+)\.toml"),
    re.compile(r"(?:heath|mishnah)/([IVX]+)/(\d+)\.md"),
    re.compile(r"figures/([IVX]+)/(\d+)[^/]*"),
)


def _plain(text: str) -> str:
    """Strip the same cell decoration as safe_push's review tables."""
    return text.strip("`*_ ")


def _section(body: str, name: str) -> str:
    """Read one unambiguous, visible section."""
    if not isinstance(body, str) or "\0" in body:
        raise ValueError("the body is not readable text")
    found = sections(body)
    count = sum(m.group(1).strip() == name for m in SECTION.finditer(visible(body)))
    if count != 1 or not found.get(name):
        raise ValueError(f'expected one written "{name}" section')
    return found[name]


def members_table(body: str) -> list[dict]:
    """Read the five cells of each Members row; raise ValueError if unreadable."""
    lines = [line.strip() for line in _section(body, "Members").splitlines()
             if line.strip()]
    cells = []
    for line in lines:
        if not line.startswith("|") or not line.endswith("|"):
            raise ValueError("Members: expected a five-column table")
        row = [c.strip() for c in line[1:-1].split("|")]
        if len(row) != len(FIELDS):
            raise ValueError("Members: expected five cells in every row")
        cells.append(row)
    if len(cells) < 3 or tuple(_plain(c) for c in cells[0]) != HEADINGS \
            or not all(re.fullmatch(r":?-{3,}:?", c) for c in cells[1]):
        raise ValueError("Members: expected the header, separator and at least one member")
    return [dict(zip(FIELDS, (_plain(c) for c in row))) for row in cells[2:]]


def _new() -> dict:
    """An empty declaration, with fresh collections for each call."""
    return {"checks": set(), "rules": [], "propositions": set(),
            "foundations": set(), "none": False}


def _path(text: str) -> str:
    """Read a relative repository path without ambiguous components."""
    path = _plain(text)
    if not written(path) or "\\" in path or any(ord(c) < 32 for c in path) \
            or any(p in {"", ".", ".."} for p in path.split("/")):
        raise ValueError(f"What is new: invalid repository path {text!r}")
    return path


def declared_new(body: str) -> dict:
    """Read What is new into sets and rule text; raise ValueError if unreadable."""
    text = _section(body, "What is new")
    result = _new()
    if text == "None.":
        result["none"] = True
        return result
    for line, item in shown(text):
        if not line.strip():
            continue
        match = re.fullmatch(r"\s*[-*+]\s+(check|rule|propositions|foundations):\s+(.+)",
                             line)
        if not item or not match:
            raise ValueError("What is new: expected None. or a check, rule, propositions "
                             "or foundations bullet")
        kind, value = match.groups()
        if kind == "rule":
            if not written(value):
                raise ValueError("What is new: the rule is not written")
            result["rules"].append(value.strip())
        elif kind == "propositions":
            refs = [_plain(ref) for ref in value.split(",")]
            if not all(re.fullmatch(r"[IVX]+\.[1-9]\d*", ref) for ref in refs):
                raise ValueError("What is new: expected propositions such as I.5, II.3")
            result["propositions"].update(refs)
        else:
            result["checks" if kind == "check" else kind].add(_path(value))
    if not any(result[k] for k in ("checks", "rules", "propositions", "foundations")):
        raise ValueError("What is new: no declaration could be read")
    return result


def _commit(repo: Path, rev: str) -> str:
    """Resolve a commit without accepting command options as revisions."""
    value = git(repo, "rev-parse", "--verify", "--end-of-options", f"{rev}^{{commit}}")
    value = value.strip()
    if not OID.fullmatch(value):
        raise ValueError(f"could not read commit {rev!r}")
    return value


def derive_new(repo: Path, base: str, sha: str) -> dict:
    """Derive file coverage from base..sha; rule prose cannot be inferred from a diff."""
    base, sha = _commit(repo, base), _commit(repo, sha)
    result = _new()
    for _, path in changed_files(repo, base, sha):
        if under(path, CHECK_PATHS):
            result["checks"].add(path)
        if under(path, FOUNDATION_PATHS):
            result["foundations"].add(path)
        for pattern in PROPOSITION_PATHS:
            if match := pattern.fullmatch(path):
                book, number = match.groups()
                result["propositions"].add(f"{book}.{int(number)}")
                break
    result["none"] = not any(result[k] for k in ("checks", "propositions", "foundations"))
    return result


def undeclared(derived: dict, declared: dict) -> list[str]:
    """Report derived changes absent from the declaration; extra declarations are allowed."""
    problems = []
    for key, label in (("checks", "check"), ("propositions", "proposition"),
                       ("foundations", "foundation")):
        for value in sorted(derived[key] - declared[key]):
            problems.append(f"What is new: undeclared {label}: {value}")
    for rule in derived["rules"]:
        if rule not in declared["rules"]:
            problems.append(f"What is new: undeclared rule: {rule}")
    return problems


def _placeholder(cell: str) -> bool:
    """A cell that, as a whole, says only that the review is absent or still to come."""
    return bool(PLACEHOLDER.fullmatch(" ".join(_plain(cell).split())
                                      .rstrip(".!;:, ").casefold()))


def _evidence(rows: list[dict]) -> list[str]:
    """Check the evidence that can be read without a repository."""
    problems = []
    branches = Counter(row["branch"] for row in rows)
    for branch, count in branches.items():
        if count > 1:
            problems.append(f"Members: duplicate branch: {branch}")
    for row in rows:
        branch, head = row["branch"], row["head"]
        if not written(branch) or any(c.isspace() for c in branch):
            problems.append("Members: the branch is not written as one name")
        if not HEAD.fullmatch(head):
            problems.append(f"Members: {branch}: Head must be 12 to 40 lower-case hex digits")
        for key, label in zip(FIELDS[2:], HEADINGS[2:]):
            cell = row[key]
            if not written(cell) or (key != "no_mistakes" and _placeholder(cell)):
                problems.append(f"Members: {branch}: {label} is not written, or says the "
                                "review is not done")
            elif key != "no_mistakes" and not COMMIT.search(cell) and not (
                    key == "security_review" and NOT_REQUIRED.match(cell)):
                problems.append(f"Members: {branch}: {label} names no reviewed commit "
                                "(7 to 40 lower-case hex digits)")
        evidence = row["no_mistakes"]
        if match := PASSED.fullmatch(evidence):
            checked = match.group(1)
            if not (head.startswith(checked) or checked.startswith(head)):
                problems.append(f"Members: {branch}: /no-mistakes names another head")
        elif evidence.startswith("not run:"):
            reason = evidence.removeprefix("not run:").strip()
            words = re.findall(r"[^\W_]+(?:['’-][^\W_]+)*", reason)
            if len(words) < 5:
                problems.append(f"Members: {branch}: /no-mistakes reason needs at least "
                                "five words")
        else:
            problems.append(f"Members: {branch}: /no-mistakes must say passed at <head> "
                            "or not run: <reason>")
    for i, row in enumerate(rows):
        head = row["head"]
        if HEAD.fullmatch(head) and any(
                HEAD.fullmatch(other["head"]) and
                (head.startswith(other["head"]) or other["head"].startswith(head))
                for other in rows[:i]):
            problems.append(f"Members: duplicate or ambiguous Head: {head}")
    return problems


def body_problems(body: str) -> list[str]:
    """Check the body's structure and evidence without git; protected paths need git."""
    problems = []
    try:
        problems.extend(_evidence(members_table(body)))
    except ValueError as error:
        problems.append(str(error))
    try:
        declared_new(body)
    except ValueError as error:
        problems.append(str(error))
    return problems


def _decision_path(path: str) -> bool:
    """The decisions page or one of its Markdown entry files. The entry files, one per
    decision directly under docs/decisions/, come with tooling/decision-entries, which
    lands before this check; until then main has none, and the allowance covers only
    such an entry."""
    return path == DECISIONS or bool(
        re.fullmatch(r"docs/decisions/[^/]+\.md", path))


def _coordinator_path(path: str, repo: Path | None = None, old: str | None = None,
                      new: str | None = None) -> bool:
    """Generated files and the decisions page or a Markdown decision entry. README.md and
    docs/PROGRAM.md are generated only between their markers: given the two revisions,
    a change to them counts only when it leaves the rest, written by hand, as it was."""
    if path in GENERATED_REGIONS:
        return repo is not None and not generated_parts(repo, old, new, path)[1]
    return under(path, (*GENERATED, "book/")) or _decision_path(path)


def _merge_problems(repo: Path, merge: str, parents: list[str], attrs: str) -> list[str]:
    """Compare a merge with git's automatic tree, including every conflicted path. Merge
    attributes (merge=union, say) are read from `attrs`, origin/main's commit, never from
    the checkout or the merged sides."""
    result = run(["git", f"--attr-source={attrs}", "merge-tree", "--write-tree",
                  "--name-only", "-z", "--no-messages", *parents], repo)
    if result.returncode not in (0, 1):
        raise ValueError(f"could not read automatic merge {merge} (Git 2.42 or later is "
                         f"needed): {result.stderr.strip()}")
    fields = result.stdout.split("\0")
    if not fields or not OID.fullmatch(fields[0]) or fields[-1] != "":
        raise ValueError(f"could not read automatic merge {merge}")
    tree = fields[0]
    conflicts = fields[1:-1]
    if conflicts and conflicts[-1] == "":
        conflicts.pop()
    if any(not path for path in conflicts) or bool(conflicts) != (result.returncode == 1):
        raise ValueError(f"could not read conflicted paths for merge {merge}")
    paths = set(conflicts) | {p for _, p in changed_files(repo, tree, merge)}
    return [f"merge {merge[:12]}: resolution or added content outside generated files "
            f"and decisions: {path}" for path in sorted(paths)
            if not _coordinator_path(path, repo, tree, merge)]


def _merge_bases(repo: Path, left: str, right: str) -> list[str]:
    """Read every merge base, more than one after criss-cross merges; none is unreadable."""
    bases = git(repo, "merge-base", "--all", left, right).split()
    if not bases or not all(OID.fullmatch(b) for b in bases):
        raise ValueError("could not read a merge base")
    return bases


def _contains(repo: Path, older: str, newer: str) -> bool:
    """Whether `older` is an ancestor of `newer` or the same commit."""
    result = run(["git", "merge-base", "--is-ancestor", older, newer], repo)
    if result.returncode not in (0, 1):
        raise ValueError("could not read ancestry")
    return result.returncode == 0


def _commits(repo: Path, *args: str) -> set[str]:
    """Read full commit names, refusing unexpected revision-list output."""
    commits = git(repo, "rev-list", *args).splitlines()
    if not all(OID.fullmatch(commit) for commit in commits):
        raise ValueError("could not read commit history")
    return set(commits)


def check_train(repo: Path, base: str, sha: str, body: str) -> list[str]:
    """Check rules 1 to 6, returning refusals; unreadable inputs raise ValueError or Refusal.

    The base is origin/main's supplied tip. The train's own first-parent chain is read:
    its merges and its own commits; a member's history is the member's. Keep-apart is
    stricter than safe_push.keep_apart: check changes with judged content refuse even
    when origin/main's checks pass.
    """
    rows, declared = members_table(body), declared_new(body)
    base, sha = _commit(repo, base), _commit(repo, sha)
    if git(repo, "rev-parse", "--is-shallow-repository").strip() != "false":
        raise ValueError("could not read complete history: the repository is shallow")
    if not _contains(repo, base, sha):
        return ["train head does not contain the supplied base"]
    problems = _evidence(rows)
    history = _commits(repo, base)
    # Rules 1 to 3 read the train's own first-parent chain: its merges of members and of
    # main, and its own commits. A member's history inside it, merges of main with their
    # resolutions included, is the member's, judged by the member's own reviews.
    graph = []
    for line in git(repo, "rev-list", "--first-parent", "--parents",
                    f"{base}..{sha}").splitlines():
        fields = line.split()
        if not fields or not all(OID.fullmatch(field) for field in fields):
            raise ValueError("could not read the train's parents")
        graph.append((fields[0], fields[1:]))
    members = Counter()
    for commit, parents in graph:
        if len(parents) > 2:
            problems.append(f"merge {commit[:12]}: expected exactly two parents")
        elif len(parents) == 2:
            if parents[1] not in history:
                members[parents[1]] += 1
            problems.extend(_merge_problems(repo, commit, parents, base))
    matched = Counter()
    for row in rows:
        heads = [head for head in members if HEAD.fullmatch(row["head"])
                 and head.startswith(row["head"])]
        if len(heads) != 1:
            problems.append(f"Members: {row['branch']}: row has no unique member merge "
                            f"for {row['head']}")
            continue
        head = heads[0]
        matched[head] += 1
        evidence = PASSED.fullmatch(row["no_mistakes"])
        if evidence and not head.startswith(evidence.group(1)):
            problem = f"Members: {row['branch']}: /no-mistakes names another head"
            if problem not in problems:
                problems.append(problem)
        # After criss-cross merges a member has several merge bases with main: the paths
        # it changes against any of them count, so more bases never mean fewer paths.
        try:
            protected = {p for member_base in _merge_bases(repo, base, head)
                         for _, p in changed_files(repo, member_base, head) if is_protected(p)}
        except (ValueError, Refusal) as error:
            raise ValueError(f"Members: {row['branch']} ({head[:12]}): {error}") from None
        if protected and NOT_REQUIRED.match(row["security_review"]):
            problems.append(f"Members: {row['branch']}: /security-review says Not required "
                            f"for protected paths: {', '.join(sorted(protected))}")
    for head, count in sorted(members.items()):
        if count != 1:
            problems.append(f"member {head[:12]} merged more than once ({count} merges)")
        if not matched[head]:
            problems.append(f"member {head[:12]} has no Members row")
        elif matched[head] != 1:
            problems.append(f"member {head[:12]} has more than one Members row")
    covered = _commits(repo, *members, "--not", base) if members else set()
    for commit, parents in graph:
        if len(parents) < 2 and commit not in covered:
            if len(parents) != 1:
                raise ValueError(f"could not read a parent for coordinator commit {commit}")
            for _, path in changed_files(repo, parents[0], commit):
                if not _coordinator_path(path, repo, parents[0], commit):
                    problems.append(f"coordinator commit {commit[:12]} changes forbidden "
                                    f"path: {path}")
    inputs = sorted(p for _, p in changed_files(repo, base, sha)
                    if under(p, CHECK_INPUTS) and not pinned(repo, base, sha, p))
    # Decision entry files (tooling/decision-entries) have the same allowance as the
    # decisions page, including when safe_push's guides do not yet include their directory.
    judged = [p for p in judged_files(repo, base, sha)
              if not _decision_path(p)] if inputs else []
    if inputs and judged:
        problems.append(f"check changes must be kept apart from judged content: "
                        f"{', '.join(inputs)}; judged: {', '.join(judged)}")
    problems.extend(undeclared(derive_new(repo, base, sha), declared))
    return problems


def main(argv=None) -> int:
    """Print the verdict, distinguishing refused trains from unreadable inputs."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--body-file", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        body = args.body_file.read_text(encoding="utf-8")
        problems = check_train(Path.cwd(), args.base, args.head, body)
    except (OSError, UnicodeError, ValueError, Refusal) as error:
        print(f"train: could not read: {error}", file=sys.stderr)
        return 2
    if problems:
        for problem in problems:
            print(f"train: REFUSED: {problem}")
        return 1
    print("train: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
