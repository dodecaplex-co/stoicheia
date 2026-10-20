#!/usr/bin/env python3
"""Check a merge group's preserved changes, evidence, order and generated tree.

    python3 scripts/check_queue.py --head <sha> --base <sha> --repo <owner/name>
    python3 scripts/check_queue.py --gaps --head <sha> --base <sha> --repo <owner/name>
    python3 scripts/check_queue.py --tree <dir> [--render]

Group commands require a checkout of the supplied head. CI builds its certificate
before this check runs render.py. --tree checks for repeated dated decisions
headings, adding freshness with --render. Conflict markers are checked by S23 in
check_style.py, in the check job on the same merge group.

GitHub reads use gh api and gh api graphql, with GH_TOKEN inherited and never
printed. --github-json replaces that boundary completely: an object with
pull_requests (REST pulls responses keyed by number), queue (the GraphQL response)
and main (the REST commits/main response). Queue entries include pageInfo so a
truncated answer cannot pass. The subject's pull request number and the queue's
headRefOid must agree. A different queue merge subject is accepted only when its
second parent uniquely identifies a queue entry; no subject fallback is allowed
for the already merged prefix.

Reversing T with merge-base T.head merges the group with T's original base. This
is T's diff reverse-applied by a three-way merge, without context-only false
alarms from a patch. Generated files are excluded; added decisions lines must
remain a subsequence. An automatic revert instead requires an exact git revert
tree and the Bot login set by trusted CI in STOICHEIA_REVERT_BOT.

safe_push records abbreviated harness blobs. They must resolve unambiguously to
the full blob at the pre-flight's recorded base, an ancestor of the group base.
ACCEPTANCE_VERDICTS names the acceptance job's JSON for proposition gap reports.
Exit 0 means pass, 1 refused, and 2 unreadable. Standard library, Python 3.11+, git.
"""

from __future__ import annotations

import argparse
import contextlib
import datetime
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import safe_push
from check_train import members_table, declared_new, derive_new, undeclared, body_problems

OID = re.compile(r"[0-9a-f]{40}")
SLUG = re.compile(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+")
SUBJECT = re.compile(r"Merge pull request #([1-9][0-9]*) from \S+")
MONTHS = ("January", "February", "March", "April", "May", "June", "July",
          "August", "September", "October", "November", "December")
GENERATED = (*safe_push.GENERATED, "book/", safe_push.DECISIONS)


class Refused(Exception):
    """A readable input which does not meet the queue's rules."""


class GitHub:
    """The only GitHub boundary; fixture reads never fall back to the network."""

    def __init__(self, repo: str, fixture: Path | None):
        self.repo = repo
        self.fixture = json.loads(fixture.read_text(encoding="utf-8")) if fixture else None
        if fixture and not isinstance(self.fixture, dict):
            raise ValueError("GitHub fixture must be an object")

    def read(self, kind: str, number: int | None = None):
        if self.fixture is not None:
            try:
                value = self.fixture[kind]
                return value[str(number)] if kind == "pull_requests" else value
            except (KeyError, TypeError):
                raise ValueError(f"GitHub fixture lacks {kind}") from None
        if not os.environ.get("GH_TOKEN"):
            raise ValueError("GitHub: GH_TOKEN is not set")
        if kind == "queue":
            owner, name = self.repo.split("/")
            query = (
                "query($owner:String!,$name:String!){repository(owner:$owner,name:$name){"
                'mergeQueue(branch:"main"){entries(first:100){'
                "nodes{position pullRequest{number headRefOid}} "
                "pageInfo{hasNextPage}}}}}"
            )
            command = ["gh", "api", "graphql", "-f", f"query={query}",
                       "-f", f"owner={owner}", "-f", f"name={name}"]
        else:
            endpoint = "commits/main" if kind == "main" else f"pulls/{number}"
            command = ["gh", "api", "--method", "GET", f"repos/{self.repo}/{endpoint}"]
        try:
            result = subprocess.run(command, capture_output=True, text=True, timeout=60)
            if result.returncode:
                raise ValueError("GitHub request failed")
            return json.loads(result.stdout)
        except Exception:
            # Neither gh's output nor an exception can disclose an inherited token.
            raise ValueError(f"GitHub: could not read {kind}") from None


def oid(value, label: str) -> str:
    """Read one full object name, with a useful error for malformed metadata."""
    if not isinstance(value, str) or not OID.fullmatch(value):
        raise ValueError(f"could not read {label}: expected a full object name")
    return value


def commit(repo: Path, value: str) -> str:
    """Resolve a revision without treating it as a command option."""
    return oid(safe_push.git(repo, "rev-parse", "--verify", "--end-of-options",
                            f"{value}^{{commit}}").strip(), "commit")


def parents(repo: Path, sha: str) -> list[str]:
    values = safe_push.git(repo, "show", "-s", "--format=%P", sha).split()
    return [oid(value, "parent") for value in values]


def merge_base(repo: Path, left: str, right: str) -> str:
    values = safe_push.git(repo, "merge-base", "--all", left, right).split()
    if len(values) != 1:
        raise ValueError("could not read a unique merge base")
    return oid(values[0], "merge base")


def ancestor(repo: Path, older: str, newer: str) -> bool:
    result = safe_push.run(["git", "merge-base", "--is-ancestor", older, newer], repo)
    if result.returncode not in (0, 1):
        raise ValueError("could not read ancestry")
    return result.returncode == 0


def automatic(repo: Path, left: str, right: str, base: str | None = None) -> tuple:
    """Read the automatic tree and every conflicted path, including binary files."""
    args = ["git", "merge-tree", "--write-tree", "--name-only", "-z", "--no-messages"]
    if base:
        args.append(f"--merge-base={base}")
    result = safe_push.run([*args, left, right], repo)
    if result.returncode not in (0, 1):
        raise ValueError("could not read an automatic merge")
    fields = result.stdout.split("\0")
    if not fields or fields[-1] != "":
        raise ValueError("could not read automatic merge paths")
    tree, conflicts = oid(fields[0], "automatic tree"), fields[1:-1]
    if conflicts and conflicts[-1] == "":
        conflicts.pop()
    if any(not path for path in conflicts) or bool(conflicts) != (result.returncode == 1):
        raise ValueError("could not read automatic merge conflicts")
    return tree, conflicts


def queue_entries(answer) -> list[tuple[int, str]]:
    """Require a complete, ordered queue starting at position one."""
    try:
        if not isinstance(answer, dict) or answer.get("errors"):
            raise ValueError
        entries = answer["data"]["repository"]["mergeQueue"]["entries"]
        nodes = entries["nodes"]
        if entries["pageInfo"]["hasNextPage"] is not False or not isinstance(nodes, list):
            raise ValueError
        result = []
        for position, node in enumerate(nodes, 1):
            pr = node["pullRequest"]
            if type(node["position"]) is not int or node["position"] != position \
                    or type(pr["number"]) is not int or pr["number"] < 1:
                raise ValueError
            result.append((pr["number"], oid(pr["headRefOid"], "queue head")))
        if len({n for n, _ in result}) != len(result) \
                or len({s for _, s in result}) != len(result):
            raise ValueError
        return result
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read a complete queue in position order") from None


def pull_request(answer, number: int) -> dict:
    """Read the required fields of a REST pull request without defaulting missing data."""
    try:
        if type(answer["number"]) is not int or answer["number"] != number:
            raise ValueError
        head = oid(answer["head"]["sha"], "pull request head")
        ref, body = answer["head"]["ref"], answer["body"]
        author = answer["user"]
        if not all(isinstance(v, str) and v for v in
                   (ref, author["login"], author["type"])) \
                or not isinstance(body, str) or "\0" in body:
            raise ValueError
        if answer["state"] not in ("open", "closed") or type(answer["merged"]) is not bool:
            raise ValueError
        if answer["merged"] and answer["state"] != "closed":
            raise ValueError
        labels = answer["labels"]
        if not isinstance(labels, list) or not all(
                isinstance(label["name"], str) and label["name"] for label in labels):
            raise ValueError
        return dict(number=number, head=head, ref=ref, body=body, author=author,
                    labels={label["name"] for label in labels},
                    state="MERGED" if answer["merged"] else answer["state"].upper(),
                    merged=oid(answer["merge_commit_sha"], "merged commit")
                    if answer["merged"] else None)
    except (KeyError, TypeError, ValueError):
        raise ValueError(f"GitHub: could not read pull request #{number}") from None


def chain(repo: Path, base: str, head: str, api: GitHub) -> list[dict]:
    """Identify the first-parent chain and prove its queue order and merge trees."""
    queued = queue_entries(api.read("queue"))
    main = commit(repo, oid(api.read("main")["sha"], "main head"))
    main_chain = safe_push.git(repo, "rev-list", "--first-parent", main).splitlines()
    if base not in main_chain:
        raise Refused("group base is not on main's first-parent chain")
    backwards = []
    current = head
    while current != base:
        pp = parents(repo, current)
        if len(pp) != 2:
            raise Refused(f"batching: {current[:12]} must have exactly two parents")
        subject = safe_push.git(repo, "show", "-s", "--format=%s", current).strip()
        match = SUBJECT.fullmatch(subject)
        matching = [number for number, sha in queued if sha == pp[1]]
        if match:
            number = int(match.group(1))
            if matching and matching != [number]:
                raise Refused("batching: merge subject and queue head identify different "
                              "pull requests")
        elif subject.startswith("Merge pull request #") or len(matching) != 1:
            raise Refused("batching: cannot identify the merge's pull request")
        else:
            number = matching[0]
        pr = pull_request(api.read("pull_requests", number), number)
        if pr["head"] != pp[1]:
            raise Refused(f"batching: #{number} head differs from the second parent")
        tree, conflicts = automatic(repo, *pp)
        if conflicts or tree != safe_push.git(repo, "rev-parse", f"{current}^{{tree}}").strip():
            raise Refused(f"batching: merge {current[:12]} has conflicts or extra content")
        backwards.append(dict(pr, merge=current, main=main))
        current = pp[0]
    entries = list(reversed(backwards))
    if not entries or len({p["number"] for p in entries}) != len(entries):
        raise Refused("batching: expected a non-empty chain without repeated pull requests")
    waiting, passed_queue = [], False
    for pr in entries:
        if pr["state"] == "MERGED" and not passed_queue:
            if pr["merged"] != pr["merge"] or pr["merge"] not in main_chain:
                raise Refused("batching: merged prefix is not held by main")
        elif pr["state"] == "OPEN":
            passed_queue = True
            waiting.append((pr["number"], pr["head"]))
        else:
            raise Refused("batching: only a merged prefix may precede open queue entries")
    if not waiting or waiting != queued[:len(waiting)]:
        raise Refused("batching: skipped train or trains out of queue order")
    return entries


def preflight(repo: Path, base: str, pr: dict) -> None:
    """Require one visible pre-flight with the exact head and recorded harness."""
    body = pr["body"]
    blocks = list(safe_push.BLOCK.finditer(body))
    if len(blocks) != 1 or body.count("<!-- safe_push:preflight begin") != 1 \
            or body.count("<!-- safe_push:preflight end") != 1:
        raise Refused("pre-flight: missing or malformed block")
    block = blocks[0]
    checked, against = block.groups()
    if not checked or not OID.fullmatch(checked) or not against or not OID.fullmatch(against):
        raise Refused("pre-flight: malformed head or base")
    if checked != pr["head"]:
        raise Refused("pre-flight: sha differs from the pull request head")
    sentinel = "Queue preflight visibility witness."
    visible = safe_push.visible(body[:block.start()] + sentinel + body[block.end():])
    if visible.splitlines().count(sentinel) != 1:
        raise Refused("pre-flight: block is hidden by code or HTML")
    commit(repo, against)
    if not ancestor(repo, against, base) or not ancestor(repo, against, checked):
        raise Refused("pre-flight: recorded base is not an ancestor of the head and group base")
    inner = "\n".join(block.group().splitlines()[1:-1])
    harness = re.findall(
        r"origin/main's `scripts/safe_push\.py` \(blob `([0-9a-f]{12,40})`\)",
        safe_push.visible(inner))
    if len(harness) != 1 or "full checks skipped" in inner:
        raise Refused("pre-flight: missing origin/main harness or full checks skipped")
    actual = oid(safe_push.git(repo, "rev-parse",
                              f"{against}:scripts/safe_push.py").strip(), "base harness")
    candidates = safe_push.git(repo, "rev-parse", f"--disambiguate={harness[0]}").split()
    if candidates != [actual]:
        raise Refused("pre-flight: harness blob is not the recorded base's safe_push.py")
    if pr["ref"].startswith("train/"):
        problems = body_problems(body)
        if problems:
            raise Refused("; ".join(problems))
        declared = declared_new(body)
        problems = undeclared(derive_new(repo, merge_base(repo, base, checked), checked),
                              declared)
        for row in members_table(body):
            member = commit(repo, row["head"])
            if row["no_mistakes"].startswith("passed at "):
                evidence = row["no_mistakes"].split()[2]
                if not member.startswith(evidence):
                    problems.append("Members: /no-mistakes names another head")
            mb = merge_base(repo, base, member)
            protected = any(safe_push.is_protected(path)
                            for _, path in safe_push.changed_files(repo, mb, member))
            if protected and row["security_review"].casefold().startswith("not required"):
                problems.append("Members: /security-review says Not required for protected paths")
        if problems:
            raise Refused("; ".join(problems))


def intact(repo: Path, base: str, head: str, pr: dict) -> None:
    """Check reverse application and preserve added decisions lines in their order."""
    mb = merge_base(repo, pr["head"], base)
    _, conflicts = automatic(repo, head, mb, pr["head"])
    lost = [path for path in conflicts if not safe_push.under(path, GENERATED)]
    if lost:
        raise Refused(f"not overwriting: #{pr['number']} changed lines were overwritten: "
                      + ", ".join(sorted(lost)))
    added = [line.text for line in safe_push.added_lines(repo, mb, pr["head"],
                                                      safe_push.DECISIONS)]
    if added:
        page = safe_push.git(repo, "show", f"{head}:{safe_push.DECISIONS}").splitlines()
        remaining = iter(page)
        if not all(any(line == present for present in remaining) for line in added):
            raise Refused(f"not overwriting: #{pr['number']} decisions added lines "
                          "are missing or out of order")


@contextlib.contextmanager
def revert_checkout(repo: Path, start: str):
    """Use a temporary object store and index; never change the group's checkout."""
    objects = Path(safe_push.git(repo, "rev-parse", "--git-path", "objects").strip())
    objects = (repo / objects).resolve()
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_TERMINAL_PROMPT="0", GIT_ALLOW_PROTOCOL="")
    with tempfile.TemporaryDirectory(prefix="queue-revert-") as tmp:
        root = Path(tmp)

        def git(*args):
            result = safe_push.run(["git", "-c", "core.hooksPath=/dev/null", *args],
                                   root, env=env)
            if result.returncode:
                raise ValueError("could not prepare or read the temporary revert checkout")
            return result.stdout.strip()

        git("init", "--quiet")
        (root / ".git/objects/info/alternates").write_text(str(objects) + "\n",
                                                        encoding="utf-8")
        git("update-ref", "HEAD", start)
        git("read-tree", "--reset", "-u", start)
        yield root, env, git


def exact_revert(repo: Path, pr: dict) -> None:
    """Allow only the configured App bot and precisely the named main merge reverts."""
    expected = os.environ.get("STOICHEIA_REVERT_BOT", "")
    if not expected or not expected.endswith("[bot]") or pr["author"]["type"] != "Bot" \
            or pr["author"]["login"] != expected or not pr["ref"].startswith("revert/") \
            or "auto-revert" not in pr["labels"]:
        raise Refused("auto-revert: label, revert branch and configured App bot must agree")
    text = safe_push.visible(pr["body"])
    lines = [line for line in text.splitlines() if line.startswith("Reverts:")]
    if not lines or any(not re.fullmatch(r"Reverts: [0-9a-f]{40}", line) for line in lines):
        raise Refused("auto-revert: missing or malformed Reverts lines")
    named = [line.split()[1] for line in lines]
    main = safe_push.git(repo, "rev-list", "--first-parent", pr["main"]).splitlines()
    start = merge_base(repo, pr["head"], pr["main"])
    if len(set(named)) != len(named) or any(sha not in main for sha in named):
        raise Refused("auto-revert: every named commit must be a distinct merge on main")
    if named != sorted(named, key=main.index):
        raise Refused("auto-revert: named merges must be newest first")
    for sha in named:
        if len(parents(repo, sha)) != 2 or not ancestor(repo, sha, start):
            raise Refused("auto-revert: every named commit must be a merge before its base")
    with revert_checkout(repo, start) as (root, env, git):
        for sha in named:
            result = safe_push.run(["git", "-c", "core.hooksPath=/dev/null", "revert",
                                   "--no-commit", "-m", "1", sha], root, env=env)
            if result.returncode == 1:
                raise Refused("auto-revert: named reversals do not apply cleanly")
            if result.returncode:
                raise ValueError("could not compute the automatic revert")
        wanted = git("write-tree")
    actual = safe_push.git(repo, "rev-parse", f"{pr['head']}^{{tree}}").strip()
    if actual != wanted:
        raise Refused("auto-revert: head is not the exact revert tree (extra change)")


def dated_heading(line: str):
    """Recognise the decisions page's dated level-two headings."""
    match = re.fullmatch(r"##[ \t]+(.+?)[ \t]*(?:[ \t]+#+[ \t]*)?", line)
    if not match:
        return None
    value = match.group(1)
    try:
        return datetime.date.fromisoformat(value)
    except ValueError:
        parts = value.split()
        if len(parts) != 3 or parts[1] not in MONTHS:
            return None
        try:
            return datetime.date(int(parts[2]), MONTHS.index(parts[1]) + 1, int(parts[0]))
        except ValueError:
            return None


def tree_problems(repo: Path, render: bool = False) -> list[str]:
    """Check dated decisions headings and optionally require fresh renderer output."""
    root = Path(safe_push.git(repo, "rev-parse", "--show-toplevel").strip()).resolve()
    if root != repo.resolve():
        raise ValueError("--tree must name the repository root")
    paths = safe_push.git(repo, "ls-files", "-z").split("\0")
    if not paths or paths[-1] != "" or not any(paths):
        raise ValueError("could not read tracked files")
    problems, dates = [], set()
    for rel in paths[:-1]:
        path = repo / rel
        if path.is_symlink():
            raise ValueError(f"{rel}: cannot scan a symbolic link as tracked text")
        if not path.resolve().is_relative_to(root) or not path.is_file():
            raise ValueError(f"{rel}: cannot read a tracked file")
        data = path.read_bytes()
        if b"\0" in data:
            if rel == safe_push.DECISIONS:
                raise ValueError("the decisions page is not text")
            continue
        if rel == safe_push.DECISIONS:
            for number, line in enumerate(data.decode("utf-8").splitlines(), 1):
                date = dated_heading(line)
                if date is not None:
                    if date in dates:
                        problems.append(f"{rel}:{number}: repeated dated heading: {line}")
                    dates.add(date)
    if safe_push.DECISIONS not in paths:
        raise ValueError("the tracked decisions page is missing")
    if render:
        result = safe_push.run(["python3", "scripts/render.py"], repo)
        if result.returncode:
            problems.append(f"render.py failed (exit {result.returncode})")
        status = safe_push.git(repo, "status", "--porcelain", "--untracked-files=all",
                               "--", *GENERATED)
        if status:
            problems.append("render freshness: generated files changed:\n" + status.rstrip())
    return problems


def checkout(repo: Path, head: str) -> None:
    """Require the checked commit and unchanged sources before running its commands."""
    if commit(repo, "HEAD") != head:
        raise Refused("checkout is not the supplied group head")
    changed = safe_push.git(repo, "diff", "--name-only", "-z", head, "--").split("\0")
    if any(path and not safe_push.under(path, GENERATED) for path in changed):
        raise Refused("checkout has source changes outside the supplied group head")


def gap_commands(repo: Path, checks: set[str]) -> list[list[str]]:
    """Choose each existing test once, refusing a changed test which is absent."""
    commands = set()
    for path in sorted(checks):
        if re.fullmatch(r"tests/test_[^/]+\.py", path):
            candidates = [path]
        elif path == "scripts/safe_push.py":
            candidates = ["scripts/test_safe_push.py"]
        elif re.fullmatch(r"scripts/[^/]+\.py", path):
            name = Path(path).stem
            candidates = [f"tests/test_{name}.py", f"scripts/test_{name}.py"]
            candidates = [p for p in candidates if (repo / p).is_file()]
        else:
            candidates = []
        for candidate in candidates:
            target = repo / candidate
            if not target.is_file() or target.is_symlink():
                raise Refused(f"gaps: declared test is missing or not a regular file: {candidate}")
            command = ("python3", candidate) if candidate == "scripts/test_safe_push.py" \
                else ("python3", "-I", candidate)
            commands.add(command)
    return [list(command) for command in sorted(commands)]


def gaps(repo: Path, base: str, entries: list[dict]) -> list[str]:
    """Run focused tests and report acceptance's existing proposition verdicts."""
    checks, propositions, foundations = set(), set(), set()
    for pr in entries:
        changes = [derive_new(repo, merge_base(repo, base, pr["head"]), pr["head"])]
        if pr["ref"].startswith("train/"):
            changes.append(declared_new(pr["body"]))
        for change in changes:
            checks.update(change["checks"])
            propositions.update(change["propositions"])
            foundations.update(change["foundations"])
            for rule in change["rules"]:
                print(f"gaps: declared rule: {rule}", flush=True)
    if propositions:
        source = os.environ.get("ACCEPTANCE_VERDICTS")
        if not source:
            raise ValueError("gaps: ACCEPTANCE_VERDICTS is required for proposition reports")
        from check_acceptance import read_verdicts
        report = read_verdicts(Path(source))
        for ref in sorted(propositions):
            items = report["verdicts"].get(ref)
            if not isinstance(items, dict) or not items:
                raise ValueError(f"gaps: acceptance has no items for {ref}")
            for item, verdict in sorted(items.items()):
                print(f"gaps: {ref} {item}: {verdict} (acceptance report only)", flush=True)
    if foundations:
        print("gaps: foundations covered by model and formal-model: "
              + ", ".join(sorted(foundations)), flush=True)
    problems = []
    for command in gap_commands(repo, checks):
        print("gaps: " + shlex.join(command), flush=True)
        result = safe_push.run(command, repo)
        print(result.stdout, end="", flush=True)
        print(result.stderr, end="", file=sys.stderr, flush=True)
        if result.returncode:
            problems.append(f"gaps: {shlex.join(command)} failed (exit {result.returncode})")
    return problems


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head")
    parser.add_argument("--base")
    parser.add_argument("--repo")
    parser.add_argument("--github-json", type=Path)
    parser.add_argument("--gaps", action="store_true")
    parser.add_argument("--tree", type=Path)
    parser.add_argument("--render", action="store_true")
    args = parser.parse_args(argv)
    if args.tree is not None:
        if any((args.head, args.base, args.repo, args.github_json, args.gaps)):
            parser.error("--tree accepts only --render")
    elif not all((args.head, args.base, args.repo)) or args.render:
        parser.error("group checks need --head, --base and --repo; --render belongs to --tree")
    try:
        if args.tree is not None:
            problems = tree_problems(args.tree.resolve(), args.render)
        else:
            if not SLUG.fullmatch(args.repo):
                raise ValueError("--repo must be owner/name")
            repo = Path.cwd()
            head, base = commit(repo, oid(args.head, "head")), commit(repo, oid(args.base, "base"))
            if safe_push.git(repo, "rev-parse", "--is-shallow-repository").strip() != "false":
                raise ValueError("could not read complete history: shallow repository")
            checkout(repo, head)
            entries = chain(repo, base, head, GitHub(args.repo, args.github_json))
            for pr in entries:
                if "auto-revert" in pr["labels"] or pr["ref"].startswith("revert/"):
                    exact_revert(repo, pr)
                else:
                    preflight(repo, base, pr)
                    intact(repo, base, head, pr)
            problems = gaps(repo, base, entries) if args.gaps else tree_problems(repo, True)
    except Refused as error:
        problems = [str(error)]
    except (OSError, UnicodeError, ValueError, safe_push.Refusal) as error:
        print(f"queue: could not read: {error}", file=sys.stderr)
        return 2
    except Exception as error:
        print(f"queue: could not read: unexpected {type(error).__name__}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("queue: could not read: interrupted", file=sys.stderr)
        return 2
    if problems:
        for problem in problems:
            print(f"queue: REFUSED: {problem}")
        return 1
    print("queue: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
