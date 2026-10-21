#!/usr/bin/env python3
"""Check a merge group's preserved changes, evidence, order and generated tree.

    python3 scripts/check_queue.py --head <sha> --base <sha> --repo <owner/name>
    python3 scripts/check_queue.py --gaps --head <sha> --base <sha> --repo <owner/name>
    python3 scripts/check_queue.py --tree <dir> [--render]

Group commands require a checkout of the supplied head. --tree checks the decisions page
line by line (heading_problems): a line that could render as a level-one or level-two
heading counts, in code too; its text must be plain; every year in it must stand in a
date the check reads; no two of them may contain the same date; and no HTML <h1> or
<h2> tag may stand anywhere. --render adds the generated pages' freshness. Conflict
markers are checked by S23 in check_style.py, in the check job on the same merge group.

Every merge-tree reads merge attributes from the group's base, main, never from the
group's checkout (git --attr-source). Judging a group, every file read comes from Git's
objects, the decisions page among them (page_blob), never from the checkout, which the
group's attributes shape (working-tree-encoding or a filter, say): an entry's
.gitattributes cannot change what is judged; it can shape only the checkout, and no
verdict reads the checkout. --tree reads the page in the checkout it is given,
so it exits 2 when Git gives the page an attribute that can change how a checkout writes
it (CHECKOUT_ATTRIBUTES). --gaps runs the group's own tests, in its checkout. Git 2.42 or
later: merge-tree --write-tree came in 2.38, its --merge-base in 2.40 and --attr-source
in 2.42; an older Git makes every group unreadable.

GitHub reads use gh api and gh api graphql, with GH_TOKEN inherited and never
printed. --github-json replaces that boundary completely: an object with
pull_requests and runs (REST responses keyed by number), queue (the GraphQL response),
main (the REST commits/main response), and pushes, queue_merges and main_red (lists of
REST pages, as returned by gh api --paginate --slurp: main's push and queue merge
activity, and the open issues labelled main-red). Queue entries include
pageInfo so a truncated answer cannot pass. The subject's number and the queue's
headRefOid must agree. A different queue merge subject is accepted only when its
second parent uniquely identifies a queue entry; no subject fallback is allowed
for the already merged prefix.

Reversing T with merge-base T.head merges the group with T's original base, once for
each of T's merge bases with the group's base (more than one after criss-cross merges).
A clean reverse merge alone does not prove preservation: a complete cancellation
also merges cleanly. Reapplying T must reproduce the group on every non-exempt
path. Generated files are excluded; added decisions lines must remain a
subsequence. An automatic revert instead requires an exact git revert tree,
the failed post-merge run's push range and the configured STOICHEIA_REVERT_BOT.

safe_push records abbreviated harness blobs. They must resolve unambiguously to the
full blob at the pre-flight's harness commit. The block's base must be the newest
commit of the group base's first-parent chain that the head contains, which is what
safe_push records, and its harness that base or a later commit of the same chain. Older
blocks without a harness field use their recorded base as that commit. The summary and
steps must report a passing verdict and every full check its harness runs. The block
is a declaration that anyone who can edit the pull request body can type: the judge
checks it for consistency, not as proof that a pre-flight ran.

GitHub runs the group's own copy of the workflow file, so this judge's verdict, and any
evidence check added to it, counts only while the group's .github/workflows/ci.yml still
calls it. The protection of .github/, scripts/ and tests/, and the authenticity of the
pre-flight's evidence, must be held by something a group cannot change: a ruleset
requiring code-owner review, with a CODEOWNERS file naming the owner for those paths; a
required workflow pinned to main, if the account offers one; or a status posted by an
App running main's code. The queue must not be turned on until one exists.

ACCEPTANCE_VERDICTS names the acceptance job's JSON for proposition gap reports.
Exit 0 means pass, 1 refused, and 2 unreadable. Standard library, Python 3.11+, git.
"""

from __future__ import annotations

import argparse
import ast
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
import check_train
from check_train import declared_new, derive_new

# Isolated invocation and this directory supply the judge's complete script imports.
for module in (safe_push, check_train):
    if Path(module.__file__).resolve().parent != Path(__file__).resolve().parent:
        raise ImportError("queue judge dependencies must come from its own directory")

OID = re.compile(r"[0-9a-f]{40}")
SLUG = re.compile(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+")
SUBJECT = re.compile(r"Merge pull request #([1-9][0-9]*) from \S+")
MONTHS = ("January", "February", "March", "April", "May", "June", "July",
          "August", "September", "October", "November", "December")
# Rule (d) reads the decisions page line by line, never as blocks, so it can only
# over-approximate what renders (heading_problems). Lines end as CommonMark's do, and a
# line of spaces and tabs is blank. Before a line is read, its leading whitespace and
# container markers are taken off, again and again: block quote markers (>), list
# markers (-, * or +, or digits then . or ), each followed by whitespace or the end),
# task markers ([ ], [x] or [X], followed by whitespace or the end) and footnote markers
# ([^label]:). A list number that cannot open a list there, or a footnote marker, may be
# a paragraph's own text, so the words and characters of those two (CONTAINER's group
# text) are read with the rest of the line too, wherever the line is part of an
# underlined heading's text. No pattern here backtracks over a line: each match starts
# where the last ended, and a closing run of # is taken off with str.rstrip (_atx_text).
LINE_END = re.compile(r"\r\n|\r|\n")
BOM = "\N{BYTE ORDER MARK}"  # which a renderer skips at the start of a page
BLANK = re.compile(r"[ \t]*")
CONTAINER = re.compile(r"\s+|>|[-*+](?=\s|$)|\[[ xX]\](?=\s|$)"
                       r"|(?P<text>[0-9]+[.)](?=\s|$)|\[\^[^\]]*\]:)")
OPENER = re.compile(r"#{1,2}(?=[ \t]|$)")
ANY_OPENER = re.compile(r"#{1,6}(?=[ \t]|$)")
THEMATIC = re.compile(r" {0,3}(?:(?:\*[ \t]*){3,}|(?:_[ \t]*){3,}|(?:-[ \t]*){3,})")
# A heading's text is plain: ASCII letters, digits, spaces and . , : ; ' ( ) - / only.
PLAIN = frozenset("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
                  " .,:;'()-/")
NOT_PLAIN = re.compile("[^" + re.escape("".join(sorted(PLAIN))) + "]")
# A date is three neighbouring words: a day (with st, nd, rd or th, or not), a month
# and a year, day first or month first; or the year, month and day in numbers. A year a
# heading might be dated by is four digits from 1900 to 2199, standing apart from other
# digits, inside a word or alone; each must be a date's year, read in its own line.
WORD = re.compile(r"[A-Za-z0-9]+")
DAY = re.compile(r"(?i)([0-9]{1,2})(?:st|nd|rd|th)?")
NUMBER = re.compile(r"[0-9]{1,2}")
YEAR = re.compile(r"[0-9]{4}")
YEARLIKE = re.compile(r"(?<![0-9])(?:19|20|21)[0-9]{2}(?![0-9])")
ORDERED_TEXT = re.compile(r"(?:^| )([0-9]+)[.)]$")
# An HTML heading tag of level one or two, which this reading refuses rather than reads.
RAW_HEADING = re.compile(r"(?i)<h[12](?=[\s/>]|$)")
GENERATED = (*safe_push.GENERATED, "book/", safe_push.DECISIONS)
# The attributes with which Git may write a file to a checkout other than as its blob
# holds it; --tree, which reads the checkout, refuses to read a page that has any of them.
CHECKOUT_ATTRIBUTES = ("working-tree-encoding", "filter", "ident", "text", "eol", "crlf")
PREFLIGHT = re.compile(
    r"(?ms)^<!-- safe_push:preflight begin sha=([0-9a-f]{40}) base=([0-9a-f]{40})"
    r"(?: harness=([0-9a-f]{40}))? -->[ \t\r]*$"
    r"(?:(?!<!-- safe_push:preflight begin).)*?"
    r"^<!-- safe_push:preflight end -->[ \t\r]*$")
DECISION_HUNK = re.compile(
    r"^@@ -([0-9]+)(?:,([0-9]+))? \+[0-9]+(?:,([0-9]+))? @@")


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
                return value[str(number)] if kind in ("pull_requests", "runs") else value
            except (KeyError, TypeError):
                raise ValueError(f"GitHub fixture lacks {kind}") from None
        if not os.environ.get("GH_TOKEN"):
            raise ValueError("GitHub: GH_TOKEN is not set")
        if kind == "queue":
            owner, name = self.repo.split("/")
            query = (
                "query($owner:String!,$name:String!){repository(owner:$owner,name:$name){"
                'mergeQueue(branch:"main"){entries(first:100){'
                "nodes{position enqueuer{__typename login} "
                "pullRequest{number headRefOid editor{__typename login}}} "
                "pageInfo{hasNextPage}}}}}"
            )
            command = ["gh", "api", "graphql", "-f", f"query={query}",
                       "-f", f"owner={owner}", "-f", f"name={name}"]
        elif kind == "main_red":
            endpoint = f"repos/{self.repo}/issues?state=open&labels=main-red&per_page=100"
            command = ["gh", "api", "--method", "GET", "--paginate", "--slurp", endpoint]
        elif kind in ("pushes", "queue_merges"):
            activity = "push" if kind == "pushes" else "merge_queue_merge"
            endpoint = (f"repos/{self.repo}/activity?ref=refs/heads/main"
                        f"&activity_type={activity}&per_page=100")
            command = ["gh", "api", "--method", "GET", "--paginate", "--slurp", endpoint]
        else:
            endpoints = {"main": "commits/main", "pull_requests": f"pulls/{number}",
                         "runs": f"actions/runs/{number}"}
            if kind not in endpoints:
                raise ValueError("GitHub: unknown read")
            endpoint = endpoints[kind]
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


def merge_bases(repo: Path, left: str, right: str, entry: int) -> list[str]:
    """Every merge base of an entry's commit with another, more than one after
    criss-cross merges; none, or an unreadable answer, is unreadable, naming the entry."""
    result = safe_push.run(["git", "merge-base", "--all", left, right], repo)
    values = result.stdout.split() if result.returncode == 0 else []
    if result.returncode not in (0, 1) or not values:
        raise ValueError(f"#{entry}: could not read a merge base")
    return [oid(value, f"#{entry}'s merge base") for value in values]


def ancestor(repo: Path, older: str, newer: str) -> bool:
    result = safe_push.run(["git", "merge-base", "--is-ancestor", older, newer], repo)
    if result.returncode not in (0, 1):
        raise ValueError("could not read ancestry")
    return result.returncode == 0


def automatic(repo: Path, left: str, right: str, attrs: str,
              base: str | None = None) -> tuple:
    """Read the automatic tree and every conflicted path, including binary files. Merge
    attributes are read from `attrs`, main's commit, never from the checkout."""
    args = ["git", f"--attr-source={attrs}", "merge-tree", "--write-tree", "--name-only",
            "-z", "--no-messages"]
    if base:
        args.append(f"--merge-base={base}")
    result = safe_push.run([*args, left, right], repo)
    if result.returncode not in (0, 1):
        raise ValueError("could not read an automatic merge (Git 2.42 or later is needed)")
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


def queue_actors(answer) -> dict[int, tuple[bool, bool]]:
    """Whether a bot put each queued pull request in the queue, and whether a bot last
    edited its body (False when nobody has), read by GraphQL's type of the actor: GraphQL
    spells a bot's login without the "[bot]" REST adds, so logins are not compared.
    Missing or malformed data refuses."""
    try:
        actors = {}
        for node in answer["data"]["repository"]["mergeQueue"]["entries"]["nodes"]:
            enqueuer, editor = node["enqueuer"], node["pullRequest"]["editor"]
            for actor, may_be_none in ((enqueuer, False), (editor, True)):
                if actor is None and may_be_none:
                    continue
                if not isinstance(actor, dict) or not isinstance(actor["login"], str) \
                        or not actor["login"] or not isinstance(actor["__typename"], str):
                    raise ValueError
            actors[node["pullRequest"]["number"]] = (
                enqueuer["__typename"] == "Bot",
                editor is not None and editor["__typename"] == "Bot")
        return actors
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read who queued and edited each entry") from None


def ordinary_entry(pr: dict, actors: dict, repo_slug: str) -> None:
    """An entry that is not an automatic revert: its head is in this repository, and no
    bot (the revert App's above all) wrote it, put it in the queue or last edited its
    body, so the App's key cannot land anything but the revert the queue checks it to
    be. Trains are written and queued by people."""
    if pr["head_repo"] != repo_slug:
        raise Refused(f"#{pr['number']}: its head is not in {repo_slug}")
    if pr["author"]["type"] == "Bot":
        raise Refused(f"#{pr['number']}: a bot wrote, queued or edited a pull request that "
                      "is not an automatic revert (a bot wrote it)")
    if pr["state"] == "MERGED":
        # Already on main: GitHub's queue no longer lists it, so who queued it cannot be
        # read here; it was judged by its own group when it merged.
        return
    if pr["number"] not in actors:
        raise ValueError(f"GitHub: #{pr['number']} is open but not in the queue read")
    queued_by_bot, edited_by_bot = actors[pr["number"]]
    if queued_by_bot or edited_by_bot:
        raise Refused(f"#{pr['number']}: a bot wrote, queued or edited a pull request that "
                      "is not an automatic revert")


def pull_request(answer, number: int) -> dict:
    """Read the required fields of a REST pull request without defaulting missing data."""
    try:
        if type(answer["number"]) is not int or answer["number"] != number:
            raise ValueError
        head = oid(answer["head"]["sha"], "pull request head")
        ref, body = answer["head"]["ref"], answer["body"]
        head_repo = answer["head"]["repo"]["full_name"]
        if not isinstance(head_repo, str) or not head_repo:
            raise ValueError
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
                    head_repo=head_repo,
                    labels={label["name"] for label in labels},
                    state="MERGED" if answer["merged"] else answer["state"].upper(),
                    merged=oid(answer["merge_commit_sha"], "merged commit")
                    if answer["merged"] else None)
    except (KeyError, TypeError, ValueError):
        raise ValueError(f"GitHub: could not read pull request #{number}") from None


def chain(repo: Path, base: str, head: str, api: GitHub, queue_answer=None) -> list[dict]:
    """Identify the first-parent chain and prove its queue order and merge trees."""
    queued = queue_entries(queue_answer if queue_answer is not None else api.read("queue"))
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
        tree, conflicts = automatic(repo, *pp, attrs=base)
        if conflicts or tree != safe_push.git(repo, "rev-parse",
                                              f"{current}^{{tree}}").strip():
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


def harness_check_names(repo: Path, harness_commit: str) -> set[str]:
    """The names of the full checks the harness at `harness_commit` runs: its CHECKS and
    NEGATIVE lists, read from its source by ast (never run), so that a train pre-flighted
    before a check was added is judged by the checks its harness had, and a group's own
    harness never decides what its pre-flight needed."""
    source = safe_push.show(repo, harness_commit, "scripts/safe_push.py")
    if source is None:
        raise Refused("pre-flight: the recorded harness commit has no scripts/safe_push.py")
    try:
        tree = ast.parse(source)
    except SyntaxError:
        raise Refused("pre-flight: the recorded harness could not be read") from None
    names: dict[str, list[str]] = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id in ("CHECKS", "NEGATIVE"):
            if not isinstance(node.value, ast.List) or node.targets[0].id in names:
                raise Refused("pre-flight: the recorded harness's checks could not be read")
            found = []
            for elt in node.value.elts:
                if not (isinstance(elt, ast.Tuple) and elt.elts
                        and isinstance(elt.elts[0], ast.Constant)
                        and isinstance(elt.elts[0].value, str)):
                    raise Refused("pre-flight: the recorded harness's checks could not be read")
                found.append(elt.elts[0].value)
            names[node.targets[0].id] = found
    if set(names) != {"CHECKS", "NEGATIVE"} or not all(names.values()):
        raise Refused("pre-flight: the recorded harness's checks could not be read")
    return {f"4. {name}" for name in names["CHECKS"] + names["NEGATIVE"]}


def preflight_steps(inner: str, head: str, base: str,
                    expected: set[str] | None = None) -> None:
    """Read one passing verdict and a steps table whose passing rows include every full
    check expected, with no failing row: a record standing in for them does not count.
    The full checks expected are those of the harness that ran the pre-flight."""
    visible = safe_push.visible(inner)
    verdicts = [line.strip().strip("*") for line in visible.splitlines()
                if re.match(r"(?:\*\*)?(?:Pre-flight )?Verdict:", line.strip(), re.I)]
    if len(verdicts) != 1 or not re.fullmatch(
            r"(?:Pre-flight )?Verdict: (?:\*\*)?PASS(?:\*\*)?\.?", verdicts[0], re.I):
        raise Refused("pre-flight: summary must give one passing verdict")
    lines = [line.strip() for line in visible.splitlines() if line.strip().startswith("|")]
    if any(not line.endswith("|") for line in lines):
        raise Refused("pre-flight: malformed steps table row")
    rows = [[cell.strip().strip("`*") for cell in line[1:-1].split("|")] for line in lines]
    if len(rows) < 3 or rows[0] != ["Step", "Outcome", "Seconds"] \
            or len(rows[1]) != 3 \
            or not all(re.fullmatch(r":?-{3,}:?", cell) for cell in rows[1]):
        raise Refused("pre-flight: missing or malformed steps table")
    steps = []
    for row in rows[2:]:
        if len(row) != 3 or row[1].casefold() not in {"ok", "pass", "fail", "skip", "note"} \
                or not re.fullmatch(r"(?:[0-9]+(?:\.[0-9]+)?)?", row[2]):
            raise Refused("pre-flight: malformed steps table row")
        if row[1].casefold() == "fail":
            raise Refused("pre-flight: steps table contains a FAIL row")
        steps.append((row[0], row[1].casefold()))
    if len({name for name, _ in steps}) != len(steps):
        raise Refused("pre-flight: duplicate steps table row")
    if expected is None:
        expected = {f"4. {name}" for name, _ in (*safe_push.CHECKS, *safe_push.NEGATIVE)}
    passed = {name for name, outcome in steps if outcome in {"ok", "pass"}}
    complete = any({name + suffix for name in expected} <= passed
                   for suffix in ("", " (the commit's checks)"))
    if not complete:
        raise Refused("pre-flight: steps must run the full checks")


def preflight(repo: Path, base: str, pr: dict) -> None:
    """Require one visible pre-flight with the exact head and recorded harness."""
    body = pr["body"]
    blocks = list(PREFLIGHT.finditer(body))
    if len(blocks) != 1 or body.count("<!-- safe_push:preflight begin") != 1 \
            or body.count("<!-- safe_push:preflight end") != 1:
        raise Refused("pre-flight: missing or malformed block")
    block = blocks[0]
    checked, against, harness_commit = block.groups()
    harness_commit = harness_commit or against
    if checked != pr["head"]:
        raise Refused("pre-flight: sha differs from the pull request head")
    sentinel = "Queue preflight visibility witness."
    visible = safe_push.visible(body[:block.start()] + sentinel + body[block.end():])
    if visible.splitlines().count(sentinel) != 1:
        raise Refused("pre-flight: block is hidden by code or HTML")
    commit(repo, against)
    commit(repo, harness_commit)
    # Main's tips, newest first: the base compared against was one of them, and the
    # harness that ran is that base or a later tip, never an older one.
    main_chain = safe_push.git(repo, "rev-list", "--first-parent", base).split()
    if against not in main_chain:
        raise Refused("pre-flight: recorded base was never main (not on the first-parent "
                      "chain of the group base)")
    if not ancestor(repo, against, checked):
        raise Refused("pre-flight: recorded base is not an ancestor of the head")
    # safe_push records origin/main's tip, which the head contains: the newest commit of
    # main's chain that the head holds. An older one is a pre-flight of another head.
    held = set(safe_push.git(repo, "rev-list", checked).split())
    if next((tip for tip in main_chain if tip in held), None) != against:
        raise Refused("pre-flight: recorded base is not the newest commit of main's "
                      "first-parent chain that the head contains")
    if harness_commit not in main_chain:
        raise Refused("pre-flight: harness commit was never main (not on the first-parent "
                      "chain of the group base)")
    if main_chain.index(harness_commit) > main_chain.index(against):
        raise Refused("pre-flight: harness commit is older than the recorded base")
    inner = "\n".join(block.group().splitlines()[1:-1])
    # The harness is named by the summary's first line, which safe_push writes; a note
    # further down (a record that stood in, say) may quote the same words again.
    summary = next((line for line in safe_push.visible(inner).splitlines() if line.strip()),
                   "")
    named = re.match(
        r"^Pre-flight of `([0-9a-f]{7,40})` against origin/main `([0-9a-f]{7,40})`,",
        summary)
    if not named or not checked.startswith(named.group(1)) \
            or not against.startswith(named.group(2)):
        raise Refused("pre-flight: visible summary must name the recorded head and base")
    harness = re.findall(
        r"origin/main's `scripts/safe_push\.py` \(blob `([0-9a-f]{12,40})`\)", summary)
    if len(harness) != 1 or "full checks skipped" in inner:
        raise Refused("pre-flight: missing origin/main harness or full checks skipped")
    actual = oid(safe_push.git(repo, "rev-parse",
                               f"{harness_commit}:scripts/safe_push.py").strip(),
                 "harness blob")
    if safe_push.git(repo, "cat-file", "-t", actual).strip() != "blob":
        raise Refused("pre-flight: the recorded harness is not a blob")
    candidates = safe_push.git(repo, "rev-parse", f"--disambiguate={harness[0]}").split()
    if candidates != [actual]:
        raise Refused("pre-flight: harness blob is not the recorded harness commit's "
                      "safe_push.py")
    preflight_steps(inner, checked, against, harness_check_names(repo, harness_commit))
    if pr["ref"].startswith("train/"):
        try:
            problems = check_train.check_train(repo, base=against, sha=checked, body=body)
        except ValueError:
            problems = check_train.body_problems(body)
            if problems:
                raise Refused("; ".join(problems)) from None
            raise
        if problems:
            raise Refused("; ".join(problems))


def hand_written_intact(repo: Path, path: str, group: str, mb: str, train: str) -> bool:
    """Revert and reapply a train's change to the hand-written part of `path`, the file
    less its generated regions, by git merge-file; true when the group keeps it whole."""
    pattern = safe_push.GENERATED_REGIONS[path]

    def text(rev):
        return pattern.sub("", safe_push.show(repo, rev, path) or "")

    g, b, t = text(group), text(mb), text(train)
    if t == b:
        return True

    def merge3(ours, ancestor, theirs):
        with tempfile.TemporaryDirectory(prefix="queue-merge-") as tmp:
            files = []
            for name, value in (("ours", ours), ("base", ancestor), ("theirs", theirs)):
                file = Path(tmp) / name
                file.write_text(value, encoding="utf-8")
                files.append(str(file))
            result = safe_push.run(["git", "merge-file", "-p", "-q", *files], repo)
        if result.returncode < 0 or result.returncode > 127:
            raise ValueError(f"could not merge the hand-written part of {path}")
        return result.returncode == 0, result.stdout

    clean, reverted = merge3(g, t, b)
    if not clean:
        return False
    clean, reapplied = merge3(reverted, b, t)
    return clean and reapplied == g


def decision_additions(repo: Path, old: str, new: str) -> dict[tuple[int, int], list[str]]:
    """Decision lines added from `old` to `new`, grouped by their old-file hunk anchor."""
    output = safe_push.git(
        repo, "diff", "--no-color", "--text", "--no-ext-diff", "--no-textconv",
        "--no-renames", "--unified=0", old, new, "--", safe_push.DECISIONS,
        binary=True).decode("utf-8", errors="replace")
    additions: dict[tuple[int, int], list[str]] = {}
    old_left = new_left = 0
    anchor = None
    for line in output.split("\n"):
        if old_left > 0 or new_left > 0:
            if line.startswith("+"):
                additions[anchor].append(line[1:])
                new_left -= 1
            elif line.startswith("-"):
                old_left -= 1
            elif not line.startswith("\\"):
                old_left = new_left = 0
            continue
        match = DECISION_HUNK.match(line)
        if match:
            old_left = int(match.group(2)) if match.group(2) is not None else 1
            new_left = int(match.group(3)) if match.group(3) is not None else 1
            anchor = (int(match.group(1)), old_left)
            additions.setdefault(anchor, [])
    return {anchor: lines for anchor, lines in additions.items() if lines}


def intact(repo: Path, base: str, head: str, pr: dict) -> None:
    """Require reversal then reapplication to preserve the non-exempt group tree, against
    every merge base of the entry with the group's base: after criss-cross merges there
    is more than one, and each must preserve it, so more bases never mean less checked.
    Merge attributes are read from the group's base."""
    for mb in merge_bases(repo, pr["head"], base, pr["number"]):
        reversed_tree, conflicts = automatic(repo, head, mb, attrs=base, base=pr["head"])
        # merge-tree takes commits for its sides. This object has no ref or checkout.
        reversed_commit = oid(safe_push.git(
            repo, "-c", "user.name=Queue integrity", "-c", "user.email=queue@example.invalid",
            "commit-tree", reversed_tree, "-m", "Queue reverse application").strip(),
            "reverse application commit")
        reapplied, forward_conflicts = automatic(repo, reversed_commit, pr["head"],
                                                 attrs=base, base=mb)
        changed = {path for _, path in safe_push.changed_files(repo, head, reapplied)}
        lost = [path for path in set(conflicts) | set(forward_conflicts) | changed
                if not safe_push.under(path, GENERATED)]
        # README.md and docs/PROGRAM.md are generated only between their markers: the
        # rest, written by hand, is held to the same revert and reapply, read with the
        # markers' regions taken out.
        lost += [path for path in safe_push.GENERATED_REGIONS
                 if not hand_written_intact(repo, path, head, mb, pr["head"])]
        if lost:
            raise Refused(f"not overwriting: #{pr['number']} changed lines were "
                          "overwritten: " + ", ".join(sorted(lost)))
        added = decision_additions(repo, mb, pr["head"])
        if added:
            present = decision_additions(repo, mb, head)
            preserved = True
            for anchor, lines in added.items():
                remaining = iter(present.get(anchor, []))
                if not all(any(line == candidate for candidate in remaining)
                           for line in lines):
                    preserved = False
                    break
            if not preserved:
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


def failed_push(api: GitHub, run_id: int) -> tuple[str, str]:
    """Find the failed main post-merge run's exact push, reading every activity page."""
    run = api.read("runs", run_id)
    try:
        if type(run["id"]) is not int or run["id"] != run_id:
            raise ValueError
        after = oid(run["head_sha"], "failed run head")
        if any(run[key] != value for key, value in (
                ("path", ".github/workflows/post-merge.yml"), ("event", "push"),
                ("head_branch", "main"), ("conclusion", "failure"))):
            raise Refused("auto-revert: run must be a failed post-merge push on main")
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read the failed run") from None
    found = set()
    for kind, activity_type in (("pushes", "push"), ("queue_merges", "merge_queue_merge")):
        pages = api.read(kind)
        if not isinstance(pages, list) or not pages:
            raise ValueError("GitHub: could not read main activity pages")
        for page in pages:
            if not isinstance(page, list):
                raise ValueError("GitHub: could not read a main activity page")
            for activity in page:
                try:
                    if activity["ref"] != "refs/heads/main" \
                            or activity["activity_type"] != activity_type:
                        raise ValueError
                    before = oid(activity["before"], "push before")
                    pushed = oid(activity["after"], "push after")
                except (KeyError, TypeError, ValueError):
                    raise ValueError("GitHub: could not read main push activity") from None
                if pushed == after:
                    found.add((before, after))
    if len(found) != 1:
        raise Refused("auto-revert: failed run's push is missing or ambiguous in main activity")
    return found.pop()


def red_issue_names(pages, run_id: int) -> None:
    """Require an open issue labelled main-red that names the failed run: the issue the
    post-merge workflow opened, which landing waits on; so an old failure, whose issue
    was closed or whose label was cleared when main passed again, admits no revert."""
    try:
        if not isinstance(pages, list) or not all(isinstance(page, list) for page in pages):
            raise ValueError
        named = False
        pattern = re.compile(r"/actions/runs/%d(?![0-9])" % run_id)
        for issue in (issue for page in pages for issue in page):
            if not isinstance(issue["body"] or "", str) or issue["state"] != "open" \
                    or not any(label["name"] == "main-red" for label in issue["labels"]):
                raise ValueError
            if "pull_request" not in issue and pattern.search(issue["body"] or ""):
                named = True
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read the open main-red issues") from None
    if not named:
        raise Refused("auto-revert: no open main-red issue names the failed run")


def exact_revert(repo: Path, pr: dict, api: GitHub) -> None:
    """Require the configured bot and exactly the failed run's main merge reversals."""
    expected = os.environ.get("STOICHEIA_REVERT_BOT", "")
    if not expected or not expected.endswith("[bot]") or pr["author"]["type"] != "Bot" \
            or pr["author"]["login"] != expected or not re.fullmatch(r"revert/\S+", pr["ref"]) \
            or "auto-revert" not in pr["labels"]:
        raise Refused("auto-revert: label, revert branch and configured App bot must agree")
    text = safe_push.visible(pr["body"])
    lines = [line for line in text.splitlines() if line.startswith("Reverts:")]
    if not lines or any(not re.fullmatch(r"Reverts: [0-9a-f]{40}", line) for line in lines):
        raise Refused("auto-revert: missing or malformed Reverts lines")
    named = [line.split()[1] for line in lines]
    runs = [line for line in text.splitlines() if line.startswith("Failed run:")]
    if len(runs) != 1 or not re.fullmatch(r"Failed run: [1-9][0-9]*", runs[0]):
        raise Refused("auto-revert: expected exactly one Failed run line")
    run_id = int(runs[0].split()[2])
    before, after = failed_push(api, run_id)
    main = safe_push.git(repo, "rev-list", "--first-parent", pr["main"]).splitlines()
    starts = merge_bases(repo, pr["head"], pr["main"], pr["number"])
    if len(starts) != 1:
        raise Refused(f"auto-revert: #{pr['number']} has more than one merge base with main")
    start = starts[0]
    if len(set(named)) != len(named) or any(sha not in main for sha in named):
        raise Refused("auto-revert: every named commit must be a distinct merge on main")
    if named != sorted(named, key=main.index):
        raise Refused("auto-revert: named merges must be newest first")
    for sha in named:
        if len(parents(repo, sha)) != 2 or not ancestor(repo, sha, start):
            raise Refused("auto-revert: every named commit must be a merge before its base")
    if before not in main or after not in main or main.index(after) >= main.index(before):
        raise Refused("auto-revert: failed push range is not on main's first-parent chain")
    expected_merges = []
    for sha in main[main.index(after):main.index(before)]:
        pp = parents(repo, sha)
        if len(pp) not in (1, 2):
            raise Refused("auto-revert: failed push has an unexpected merge shape")
        if len(pp) == 2:
            expected_merges.append(sha)
    if named != expected_merges:
        raise Refused("auto-revert: Reverts lines do not equal the failed push's merges")
    if pr["ref"] != f"revert/{after[:12]}":
        raise Refused("auto-revert: the branch must be revert/<the failed push's 12 hex>")
    red_issue_names(api.read("main_red"), run_id)
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


def _stripped(line: str) -> tuple[str, str]:
    """A line without its leading whitespace and container markers, taken off again and
    again, each match starting where the last ended; and before it, the list numbers and
    footnote markers taken off, joined by spaces, which may be the line's own text."""
    position, kept = 0, []
    while (match := CONTAINER.match(line, position)) and match.end() > position:
        if match.group("text"):
            kept.append(match.group())
        position = match.end()
    return " ".join(kept), line[position:]


def _atx_text(rest: str) -> str:
    """The text of a line that begins with one or two #, from what follows them: without
    the spaces and tabs around it, and without a closing run of # that follows a space
    or a tab, or that is the whole text."""
    text = rest.strip(" \t")
    bare = text.rstrip("#")
    if not bare:
        return ""
    return bare.rstrip(" \t") if bare != text and bare[-1] in " \t" else text


def _underline(stripped: str, line: str) -> bool:
    """Whether a line that is not blank is, once stripped, a run of = or of -, of any
    length, with whitespace after it. A lone -, which stripping takes for a list
    marker, is one too: then the line's last character but whitespace is that -."""
    core = stripped.rstrip()
    if not core:
        return line.rstrip().endswith("-")
    return not core.strip("=") or not core.strip("-")


def _indent(line: str) -> int:
    """The CommonMark column of the first non-space-or-tab character."""
    column = 0
    for character in line:
        if character == " ":
            column += 1
        elif character == "\t":
            column += 4 - column % 4
        else:
            break
    return column


def _continues_paragraph(line: str, stripped: str, opening: bool) -> bool:
    """Whether the line can leave a paragraph open for the following source line."""
    return bool(stripped.rstrip(" \t")) and not ANY_OPENER.match(stripped) \
        and not _underline(stripped, line) and not THEMATIC.fullmatch(line) \
        and not (opening and _indent(line) >= 4)


def _month(word: str) -> int | None:
    """A month's number from its English name or first three letters, in any case."""
    word = word.casefold()
    for number, name in enumerate(MONTHS, 1):
        if word in (name.casefold(), name[:3].casefold()) or (number, word) == (9, "sept"):
            return number
    return None


def _date(first: str, second: str, third: str) -> datetime.date | None:
    """The date three neighbouring words name, or None: a day, a month and a year, day
    first or month first, or the year, month and day in numbers (ISO's order)."""
    try:
        if YEAR.fullmatch(first) and NUMBER.fullmatch(second) and NUMBER.fullmatch(third):
            return datetime.date(int(first), int(second), int(third))
        if YEAR.fullmatch(third):
            if (day := DAY.fullmatch(first)) and (month := _month(second)):
                return datetime.date(int(third), month, int(day.group(1)))
            if (month := _month(first)) and (day := DAY.fullmatch(second)):
                return datetime.date(int(third), month, int(day.group(1)))
    except ValueError:
        pass
    return None


def heading_dates(text: str) -> list[datetime.date]:
    """Every date a heading's text contains, once each, in the order found."""
    words = WORD.findall(text)
    found = (_date(*words[at:at + 3]) for at in range(len(words) - 2))
    return list(dict.fromkeys(date for date in found if date))


def undated_year(text: str) -> str | None:
    """The first word of the text that holds a year (YEARLIKE) but is no date's year, as
    heading_dates reads the text's dates, or None: so that a date written in a way this
    check does not read (20/10/2026, the 20th of October 2026) refuses, never passes."""
    if not YEARLIKE.search(text):
        return None
    words = WORD.findall(text)
    years = set()
    for at in range(len(words) - 2):
        if _date(*words[at:at + 3]):
            years.add(at if YEAR.fullmatch(words[at]) else at + 2)
    return next((word for at, word in enumerate(words)
                 if at not in years and YEARLIKE.search(word)), None)


def heading_problems(page: str) -> list[str]:
    """Rule (d), read line by line, never as the page renders, so that it can only
    over-approximate: a line that could render as a level-one or level-two heading
    counts wherever it stands, in code, HTML and every container too.

    Each line is read stripped (_stripped). One that begins with one or two # followed
    by a space, a tab or the end is a heading, its text what follows (_atx_text). One
    that is a run of = or of - (_underline), under one or more lines that are not blank,
    underlines a heading whose text is every line back to the previous blank line, each
    stripped, with its list numbers and footnote markers before it, joined by spaces.
    Every heading's text must be plain (PLAIN): any other character refuses the page,
    naming the line. Every year in it must be a date's year (undated_year), read in the
    year's own line as stripped, since a heading's text may begin at any of its lines and
    a list number or footnote marker may be a container; a year in one of those is no
    date's. Any other year refuses the page, naming the line. A heading is dated when its
    text contains a date (heading_dates), read in the lines both as stripped and with
    their list numbers and footnote markers, and two headings with the same date refuse
    the page, naming both. A later underline's text holds an earlier one's, so two
    underlines in one stretch of lines repeat the first's dates. An HTML <h1> or <h2> tag
    anywhere refuses too. Each line is read a bounded number of times, and a stretch's
    text is never joined: its dates are read word by word as it grows."""
    problems: list[str] = []
    first: dict[datetime.date, str] = {}

    def spoken(date: datetime.date) -> str:
        return f"{date.day} {MONTHS[date.month - 1]} {date.year}"

    def dated(dates, where: str) -> None:
        for date in dates:
            if date in first:
                problems.append(f"{safe_push.DECISIONS}:{where}: repeated dated heading: "
                                f"{spoken(date)} (first at {safe_push.DECISIONS}:"
                                f"{first[date]})")
            else:
                first[date] = where

    def readable(number: int, text: str, kept: str = "", paragraph: bool = False) -> None:
        # `kept`, the line's list numbers and footnote markers, may be its own text or
        # its containers': it is read as text for plainness, and no year in it is dated.
        if odd := NOT_PLAIN.search(f"{kept} {text}" if kept else text):
            problems.append(f"{safe_push.DECISIONS}:{number}: a line that could render as a "
                            f"heading, or as part of one, holds {odd.group()!r} "
                            f"(U+{ord(odd.group()):04X}), which is not plain: write it with "
                            "ASCII letters, digits, spaces and . , : ; ' ( ) - / only")
        year = next((word for word in WORD.findall(kept) if YEARLIKE.search(word)), None)
        marker = ORDERED_TEXT.search(kept)
        dated_text = (f"{kept} {text}" if paragraph and marker
                      and int(marker.group(1)) != 1 and year is None else text)
        if (year := year or undated_year(dated_text)) is not None:
            problems.append(f"{safe_push.DECISIONS}:{number}: a line that could render as a "
                            f"heading, or as part of one, holds {year!r}, a year in no date "
                            "this check reads: write a heading's date in its line as 20 "
                            "October 2026, October 20, 2026 or 2026-10-20")

    # The stretch of lines that are not blank since the last blank one: its first line,
    # the last words of its lines as stripped and of its lines with their list numbers
    # and footnote markers (one list, until such a marker makes them differ, and again
    # once a line without one has given both its last two words), its dates in order
    # and as a set, how many an underline has noted, its lines since its last underline
    # (not yet read as a heading's), and its last underline, with whether that
    # underline's text was dated.
    start = last = None
    words: list[str] = []
    own_words = words
    dates: list[datetime.date] = []
    held: set[datetime.date] = set()
    noted = 0
    unread: list[tuple[int, str, str, bool]] = []
    continues = False
    for number, line in enumerate(LINE_END.split(page.removeprefix(BOM)), 1):
        if RAW_HEADING.search(line):
            problems.append(f"{safe_push.DECISIONS}:{number}: an HTML heading tag (<h1> or "
                            "<h2>), which this check does not read: write the heading in "
                            "Markdown")
        if BLANK.fullmatch(line):
            start = last = None
            words, dates, held, noted, unread = [], [], set(), 0, []
            own_words = words
            continues = False
            continue
        kept, stripped = _stripped(line)
        opening = start is None
        paragraph = continues
        if opener := OPENER.match(stripped):
            text = _atx_text(stripped[opener.end():])
            readable(number, text)
            dated(heading_dates(text), str(number))
        elif start is not None and _underline(stripped, line):
            where = f"{start}-{number}"
            for read in unread:
                readable(*read)
            unread = []
            if last is not None and last[1]:
                problems.append(f"{safe_push.DECISIONS}:{where}: repeated dated heading: "
                                f"{spoken(dates[0])} (first at {safe_push.DECISIONS}:"
                                f"{last[0]}, whose text this one holds)")
            dated(dates[noted:], where)
            noted, last = len(dates), (where, bool(dates))
        if start is None:
            start = number
        text = stripped.rstrip(" \t")
        unread.append((number, text, kept, paragraph))
        found = WORD.findall(text)
        streams = [(words, found)]
        if kept or own_words is not words:
            if own_words is words:
                own_words = list(words)
            streams.append((own_words, WORD.findall(kept) + found if kept else found))
        for stream, new in streams:
            for word in new:
                if len(stream) == 3:
                    del stream[0]
                stream.append(word)
                if len(stream) == 3 and (date := _date(*stream)) and date not in held:
                    held.add(date)
                    dates.append(date)
        if not kept and len(found) >= 2:
            own_words = words
        continues = _continues_paragraph(line, stripped, opening)
    return problems


def _page_text(data: bytes) -> str:
    """The decisions page's text, which must be UTF-8 without a NUL."""
    if b"\0" in data:
        raise ValueError("the decisions page is not text")
    return data.decode("utf-8")


def page_blob(repo: Path, head: str) -> str:
    """The decisions page at `head` as its blob holds it: a regular file (100644), read
    from the object store by cat-file, so that no attribute of the group's checkout
    (working-tree-encoding, a filter) stands between the rule and what GitHub shows."""
    entry = safe_push.git(repo, "ls-tree", "-z", "--full-tree", head, "--",
                          safe_push.DECISIONS)
    match = re.fullmatch(r"100644 blob ([0-9a-f]{40,64})\t" + re.escape(safe_push.DECISIONS)
                         + "\0", entry)
    if not match:
        raise ValueError("the decisions page at the group head is not a regular file")
    return _page_text(safe_push.git(repo, "cat-file", "blob", match.group(1), binary=True))


def checkout_attributes(repo: Path) -> list[str]:
    """Each attribute of CHECKOUT_ATTRIBUTES that Git gives the decisions page, set, unset
    or with a value, as attribute=value; an unreadable answer raises ValueError."""
    out = safe_push.git(repo, "check-attr", "-z", *CHECKOUT_ATTRIBUTES, "--",
                        safe_push.DECISIONS)
    fields = out.split("\0")
    if len(fields) != 3 * len(CHECKOUT_ATTRIBUTES) + 1 or fields[-1] != "":
        raise ValueError("could not read the decisions page's attributes")
    found = []
    for at, name in enumerate(CHECKOUT_ATTRIBUTES):
        path, attribute, value = fields[3 * at:3 * at + 3]
        if path != safe_push.DECISIONS or attribute != name or not value:
            raise ValueError("could not read the decisions page's attributes")
        if value != "unspecified":
            found.append(f"{name}={value}")
    return found


def tree_problems(repo: Path, render: bool = False) -> list[str]:
    """Check dated decisions headings and optionally require fresh renderer output. The
    page is read in the checkout, so a page Git may write there other than as its blob
    holds it (checkout_attributes) is unreadable."""
    root = Path(safe_push.git(repo, "rev-parse", "--show-toplevel").strip()).resolve()
    if root != repo.resolve():
        raise ValueError("--tree must name the repository root")
    tracked = safe_push.git(repo, "ls-files", "-z", "--", safe_push.DECISIONS).split("\0")
    if tracked != [safe_push.DECISIONS, ""]:
        raise ValueError("the tracked decisions page is missing")
    if attributes := checkout_attributes(repo):
        raise ValueError(f"the decisions page has {', '.join(attributes)}, with which Git may "
                         "write it to the checkout other than as its blob holds it: --tree "
                         "reads the checkout, so take the attribute off the page")
    path = repo / safe_push.DECISIONS
    if path.is_symlink() or not path.resolve().is_relative_to(root) or not path.is_file():
        raise ValueError("cannot read the decisions page")
    problems = heading_problems(_page_text(path.read_bytes()))
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


def gap_commands(repo: Path, checks: set[str], deleted: set[str] | None = None) -> list[list[str]]:
    """Choose tests once; skip proven deletions and refuse unexplained missing tests."""
    commands = set()
    deleted = deleted or set()
    for path in sorted(checks):
        if path in deleted:
            continue
        if re.fullmatch(r"(?:tests|scripts)/test_[^/]+\.py", path):
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
            if candidate in deleted:
                continue
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
    deleted = set()
    for pr in entries:
        # After criss-cross merges an entry has several merge bases: it asks for the
        # tests of what it changes against any of them, and is excused a test only for
        # a file it deletes against all of them.
        bases = merge_bases(repo, base, pr["head"], pr["number"])
        changes = [derive_new(repo, mb, pr["head"]) for mb in bases]
        deleted.update(set.intersection(*(
            {path for status, path in safe_push.changed_files(repo, mb, pr["head"])
             if status == "D"} for mb in bases)))
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
    # An entry's deletion excuses no file restored by a later entry in the group.
    tracked = set(safe_push.git(repo, "ls-tree", "-r", "--name-only", "-z", "HEAD").split("\0"))
    for command in gap_commands(repo, checks, deleted - tracked):
        print("gaps: " + shlex.join(command), flush=True)
        # The group's tests run with no token of the job in their environment.
        env = {k: v for k, v in os.environ.items() if "TOKEN" not in k.upper()}
        result = safe_push.run(command, repo, env=env)
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
            api = GitHub(args.repo, args.github_json)
            # The queue is read once, for its order and for who queued and edited each entry.
            queue_answer = api.read("queue")
            entries = chain(repo, base, head, api, queue_answer)
            actors = queue_actors(queue_answer)
            for pr in entries:
                if "auto-revert" in pr["labels"] or pr["ref"].startswith("revert/"):
                    if pr["head_repo"] != args.repo:
                        raise Refused(f"#{pr['number']}: its head is not in {args.repo}")
                    exact_revert(repo, pr, api)
                else:
                    ordinary_entry(pr, actors, args.repo)
                    preflight(repo, base, pr)
                    intact(repo, base, head, pr)
            # The judge runs none of the group's scripts: the generated pages' freshness
            # is the check job's (render.py and git status, on the same group), so rule
            # (d) here reads the page's blob only, never the checkout.
            problems = gaps(repo, base, entries) if args.gaps \
                else heading_problems(page_blob(repo, head))
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
