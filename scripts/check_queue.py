#!/usr/bin/env python3
"""Check a merge group's preserved changes, evidence, order and generated tree.

    python3 scripts/check_queue.py --head <sha> --base <sha> --repo <owner/name>
    python3 scripts/check_queue.py --gaps --head <sha> --base <sha> --repo <owner/name>
        [--plan <new file>]
    python3 scripts/check_queue.py --run-plan <file> --head <sha>
    python3 scripts/check_queue.py --acceptance-run --head <sha> --repo <owner/name>
        --ci-workflow <file> --out <dir>
    python3 scripts/check_queue.py --tree <dir> [--render]

Group commands require a checkout of the supplied head. --gaps chooses the tests of what
the group changes: for a path under .github/, changed or deleted, every test GITHUB_TESTS
names for it, none excused for being deleted, and a refusal if it names none or one is
missing; and a test GITHUB_TESTS names refuses if it is deleted, whatever else the group
changes. With --plan it writes them to a new file and runs nothing, and
--run-plan runs that file's tests in the checkout of its head, reading no GitHub. No
test runs while this process's environment holds a variable named with TOKEN: a test
could read it there or, on Linux, in its parent's environment in /proc. So CI chooses
the tests in a step that holds the token, to read GitHub, and runs them in a later step
that holds none. That keeps the token out of the tests' environment, files, caches and
artifacts, but not out of the job: the runner process holds the job's token until the
job ends, every step runs beneath it, and a test that can read the runner's memory (a
hosted runner gives its steps sudo) could read it there. So the token is read-only by
design: queue-gaps has contents, pull-requests, actions and issues read, and no write.

--acceptance-run finds, for queue-gaps, the verdicts of the acceptance job of the group's
own CI run, which a job of another workflow cannot need. It reads GitHub alone, and each
list whole: one page of at most 100 whose total_count is the number of items it gives.
It reads, every ACCEPTANCE_POLL seconds until it is there, the one run of the
--ci-workflow file of .github/workflows/ for the head on the merge group event, in this
repository; then that run's jobs, each as its latest execution, until the one named
acceptance has completed, which must have passed; then that run's artifacts named
acceptance, until exactly one unexpired artifact of that run and head was made within
that job's execution, so that an earlier attempt's artifacts never count. It downloads
that artifact by its id, holding at most ACCEPTANCE_ZIP_MAX bytes of it as they come, and
takes verdicts.json alone from it, at most ACCEPTANCE_VERDICTS_MAX bytes, read through a
bounded stream; it refuses a zip that holds a path, a link, a name twice, a file the
acceptance job does not keep (ACCEPTANCE_FILES), or a file compressed by another method
than deflate or declaring more than ACCEPTANCE_VERDICTS_MAX bytes, before any is
decompressed. Then it reads the run, the job and the complete artifact list again: any change,
the run's attempt among them (a re-run of any job begun meanwhile), refuses. Only then
does it write the verdicts to <dir>/verdicts.json, a new file. Its one deadline,
ACCEPTANCE_WAIT, is the queue's status check timeout, so that it cuts no group off before
the queue's own timeout would; passed at any point, during the reads after the job ends
among them, it refuses. The verdicts are the group's own, written by its ci.yml: --gaps
reports them, and refuses only a changed proposition they give no items for.

--tree checks the decisions page line by line (heading_problems): a line that could
render as a level-one or level-two heading counts, in code too; its text must be plain;
every year in it must stand in a date the check reads; no two of them may contain the
same date; and no HTML <h1> or <h2> tag may stand anywhere. --render adds the generated
pages' freshness. Conflict markers are checked by S23 in check_style.py, in the check
job on the same merge group.

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
headRefOid must agree. That GraphQL answer gives each queued entry's head, body, editor
and last rename at once, and the head and body the verdict reads, by REST afterwards,
must equal its own: a head that differs refuses (the queue order compares them), and a
body that differs, or that the answer lacks, is unreadable, so an edit made between the
two reads (a bot's, which the editor read before it would name as a person's) never
passes. A different queue merge subject is accepted only when its
second parent uniquely identifies a queue entry; no subject fallback is allowed
for the already merged prefix.

Reversing T with merge-base T.head merges the group with T's original base, once for
each of T's merge bases with the group's base (more than one after criss-cross merges).
A clean reverse merge alone does not prove preservation: a complete cancellation
also merges cleanly. Reapplying T must reproduce the group on every non-exempt
path. Generated files are excluded; added decisions lines must remain a
subsequence. An automatic revert instead requires the configured STOICHEIA_REVERT_BOT
and the failed post-merge run's push range, before to after, every commit of which must
be a pull request's two-parent merge, as auto_revert's trains and read_trains require,
before any revert is computed (pushed_pull_requests): its subject names the pull
request, no number comes twice, and GitHub's REST answer for that number records it
merged as that merge, from the merge's second parent, into main of this repository,
with a title that is not blank and a kind label. Its one merge base with main must
be after, the failed push's tip, and after..head exactly the reverts and at most one
keep commit, with no merge (exact_revert): one commit for each of the push's merges,
newest first, whose tree is that merge reverted onto the last (git revert -m 1, merge
attributes read from before, as the revert job reads them), then, only where the
reverts changed the decisions record, one commit that keeps it. The record is history,
only ever added to, so docs/decisions/ and the decisions page stay as at after
(auto_revert.keep_decisions makes the same tree); the commits' messages are not read.
A failed run that is still in progress, as it is while its own revert job ends, is read
again every RUN_POLL seconds for up to RUN_WAIT seconds, and refuses if it has not
completed by then. An open main-red issue must name that run on its own Run: line, by
this repository's address.

While an open issue is labelled main-red, an ordinary entry lands only as main's fix:
its body names every open main-red issue, and no other, on the line that
safe_push.main_red_fix reads (WORKFLOW, "Out of a red main"). No bot may have written an
ordinary entry, put it in the queue, last edited its body or last renamed it: its title
goes into main's merge commit.

safe_push records abbreviated harness blobs. They must resolve unambiguously to the
full blob at the pre-flight's harness commit. The block's base must be the newest
commit of the group base's first-parent chain that the head contains, which is what
safe_push records, and its harness that base or a later commit of the same chain. Older
blocks without a harness field use their recorded base as that commit. The summary and
steps must report a passing verdict and every full check its harness runs, save for a
pre-flight that left them to CI for its class (safe_push.short_path, since #329): its
summary and its Risk class line name the same class of R0 to R2, which its harness's
LOW_CLASSES holds (read by ast, never run); its step 4 is the row `4. class`, passed,
and the full local checks, skipped, and nothing else; and two diffs are each classed R0
to R2 by the group base's scripts/risk.py, with the entry's labels, and touch no check
input nor any protected path but judged content (safe_push.beyond_low): the block's
own, from its base to its head, and what the entry's merge brings into the group, from
the merge's first parent to the merge, as CI's risk job classes a pull request's merge
commit. The group's own CI run is R5, so every check still runs on it before it merges.
The block is a declaration that anyone who can edit the pull request body can type: the
judge checks it for consistency, not as proof that a pre-flight ran.

Rule (b) asks two things of something a group cannot change (WORKFLOW, section 10, "The
merge queue"). The first, the judge's code and its running, is to be held by the
organization ruleset of docs/rulesets/queue-judge.json, which requires the queue's judge
workflow from main, once the owner imports it and the trial shows it holding a group;
until then nothing holds it. Under that rule GitHub runs main's copy of the workflow in
place of a pull request's own (shown on a pull request; on a merge group, to be shown
before the queue goes on), and each of its steps that judges takes scripts/ from the
group's base. The second, the authenticity of the pre-flight's evidence, is not held: the
block is a declaration (above), and a block typed to be consistent with the repository
passes this judge, as tests/test_check_queue.py shows. The queue must not be turned on
until both are held.

ACCEPTANCE_VERDICTS names the acceptance job's JSON for proposition gap reports.
Exit 0 means pass, 1 refused, and 2 unreadable. Standard library, Python 3.11+, git.
"""

from __future__ import annotations

import argparse
import ast
import base64
import contextlib
import copy
import datetime
import io
import json
import os
import re
import shlex
import stat
import subprocess
import sys
import tempfile
import threading
import time
import zipfile
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import safe_push
import check_train
import heath
from check_train import declared_new, derive_new

# Isolated invocation and this directory supply the judge's complete script imports.
for module in (safe_push, check_train, heath):
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
# An HTML heading tag of level one or two, which this reading refuses rather than reads.
RAW_HEADING = re.compile(r"(?i)<h[12](?=[\s/>]|$)")
GENERATED = (*safe_push.GENERATED, "book/", safe_push.DECISIONS)
# The decisions record: its entries (tooling/decision-entries), each a file of its own,
# and its page. An automatic revert keeps both.
ENTRIES = "docs/decisions"
KEPT = (ENTRIES, safe_push.DECISIONS)
# A failed run still in progress is read again this often, in seconds, for at most this
# long: the revert job is one of that run's own jobs.
RUN_POLL = 15
RUN_WAIT = 600
# --acceptance-run reads again this often, in seconds: a minute, since the token allows
# about 1,000 requests an hour per repository and several groups may wait at once. It
# waits for at most this long: the queue's status check timeout, 150 minutes from the
# group's start (WORKFLOW, "Turning it on"), so that it has no earlier cutoff than the
# queue's own. After acceptance ends the handover is serial (a poll, then the reads and
# the download, each allowed 60 seconds), so a group that ends near the timeout may be
# ejected at it; a deadline passed during the handover refuses.
ACCEPTANCE_POLL = 60
ACCEPTANCE_WAIT = 150 * 60
# The job of CI that checks the acceptance checklist, and the artifact it keeps; and the
# files it keeps there (ci.yml, "Keep the reports"): its report and verdicts and, in the
# ratchet, main's. --acceptance-run takes verdicts.json alone, and refuses any other file.
ACCEPTANCE = "acceptance"
ACCEPTANCE_FILES = ("report.md", "verdicts.json", "main-report.md", "main.json")
# The most bytes --acceptance-run holds of the artifact's zip, and of verdicts.json, the
# most any file of the zip may declare: a group's own CI makes the artifact. Each is ten
# times an estimate. check_acceptance.py --json writes 29,866 bytes of verdicts for Books
# I to III's 1,602 items, all passing (its verdicts() over its cells, written as --json
# writes them), and the report beside them is shorter: the committed one, with 11 items
# failing, is 18,960 bytes. The Elements' 465 propositions, at 16 items each, would give
# some 140,000 bytes of verdicts, say 200,000 with failures' notes; and the zip holds at
# most four such files (ACCEPTANCE_FILES), 800,000 bytes, stored or compressed.
ACCEPTANCE_VERDICTS_MAX = 2 * 1024 * 1024
ACCEPTANCE_ZIP_MAX = 8 * 1024 * 1024
# How a file of the zip may be compressed: not at all, or by deflate, which zipfile
# decompresses a bounded piece at a time. Any other method (bzip2 or LZMA, say) it
# decompresses a whole read at once, however much that gives.
ACCEPTANCE_METHODS = (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED)
# A workflow file of .github/workflows/, named alone, as --ci-workflow names CI's.
WORKFLOW_FILE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]*\.ya?ml")
# A time as GitHub's REST answers give it, in UTC.
STAMP = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(?:\.[0-9]+)?Z")
# A test file --gaps runs for itself: test_*.py directly under tests/ or scripts/.
GAP_TEST = re.compile(r"(?:tests|scripts)/test_[^/]+\.py")
# The tests --gaps runs for each file under .github/, changed or deleted: those that read
# it. scripts/test_safe_push.py reads every workflow and the pull request template;
# tests/test_auto_revert.py and tests/test_check_queue.py read ci.yml and post-merge.yml,
# and tests/test_check_queue.py the queue's judge workflow too, whose steps it runs;
# tests/test_release_gate.py reads the template. A test named here is never excused for
# being deleted, whether or not the group changes a file it reads (gap_commands). Any
# other path under .github/ (a new workflow, say) refuses: its tests are named here, in
# main's copy, before it can land.
GITHUB_TESTS = {
    ".github/pull_request_template.md": ("scripts/test_safe_push.py",
                                         "tests/test_release_gate.py"),
    ".github/workflows/ci.yml": ("scripts/test_safe_push.py", "tests/test_auto_revert.py",
                                 "tests/test_check_queue.py"),
    ".github/workflows/post-merge.yml": ("scripts/test_safe_push.py",
                                         "tests/test_auto_revert.py",
                                         "tests/test_check_queue.py"),
    ".github/workflows/queue-judge.yml": ("scripts/test_safe_push.py",
                                          "tests/test_check_queue.py"),
    ".github/workflows/release-gate.yml": ("scripts/test_safe_push.py",),
    ".github/workflows/safe-push-tests.yml": ("scripts/test_safe_push.py",),
}
# The attributes with which Git may write a file to a checkout other than as its blob
# holds it; --tree, which reads the checkout, refuses to read a page that has any of them.
CHECKOUT_ATTRIBUTES = ("working-tree-encoding", "filter", "ident", "text", "eol", "crlf")
PREFLIGHT = re.compile(
    r"(?ms)^<!-- safe_push:preflight begin sha=([0-9a-f]{40}) base=([0-9a-f]{40})"
    r"(?: harness=([0-9a-f]{40}))? -->[ \t\r]*$"
    r"(?:(?!<!-- safe_push:preflight begin).)*?"
    r"^<!-- safe_push:preflight end -->[ \t\r]*$")
# How safe_push's summary ends when the pre-flight left the full checks to CI for the
# change's class (short_path, preflight_block); and the step 4 of such a pre-flight, all
# of it: the class, passed, and the full local checks, skipped.
LIGHT = re.compile(r"; the full local checks left to CI, for the class (\S+)\.$")
LIGHT_STEPS = {"4. class": "ok", "4. full local checks": "skip"}


class Refused(Exception):
    """A readable input which does not meet the queue's rules."""


def bounded(stream, limit: int, what: str) -> bytes:
    """What `stream` gives, read a piece at a time, if it is at most `limit` bytes: at one
    byte more it stops reading and refuses, so that no more than that is ever held."""
    data = bytearray()
    while piece := stream.read(min(1 << 16, limit + 1 - len(data))):
        data += piece
        if len(data) > limit:
            raise Refused(f"acceptance: {what} is larger than {limit} bytes")
    return bytes(data)


def download(command: list[str]) -> bytes:
    """gh's output for an artifact's zip, read as it comes, at most ACCEPTANCE_ZIP_MAX bytes
    (bounded): at one byte more the reading stops, gh, the process this started, is
    stopped by its own handle, and the download refuses. gh is stopped too if it has not
    ended in 60 seconds, and a gh that does not exit 0 is unreadable."""
    with subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                          stderr=subprocess.DEVNULL) as process:
        timer = threading.Timer(60, process.kill)
        timer.start()
        try:
            data = bounded(process.stdout, ACCEPTANCE_ZIP_MAX, "the artifact's zip")
            process.wait()
        except BaseException:
            process.kill()
            raise
        finally:
            timer.cancel()
    if process.returncode:
        raise ValueError("GitHub request failed")
    return data


class GitHub:
    """The only GitHub boundary; fixture reads never fall back to the network. A fixture
    keys each answer of KEYED by its number, as a string, and gives an artifact's zip,
    artifact_zips, in base64; a read of ci_runs is of `workflow`'s runs for `head`."""

    KEYED = ("pull_requests", "runs", "jobs", "artifacts", "artifact_zips")

    def __init__(self, repo: str, fixture: Path | None):
        self.repo = repo
        self.fixture = json.loads(fixture.read_text(encoding="utf-8")) if fixture else None
        if fixture and not isinstance(self.fixture, dict):
            raise ValueError("GitHub fixture must be an object")

    def read(self, kind: str, number: int | None = None, workflow: str | None = None,
             head: str | None = None):
        if self.fixture is not None:
            try:
                value = self.fixture[kind]
                value = value[str(number)] if kind in self.KEYED else value
                return base64.b64decode(value, validate=True) if kind == "artifact_zips" \
                    else value
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
                "pullRequest{number headRefOid body editor{__typename login} "
                "timelineItems(itemTypes:[RENAMED_TITLE_EVENT],last:1){"
                "nodes{...on RenamedTitleEvent{actor{__typename login}}}}}} "
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
            # Each list of one page of 100, which its reader holds to its total_count.
            endpoints = {"main": "commits/main", "pull_requests": f"pulls/{number}",
                         "runs": f"actions/runs/{number}",
                         "ci_runs": f"actions/workflows/{workflow}/runs?event=merge_group"
                                    f"&head_sha={head}&per_page=100",
                         "jobs": f"actions/runs/{number}/jobs?filter=latest&per_page=100",
                         "artifacts": f"actions/runs/{number}/artifacts?name={ACCEPTANCE}"
                                      "&per_page=100",
                         "artifact_zips": f"actions/artifacts/{number}/zip"}
            if kind not in endpoints or kind == "ci_runs" and not (
                    WORKFLOW_FILE.fullmatch(str(workflow)) and OID.fullmatch(str(head))):
                raise ValueError("GitHub: unknown read")
            endpoint = endpoints[kind]
            command = ["gh", "api", "--method", "GET", f"repos/{self.repo}/{endpoint}"]
        try:
            # An artifact's zip is read as bytes, a bounded amount (download); every other
            # answer is JSON.
            if kind == "artifact_zips":
                return download(command)
            result = subprocess.run(command, capture_output=True, text=True, timeout=60)
            if result.returncode:
                raise ValueError("GitHub request failed")
            return json.loads(result.stdout)
        except Refused:
            raise
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


def queue_actors(answer) -> dict[int, tuple[bool, bool, bool]]:
    """Whether a bot put each queued pull request in the queue, whether a bot last
    edited its body (False when nobody has), and whether a bot last renamed it (False
    when nobody has: its last title rename, from its timeline), read by GraphQL's type
    of the actor: GraphQL spells a bot's login without the "[bot]" REST adds, so logins
    are not compared. Missing or malformed data refuses."""
    try:
        actors = {}
        for node in answer["data"]["repository"]["mergeQueue"]["entries"]["nodes"]:
            pr = node["pullRequest"]
            enqueuer, editor = node["enqueuer"], pr["editor"]
            renames = pr["timelineItems"]["nodes"]
            if not isinstance(renames, list) or len(renames) > 1:
                raise ValueError
            renamer = renames[0]["actor"] if renames else None
            for actor, may_be_none in ((enqueuer, False), (editor, True),
                                       (renamer, not renames)):
                if actor is None and may_be_none:
                    continue
                if not isinstance(actor, dict) or not isinstance(actor["login"], str) \
                        or not actor["login"] or not isinstance(actor["__typename"], str):
                    raise ValueError
            actors[pr["number"]] = (
                enqueuer["__typename"] == "Bot",
                editor is not None and editor["__typename"] == "Bot",
                renamer is not None and renamer["__typename"] == "Bot")
        return actors
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read who queued, edited and renamed each "
                         "entry") from None


def queue_bodies(answer) -> dict[int, str]:
    """Each queued pull request's body, as the queue read gives it, in the same answer as
    its head, its editor and its last rename. Missing or malformed data is unreadable."""
    try:
        bodies = {}
        for node in answer["data"]["repository"]["mergeQueue"]["entries"]["nodes"]:
            pr = node["pullRequest"]
            if not isinstance(pr["body"], str):
                raise ValueError
            bodies[pr["number"]] = pr["body"]
        return bodies
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read each queued entry's body") from None


def ordinary_entry(pr: dict, actors: dict, repo_slug: str) -> None:
    """An entry that is not an automatic revert: its head is in this repository, and no
    bot (the revert App's above all) wrote it, put it in the queue, last edited its body
    or last renamed it (its title goes into main's merge commit), so the App's key
    cannot land anything but the revert the queue checks it to be. Trains are written,
    named and queued by people."""
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
    queued_by_bot, edited_by_bot, renamed_by_bot = actors[pr["number"]]
    if queued_by_bot or edited_by_bot:
        raise Refused(f"#{pr['number']}: a bot wrote, queued or edited a pull request that "
                      "is not an automatic revert")
    if renamed_by_bot:
        raise Refused(f"#{pr['number']}: a bot last renamed a pull request that is not an "
                      "automatic revert, and its title goes into main's merge commit")


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
    """Identify the first-parent chain and prove its queue order and merge trees, and that
    the REST reading of each queued entry is the queue read's."""
    answer = queue_answer if queue_answer is not None else api.read("queue")
    queued = queue_entries(answer)
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
    # One GraphQL answer gives each queued entry's head, body, editor and last rename;
    # the body and head the verdict reads come later, by REST. The heads agree, by the
    # queue order above, and the bodies must too: then everything the verdict reads of a
    # queued entry is that one answer's. An edit between the two reads either changes the
    # body, which is unreadable, or leaves it as that answer gave it, with its editor.
    bodies = queue_bodies(answer)
    for pr in entries:
        if pr["state"] == "OPEN" and bodies.get(pr["number"]) != pr["body"]:
            raise ValueError(f"GitHub: #{pr['number']}'s body differs between the "
                             "queue's answer and its pull request's: it was edited "
                             "between the two reads")
    return entries


def harness_tree(repo: Path, harness_commit: str) -> ast.Module:
    """The source of the harness at `harness_commit`, parsed by ast, never run."""
    source = safe_push.show(repo, harness_commit, "scripts/safe_push.py")
    if source is None:
        raise Refused("pre-flight: the recorded harness commit has no scripts/safe_push.py")
    try:
        return ast.parse(source)
    except SyntaxError:
        raise Refused("pre-flight: the recorded harness could not be read") from None


def harness_value(tree: ast.Module, name: str) -> ast.expr | None:
    """What the harness's `name` is bound to, read by ast: by one plain assignment of its
    top level, and by nothing else anywhere in it (a second or conditional binding, an
    augmented one, an import or a definition); else None."""
    binds = [node for node in ast.walk(tree)
             if isinstance(node, ast.Name) and node.id == name
             and not isinstance(node.ctx, ast.Load)
             or str(getattr(node, "name", None)).split(".")[0] in (name, "*")
             or name in (getattr(node, "asname", None), getattr(node, "rest", None))
             or name in getattr(node, "names", ())]
    if len(binds) == 1:
        for node in tree.body:
            if isinstance(node, ast.Assign) and binds[0] in node.targets:
                return node.value
    return None


def harness_check_names(repo: Path, harness_commit: str) -> set[str]:
    """The names of the full checks the harness at `harness_commit` runs: its CHECKS and
    NEGATIVE lists, read from its source by ast (never run), so that a train pre-flighted
    before a check was added is judged by the checks its harness had, and a group's own
    harness never decides what its pre-flight needed. Each name is a string constant, or
    a name of the harness bound to one, as harness_value reads it (EMPTY_CHECK, say)."""
    tree = harness_tree(repo, harness_commit)
    names: dict[str, list[str]] = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id in ("CHECKS", "NEGATIVE"):
            if not isinstance(node.value, ast.List) or node.targets[0].id in names:
                raise Refused("pre-flight: the recorded harness's checks could not be read")
            found = []
            for elt in node.value.elts:
                first = elt.elts[0] if isinstance(elt, ast.Tuple) and elt.elts else None
                if isinstance(first, ast.Name):
                    first = harness_value(tree, first.id)
                if not (isinstance(first, ast.Constant) and isinstance(first.value, str)):
                    raise Refused("pre-flight: the recorded harness's checks could not be read")
                found.append(first.value)
            names[node.targets[0].id] = found
    if set(names) != {"CHECKS", "NEGATIVE"} or not all(names.values()):
        raise Refused("pre-flight: the recorded harness's checks could not be read")
    return {f"4. {name}" for name in names["CHECKS"] + names["NEGATIVE"]}


def harness_low_classes(repo: Path, harness_commit: str) -> set[str]:
    """The classes for which the harness at `harness_commit` leaves the full checks to CI:
    its LOW_CLASSES, read from its source by ast (never run), as harness_check_names reads
    its checks, so that a light block names a harness that writes one. A harness from
    before #329 has none, and refuses."""
    low = None
    for node in harness_tree(repo, harness_commit).body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id == "LOW_CLASSES":
            if low is not None or not isinstance(node.value, (ast.Tuple, ast.List)) \
                    or not all(isinstance(elt, ast.Constant) and isinstance(elt.value, str)
                               for elt in node.value.elts):
                raise Refused("pre-flight: the recorded harness's LOW_CLASSES could not be "
                              "read")
            low = {elt.value for elt in node.value.elts}
    if not low:
        raise Refused("pre-flight: left the full checks to CI, but the recorded harness "
                      "has no LOW_CLASSES, so never does")
    return low


def preflight_steps(inner: str, head: str, base: str,
                    expected: set[str] | None = None, light: str | None = None) -> None:
    """Read one passing verdict and a steps table whose passing rows include every full
    check expected, with no failing row: a record standing in for them does not count.
    The full checks expected are those of the harness that ran the pre-flight. A
    pre-flight that left them to CI for its class, `light`, runs none: its one Risk class
    line names that class, and its step 4 is LIGHT_STEPS, exactly."""
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
    if light is not None:
        # In any case, so that a second line in other capitals refuses.
        named = [line.strip() for line in visible.splitlines()
                 if line.strip().casefold().startswith("risk class")]
        if len(named) != 1 or not named[0].startswith(f"Risk class {light}: "):
            raise Refused(f"pre-flight: the record's class {light} and its Risk class line "
                          "disagree")
        if {name: outcome for name, outcome in steps if name.startswith("4.")} != LIGHT_STEPS:
            raise Refused("pre-flight: left the full checks to CI, but its step 4 is not the "
                          "class, passed, and the full local checks, skipped, alone")
        return
    if expected is None:
        expected = {f"4. {name}" for name, _ in (*safe_push.CHECKS, *safe_push.NEGATIVE)}
    passed = {name for name, outcome in steps if outcome in {"ok", "pass"}}
    complete = any({name + suffix for name in expected} <= passed
                   for suffix in ("", " (the commit's checks)"))
    if not complete:
        raise Refused("pre-flight: steps must run the full checks")


def light_preflight(repo: Path, base: str, against: str, checked: str, harness_commit: str,
                    pr: dict, inner: str, recorded: str) -> None:
    """Accept a pre-flight that left the full checks to CI for the class it records,
    `recorded`, only while both classes are R0 to R2, as safe_push's --merge accepts its
    record (checks_record): the recorded one, which its harness's LOW_CLASSES must hold,
    and the one recomputed now. That is recomputed for two diffs, the block's own change,
    `against` to `checked`, and what the entry's merge brings into the group, its first
    parent to the merge; and neither may touch a check input nor any protected path but
    judged content, as short_path requires (beyond_low). The group's own CI run is R5,
    so every check runs on it."""
    if recorded not in safe_push.LOW_CLASSES:
        raise Refused(f"pre-flight: left the full checks to CI for the class {recorded}, "
                      "which only a change of R0 to R2 may")
    if recorded not in (low := harness_low_classes(repo, harness_commit)):
        raise Refused(f"pre-flight: left the full checks to CI for the class {recorded}, "
                      "which the recorded harness never does (its LOW_CLASSES are "
                      f"{', '.join(sorted(low))})")
    preflight_steps(inner, checked, against, light=recorded)
    # The class is recomputed by the group base's scripts/risk.py, main's, never taken
    # from the record: the block is a declaration anyone who can edit the body can type,
    # and main's classifier may since have put the change's paths higher. risk_class reads
    # that copy out of Git at the base, never the checkout, so no entry's copy classes
    # anything; a release label, or any failure to compute the class, gives R5. The
    # block's own diff, from its base to its head, is the one its pre-flight classed. It
    # need not be what the entry brings into the group, which may stand on a newer main;
    # nor need `git diff <group base>...<head>`, which after criss-cross merges uses one
    # of several merge bases. So the entry's merge is classed too, from its first
    # parent, as CI's risk job classes a pull request's merge commit.
    merge = pr["merge"]
    for what, start, end in (("the change", against, checked),
                             ("what its merge brings into the group",
                              parents(repo, merge)[0], merge)):
        risk = safe_push.risk_class(repo, base, end, pr["labels"], diff_base=start)
        if risk.cls not in safe_push.LOW_CLASSES:
            raise Refused("pre-flight: left the full checks to CI, but the class by main's "
                          f"scripts/risk.py is {risk.cls} ({risk.why}), of {what}")
        if beyond := safe_push.beyond_low(repo, start, end):
            shown = ", ".join(beyond[:8]) + (f" and {len(beyond) - 8} more"
                                             if len(beyond) > 8 else "")
            raise Refused(f"pre-flight: left the full checks to CI, but {what} touches "
                          f"{safe_push.printable_text(shown)}, which no change of R0 to R2 "
                          "may")


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
    harness = re.findall(
        r"origin/main's `scripts/safe_push\.py` \(blob `([0-9a-f]{12,40})`\)", summary)
    if len(harness) != 1 or not summary.startswith("Pre-flight of ") \
            or "full checks skipped" in inner:
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
    # A pre-flight of R0 to R2 leaves the full checks to CI, and its summary ends saying so.
    if light := LIGHT.search(summary.rstrip()):
        light_preflight(repo, base, against, checked, harness_commit, pr, inner,
                        light.group(1))
    else:
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
    with its regions' bodies emptied and their markers kept (heath.outside), by git
    merge-file; true when the group keeps it whole."""
    def text(rev):
        return heath.outside(path, safe_push.show(repo, rev, path) or "")

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
        # README.md, docs/PROGRAM.md and docs/WORKFLOW.md are generated only between their
        # markers: the rest, written by hand, the markers among it, is held to the same
        # revert and reapply, read with the regions' bodies emptied (heath.outside).
        lost += [path for path in safe_push.GENERATED_REGIONS
                 if not hand_written_intact(repo, path, head, mb, pr["head"])]
        if lost:
            raise Refused(f"not overwriting: #{pr['number']} changed lines were "
                          "overwritten: " + ", ".join(sorted(lost)))
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


def completed_run(api: GitHub, run_id: int, sleep=time.sleep, clock=time.monotonic) -> dict:
    """The named run once GitHub reports it completed. The revert job is one of the failed
    run's own jobs, so its revert can be judged while the run is still in progress: such
    a run is read again every RUN_POLL seconds for up to RUN_WAIT seconds, and a run not
    completed by then refuses."""
    deadline = clock() + RUN_WAIT
    while True:
        run = api.read("runs", run_id)
        try:
            if type(run["id"]) is not int or run["id"] != run_id \
                    or not isinstance(run["status"], str):
                raise ValueError
        except (KeyError, TypeError, ValueError):
            raise ValueError("GitHub: could not read the failed run") from None
        if run["status"] == "completed":
            return run
        if clock() >= deadline:
            raise Refused("auto-revert: the failed run had not completed after "
                          f"{RUN_WAIT // 60} minutes")
        sleep(RUN_POLL)


def failed_push(api: GitHub, run_id: int, sleep=time.sleep,
                clock=time.monotonic) -> tuple[str, str]:
    """Find the failed main post-merge run's exact push, reading every activity page, once
    the run has completed (completed_run)."""
    run = completed_run(api, run_id, sleep, clock)
    try:
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


def listed(answer, key: str, what: str) -> list[dict]:
    """The items of a REST list, read whole: one page of at most 100, whose total_count is
    the number of items it gives, each an object. Anything else is unreadable, so that a
    list GitHub gave in part never passes for the whole."""
    try:
        items, total = answer[key], answer["total_count"]
        if not isinstance(items, list) or type(total) is not int or total != len(items) \
                or total > 100 or not all(isinstance(item, dict) for item in items):
            raise ValueError
        return items
    except (KeyError, TypeError, ValueError):
        raise ValueError(f"GitHub: could not read {what} whole, in one page of 100") from None


def stamp(value, label: str) -> datetime.datetime:
    """A time of a REST answer, in UTC."""
    if not isinstance(value, str) or not STAMP.fullmatch(value):
        raise ValueError(f"could not read {label}: expected a time in UTC")
    return datetime.datetime.fromisoformat(value)


def ci_run(run, head: str, workflow: str, repo: str) -> tuple[int, int, str]:
    """The id, attempt and status of the group's CI run, from GitHub's REST answer for a
    run, which must be of `workflow` in .github/workflows/, on the merge group event, for
    `head`, with its head in this repository. Missing or malformed data is unreadable."""
    try:
        number, attempt, status = run["id"], run["run_attempt"], run["status"]
        path = run["path"]
        found = (oid(run["head_sha"], "run head"), run["event"], path,
                 run["head_repository"]["full_name"])
        if type(number) is not int or number < 1 or type(attempt) is not int or attempt < 1 \
                or not isinstance(status, str) \
                or not all(isinstance(value, str) for value in found):
            raise ValueError
        workflow_path, separator, workflow_ref = path.partition("@")
        if separator and not workflow_ref:
            raise ValueError
        found = (found[0], found[1], workflow_path, found[3])
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read the group's CI run") from None
    for name, value, wanted in zip(("head", "event", "workflow file", "head repository"),
                                   found, (head, "merge_group",
                                           f".github/workflows/{workflow}", repo)):
        if value != wanted:
            raise Refused(f"acceptance: the CI run {number} has another {name} than {wanted}")
    return number, attempt, status


def acceptance_job(answer, run_id: int, attempt: int) -> dict | None:
    """The job named acceptance among the jobs of the group's CI run, each as its latest
    execution: None while none is listed; else its id, attempt, status and conclusion,
    and, once it has passed, when it started and completed. Two such jobs, a job of
    another run, and a job of another attempt than `attempt`, the run's when first read,
    refuse. Missing or malformed data is unreadable."""
    jobs = listed(answer, "jobs", "the CI run's jobs")
    try:
        if not all(isinstance(job["name"], str) for job in jobs):
            raise ValueError
        named = [job for job in jobs if job["name"] == ACCEPTANCE]
        if len(named) != 1:
            if named:
                raise Refused(f"acceptance: the CI run {run_id} has {len(named)} jobs named "
                              "acceptance, not one")
            return None
        job = named[0]
        found = {key: job[key] for key in ("id", "run_id", "run_attempt", "status",
                                           "conclusion")}
        if type(found["id"]) is not int or found["id"] < 1 \
                or type(found["run_id"]) is not int or type(found["run_attempt"]) is not int \
                or found["run_attempt"] < 1 or not isinstance(found["status"], str) \
                or not isinstance(found["conclusion"], (str, type(None))):
            raise ValueError
        if found["status"] == "completed" and found["conclusion"] == "success":
            found["started"] = stamp(job["started_at"], "the acceptance job's start")
            found["completed"] = stamp(job["completed_at"], "the acceptance job's end")
            if found["started"] > found["completed"]:
                raise ValueError
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read the CI run's acceptance job") from None
    if found["run_id"] != run_id:
        raise Refused(f"acceptance: the CI run {run_id} lists an acceptance job of another run")
    if found["run_attempt"] > attempt:
        raise Refused(f"acceptance: the CI run {run_id} was run again after it was first read "
                      f"at attempt {attempt}: its acceptance job is of attempt "
                      f"{found['run_attempt']}")
    if found["run_attempt"] < attempt:
        raise Refused(f"acceptance: the CI run {run_id} lists an acceptance job of attempt "
                      f"{found['run_attempt']}, not its current attempt {attempt}")
    return found


def acceptance_artifact(answer, run_id: int, head: str, job: dict) -> dict | None:
    """The artifact named acceptance made during `job`, the acceptance job that passed:
    None while none is listed; else its id, when it was made and a normalized snapshot of
    the complete artifact list. Every listed artifact must be of this run and head. The
    selected artifact must be the only one made from the job's start to its end and must
    be unexpired, so that an earlier attempt's never counts. Missing or malformed data is
    unreadable."""
    artifacts = listed(answer, "artifacts", "the CI run's artifacts")
    if not artifacts:
        return None
    found = []
    try:
        for artifact in artifacts:
            current = {
                "id": artifact["id"],
                "created": stamp(artifact["created_at"], "the acceptance artifact's time"),
                "expired": artifact["expired"],
            }
            name, origin = artifact["name"], artifact["workflow_run"]
            origin = (origin["id"], oid(origin["head_sha"],
                                        "the acceptance artifact's head"))
            if type(current["id"]) is not int or current["id"] < 1 \
                    or not isinstance(name, str) or type(current["expired"]) is not bool \
                    or type(origin[0]) is not int:
                raise ValueError
            if name != ACCEPTANCE:
                raise Refused(f"acceptance: the CI run {run_id} lists an artifact of another "
                              "name")
            if origin != (run_id, head):
                raise Refused(f"acceptance: an artifact listed for the CI run {run_id} is "
                              "another run's, or another head's")
            found.append(current)
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read the CI run's acceptance artifact") from None
    candidates = [artifact for artifact in found
                  if job["started"] <= artifact["created"] <= job["completed"]]
    if len(candidates) > 1:
        raise Refused(f"acceptance: the CI run {run_id} lists {len(candidates)} artifacts made "
                      "during its acceptance job, not one")
    if not candidates:
        return None
    selected = candidates[0]
    if selected["expired"]:
        raise Refused(f"acceptance: the CI run {run_id}'s acceptance artifact has expired")
    selected["listed"] = tuple(sorted((artifact["id"], artifact["created"],
                                        artifact["expired"]) for artifact in found))
    return selected


def acceptance_verdicts(data) -> bytes:
    """verdicts.json, from the acceptance artifact's zip, of at most ACCEPTANCE_ZIP_MAX
    bytes. It may hold only files the acceptance job keeps (ACCEPTANCE_FILES), each once,
    named alone and regular: a path, a link or another file that is not regular, a name
    twice or any other file refuses. Each name is read as the zip stores it, before
    zipfile cuts it at a NUL. Before anything is decompressed, each file must be stored or
    deflated (ACCEPTANCE_METHODS) and declare at most ACCEPTANCE_VERDICTS_MAX bytes; then
    verdicts.json is read through a bounded stream, which refuses past that limit whatever
    its header said, and must hold the bytes its header declares. A zip that cannot be
    read is unreadable."""
    if not isinstance(data, bytes):
        raise ValueError("GitHub: could not read the acceptance artifact")
    if len(data) > ACCEPTANCE_ZIP_MAX:
        raise Refused(f"acceptance: the artifact's zip is larger than {ACCEPTANCE_ZIP_MAX} "
                      "bytes")
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            members = archive.infolist()
            names = [member.orig_filename for member in members]
            if any("/" in name or "\\" in name or name in ("", ".", "..") for name in names):
                raise Refused("acceptance: the artifact holds a path, where only a file's "
                              "name may stand")
            if len(set(names)) != len(names):
                raise Refused("acceptance: the artifact holds a name twice")
            if any(stat.S_IFMT(member.external_attr >> 16) not in (0, stat.S_IFREG)
                   for member in members):
                raise Refused("acceptance: the artifact holds a link, or another file that is "
                              "not regular")
            if others := sorted(set(names) - set(ACCEPTANCE_FILES)):
                raise Refused("acceptance: the artifact holds a file the acceptance job does "
                              "not keep: " + safe_push.printable_text(", ".join(others)))
            if "verdicts.json" not in names:
                raise Refused("acceptance: the artifact holds no verdicts.json")
            for member in members:
                if member.compress_type not in ACCEPTANCE_METHODS:
                    raise Refused(f"acceptance: the artifact holds {member.orig_filename} "
                                  "compressed by another method than deflate")
                if member.file_size > ACCEPTANCE_VERDICTS_MAX:
                    raise Refused(f"acceptance: the artifact holds {member.orig_filename}, "
                                  f"which declares {member.file_size} bytes, more than "
                                  f"{ACCEPTANCE_VERDICTS_MAX}")
            # zipfile reads a file no further than the size its header declares, so that a
            # header that understates it would cut the file short: the bound is the
            # stream's instead, the file opened by a copy of its entry whose size the read
            # never reaches, and what it gives is then held to the declared size.
            declared = members[names.index("verdicts.json")]
            entry = copy.copy(declared)
            entry.file_size = sys.maxsize
            with archive.open(entry) as stream:
                verdicts = bounded(stream, ACCEPTANCE_VERDICTS_MAX,
                                   "the artifact's verdicts.json")
            if len(verdicts) != declared.file_size:
                raise Refused(f"acceptance: the artifact's verdicts.json holds {len(verdicts)} "
                              f"bytes, not the {declared.file_size} its header declares")
            return verdicts
    except (zipfile.BadZipFile, EOFError, NotImplementedError, RuntimeError):
        raise ValueError("GitHub: could not read the acceptance artifact's zip") from None


def acceptance_run(api: GitHub, head: str, workflow: str, sleep=time.sleep,
                   clock=time.monotonic) -> bytes:
    """The verdicts of the acceptance job of the group's CI run, the run of `workflow` for
    `head` (the module's docstring, --acceptance-run), in four steps: the run, the job,
    the artifact and its download, and the second reading. Each wait reads again every
    ACCEPTANCE_POLL seconds, against one deadline, ACCEPTANCE_WAIT from the start, which
    holds to the end: passed during the handover, it refuses."""
    deadline = clock() + ACCEPTANCE_WAIT

    def wait(what: str) -> None:
        if clock() >= deadline:
            raise Refused(f"acceptance: {what} after {ACCEPTANCE_WAIT // 60} minutes")
        sleep(ACCEPTANCE_POLL)

    # 1. The run: exactly one, read whole. A rebuilt group has a new head, so an earlier
    # group's run never matches.
    while not (runs := listed(api.read("ci_runs", workflow=workflow, head=head),
                              "workflow_runs", f"the runs of {workflow}")):
        wait(f"no run of {workflow} for the group's head had begun")
    if len(runs) != 1:
        raise Refused(f"acceptance: GitHub lists {len(runs)} runs of {workflow} for the "
                      "group's head on the merge group event, not one")
    run_id, attempt, _ = ci_run(runs[0], head, workflow, api.repo)

    def same_run() -> str:
        """The run read again by its id, as it was first read but for its status."""
        number, again, status = ci_run(api.read("runs", run_id), head, workflow, api.repo)
        if number != run_id:
            raise ValueError("GitHub: could not read the group's CI run")
        if again != attempt:
            raise Refused(f"acceptance: the CI run {run_id} was run again after it was first "
                          f"read at attempt {attempt}: it is at attempt {again}")
        return status

    # 2. The job, until it completes. While none is listed, the run is read again: one
    # that has completed without it refuses. While it is listed and running, the jobs
    # alone are read, once a poll.
    while True:
        job = acceptance_job(api.read("jobs", run_id), run_id, attempt)
        if job is None:
            if same_run() == "completed":
                raise Refused(f"acceptance: the CI run {run_id} completed with no job named "
                              "acceptance")
        elif job["status"] == "completed":
            break
        wait("the acceptance job had not completed")
    if job["conclusion"] != "success":
        raise Refused(f"acceptance: the acceptance job of the CI run {run_id} ended "
                      f"{safe_push.printable_text(str(job['conclusion']))}, not success")

    # 3. The artifact, until it is listed, downloaded by its id.
    while (artifact := acceptance_artifact(api.read("artifacts", run_id), run_id, head,
                                           job)) is None:
        wait("the acceptance job's artifact had not been listed")
    verdicts = acceptance_verdicts(api.read("artifact_zips", artifact["id"]))

    # 4. Again, after the download: the same run at the same attempt, the same job, still
    # its latest execution and passed, and the same artifact, unexpired, in its window.
    same_run()
    if acceptance_job(api.read("jobs", run_id), run_id, attempt) != job \
            or acceptance_artifact(api.read("artifacts", run_id), run_id, head, job) != artifact:
        raise Refused(f"acceptance: the CI run {run_id}'s acceptance job or its artifact "
                      "changed while the artifact was read (a re-run begun meanwhile)")
    if clock() >= deadline:
        raise Refused(f"acceptance: the deadline, {ACCEPTANCE_WAIT // 60} minutes, passed "
                      "during the handover after the acceptance job ended")
    print(f"acceptance: run {run_id}, attempt {attempt}: job {job['id']} passed; artifact "
          f"{artifact['id']} read, and the run, the job and the artifact read again",
          flush=True)
    return verdicts


def red_issues(pages) -> list[dict]:
    """The open issues labelled main-red, from every page of GitHub's answer; a pull
    request is not one. Missing or malformed data is unreadable."""
    try:
        if not isinstance(pages, list) or not all(isinstance(page, list) for page in pages):
            raise ValueError
        issues = []
        for issue in (issue for page in pages for issue in page):
            if type(issue["number"]) is not int or issue["number"] < 1 \
                    or not isinstance(issue["body"] or "", str) or issue["state"] != "open" \
                    or not any(label["name"] == "main-red" for label in issue["labels"]):
                raise ValueError
            if "pull_request" not in issue:
                issues.append(issue)
        return issues
    except (KeyError, TypeError, ValueError):
        raise ValueError("GitHub: could not read the open main-red issues") from None


def red_issue_names(pages, run_id: int, repo_slug: str) -> None:
    """Require an open issue labelled main-red that names the failed run: the issue the
    post-merge workflow opened, which landing waits on; so an old failure, whose issue
    was closed or whose label was cleared when main passed again, admits no revert. The
    issue names the run on its own Run: line, the one line of its body that begins so,
    by this repository's address for the run (an attempt's too): a run of another
    repository, or an address elsewhere in the body, names nothing."""
    pattern = re.compile(rf"Run: https://github\.com/{re.escape(repo_slug)}/actions/runs/"
                         rf"{run_id}(?:/attempts/[1-9][0-9]*)?")
    for issue in red_issues(pages):
        lines = [line.rstrip() for line in (issue["body"] or "").splitlines()
                 if line.startswith("Run:")]
        if len(lines) == 1 and pattern.fullmatch(lines[0]):
            return
    raise Refused("auto-revert: no open main-red issue names the failed run")


def red_main_fix(pr: dict, red: list[int]) -> None:
    """While main is red, an ordinary entry lands only as its fix: its body names every
    open main-red issue, and no other, as safe_push.main_red_fix reads it. So a train
    queued before main went red, or queued without safe_push, waits as --merge does."""
    if not red:
        return
    try:
        fixes = safe_push.main_red_fix(pr["body"])
    except safe_push.Refusal as error:
        raise Refused(f"#{pr['number']}: {error}") from None
    if fixes != set(red):
        raise Refused(f"#{pr['number']}: main is red (open main-red issues "
                      + ", ".join(f"#{n}" for n in sorted(red)) + "), and only its fix "
                      "lands: a pull request whose body has the line `Fixes main-red: "
                      "#<n>`, naming every open main-red issue and no other")


def kept_decisions(git, after: str) -> None:
    """In the temporary revert checkout, put docs/decisions/ and the decisions page back as
    they were at `after`, the failed push's tip and the revert's base: the decisions
    record is history, only ever added to. Nothing else may differ from the exact
    revert; a path absent at `after` is left absent. The reverts leave their changes
    staged, which git rm refuses to remove unless forced."""
    for path in KEPT:
        git("rm", "-r", "-q", "-f", "--ignore-unmatch", "--", path)
        if git("ls-tree", after, "--", path):
            git("checkout", after, "--", path)


def revert_commits(repo: Path, after: str, head: str, most: int) -> list[str]:
    """The commits of after..head, oldest first: a line of one-parent commits from
    `after`, at most `most` of them. A merge, or a longer line, refuses."""
    found, current = [], head
    while current != after:
        pp = parents(repo, current)
        if len(pp) != 1 or len(found) >= most:
            raise Refused("auto-revert: the branch must hold, from the failed push's tip, "
                          "only one-parent commits: its reverts and at most one keep commit")
        found.append(current)
        current = pp[0]
    return found[::-1]


def pushed_pull_requests(repo: Path, api: GitHub, merges: list[str]) -> None:
    """Require each two-parent merge of the failed push to be a pull request's, as
    auto_revert's trains and read_trains require before it reverts any: its subject
    names the pull request, read as auto_revert reads it, no number comes twice, and
    GitHub's REST answer for that number records it merged as that merge, from the
    merge's second parent, into main of this repository, with a title that is not blank
    and a kind label (safe_push.KIND_LABELS, which auto_revert's KINDS copies). So the
    queue admits no revert that auto_revert would not make. Malformed data is
    unreadable."""
    found = []
    for sha in merges:
        # As auto_revert reads it: Git's %s, with only its line end taken off.
        match = SUBJECT.fullmatch(safe_push.git(repo, "show", "-s", "--format=%s",
                                                sha).rstrip("\n"))
        if not match:
            raise Refused(f"auto-revert: the failed push's merge {sha[:12]} names no "
                          "pull request in its subject, and only pull request merges are "
                          "reverted")
        found.append((sha, parents(repo, sha)[1], int(match.group(1))))
    numbers = [number for _, _, number in found]
    if repeated := sorted({number for number in numbers if numbers.count(number) > 1}):
        raise Refused("auto-revert: the failed push repeats pull request "
                      + ", ".join(f"#{number}" for number in repeated))
    for sha, second, number in found:
        answer = api.read("pull_requests", number)
        try:
            if type(answer["number"]) is not int or answer["number"] != number \
                    or type(answer["merged"]) is not bool:
                raise ValueError
            merged = oid(answer["merge_commit_sha"], "merged commit") \
                if answer["merged"] else None
            head = oid(answer["head"]["sha"], "pull request head")
            base, base_repo = answer["base"]["ref"], answer["base"]["repo"]["full_name"]
            title, labels = answer["title"], answer["labels"]
            if not all(isinstance(value, str) and value for value in (base, base_repo)) \
                    or not isinstance(title, str) or not isinstance(labels, list) \
                    or not all(isinstance(label["name"], str) and label["name"]
                               for label in labels):
                raise ValueError
        except (KeyError, TypeError, ValueError):
            raise ValueError(f"GitHub: could not read pull request #{number}") from None
        if merged != sha or head != second:
            raise Refused(f"auto-revert: #{number} does not confirm the failed push's "
                          f"merge {sha[:12]}: GitHub must record it merged as that merge, "
                          "from the merge's second parent")
        if base != "main" or base_repo != api.repo:
            raise Refused(f"auto-revert: #{number} was not merged into main of "
                          f"{api.repo}")
        if not title.strip():
            raise Refused(f"auto-revert: #{number} has a blank title")
        if not {label["name"] for label in labels} & set(safe_push.KIND_LABELS):
            raise Refused(f"auto-revert: #{number} has no kind label, one of "
                          + ", ".join(safe_push.KIND_LABELS))


def exact_revert(repo: Path, pr: dict, api: GitHub) -> None:
    """Require the configured bot and exactly the failed run's main merge reversals: a
    push of pull request merges only (pushed_pull_requests), read before any revert; a
    branch whose one merge base with main is the push's tip, `after`; and after..head
    exactly the reverts, one commit for each merge, newest first, each that merge
    reverted onto the last (merge attributes read from the push's `before`, as the
    revert job reads them), then a commit keeping the decisions record as at `after`
    only where the reverts changed it. No merge and no other commit; the commits'
    messages are not read."""
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
        if len(parents(repo, sha)) != 2:
            # auto_revert.trains reverts none of such a push: it is reverted by hand.
            raise Refused("auto-revert: the failed push holds a commit that is not a "
                          "two-parent merge")
        expected_merges.append(sha)
    pushed_pull_requests(repo, api, expected_merges)
    if named != expected_merges:
        raise Refused("auto-revert: Reverts lines do not equal the failed push's merges")
    if start != after:
        raise Refused("auto-revert: the revert's base must be the failed push's tip")
    if pr["ref"] != f"revert/{after[:12]}":
        raise Refused("auto-revert: the branch must be revert/<the failed push's 12 hex>")
    red_issue_names(api.read("main_red"), run_id, api.repo)
    steps = []
    with revert_checkout(repo, after) as (root, env, git):
        for sha in named:
            result = safe_push.run(["git", "-c", "core.hooksPath=/dev/null",
                                    f"--attr-source={before}", "revert", "--no-commit",
                                    "-m", "1", sha], root, env=env)
            if result.returncode == 1:
                raise Refused("auto-revert: named reversals do not apply cleanly")
            if result.returncode:
                raise ValueError("could not compute the automatic revert "
                                 "(Git 2.42 or later is needed)")
            steps.append(git("write-tree"))
        kept_decisions(git, after)
        wanted = git("write-tree")
    actual = safe_push.git(repo, "rev-parse", f"{pr['head']}^{{tree}}").strip()
    if actual != wanted:
        raise Refused("auto-revert: head is not the exact revert tree (extra change)")
    commits = revert_commits(repo, after, pr["head"], len(named) + 1)
    trees = [safe_push.git(repo, "rev-parse", f"{sha}^{{tree}}").strip() for sha in commits]
    if trees != steps + ([wanted] if steps[-1] != wanted else []):
        raise Refused("auto-revert: the branch must hold one commit for each named merge, "
                      "its revert, in order, then a commit keeping the decisions record "
                      "only where the reverts changed it, and nothing else")


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

    def readable(number: int, text: str, kept: str = "") -> None:
        # `kept`, the line's list numbers and footnote markers, may be its own text or
        # its containers': it is read as text for plainness, and no year in it is dated.
        if odd := NOT_PLAIN.search(f"{kept} {text}" if kept else text):
            problems.append(f"{safe_push.DECISIONS}:{number}: a line that could render as a "
                            f"heading, or as part of one, holds {odd.group()!r} "
                            f"(U+{ord(odd.group()):04X}), which is not plain: write it with "
                            "ASCII letters, digits, spaces and . , : ; ' ( ) - / only")
        year = next((word for word in WORD.findall(kept) if YEARLIKE.search(word)), None)
        if (year := year or undated_year(text)) is not None:
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
    unread: list[tuple[int, str, str]] = []
    for number, line in enumerate(LINE_END.split(page.removeprefix(BOM)), 1):
        if RAW_HEADING.search(line):
            problems.append(f"{safe_push.DECISIONS}:{number}: an HTML heading tag (<h1> or "
                            "<h2>), which this check does not read: write the heading in "
                            "Markdown")
        if BLANK.fullmatch(line):
            start = last = None
            words, dates, held, noted, unread = [], [], set(), 0, []
            own_words = words
            continue
        kept, stripped = _stripped(line)
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
        unread.append((number, text, kept))
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
    """Require the checked commit and unchanged sources before running its commands. A
    file generated whole may differ from the head; one of safe_push.GENERATED_REGIONS only
    in its regions' bodies, since the rest, its markers among it, is written by hand
    (heath.outside). Its bytes are compared as they are, and a working file that is missing,
    a link or unreadable counts as changed."""
    if commit(repo, "HEAD") != head:
        raise Refused("checkout is not the supplied group head")
    changed = safe_push.git(repo, "diff", "--name-only", "-z", head, "--").split("\0")
    if any(path and not safe_push.under(path, GENERATED) for path in changed):
        raise Refused("checkout has source changes outside the supplied group head")
    for path in safe_push.GENERATED_REGIONS:
        if path not in changed:
            continue
        working = repo / path
        try:
            same = not working.is_symlink() and (
                heath.outside(path, working.read_bytes().decode("utf-8", "surrogateescape"))
                == heath.outside(path, (safe_push.show_bytes(repo, head, path) or b"")
                                 .decode("utf-8", "surrogateescape")))
        except OSError:
            same = False
        if not same:
            raise Refused("checkout has source changes outside the supplied group head: the "
                          f"part of {path} written by hand, outside its regions' bodies")


def gap_commands(repo: Path, checks: set[str], deleted: set[str] | None = None) -> list[list[str]]:
    """Choose tests once; skip proven deletions and refuse unexplained missing tests. A
    path under .github/, deleted or not, asks for every test GITHUB_TESTS names for it,
    and a deletion excuses none of them: while one is missing, the path refuses, naming
    it. A path it names no tests for refuses, naming it. A test GITHUB_TESTS names asks
    for itself, deleted or not, whether or not the group changes what it reads, so its
    deletion always refuses."""
    commands = set()
    deleted = deleted or set()
    readers = {}
    for path, tests in GITHUB_TESTS.items():
        for test in tests:
            readers.setdefault(test, []).append(path)
    for path in sorted(checks | (deleted & readers.keys())):
        github = path == ".github" or path.startswith(".github/")
        if github:
            if path not in GITHUB_TESTS:
                raise Refused(f"gaps: no tests are mapped to {path}: a path under .github/ "
                              "lands only once main's check_queue.py names its tests in "
                              "GITHUB_TESTS")
            candidates = list(GITHUB_TESTS[path])
        elif path in readers:
            candidates = [path]
        elif path in deleted:
            continue
        elif GAP_TEST.fullmatch(path):
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
            if candidate in deleted and candidate not in readers:
                continue
            target = repo / candidate
            if not target.is_file() or target.is_symlink():
                named = path if github else ", ".join(readers.get(candidate, ()))
                raise Refused(f"gaps: declared test is missing or not a regular file: {candidate}"
                              + (f", which GITHUB_TESTS names for {named}: it is never excused, "
                                 "deleted or not, until main's check_queue.py names others"
                                 if named else ""))
            command = ("python3", candidate) if candidate == "scripts/test_safe_push.py" \
                else ("python3", "-I", candidate)
            commands.add(command)
    return [list(command) for command in sorted(commands)]


def gaps(repo: Path, base: str, entries: list[dict]) -> list[list[str]]:
    """Choose the focused tests, and report acceptance's existing proposition verdicts;
    run nothing (run_gaps runs what this chooses)."""
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
    # An entry's deletion excuses no file restored by a later entry in the group.
    tracked = set(safe_push.git(repo, "ls-tree", "-r", "--name-only", "-z", "HEAD").split("\0"))
    return gap_commands(repo, checks, deleted - tracked)


def tokens_held() -> list[str]:
    """The names of this process's environment variables that may hold a token."""
    return sorted(key for key in os.environ if "TOKEN" in key.upper())


def run_gaps(repo: Path, commands: list[list[str]]) -> list[str]:
    """Run the chosen tests, the group's own code, each once. None runs while this
    process's environment holds a token: a test could read it there, or, on Linux, in
    its parent's environment (/proc/<ppid>/environ), so CI runs them with --run-plan in
    a step that holds none, after the step that reads GitHub has chosen them. The runner
    process still holds the job's read-only token (the module's docstring)."""
    held = tokens_held()
    if held:
        raise ValueError("gaps: this process's environment holds a token ("
                         + ", ".join(held) + "), which the tests could read: run them "
                         "with --run-plan, in a process that holds none")
    problems = []
    for command in commands:
        print("gaps: " + shlex.join(command), flush=True)
        result = safe_push.run(command, repo, env=dict(os.environ))
        print(result.stdout, end="", flush=True)
        print(result.stderr, end="", file=sys.stderr, flush=True)
        if result.returncode:
            problems.append(f"gaps: {shlex.join(command)} failed (exit {result.returncode})")
    return problems


def write_plan(path: Path, head: str, commands: list[list[str]]) -> None:
    """Record the chosen tests for --run-plan, as JSON naming the group head, in a file
    that must not exist yet."""
    with open(path, "x", encoding="utf-8") as plan:
        json.dump({"head": head, "commands": commands}, plan)
        plan.write("\n")
    for command in commands:
        print("gaps: chosen: " + shlex.join(command), flush=True)


def read_plan(repo: Path, head: str, path: Path) -> list[list[str]]:
    """The commands of a plan written by --gaps --plan for this head: each one that
    gap_commands chooses, python3 -I and a test_*.py file directly under tests/ or
    scripts/, or python3 and scripts/test_safe_push.py, naming a regular file of the
    checkout, each once. Anything else is unreadable."""
    plan = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(plan, dict) or set(plan) != {"head", "commands"} \
            or plan["head"] != head or not isinstance(plan["commands"], list):
        raise ValueError("gaps: the plan is not one for this head")
    commands = []
    for command in plan["commands"]:
        if command == ["python3", "scripts/test_safe_push.py"]:
            test = command[1]
        elif isinstance(command, list) and len(command) == 3 \
                and command[:2] == ["python3", "-I"] and isinstance(command[2], str) \
                and GAP_TEST.fullmatch(command[2]) and command[2] != "scripts/test_safe_push.py":
            test = command[2]
        else:
            raise ValueError("gaps: the plan holds a command that --gaps does not choose")
        target = repo / test
        if command in commands or target.is_symlink() or not target.is_file():
            raise ValueError(f"gaps: the plan repeats or misnames a test: {test}")
        commands.append(command)
    return commands


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head")
    parser.add_argument("--base")
    parser.add_argument("--repo")
    parser.add_argument("--github-json", type=Path)
    parser.add_argument("--gaps", action="store_true")
    parser.add_argument("--plan", type=Path)
    parser.add_argument("--run-plan", type=Path)
    parser.add_argument("--tree", type=Path)
    parser.add_argument("--render", action="store_true")
    parser.add_argument("--acceptance-run", action="store_true")
    parser.add_argument("--ci-workflow")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)
    waiting = (args.acceptance_run, args.ci_workflow, args.out)
    if args.tree is not None:
        if any((args.head, args.base, args.repo, args.github_json, args.gaps, args.plan,
                args.run_plan, *waiting)):
            parser.error("--tree accepts only --render")
    elif args.run_plan is not None:
        if any((args.base, args.repo, args.github_json, args.gaps, args.plan, args.render,
                *waiting)) or not args.head:
            parser.error("--run-plan needs --head and accepts nothing else")
    elif args.acceptance_run:
        if any((args.base, args.gaps, args.plan, args.render)) \
                or not all((args.head, args.repo, args.ci_workflow, args.out)):
            parser.error("--acceptance-run needs --head, --repo, --ci-workflow and --out, and "
                         "accepts --github-json alone beside them")
    elif args.ci_workflow is not None or args.out is not None:
        parser.error("--ci-workflow and --out belong to --acceptance-run")
    elif not all((args.head, args.base, args.repo)) or args.render:
        parser.error("group checks need --head, --base and --repo; --render belongs to --tree")
    elif args.plan is not None and not args.gaps:
        parser.error("--plan belongs to --gaps")
    try:
        if args.tree is not None:
            problems = tree_problems(args.tree.resolve(), args.render)
        elif args.acceptance_run:
            # The group's CI run's acceptance verdicts, read from GitHub alone: no Git, no
            # checkout, and nothing written until every reading has passed.
            if not SLUG.fullmatch(args.repo):
                raise ValueError("--repo must be owner/name")
            if not WORKFLOW_FILE.fullmatch(args.ci_workflow):
                raise ValueError("--ci-workflow must name a workflow file of "
                                 ".github/workflows/, alone")
            verdicts = acceptance_run(GitHub(args.repo, args.github_json),
                                      oid(args.head, "head"), args.ci_workflow)
            args.out.mkdir(parents=True, exist_ok=True)
            with open(args.out / "verdicts.json", "xb") as target:
                target.write(verdicts)
            print(f"acceptance: verdicts.json written to {args.out}", flush=True)
            problems = []
        elif args.run_plan is not None:
            # The group's tests, chosen by --gaps --plan, run here with no GitHub read.
            repo = Path.cwd()
            head = oid(args.head, "head")
            checkout(repo, head)
            problems = run_gaps(repo, read_plan(repo, head, args.run_plan))
        else:
            if not SLUG.fullmatch(args.repo):
                raise ValueError("--repo must be owner/name")
            repo = Path.cwd()
            head, base = commit(repo, oid(args.head, "head")), commit(repo, oid(args.base, "base"))
            if safe_push.git(repo, "rev-parse", "--is-shallow-repository").strip() != "false":
                raise ValueError("could not read complete history: shallow repository")
            checkout(repo, head)
            api = GitHub(args.repo, args.github_json)
            # The queue is read once, for its order, each entry's body and who queued,
            # edited and renamed each entry.
            queue_answer = api.read("queue")
            entries = chain(repo, base, head, api, queue_answer)
            actors = queue_actors(queue_answer)
            red = None
            for pr in entries:
                if "auto-revert" in pr["labels"] or pr["ref"].startswith("revert/"):
                    if pr["head_repo"] != args.repo:
                        raise Refused(f"#{pr['number']}: its head is not in {args.repo}")
                    exact_revert(repo, pr, api)
                else:
                    ordinary_entry(pr, actors, args.repo)
                    if pr["state"] == "OPEN":
                        # Read once, for the queued entries; a merged one is on main.
                        if red is None:
                            red = [issue["number"] for issue in red_issues(
                                api.read("main_red"))]
                        red_main_fix(pr, red)
                    preflight(repo, base, pr)
                    intact(repo, base, head, pr)
            # The judge runs none of the group's scripts: the generated pages' freshness
            # is the check job's (render.py and git status, on the same group), so rule
            # (d) here reads the page's blob only, never the checkout. The tests --gaps
            # chooses are the group's own code: with --plan they are only recorded, for
            # --run-plan to run.
            if not args.gaps:
                problems = heading_problems(page_blob(repo, head))
            elif args.plan is not None:
                write_plan(args.plan, head, gaps(repo, base, entries))
                problems = []
            else:
                problems = run_gaps(repo, gaps(repo, base, entries))
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
