#!/usr/bin/env python3
"""Hold a release while any issue or pull request labelled blocks-release is open.

    python3 scripts/check_release_gate.py [--repo OWNER/NAME]
    python3 scripts/check_release_gate.py --issues-json FILE
    python3 scripts/check_release_gate.py --results-current [--repo-dir DIR] [--rev REV]

Exit 0 when none is open, 1 when unfinished work holds the release, 2 when the issues
cannot be read. Fixtures are arrays in REST or gh issue list's JSON form. Live reads
use gh api --paginate when gh is installed, else the REST API with GITHUB_TOKEN,
following every page. Credentials never appear in a URL or an error message.
The pure judgement and page reader live in safe_push, whose copied harness must remain
self-contained. Python 3.11 or later; standard library only.

With --results-current it reads no issue, and judges instead whether the model's
committed results are the release head's own (#701). H is REV (default HEAD) of the
repository at DIR (default this folder), and C the commit its results name: line 4 of
each run's file in tests/model/results/, line 1 of summary.txt. Every one must name the
same C, with its harness files as committed; MODEL.md's counts must name C's first 12
digits; C must be an ancestor of H; and H may differ from C only in the release steps'
own outputs (docs/WORKFLOW.md, section 10, step 10): results files that name C,
MODEL.md inside its counts block, Audit/screen-run.toml, Audit/screen.py outside the
code the screen hashes, docs/reports/overlaps.md, the acceptance report, and one
decisions entry added. Any other change, a deletion included, is refused. Exit 0 when the
results are current; 1 when they are not, naming each path and why; 2 when the head, its
results, a header in the form run.py writes or C cannot be read. It reads git's objects
alone, with replacements and grafts off and every GIT_ variable of the environment set
aside, and never imports, runs or reads the working tree of the repository it judges.
"""

import argparse
import ast
import http.client
import itertools
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request
import warnings

from safe_push import (BLOCKS_RELEASE, DECISION_ENTRY, github_slug, issue_pages,
                       open_blockers, printable_text)


def repo_slug(value: str | None) -> str:
    """Resolve the repository without asking GitHub, and refuse URL metacharacters."""
    if value is None:
        value = os.environ.get("GITHUB_REPOSITORY")
    if not value:
        try:
            result = subprocess.run(["git", "remote", "get-url", "origin"],
                                    capture_output=True, text=True)
        except (OSError, UnicodeError):
            raise ValueError("cannot read origin; give --repo OWNER/NAME") from None
        value = github_slug(result.stdout.strip()) if result.returncode == 0 else None
    if not value or not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", value) \
            or any(part in {".", ".."} for part in value.split("/")):
        raise ValueError("no valid repository; give --repo OWNER/NAME")
    return value


class NoRedirect(urllib.request.HTTPRedirectHandler):
    """A redirect must not carry the token to another host."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def rest_issues(repo: str, token: str) -> list[dict]:
    """Read every page on GitHub's API host, including its numeric repository URLs."""
    path = f"/repos/{repo}/issues"
    url = f"https://api.github.com{path}?labels={BLOCKS_RELEASE}&state=open&per_page=100"
    opener = urllib.request.build_opener(NoRedirect())
    issues, seen = [], set()
    while url:
        parsed = urllib.parse.urlsplit(url)
        if parsed.scheme != "https" or parsed.netloc != "api.github.com" \
                or not (parsed.path == path or re.fullmatch(r"/repositories/\d+/issues",
                                                           parsed.path)) \
                or parsed.fragment or url in seen:
            raise ValueError("GitHub returned an invalid pagination link")
        seen.add(url)
        request = urllib.request.Request(url, headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "stoicheia-release-gate",
        })
        try:
            with opener.open(request, timeout=30) as response:
                page = json.load(response)
                link = response.headers.get("Link", "")
        except urllib.error.HTTPError as e:
            raise ValueError(f"HTTP {e.code}: {parsed.path}") from None
        except (OSError, UnicodeError, ValueError, http.client.HTTPException):
            raise ValueError(f"cannot read GitHub issues at {path}") from None
        if not isinstance(page, list):
            raise ValueError("GitHub did not return an array of issues")
        issues.extend(page)
        url = ""
        for part in link.split(",") if link else []:
            match = re.fullmatch(r'\s*<([^>]+)>\s*;\s*rel="([^"]+)"\s*', part)
            if not match:
                raise ValueError("GitHub returned an unreadable pagination link")
            if "next" in match.group(2).split():
                if url:
                    raise ValueError("GitHub returned more than one next page")
                url = match.group(1)
        # No Link header means this is the last page.
    return issues


def read_live(repo: str) -> list[dict]:
    gh = shutil.which("gh")
    if gh:
        path = f"repos/{repo}/issues?labels={BLOCKS_RELEASE}&state=open&per_page=100"
        try:
            result = subprocess.run([gh, "api", "--paginate", path],
                                    capture_output=True, text=True)
        except (OSError, UnicodeError):
            raise ValueError("cannot run gh to read issues") from None
        if result.returncode:
            raise ValueError(f"GitHub issue read failed (exit {result.returncode})")
        return issue_pages(result.stdout)
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        raise ValueError("reading GitHub needs gh or GITHUB_TOKEN")
    return rest_issues(repo, token)


# --------------------------------------------------------------------------------------
# --results-current (#701). What tests/model/run.py writes is restated here, since the
# judged repository's code is never imported; a test of tests/test_release_gate.py pins
# each to run.py, and the screen's rule and the paths of its file, its record and the
# acceptance report to Audit/screen.py and scripts/check_acceptance.py.

RESULTS = "tests/model/results"
RESULT_FILE = re.compile(r"tests/model/results/[^/]+\.txt")
SUMMARY = "summary.txt"   # names its commit on line 1; each run's file, on line 4
MODEL_MD = "tests/model/MODEL.md"
COMMITTED = "harness files as committed"
COUNTS = re.compile(r"(<!-- counts:begin -->\n).*?(\n<!-- counts:end -->)", re.S)
COUNTS_FROM = "Counts from `run.py --full --write` at commit `"
COMMIT_LINE = re.compile(r"# commit: ([0-9a-f]{40}) \(([^()]*)\)")
SCREEN = "Audit/screen.py"
# The release steps' other outputs, each with the changes to it that they may make.
OUTPUTS = {"Audit/screen-run.toml": {"A", "M"}, "docs/reports/overlaps.md": {"M"},
           "docs/reports/acceptance-books-I-III.md": {"M"}}
DONE = {"A": "added", "M": "modified", "D": "deleted", "T": "changed in type"}


class Unreadable(Exception):
    """What leaves the results unjudged, each line a reason: exit 2."""


def git_objects(repo: str, *args: str) -> subprocess.CompletedProcess:
    """git in the judged repository, with no replacements, no grafts and no GIT_ variable
    of ours, any of which could point it at another repository, object store, index,
    config or history."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env["GIT_GRAFT_FILE"] = os.devnull
    try:
        return subprocess.run(["git", *args], cwd=repo, env=env, capture_output=True,
                              stdin=subprocess.DEVNULL, timeout=300)
    except (OSError, subprocess.TimeoutExpired):
        raise Unreadable(f"git cannot be run in {printable_text(repo)}") from None


def blob(repo: str, name: str) -> bytes | None:
    done = git_objects(repo, "cat-file", "blob", name)
    return done.stdout if done.returncode == 0 else None


def without_docstring(text: str) -> str:
    """Audit/screen.py's rule of that name, restated: the text without its docstring, or
    the whole text when code shares the docstring's last line."""
    body = ast.parse(text).body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) \
            and isinstance(body[0].value.value, str):
        if len(body) > 1 and body[1].lineno <= body[0].end_lineno:
            return text
        lines = text.splitlines(keepends=True)
        return "".join(lines[:body[0].lineno - 1] + lines[body[0].end_lineno:])
    return text


def screen_code(data: bytes | None) -> str | None:
    """What the screen hashes of its own file, read as Path.read_text reads it there; None
    when there is none, or it is not UTF-8 Python."""
    if data is None:
        return None
    try:
        with warnings.catch_warnings():   # a warning would print the judged file's text
            warnings.simplefilter("ignore")
            return without_docstring(data.decode("utf-8").replace("\r\n", "\n")
                                     .replace("\r", "\n"))
    except (ValueError, SyntaxError, RecursionError, MemoryError):
        return None


def counts_blocks(data: bytes | None) -> list[re.Match]:
    """MODEL.md's counts blocks; none unless it opens one exactly once, so that the pattern,
    slow on many openings, never runs on more than one."""
    text = data.decode("utf-8", "surrogateescape") if data else ""
    if text.count("<!-- counts:begin -->") != 1:
        return []
    return list(COUNTS.finditer(text))


def outside_counts(data: bytes | None) -> str | None:
    """MODEL.md but for what its one counts block holds; None when it has not one."""
    blocks = counts_blocks(data)
    if len(blocks) != 1:
        return None
    return blocks[0].string[:blocks[0].end(1)] + blocks[0].string[blocks[0].start(2):]


def change_refused(repo: str, base: str, head: str, status: str, path: str) -> str | None:
    """Why a change from the results' commit to the head is no release step's, or None."""
    if RESULT_FILE.fullmatch(path) and status in {"A", "M"}:
        return None   # every results file at the head names the results' commit
    for name, read, where in ((MODEL_MD, outside_counts, "outside its one counts block"),
                              (SCREEN, screen_code, "in the code the screen hashes")):
        if path == name and status == "M":
            before, after = (read(blob(repo, f"{rev}:{path}")) for rev in (base, head))
            return None if before is not None and before == after else (
                f"changed {where} since {base[:12]}, the results' commit")
    if status in OUTPUTS.get(path, ()):
        return None
    return (f"{DONE.get(status, f'changed ({status})')} since {base[:12]}, the results' "
            "commit, and no release step does that")


def judge_results(repo: str, rev: str) -> tuple[str, str | None, list[str]]:
    """The head, the commit its results name (None unless one), and each reason they are
    not current, from git's objects alone; Unreadable when they cannot be judged."""
    found = git_objects(repo, "rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}") \
        if rev and not rev.startswith("-") else None
    if found is None or found.returncode:
        raise Unreadable(f"{printable_text(rev)} names no commit of the repository at "
                         f"{printable_text(repo)}")
    head = found.stdout.decode("ascii", "replace").strip()
    listing = git_objects(repo, "ls-tree", "-z", "--full-tree", f"{head}:{RESULTS}")
    if listing.returncode:
        raise Unreadable(f"{head[:12]} holds no {RESULTS}")
    refused, unread, commits = [], [], {}
    for meta, _, name in (r.partition(b"\t") for r in listing.stdout.split(b"\0") if r):
        name = name.decode("utf-8", "surrogateescape")
        if not RESULT_FILE.fullmatch(f"{RESULTS}/{name}"):
            continue
        shown = printable_text(f"{RESULTS}/{name}")
        mode, kind, oid = (meta.decode("ascii", "replace").split(" ") + ["", ""])[:3]
        if kind != "blob" or mode not in {"100644", "100755"}:
            refused.append(f"{shown}: not a regular file, as run.py writes each")
            continue
        data = blob(repo, oid)
        if data is None:
            raise Unreadable(f"{shown} does not read")
        header = list(itertools.takewhile(lambda line: line.startswith(b"# "),
                                          data.split(b"\n")))
        at = 0 if name == SUMMARY else 3
        match = COMMIT_LINE.fullmatch(header[at].decode("utf-8", "replace")) \
            if len(header) > at else None
        if not match or sum(line.startswith(b"# commit: ") for line in header) != 1:
            unread.append(f"{shown}: its header names no commit, once, on line {at + 1}, "
                          "in the form run.py writes")
            continue
        commits.setdefault(match.group(1), []).append(shown)
        if match.group(2) != COMMITTED:
            refused.append(f"{shown}: names {match.group(1)[:12]} with "
                           f"\"({printable_text(match.group(2))})\", "
                           f"not \"({COMMITTED})\": its run read other harness files")
    if unread:
        raise Unreadable(*unread)
    if not commits and not refused:
        raise Unreadable(f"{head[:12]} holds no results in {RESULTS}")
    if len(commits) != 1:
        if commits:
            refused.append(f"the results name {len(commits)} commits: " + "; ".join(
                f"{c[:12]} in {', '.join(paths)}" for c, paths in sorted(commits.items())))
        return head, None, refused
    commit = next(iter(commits))
    kind = git_objects(repo, "cat-file", "-t", commit)
    if kind.returncode:
        raise Unreadable(f"the results name {commit}, which this repository lacks")
    if kind.stdout.strip() != b"commit":
        return head, None, refused + [f"the results name {commit}, which is no commit"]
    blocks = counts_blocks(blob(repo, f"{head}:{MODEL_MD}"))
    named = len(blocks) == 1 and re.search(re.escape(COUNTS_FROM) + r"([0-9a-f]{12})`",
                                           blocks[0].group(0))
    if not named:
        refused.append(f"{MODEL_MD}: has no one counts block that names a commit")
    elif named.group(1) != commit[:12]:
        refused.append(f"{MODEL_MD}: its counts name {named.group(1)}, not {commit[:12]}, "
                       "the results' commit")
    ancestry = git_objects(repo, "merge-base", "--is-ancestor", commit, head)
    if ancestry.returncode == 1:
        return head, commit, refused + [f"{commit[:12]}, the results' commit, is not an "
                                        f"ancestor of {head[:12]}: they were run on other "
                                        "history"]
    diff = git_objects(repo, "diff", "--name-status", "-z", "--no-renames", "--no-ext-diff",
                       "--no-textconv", "--no-relative", "--ignore-submodules=none",
                       commit, head, "--")
    fields = diff.stdout.split(b"\0")[:-1]
    if ancestry.returncode or diff.returncode or len(fields) % 2:
        raise Unreadable(f"git cannot compare {head[:12]} with {commit[:12]}")
    entries = []
    for status, path in zip(fields[::2], fields[1::2]):
        status = status.decode("ascii", "replace")
        path = path.decode("utf-8", "surrogateescape")
        if DECISION_ENTRY.fullmatch(path) and status == "A":
            entries.append(printable_text(path))
        elif why := change_refused(repo, commit, head, status, path):
            refused.append(f"{printable_text(path)}: {why}")
    if len(entries) > 1:
        refused += [f"{path}: one of {len(entries)} decisions entries added, where a "
                    "release adds one" for path in entries]
    return head, commit, refused


def results_current(repo: str, rev: str) -> int:
    """--results-current: 0 when the results are current, 1 when not, 2 when unread."""
    try:
        head, commit, refused = judge_results(repo, rev)
    except Unreadable as e:
        for line in e.args:
            print(f"release gate: {line}", file=sys.stderr)
        return 2
    if refused:
        print(f"release gate: the model's results at {head[:12]} are not current:")
        for line in refused:
            print(f"  {line}")
        print("Run python3 -I tests/model/run.py --full --write at the release head, after "
              "every other change, and commit what it writes (docs/WORKFLOW.md, "
              "section 10, step 10).")
        return 1
    print(f"the model's results are current: they name {commit[:12]}, and {head[:12]} "
          "differs from it in the release steps' own outputs alone")
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--issues-json", metavar="FILE", help="read an offline JSON array")
    parser.add_argument("--repo", metavar="OWNER/NAME",
                        help="default: GITHUB_REPOSITORY, then origin")
    parser.add_argument("--results-current", action="store_true",
                        help="judge the model's committed results instead of the issues")
    parser.add_argument("--repo-dir", metavar="DIR", help="with --results-current: "
                        "the repository (default: this folder)")
    parser.add_argument("--rev", metavar="REV",
                        help="with --results-current: the head judged (default: HEAD)")
    args = parser.parse_args(argv)
    if args.results_current:
        if args.issues_json is not None or args.repo is not None:
            parser.error("--results-current reads no issue: give neither --issues-json "
                         "nor --repo")
        return results_current("." if args.repo_dir is None else args.repo_dir,
                               "HEAD" if args.rev is None else args.rev)
    if args.repo_dir is not None or args.rev is not None:
        parser.error("--repo-dir and --rev go with --results-current")
    try:
        if args.issues_json is not None:
            # An offline fixture needs no repository, git, gh or token.
            with open(args.issues_json, encoding="utf-8") as source:
                issues = json.load(source)
        else:
            issues = read_live(repo_slug(args.repo))
        blockers = open_blockers(issues)
    except (OSError, UnicodeError, ValueError) as e:
        # A file error can include its path; keep that and malformed JSON out of the
        # diagnostic too, since neither is needed to explain why the gate is closed.
        detail = "cannot read issues JSON" if args.issues_json is not None else str(e)
        print(f"release gate: {detail}", file=sys.stderr)
        return 2
    if blockers:
        for issue in blockers:
            print(f"#{issue['number']}: {printable_text(issue['title'])} "
                  f"({printable_text(issue.get('html_url') or issue['url'])})")
        return 1
    print("no open blocks-release issue")
    return 0


if __name__ == "__main__":
    sys.exit(main())
