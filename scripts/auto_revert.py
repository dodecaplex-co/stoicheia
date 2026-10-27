#!/usr/bin/env python3
"""Revert a failed main push through the queue, and leave a release-blocking issue.

The revert job runs this file from the previous main with Python's isolated mode,
only after that commit's latest post-merge run has concluded success.
It imports no repository code. Git works in a temporary clone with hooks, global
configuration and inherited credentials disabled. The job's own GITHUB_TOKEN pushes
the revert branch and writes the issue and its labels; the App's token, which reads
contents and writes none, opens, labels and enqueues the pull request.

Only a first-parent chain of two-parent pull request merges can be reverted. The
decisions record is history, only ever added to (docs/WORKFLOW.md, "Auto-revert"), so a
revert never removes a decision's text: it keeps docs/decisions/ and the decisions page
as at the reverted push's tip, as the advice for a revert by hand keeps them as
origin/main has them; everything else is the exact revert. Each revert reads merge
attributes from the push's before, the main whose own run passed, never from the
reverted tree (git --attr-source, Git 2.42 or later), as the queue's judge does. A
relative link of the kept record that resolves at the reverted push's tip but would not
in the revert (broken_links) would fail the revert's own link check, so such a revert
is not pushed: the issue names the links and says to revert by hand.
Unreadable history or metadata, missing credentials and conflicts leave an issue
without a pull request. A slow failure's issue can open after a later push's run has
passed and cleared. So, unless the revert is enqueued, this reads main's tip afresh: if
main has moved on, it removes the issue's main-red when the tip contains after, the
tip's latest post-merge run completed with success, and main still names that tip just
before the removal; if main has moved on, or its tip cannot be read, and the label
stays, the issue says how to clear it. Exit 0 means enqueued (or cleared, or nothing to
clear because main has moved on), 1 means issue only or an incomplete revert, 2 means
the issue itself could not be recorded or updated, and 3 means the revert was enqueued
but the issue could not be updated with that outcome.
--dry-run describes the actions without network access or changing the repository.
--clear is the coordinator's, run by hand from a checkout of main: without --after it
removes main-red from every open issue. With --after it removes the label
only from an issue whose exact After line names that commit or one of its ancestors,
and checks main again before each removal. The post-merge workflow's clear job does the
same with the runner's tools alone, since that job runs no repository code. If main has
moved on, it names that commit and its post-merge run, which decides (or says that no
such run can be read yet), and exits 0. A clear that fails at main's own tip fails.
"""

from __future__ import annotations

import argparse
import base64
import html
import json
import os
import posixpath
import re
import subprocess
import sys
import tempfile
import time
import unicodedata
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import unquote


# These are safe_push.py's protected paths, PROTECTED and PROTECTED_JUDGED; their order
# decides nothing, since protected() asks only whether any entry matches. This copy keeps
# the trusted script independent of the checkout. The tests compare what the two protect,
# so a train that changes safe_push's list changes this one too.
PROTECTED = (
    "scripts/", ".github/", "Certificate/", "tests/", "review/SCHEMA.md",
    "review/terms.toml", ".gitattributes", ".gitignore", "lakefile.toml",
    "lakefile.lean", "lean-toolchain", "lake-manifest.json", "checks/",
    "docs/ACCEPTANCE.md", "Audit/", "Audit.lean",
    "model/Model/Audit.lean", "model/Model.lean", "model/lakefile.toml",
    "model/lakefile.lean", "model/lean-toolchain", "model/lake-manifest.json",
    "model/lock.sha256",
)
KINDS = {"tooling", "text", "lean", "docs"}
LABELS = {
    "blocks-release": ("b60205", "Blocks a release until resolved"),
    "main-red": ("b60205", "Main's integration checks failed"),
    "auto-revert": ("fbca04", "Automatic revert of a failed main push"),
    "security-review": ("d93f0b", "Changes a protected path"),
    "tooling": ("ededed", "Scripts, CI and the harness"),
    "text": ("ededed", "Heath's text, commentary and the reader's pages"),
    "lean": ("ededed", "Proofs and statements"),
    "docs": ("ededed", "Guides, briefs and reports"),
}
# The decisions record: its entries (tooling/decision-entries), each a file of its own,
# and its page, safe_push.DECISIONS. A revert keeps both.
ENTRIES = "docs/decisions"
DECISIONS = "docs/briefs/0002-decisions.md"
KEPT = (ENTRIES, DECISIONS)
SHA = re.compile(r"[0-9a-f]{40}")
SLUG = re.compile(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+")
MERGE = re.compile(r"Merge pull request #([1-9][0-9]*) from \S+")
AFTER_LINE = re.compile(r"^After: ([0-9a-f]{40})$", re.MULTILINE)


class Refusal(Exception):
    """A reason the automatic operation cannot safely continue."""


class HTTPFailure(Exception):
    """An HTTP status, without the response body or any credentials."""

    def __init__(self, status: int):
        self.status = status


class NoRedirect(urllib.request.HTTPRedirectHandler):
    """Never send an authenticated request to a redirect target."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def request(method: str, path: str, token: str, data=None):
    """The injectable HTTP boundary. No response or exception is printed."""
    body = None if data is None else json.dumps(data).encode()
    req = urllib.request.Request(
        "https://api.github.com" + path, data=body, method=method,
        headers={"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
                 "X-GitHub-Api-Version": "2022-11-28", "Content-Type": "application/json"})
    try:
        with urllib.request.build_opener(NoRedirect).open(req, timeout=30) as response:
            content = response.read()
            return json.loads(content) if content else None
    except urllib.error.HTTPError as exc:
        raise HTTPFailure(exc.code) from None
    except Exception:
        raise Refusal("GitHub's response could not be read.") from None


class GitHub:
    """Read and write through one injectable HTTP function."""

    def __init__(self, repo: str, token: str, http):
        self.root = f"/repos/{repo}"
        self.token = token
        self.http = http

    def call(self, method: str, path: str, data=None):
        try:
            result = self.http(method, path, self.token, data)
        except HTTPFailure as exc:
            raise Refusal(f"GitHub refused {method} {path} (HTTP {exc.status}).") from None
        except Exception:
            raise Refusal(f"GitHub could not complete {method} {path}.") from None
        if isinstance(result, dict) and result.get("errors"):
            raise Refusal("GitHub reported a GraphQL error.")
        return result

    def pages(self, path: str) -> list:
        result = []
        for page in range(1, 1001):
            separator = "&" if "?" in path else "?"
            rows = self.call("GET", f"{path}{separator}per_page=100&page={page}")
            if not isinstance(rows, list) or any(not isinstance(row, dict) for row in rows):
                raise Refusal("GitHub returned an unreadable list.")
            result.extend(rows)
            if len(rows) < 100:
                return result
        raise Refusal("GitHub's list exceeded the pagination limit.")

    def ensure_labels(self, names) -> None:
        rows = self.pages(self.root + "/labels")
        if any(not isinstance(row.get("name"), str) for row in rows):
            raise Refusal("GitHub returned an unreadable label.")
        known = {row["name"] for row in rows}
        for name in sorted(set(names) - known):
            colour, description = LABELS[name]
            label = self.call("POST", self.root + "/labels",
                              {"name": name, "color": colour, "description": description})
            if not isinstance(label, dict) or label.get("name") != name:
                raise Refusal("GitHub did not confirm the new label.")


def git_env() -> dict:
    """Give git no inherited credentials, hooks or external configuration."""
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("GIT_", "STOICHEIA_REVERT_"))
           and key not in {"GITHUB_TOKEN", "GH_TOKEN"}}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_TERMINAL_PROMPT="0", GIT_AUTHOR_NAME="Stoicheia revert",
               GIT_AUTHOR_EMAIL="revert@stoicheia.invalid",
               GIT_COMMITTER_NAME="Stoicheia revert",
               GIT_COMMITTER_EMAIL="revert@stoicheia.invalid")
    return env


def git(repo: Path, *args: str, env=None) -> str:
    result = subprocess.run(
        ["git", "-c", "core.hooksPath=/dev/null", "-c", "core.fsmonitor=false",
         "-c", "commit.gpgSign=false", *args], cwd=repo, env=env or git_env(),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False, timeout=120)
    if result.returncode:
        # A subprocess error can contain credentials or untrusted repository text.
        command = next((arg for arg in args if not arg.startswith("-")), args[0])
        raise Refusal(f"git {command} failed.")
    return result.stdout.rstrip("\n")


def blob(repo: Path, sha: str) -> bytes:
    """A blob's bytes as they are, for the link check."""
    result = subprocess.run(
        ["git", "-c", "core.hooksPath=/dev/null", "cat-file", "blob", sha], cwd=repo,
        env=git_env(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
        timeout=120)
    if result.returncode:
        raise Refusal("git cat-file failed.")
    return result.stdout


@dataclass
class Train:
    sha: str
    head: str
    number: int
    title: str = "Title not yet read"
    labels: tuple[str, ...] = ()


def trains(repo: Path, before: str, after: str) -> list[Train]:
    """Read the whole first-parent chain before attempting any revert."""
    for sha in (before, after):
        if not SHA.fullmatch(sha) or not sha.strip("0"):
            raise Refusal("Before and after must be non-zero, full commit SHAs.")
        if git(repo, "rev-parse", "--verify", sha + "^{commit}") != sha:
            raise Refusal("The push does not name an available commit.")
    rows = git(repo, "rev-list", "--first-parent", "--parents",
               f"{before}..{after}").splitlines()
    if not rows:
        raise Refusal("The push has no train merges.")
    expected = after
    result = []
    for row in rows:
        parents = row.split()
        if len(parents) != 3 or parents[0] != expected:
            raise Refusal("The first-parent chain contains a non-merge or an unexpected merge.")
        sha, expected, head = parents
        subject = git(repo, "show", "-s", "--format=%s", sha)
        match = MERGE.fullmatch(subject)
        if not match:
            raise Refusal(f"Merge {sha} does not identify a pull request.")
        result.append(Train(sha, head, int(match[1])))
    if expected != before:
        raise Refusal("Before is not on after's first-parent chain.")
    if len({train.number for train in result}) != len(result):
        raise Refusal("The first-parent chain repeats a pull request.")
    return result


def read_trains(api: GitHub, entries: list[Train], repo: str) -> None:
    for train in entries:
        data = api.call("GET", f"{api.root}/pulls/{train.number}")
        if (not isinstance(data, dict) or data.get("number") != train.number
                or data.get("merged") is not True or data.get("merge_commit_sha") != train.sha
                or data.get("head", {}).get("sha") != train.head
                or data.get("base", {}).get("ref") != "main"
                or data.get("base", {}).get("repo", {}).get("full_name") != repo
                or not isinstance(data.get("title"), str) or not data["title"].strip()):
            raise Refusal(f"Pull request #{train.number} does not confirm the train merge.")
        labels = data.get("labels")
        if (not isinstance(labels, list) or any(not isinstance(label, dict)
                or not isinstance(label.get("name"), str) for label in labels)):
            raise Refusal(f"Pull request #{train.number} has unreadable labels.")
        train.title = data["title"]
        train.labels = tuple(label["name"] for label in labels)
        if not KINDS.intersection(train.labels):
            raise Refusal(f"Pull request #{train.number} has no kind label.")


def protected(path: str) -> bool:
    return any(path == prefix or (prefix.endswith("/") and path.startswith(prefix))
               for prefix in PROTECTED)


def installation_token(api: GitHub, app_id: str, key: str, repo: str) -> str:
    """Sign an RS256 JWT with openssl, then request a repository-scoped token."""
    if not re.fullmatch(r"[1-9][0-9]*", app_id):
        raise Refusal("STOICHEIA_REVERT_APP_ID is not a numeric App id.")

    def encoded(value: bytes) -> str:
        return base64.urlsafe_b64encode(value).decode().rstrip("=")

    now = int(time.time())
    header = encoded(json.dumps({"alg": "RS256", "typ": "JWT"}).encode())
    claims = encoded(json.dumps({"iat": now - 60, "exp": now + 540, "iss": app_id}).encode())
    unsigned = f"{header}.{claims}"
    with tempfile.TemporaryDirectory(prefix="stoicheia-revert-key-") as directory:
        path = Path(directory) / "key.pem"
        path.touch(mode=0o600)
        path.write_text(key, encoding="utf-8")
        signed = subprocess.run(["openssl", "dgst", "-sha256", "-sign", str(path)],
                                input=unsigned.encode(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, env=git_env(), check=False, timeout=30)
    if signed.returncode or not signed.stdout:
        raise Refusal("openssl could not sign the App token request.")
    app = GitHub(repo, f"{unsigned}.{encoded(signed.stdout)}", api.http)
    installation = app.call("GET", api.root + "/installation")
    if (not isinstance(installation, dict) or type(installation.get("id")) is not int
            or installation["id"] <= 0):
        raise Refusal("GitHub did not identify the App installation.")
    # The App writes nothing to the repository's contents: the job's own GITHUB_TOKEN,
    # which lasts only as long as the job, pushes the revert branch. So a key taken from
    # the App can make no branch, tag or release; it opens and labels the revert
    # (pull_requests: write), which starts its CI as GITHUB_TOKEN's could not, and puts it
    # in the queue (merge_queues: write).
    permissions = {"contents": "read", "pull_requests": "write", "merge_queues": "write"}
    data = app.call("POST", f"/app/installations/{installation['id']}/access_tokens",
                    {"repositories": [repo.split("/")[1]], "permissions": permissions})
    if (not isinstance(data, dict) or not isinstance(data.get("token"), str)
            or not data["token"] or any(c.isspace() for c in data["token"])):
        raise Refusal("GitHub did not return an installation token.")
    return data["token"]


def push_branch(repo: Path, slug: str, branch: str, token: str) -> None:
    """Keep the credential out of command arguments, URLs and git's config files."""
    if not re.fullmatch(r"revert/[0-9a-f]{12}", branch):
        raise Refusal("Only revert/<12 lower-case hex digits> branches may be pushed.")
    env = git_env()
    credential = base64.b64encode(f"x-access-token:{token}".encode()).decode()
    env.update(GIT_CONFIG_COUNT="1",
               GIT_CONFIG_KEY_0="http.https://github.com/.extraheader",
               GIT_CONFIG_VALUE_0=f"Authorization: Basic {credential}")
    git(repo, "push", "--porcelain", f"https://github.com/{slug}.git",
        f"HEAD:refs/heads/{branch}", env=env)


def keep_decisions(target: Path, after: str) -> None:
    """Put docs/decisions/ and the decisions page back as they were at `after`, the
    reverted push's tip and the revert's base, in a commit of its own; nothing when the
    reverts left both as they were. A path absent at `after` is left absent."""
    kept = {path: git(target, "ls-tree", after, "--", path) for path in KEPT}
    if any(git(target, "ls-tree", "HEAD", "--", path) != kept[path] for path in KEPT):
        for path in KEPT:
            git(target, "rm", "-r", "-q", "--ignore-unmatch", "--", path)
            if kept[path]:
                git(target, "checkout", after, "--", path)
        git(target, "commit", "-q", "-m",
            f"Keep {ENTRIES}/ and {DECISIONS} as at {after[:12]}: decisions are history")
    for path in KEPT:
        if git(target, "ls-tree", "HEAD", "--", path) != kept[path]:
            raise Refusal(f"The revert could not keep {path} as at the failed push.")


# The links of the kept record, read and resolved as scripts/check_links.py reads and
# resolves them: its patterns and functions, copied, since this script imports no
# repository code. The tests hold the two together.
SCHEME = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")
LINE_ANCHOR = re.compile(r"L(\d+)(?:C\d+)?(?:-L(\d+)(?:C\d+)?)?")
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
ATX = re.compile(r"^ {0,3}(#{1,6})(?:[ \t]+(.*?))?(?:[ \t]+#+)?[ \t]*$")
SETEXT = re.compile(r"^ {0,3}(=+|-+)[ \t]*$")
COMMENT = re.compile(r"<!--.*?-->", re.S)
LINK_TEXT = re.compile(r"(?<!\\)\[(?:[^\[\]\\]|\\.|\[(?:[^\[\]\\]|\\.)*\])*\]\(")
REF_DEF = re.compile(r"^ {0,3}\[((?:[^\[\]\\]|\\.)+)\]:[ \t]*(<[^>]*>|\S+)")
HTML_URL = re.compile(r"<[A-Za-z][^>]*?\b(?:href|src)\s*=\s*(\"[^\"]*\"|'[^']*')", re.S)
HTML_ANCHOR = re.compile(r"<[A-Za-z][^>]*?\b(?:name|id)\s*=\s*(\"[^\"]*\"|'[^']*')", re.S)
# So many links are named in the issue at most, which GitHub limits in length.
SHOWN_LINKS = 20


def blank_code(text: str) -> list[str]:
    """The text's lines with fenced code blocks and HTML comments blanked, as
    check_links.blank_code does."""
    text = COMMENT.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text)
    lines = text.split("\n")
    fence = None
    for i, line in enumerate(lines):
        m = FENCE.match(line)
        if fence:
            if m and m.group(1)[0] == fence[0] and len(m.group(1)) >= len(fence) \
                    and not line.strip()[len(m.group(1)):].strip():
                fence = None
            lines[i] = ""
        elif m:
            fence = m.group(1)
            lines[i] = ""
    return lines


def blank_spans(line: str) -> str:
    """A line with its inline code spans blanked, as check_links.blank_spans does."""
    out, i = [], 0
    while i < len(line):
        if line[i] == "`":
            run = len(line[i:]) - len(line[i:].lstrip("`"))
            close = line.find("`" * run, i + run)
            while close >= 0 and line[close + run:close + run + 1] == "`":
                close = line.find("`" * run, close + run + 1)
            if close >= 0:
                out.append(" " * (close + run - i))
                i = close + run
                continue
            out.append(line[i:i + run])
            i += run
            continue
        out.append(line[i])
        i += 1
    return "".join(out)


def destination(line: str, start: int) -> str | None:
    """An inline link's target, as check_links.destination reads it."""
    rest = line[start:].lstrip()
    if rest.startswith("<"):
        end = rest.find(">")
        return rest[1:end] if end > 0 else None
    depth, out = 0, []
    for ch in rest:
        if ch == "(":
            depth += 1
        elif ch == ")":
            if depth == 0:
                break
            depth -= 1
        elif ch.isspace():
            break
        out.append(ch)
    return "".join(out)


def links(text: str):
    """(line number, target) for every link in Markdown text, as check_links.links reads
    a file."""
    for number, line in enumerate(blank_code(text), 1):
        m = REF_DEF.match(line)
        if m:
            yield number, m.group(2).strip("<>")
            continue
        spans = blank_spans(line)
        for m in LINK_TEXT.finditer(spans):
            target = destination(line, m.end())
            if target is not None:
                yield number, target
        for m in HTML_URL.finditer(spans):
            yield number, html.unescape(m.group(1)[1:-1])


def heading_text(raw: str) -> str:
    """A heading's text as GitHub renders it, as check_links.heading_text reads it."""
    s = re.sub(r"!?\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\([^)]*\)", r"\1", raw)
    s = re.sub(r"!?\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\[[^\]]*\]", r"\1", s)
    s = re.sub(r"(`+)(.*?)\1", r"\2", s)
    s = re.sub(r"<[^>]+>", "", s)
    s = re.sub(r"\\([!-/:-@\[-`{-~])", r"\1", s)
    s = s.replace("*", "")
    s = re.sub(r"(?<!\w)_+|_+(?!\w)", "", s)
    return html.unescape(s).strip()


def slug(text: str) -> str:
    """GitHub's slug of a heading's text, as check_links.slug gives it."""
    kept = [ch for ch in text.lower() if ch in " -" or unicodedata.category(ch)[0] in "LM"
            or unicodedata.category(ch) in ("Nd", "Pc")]
    return "".join(kept).replace(" ", "-")


def anchors(text: str) -> frozenset:
    """Every #anchor of Markdown text, as check_links.anchors finds a file's."""
    lines = blank_code(text)
    found, seen = set(), {}

    def add(raw):
        base = slug(heading_text(raw))
        count = seen.get(base, 0)
        found.add(base if count == 0 else f"{base}-{count}")
        seen[base] = count + 1

    previous = ""
    for line in lines:
        m = ATX.match(line)
        if m:
            add(m.group(2) or "")
        elif SETEXT.match(line) and previous.strip() and not re.match(
                r"^ {0,3}([#|>*+-]|\d+[.)]|<)", previous) and not SETEXT.match(previous):
            add(previous.strip())
        for m in HTML_ANCHOR.finditer(blank_spans(line)):
            found.add(html.unescape(m.group(1)[1:-1]))
        previous = line
    return frozenset(found)


def relative(target: str) -> bool:
    """A link check_links.py checks: not a web address, mail or other scheme, and not
    empty."""
    target = target.strip()
    return bool(target) and not SCHEME.match(target) and not target.startswith("//")


def markdown(data: bytes) -> str:
    """A Markdown file's text as check_links.py reads it: UTF-8, line ends made line
    feeds."""
    return data.decode("utf-8", errors="replace").replace("\r\n", "\n").replace("\r", "\n")


def tree_entries(repo: Path, rev: str) -> dict[str, tuple[str, str]]:
    """Every path of `rev`'s tree, folders included, with its object's type and name."""
    result = {}
    for row in git(repo, "ls-tree", "-r", "-t", "-z", rev).split("\0"):
        if row:
            meta, _, path = row.partition("\t")
            result[path] = tuple(meta.split()[1:3])
    return result


def resolves(repo: Path, tree: dict, path: str, anchor: str, cache: dict) -> bool:
    """Whether a link to `path`, from the root ("" is the root itself), with `anchor`,
    resolves in `tree`, as check_links.check_link resolves it: to a file or a folder;
    an anchor to a heading or an HTML name or id of a Markdown file (a folder's
    README.md), or to lines of any other file."""
    entry = ("tree", "") if not path else tree.get(path)
    if entry is None:
        return False
    if not anchor:
        return True
    if entry[0] == "tree":
        path = f"{path}/README.md" if path else "README.md"
        entry = tree.get(path)
        if entry is None or entry[0] != "blob":
            return False
    if entry[1] not in cache:
        cache[entry[1]] = blob(repo, entry[1])
    data = cache[entry[1]]
    if path.endswith(".md"):
        if ("#", entry[1]) not in cache:
            cache["#", entry[1]] = anchors(markdown(data))
        return anchor in cache["#", entry[1]]
    lines = LINE_ANCHOR.fullmatch(anchor)
    if not lines:
        return False
    first, last = int(lines.group(1)), int(lines.group(2) or lines.group(1))
    count = data.count(b"\n") + (0 if data.endswith(b"\n") or not data else 1)
    return 1 <= first <= last <= count


def broken_links(repo: Path, after: str, head: str) -> list[str]:
    """The relative links of the kept record, the decisions page and the Markdown files
    under docs/decisions/ as at `after`, that resolve at `after` but would not at
    `head`, the revert: a file or folder it takes away, or a heading or lines a linked
    file loses. Each is named as file:line: target. A link already broken at `after` is
    not the revert's doing, and is left to the link check."""
    kept_tree, revert_tree = tree_entries(repo, after), tree_entries(repo, head)
    files = sorted(path for path, (kind, _) in kept_tree.items()
                   if kind == "blob" and path.endswith(".md")
                   and (path == DECISIONS or path.startswith(ENTRIES + "/")))
    cache: dict = {}
    broken = []
    for name in files:
        for number, target in links(markdown(blob(repo, kept_tree[name][1]))):
            if not relative(target):
                continue
            path, _, anchor = target.strip().partition("#")
            path, anchor = unquote(path.split("?", 1)[0]), unquote(anchor)
            if not path:
                where = name
            elif path.startswith("/"):
                where = posixpath.normpath(path.lstrip("/") or ".")
            else:
                where = posixpath.normpath(posixpath.join(posixpath.dirname(name), path))
            if where == ".." or where.startswith("../"):
                continue
            where = "" if where == "." else where
            if resolves(repo, kept_tree, where, anchor, cache) \
                    and not resolves(repo, revert_tree, where, anchor, cache):
                broken.append(f"{name}:{number}: {target}")
    return broken


def make_revert(source: Path, target: Path, before: str, after: str,
                entries: list[Train]) -> tuple[str, list[str]]:
    git(source, "clone", "--local", "--no-hardlinks", "--no-checkout", str(source), str(target))
    git(target, "switch", "--create", f"revert/{after[:12]}", after)
    for train in entries:
        try:
            # Merge attributes come from before, the main whose own run passed, never
            # from the tree being reverted.
            git(target, f"--attr-source={before}", "revert", "--no-edit", "-m", "1",
                train.sha)
        except Refusal:
            raise Refusal(f"Revert of {train.sha} did not apply cleanly; "
                          "no pull request opened.") from None
    keep_decisions(target, after)
    head = git(target, "rev-parse", "HEAD")
    paths = git(target, "diff", "--no-renames", "--name-only", "-z", after, head).split("\0")
    if not any(paths):
        raise Refusal("The revert would change no files.")
    return head, [path for path in paths if path]


def issue_body(args, entries: list[Train], outcome: str) -> str:
    names = "\n".join(f"- #{t.number}: {t.title} (merge `{t.sha}`)" for t in entries)
    return (f"Main's integration checks failed.\n\nBefore: {args.before}\nAfter: {args.after}\n\n"
            f"Trains, newest first:\n{names or 'The train list could not be read.'}\n\n"
            f"Failed jobs:\n{args.failed_jobs}\n\nFailed run: {args.run_id}\n"
            f"Run: {args.run_url}\n\n{outcome}\n")


def main_tip(api: GitHub) -> str:
    """Main's tip as GitHub names it now; an unreadable answer refuses."""
    data = api.call("GET", api.root + "/git/ref/heads/main")
    named = data.get("object") if isinstance(data, dict) else None
    sha = named.get("sha") if isinstance(named, dict) else None
    if not isinstance(sha, str) or not SHA.fullmatch(sha):
        raise Refusal("Main's tip could not be read.")
    return sha


def later_run(api: GitHub, repo: str, tip: str) -> str:
    """The run that decides once main has moved on to tip, read for the message alone:
    that push's post-merge run by id and address, or, when none can be read yet, so."""
    try:
        data = api.call("GET", f"{api.root}/actions/workflows/post-merge.yml/runs?"
                               f"head_sha={tip}&event=push&branch=main&per_page=100")
    except Refusal:
        data = None
    runs = data.get("workflow_runs") if isinstance(data, dict) else None
    ids = []
    if isinstance(runs, list) and all(isinstance(run, dict) for run in runs):
        ids = [run.get("id") for run in runs
               if run.get("head_sha") == tip and run.get("head_branch") == "main"
               and run.get("event") == "push"
               and run.get("path") == ".github/workflows/post-merge.yml"]
    if not ids or any(type(run) is not int or run <= 0 for run in ids):
        return f"no post-merge run for {tip} could be read yet; the later push's run decides"
    return (f"the later push's post-merge run {max(ids)}, "
            f"https://github.com/{repo}/actions/runs/{max(ids)}, decides")


def issue_after(row: dict) -> str | None:
    body = row.get("body")
    if not isinstance(body, str):
        return None
    matches = AFTER_LINE.findall(body)
    return matches[0] if len(matches) == 1 else None


def is_ancestor(repo: Path, ancestor: str, descendant: str) -> bool:
    try:
        result = subprocess.run(
            ["git", "-c", "core.hooksPath=/dev/null", "-c", "core.fsmonitor=false",
             "merge-base", "--is-ancestor", ancestor, descendant],
            cwd=repo, env=git_env(), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            check=False, timeout=120)
    except Exception:
        return False
    return result.returncode == 0


def github_is_ancestor(api: GitHub, ancestor: str, descendant: str) -> bool:
    """Whether GitHub's comparison shows `descendant` ahead of `ancestor` and not behind
    it; any answer that cannot be read so is no."""
    try:
        data = api.call("GET", f"{api.root}/compare/{ancestor}...{descendant}")
    except Exception:
        return False
    if not isinstance(data, dict):
        return False
    base = data.get("base_commit")
    merge_base = data.get("merge_base_commit")
    return (data.get("status") == "ahead"
            and type(data.get("ahead_by")) is int and data["ahead_by"] > 0
            and type(data.get("behind_by")) is int and data["behind_by"] == 0
            and isinstance(base, dict) and base.get("sha") == ancestor
            and isinstance(merge_base, dict) and merge_base.get("sha") == ancestor)


# What a failure's issue says when its main-red stays although main may have moved on.
HOW_TO_CLEAR = ("Once main's tip has a post-merge run that passed, re-run that run's clear "
                "job: it removes main-red from every open issue whose After main's tip "
                "contains (docs/WORKFLOW.md, \"Out of a red main\").")


def runs_at(api: GitHub, sha: str) -> list[dict]:
    """Every post-merge run of a push to main at `sha`, every page read, as the revert job
    reads the previous main's: a list unreadable, miscounted, with a run twice, or with a
    run of another commit, branch, event or workflow refuses."""
    query = (f"{api.root}/actions/workflows/post-merge.yml/runs?head_sha={sha}"
             "&event=push&branch=main&per_page=100")
    runs, count = [], None
    for page in range(1, 1001):
        data = api.call("GET", f"{query}&page={page}")
        rows = data.get("workflow_runs") if isinstance(data, dict) else None
        total = data.get("total_count") if isinstance(data, dict) else None
        if (not isinstance(rows, list) or type(total) is not int or total < 0
                or count not in (None, total)):
            raise Refusal(f"The post-merge runs at {sha} could not be read.")
        count = total
        runs.extend(rows)
        if len(rows) < 100:
            break
    else:
        raise Refusal("GitHub's list exceeded the pagination limit.")
    if (len(runs) != count or any(
            not isinstance(run, dict) or type(run.get("id")) is not int or run["id"] <= 0
            or run.get("head_sha") != sha or run.get("head_branch") != "main"
            or run.get("event") != "push"
            or run.get("path") != ".github/workflows/post-merge.yml"
            or not isinstance(run.get("status"), str) or "conclusion" not in run
            or not isinstance(run["conclusion"], (str, type(None))) for run in runs)
            or len({run["id"] for run in runs}) != len(runs)):
        raise Refusal(f"The post-merge runs at {sha} could not be read.")
    return runs


def clear_moved_on(api: GitHub, repo: str, after: str, number: int) -> str:
    """What becomes of the main-red of issue `number`, which the failed push `after` has
    just opened: "" while main's tip is still `after`, since a later push's clear will
    see the issue. A later push's run may have passed, and cleared, before the issue
    existed, so the label comes off here, but only on evidence read now: main's tip
    contains `after`, by GitHub's comparison (this job's checkout, of `after`, cannot
    hold a later tip), the tip's latest post-merge run, by id with every page read,
    completed with success, and main names that tip still just before the removal.
    Otherwise the label stays, and the issue says how to clear it."""
    try:
        tip = main_tip(api)
    except Exception:
        return (f"Main's tip could not be read to see whether main has moved on from "
                f"{after}, and main-red stays. {HOW_TO_CLEAR}")
    if tip == after:
        return ""
    try:
        if not github_is_ancestor(api, after, tip):
            raise Refusal(f"{tip} could not be shown to contain {after}")
        try:
            runs = runs_at(api, tip)
        except Exception:
            raise Refusal(f"the post-merge runs at {tip} could not be read") from None
        if not runs:
            raise Refusal(f"no post-merge run at {tip} can be read yet")
        latest = max(runs, key=lambda run: run["id"])
        if latest["status"] != "completed" or latest["conclusion"] != "success":
            raise Refusal(f"its latest post-merge run, {latest['id']}, has not completed "
                          "with success")
        try:
            now = main_tip(api)
        except Exception:
            raise Refusal("main's tip could not be read again before the label could be "
                          "removed") from None
        if now != tip:
            raise Refusal(f"main moved again, to {now}, before the label could be removed")
        try:
            labels = api.call("DELETE", f"{api.root}/issues/{number}/labels/main-red")
        except Exception:
            labels = None
        if (not isinstance(labels, list) or any(not isinstance(label, dict)
                or not isinstance(label.get("name"), str) or label["name"] == "main-red"
                for label in labels)):
            raise Refusal("GitHub did not confirm the removal")
    except Exception as exc:
        reason = str(exc) if isinstance(exc, Refusal) else "its evidence could not be read"
        return (f"Main has moved on from {after} to {tip}, and main-red stays: {reason}. "
                f"{HOW_TO_CLEAR}")
    return (f"Main has moved on from {after} to {tip}, which contains it, and its latest "
            f"post-merge run, {latest['id']}, https://github.com/{repo}/actions/runs/"
            f"{latest['id']}, completed with success: main-red was removed from this issue; "
            "blocks-release and the issue remain.")


def clear(api: GitHub, repo: str, after: str | None, source: Path) -> int:
    if after:
        tip = main_tip(api)
        if tip != after:
            # Main has moved on only when its tip, read now, is another commit: then
            # this success clears nothing and the later push's run decides. Any other
            # failure of the clear, at main's own tip, fails.
            print(f"Main has moved on from {after} to {tip}: {later_run(api, repo, tip)}, "
                  "and no label was changed.")
            return 0
    rows = api.pages(api.root + "/issues?state=open&labels=main-red")
    numbers = []
    for row in rows:
        if (type(row.get("number")) is not int or row["number"] <= 0
                or row.get("state") != "open" or not isinstance(row.get("labels"), list)
                or not any(isinstance(label, dict) and label.get("name") == "main-red"
                           for label in row["labels"])):
            raise Refusal("GitHub returned an unreadable main-red issue.")
        if "pull_request" in row:
            continue
        number = row["number"]
        if after:
            recorded = issue_after(row)
            if recorded is None:
                print(f"Issue #{number} keeps main-red: its After line is missing or unreadable.")
                continue
            if not is_ancestor(source, recorded, after):
                print(f"Issue #{number} keeps main-red: its After commit is not {after} "
                      "or an ancestor of it.")
                continue
        numbers.append(number)
    for number in numbers:
        if after:
            tip = main_tip(api)
            if tip != after:
                print(f"Main has moved on from {after} to {tip}: {later_run(api, repo, tip)}, "
                      "and no further label was changed.")
                return 0
        labels = api.call("DELETE", f"{api.root}/issues/{number}/labels/main-red")
        if (not isinstance(labels, list) or any(not isinstance(label, dict)
                or not isinstance(label.get("name"), str) or label["name"] == "main-red"
                for label in labels)):
            raise Refusal(f"GitHub did not confirm clearing main-red from issue #{number}.")
        print(f"Removed main-red from issue #{number}; blocks-release and the issue remain.")
    return 0


def dry_run(args, repo: Path, env: dict) -> int:
    root = f"/repos/{args.repo}"
    if args.clear:
        if args.after:
            print(f"Would check main still names {args.after}, and change no label if "
                  "it has moved on, naming the later push's post-merge run.")
            print("Would keep main-red on an issue without one exact After line naming "
                  "that commit or its ancestor, and check main again before each removal.")
        print(f"Would GET every page of {root}/issues?state=open&labels=main-red.")
        print("Would DELETE main-red from each eligible open issue, keeping blocks-release "
              "and the issue.")
        return 0
    entries = trains(repo, args.before, args.after)
    for train in entries:
        print(f"Would GET {root}/pulls/{train.number} and verify merge {train.sha} "
              "and its labels.")
    print("Would list labels, create missing blocks-release and main-red labels, "
          "and open the issue.")
    print(issue_body(args, entries, "Dry run; no requests sent."))
    print("Would, unless a revert is enqueued, read main's tip afresh and remove main-red "
          "from the issue only if main has moved on to a commit that contains after, whose "
          "latest post-merge run completed with success, and which main still names just "
          "before the removal; if main has moved on, or its tip cannot be read, and the "
          "label stays, say in the issue how to clear it.")
    if not env.get("STOICHEIA_REVERT_APP_ID") or not env.get("STOICHEIA_REVERT_APP_KEY"):
        print("No App secrets: would record issue only, saying automatic revert is unavailable.")
        return 1
    print(f"Would clone locally and create branch revert/{args.after[:12]} from {args.after}.")
    for train in entries:
        print(f"Would git revert --no-edit -m 1 {train.sha}, with merge attributes from "
              f"{args.before} (git --attr-source).")
    print(f"Would keep {ENTRIES}/ and {DECISIONS} as at {args.after}: "
          "the decisions record is history.")
    print("Would stop on any conflict, update the issue and open no pull request.")
    print("Would push nothing, and say to revert by hand, if a relative link of the kept "
          "record that resolves at after would not resolve in the revert.")
    print("Would sign an RS256 JWT with openssl, find the installation and mint its scoped token.")
    print("Would ensure auto-revert, the trains' kind labels and security-review "
          "for protected paths.")
    print("Would check main still names after, push with the job's token and open "
          "the pull request with the App's.")
    print("Would label the pull request, verify its head and enqueue it with expectedHeadOid.")
    print("Would update the issue with the pull request and queue outcome using GITHUB_TOKEN.")
    return 0


def revert(args, source: Path, api: GitHub, env: dict, push) -> int:
    entries = []
    problem = ""
    try:
        entries = trains(source, args.before, args.after)
        read_trains(api, entries, args.repo)
    except Exception as exc:
        problem = str(exc) if isinstance(exc, Refusal) else "The train metadata could not be read."
    if not env.get("STOICHEIA_REVERT_APP_ID") or not env.get("STOICHEIA_REVERT_APP_KEY"):
        problem = (problem + "\n" if problem else "") + (
            "App secrets STOICHEIA_REVERT_APP_ID and STOICHEIA_REVERT_APP_KEY are not both set; "
            "issue only, no automatic revert.")
    api.ensure_labels({"blocks-release", "main-red"})
    outcome = problem or "The automatic revert is being prepared."
    body = issue_body(args, entries, outcome)
    issue = api.call("POST", api.root + "/issues",
                     {"title": f"Main integration failed at {args.after[:12]}",
                      "body": body, "labels": ["blocks-release", "main-red"]})
    if not isinstance(issue, dict) or type(issue.get("number")) is not int or issue["number"] <= 0:
        raise Refusal("GitHub did not confirm the failure issue.")
    print(f"Opened failure issue #{issue['number']}.")
    if problem:
        print(problem)
        moved = clear_moved_on(api, args.repo, args.after, issue["number"])
        if not moved:
            return 1
        print(moved)
        return record(api, args, entries, issue["number"], f"{problem}\n{moved}", 1)
    result = 1
    stage = "No branch pushed and no pull request opened."
    try:
        with tempfile.TemporaryDirectory(prefix="stoicheia-revert-") as directory:
            target = Path(directory) / "tree"
            head, paths = make_revert(source, target, args.before, args.after, entries)
            if any(path.startswith(".github/workflows/") for path in paths):
                # The job's token cannot push a change to a workflow, and the App writes
                # no contents: such a revert is the coordinator's, by hand.
                raise Refusal("The revert changes .github/workflows/, which the job's token "
                              "cannot push: revert it by hand.")
            broken = broken_links(target, args.after, head)
            if broken:
                # Its own check_links.py step would fail, and the queue eject it.
                more = len(broken) - SHOWN_LINKS
                raise Refusal(
                    "The revert would break these relative links of the kept decisions "
                    "record, which resolve at the failed push:\n"
                    + "\n".join(f"- {link}" for link in broken[:SHOWN_LINKS])
                    + (f"\n- and {more} more" if more > 0 else "")
                    + "\nRevert it by hand, mending each link (docs/WORKFLOW.md, "
                    "\"Auto-revert\").")
            labels = {"auto-revert"} | {label for t in entries for label in t.labels
                                        if label in KINDS}
            if any(protected(path) for path in paths):
                labels.add("security-review")
            api.ensure_labels(labels)
            token = installation_token(api, env["STOICHEIA_REVERT_APP_ID"],
                                       env["STOICHEIA_REVERT_APP_KEY"], args.repo)
            app = GitHub(args.repo, token, api.http)
            if main_tip(api) != args.after:
                raise Refusal("Main has moved on from the failed push: a later push's own "
                              "run decides.")
            branch = f"revert/{args.after[:12]}"
            stage = f"Push of {branch} was attempted; its remote state may need inspection."
            # The job's own token pushes; a GITHUB_TOKEN cannot push a change to
            # .github/workflows/, so such a revert fails here and leaves the issue.
            push(target, args.repo, branch, env["GITHUB_TOKEN"])
            stage = f"Branch {branch} was pushed; pull request creation may need inspection."
            # Quote job names so they cannot add run or revert metadata lines.
            jobs = "\n".join("> " + line for line in args.failed_jobs.splitlines())
            pr = app.call("POST", api.root + "/pulls",
                          {"title": f"Revert failed main push {args.after[:12]}", "head": branch,
                           "base": "main", "body": "\n".join(f"Reverts: {t.sha}" for t in entries)
                           + f"\nFailed run: {args.run_id}\n\nFailed jobs:\n{jobs}\n\n"
                           f"Run: {args.run_url}\n"})
            if (not isinstance(pr, dict) or type(pr.get("number")) is not int or pr["number"] <= 0
                    or not isinstance(pr.get("node_id"), str) or not pr["node_id"]
                    or pr.get("head", {}).get("sha") != head):
                raise Refusal("GitHub did not confirm the revert pull request and its head.")
            number = pr["number"]
            stage = f"Pull request #{number} is open; enqueueing is not confirmed."
            applied = app.call("POST", f"{api.root}/issues/{number}/labels",
                               {"labels": sorted(labels)})
            if (not isinstance(applied, list) or any(not isinstance(row, dict) for row in applied)
                    or not labels.issubset({row.get("name") for row in applied})):
                raise Refusal("GitHub did not confirm all revert labels.")
            queued = app.call("POST", "/graphql", {
                "query": "mutation($input: EnqueuePullRequestInput!) { "
                         "enqueuePullRequest(input: $input) { mergeQueueEntry { id } } }",
                "variables": {"input": {"pullRequestId": pr["node_id"], "expectedHeadOid": head}}})
            try:
                entry = queued["data"]["enqueuePullRequest"]["mergeQueueEntry"]["id"]
            except (KeyError, TypeError):
                raise Refusal("GitHub did not confirm the queue entry.") from None
            if not isinstance(entry, str) or not entry:
                raise Refusal("GitHub returned an unreadable queue entry.")
            outcome = f"Revert pull request #{number} was enqueued at {head}."
            result = 0
    except Exception as exc:
        reason = (str(exc) if isinstance(exc, Refusal)
                  else "The automatic revert could not be completed.")
        outcome = f"{reason}\n{stage}"
    if result:
        moved = clear_moved_on(api, args.repo, args.after, issue["number"])
        outcome += f"\n{moved}" if moved else ""
    print(outcome)
    return record(api, args, entries, issue["number"], outcome, result)


def record(api: GitHub, args, entries: list[Train], number: int, outcome: str,
           result: int) -> int:
    """Put the outcome in the failure issue, and exit `result`; if the issue could not be
    updated, 3 for an enqueued revert and 2 for anything else."""
    try:
        updated = api.call("PATCH", f"{api.root}/issues/{number}",
                           {"body": issue_body(args, entries, outcome)})
        if not isinstance(updated, dict) or updated.get("number") != number:
            raise Refusal("GitHub did not confirm the issue's outcome.")
    except Exception as exc:
        reason = str(exc) if isinstance(exc, Refusal) else "The issue could not be updated."
        # An enqueued revert stays enqueued: only the issue's account of it is missing.
        print(f"Issue #{number} was not updated with this outcome: {reason}", file=sys.stderr)
        return 3 if result == 0 else 2
    return result


def main(argv=None, *, http=None, push=None, repo_dir=None, env=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before")
    parser.add_argument("--after")
    parser.add_argument("--repo", required=True)
    parser.add_argument("--run-url")
    parser.add_argument("--failed-jobs")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--clear", action="store_true")
    args = parser.parse_args(argv)
    if not SLUG.fullmatch(args.repo) or args.repo.split("/")[-1] in {".", ".."}:
        parser.error("--repo must be owner/name")
    if args.clear:
        if args.before or args.run_url or args.failed_jobs:
            parser.error("--clear takes --repo, optionally --after and --dry-run")
    elif not all((args.before, args.after, args.run_url, args.failed_jobs)):
        parser.error("--before, --after, --run-url and --failed-jobs are required")
    if args.after and (not SHA.fullmatch(args.after) or not args.after.strip("0")):
        parser.error("--after must be a non-zero, full commit SHA")
    args.run_id = None
    if args.run_url:
        run = re.fullmatch(
            rf"https://github\.com/{re.escape(args.repo)}/actions/runs/([1-9][0-9]*)"
            r"(?:/attempts/[1-9][0-9]*)?",
            args.run_url)
        if not run:
            parser.error("--run-url must name a GitHub Actions run in --repo")
        args.run_id = run[1]
    environment = dict(os.environ if env is None else env)
    source = Path.cwd() if repo_dir is None else Path(repo_dir)
    try:
        if args.dry_run:
            return dry_run(args, source, environment)
        token = environment.get("GITHUB_TOKEN")
        if not token:
            raise Refusal("GITHUB_TOKEN is required to record or clear main-red.")
        api = GitHub(args.repo, token, http or request)
        if args.clear:
            return clear(api, args.repo, args.after, source)
        return revert(args, source, api, environment, push or push_branch)
    except Exception as exc:
        reason = str(exc) if isinstance(exc, Refusal) else "The operation could not be completed."
        print(f"auto_revert: {reason}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
