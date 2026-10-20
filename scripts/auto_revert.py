#!/usr/bin/env python3
"""Revert a failed main push through the queue, and leave a release-blocking issue.

The revert job runs this file from the previous main with Python's isolated mode,
only after that commit's latest post-merge run has concluded success.
It imports no repository code. Git works in a temporary clone with hooks, global
configuration and inherited credentials disabled. Only the push receives the App
token; the issue and its labels always use GITHUB_TOKEN.

Only a first-parent chain of two-parent pull request merges can be reverted.
Unreadable history or metadata, missing credentials and conflicts leave an issue
without a pull request. Exit 0 means enqueued (or cleared), 1 means issue only or
an incomplete revert, and 2 means the issue itself could not be recorded.
--dry-run describes the actions without network access or changing the repository.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path


# These are safe_push.py's protected paths. This copy keeps the trusted script
# independent of the checkout. The tests compare it with that policy.
PROTECTED = (
    "scripts/", ".github/", "Certificate/", "tests/", "review/SCHEMA.md",
    "review/terms.toml", ".gitattributes", ".gitignore", "lakefile.toml",
    "lakefile.lean", "lean-toolchain", "lake-manifest.json", "Audit/", "Audit.lean",
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
SHA = re.compile(r"[0-9a-f]{40}")
SLUG = re.compile(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+")
MERGE = re.compile(r"Merge pull request #([1-9][0-9]*) from \S+")


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
        raise Refusal(f"git {args[0]} failed.")
    return result.stdout.rstrip("\n")


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


def installation_token(api: GitHub, app_id: str, key: str, repo: str,
                       workflows: bool) -> str:
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
    permissions = {"contents": "write", "pull_requests": "write"}
    if workflows:
        permissions["workflows"] = "write"
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


def make_revert(source: Path, target: Path, after: str, entries: list[Train]) -> tuple[str, list[str]]:
    git(source, "clone", "--local", "--no-hardlinks", "--no-checkout", str(source), str(target))
    git(target, "switch", "--create", f"revert/{after[:12]}", after)
    for train in entries:
        try:
            git(target, "revert", "--no-edit", "-m", "1", train.sha)
        except Refusal:
            raise Refusal(f"Revert of {train.sha} did not apply cleanly; no pull request opened.") from None
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


def main_tip(api: GitHub, after: str) -> None:
    data = api.call("GET", api.root + "/git/ref/heads/main")
    if not isinstance(data, dict) or data.get("object", {}).get("sha") != after:
        raise Refusal("Main has moved or its tip could not be read.")


def clear(api: GitHub, after: str | None) -> int:
    if after:
        main_tip(api, after)
    rows = api.pages(api.root + "/issues?state=open&labels=main-red")
    numbers = []
    for row in rows:
        if (type(row.get("number")) is not int or row["number"] <= 0
                or row.get("state") != "open" or not isinstance(row.get("labels"), list)
                or not any(isinstance(label, dict) and label.get("name") == "main-red"
                           for label in row["labels"])):
            raise Refusal("GitHub returned an unreadable main-red issue.")
        if "pull_request" not in row:
            numbers.append(row["number"])
    for number in numbers:
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
            print(f"Would check main still names {args.after}.")
        print(f"Would GET every page of {root}/issues?state=open&labels=main-red.")
        print("Would DELETE main-red from each open issue, keeping blocks-release and the issue.")
        return 0
    entries = trains(repo, args.before, args.after)
    for train in entries:
        print(f"Would GET {root}/pulls/{train.number} and verify merge {train.sha} and its labels.")
    print("Would list labels, create missing blocks-release and main-red labels, and open the issue.")
    print(issue_body(args, entries, "Dry run; no requests sent."))
    if not env.get("STOICHEIA_REVERT_APP_ID") or not env.get("STOICHEIA_REVERT_APP_KEY"):
        print("No App secrets: would record issue only, saying automatic revert is unavailable.")
        return 1
    print(f"Would clone locally and create branch revert/{args.after[:12]} from {args.after}.")
    for train in entries:
        print(f"Would git revert --no-edit -m 1 {train.sha}.")
    print("Would stop on any conflict, update the issue and open no pull request.")
    print("Would sign an RS256 JWT with openssl, find the installation and mint its scoped token.")
    print("Would ensure auto-revert, the trains' kind labels and security-review for protected paths.")
    print("Would check main still names after, push with the App token and open the pull request.")
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
        return 1
    result = 1
    stage = "No branch pushed and no pull request opened."
    try:
        with tempfile.TemporaryDirectory(prefix="stoicheia-revert-") as directory:
            target = Path(directory) / "tree"
            head, paths = make_revert(source, target, args.after, entries)
            labels = {"auto-revert"} | {label for t in entries for label in t.labels if label in KINDS}
            if any(protected(path) for path in paths):
                labels.add("security-review")
            api.ensure_labels(labels)
            token = installation_token(api, env["STOICHEIA_REVERT_APP_ID"],
                                       env["STOICHEIA_REVERT_APP_KEY"], args.repo,
                                       any(path.startswith(".github/workflows/") for path in paths))
            app = GitHub(args.repo, token, api.http)
            main_tip(api, args.after)
            branch = f"revert/{args.after[:12]}"
            stage = f"Push of {branch} was attempted; its remote state may need inspection."
            push(target, args.repo, branch, token)
            stage = f"Branch {branch} was pushed; pull request creation may need inspection."
            # Quote job names so they cannot add run or revert metadata lines.
            jobs = "\n".join("> " + line for line in args.failed_jobs.splitlines())
            pr = app.call("POST", api.root + "/pulls",
                          {"title": f"Revert failed main push {args.after[:12]}", "head": branch,
                           "base": "main", "body": "\n".join(f"Reverts: {t.sha}" for t in entries)
                           + f"\nFailed run: {args.run_id}\n\nFailed jobs:\n{jobs}\n\nRun: {args.run_url}\n"})
            if (not isinstance(pr, dict) or type(pr.get("number")) is not int or pr["number"] <= 0
                    or not isinstance(pr.get("node_id"), str) or not pr["node_id"]
                    or pr.get("head", {}).get("sha") != head):
                raise Refusal("GitHub did not confirm the revert pull request and its head.")
            number = pr["number"]
            stage = f"Pull request #{number} is open; enqueueing is not confirmed."
            applied = app.call("POST", f"{api.root}/issues/{number}/labels", {"labels": sorted(labels)})
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
        reason = str(exc) if isinstance(exc, Refusal) else "The automatic revert could not be completed."
        outcome = f"{reason}\n{stage}"
    updated = api.call("PATCH", f"{api.root}/issues/{issue['number']}",
                       {"body": issue_body(args, entries, outcome)})
    if not isinstance(updated, dict) or updated.get("number") != issue["number"]:
        raise Refusal("GitHub did not confirm the issue's outcome.")
    print(outcome)
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
            rf"https://github\.com/{re.escape(args.repo)}/actions/runs/([1-9][0-9]*)(?:/attempts/[1-9][0-9]*)?",
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
            return clear(api, args.after)
        return revert(args, source, api, environment, push or push_branch)
    except Exception as exc:
        reason = str(exc) if isinstance(exc, Refusal) else "The operation could not be completed."
        print(f"auto_revert: {reason}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
