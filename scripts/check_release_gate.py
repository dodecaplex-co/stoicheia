#!/usr/bin/env python3
"""Hold a release while any issue or pull request labelled blocks-release is open.

    python3 scripts/check_release_gate.py [--repo OWNER/NAME]
    python3 scripts/check_release_gate.py --issues-json FILE

Exit 0 when none is open, 1 when unfinished work holds the release, 2 when the issues
cannot be read. Fixtures are arrays in REST or gh issue list's JSON form. Live reads
use gh api --paginate when gh is installed, else the REST API with GITHUB_TOKEN,
following every page. Credentials never appear in a URL or an error message.
The pure judgement and page reader live in safe_push, whose copied harness must remain
self-contained. Python 3.11 or later; standard library only.
"""

import argparse
import http.client
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request

from safe_push import BLOCKS_RELEASE, github_slug, issue_pages, open_blockers


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


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--issues-json", metavar="FILE", help="read an offline JSON array")
    parser.add_argument("--repo", metavar="OWNER/NAME",
                        help="default: GITHUB_REPOSITORY, then origin")
    args = parser.parse_args(argv)
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
            print(f"#{issue['number']}: {issue['title']} "
                  f"({issue.get('html_url') or issue['url']})")
        return 1
    print("no open blocks-release issue")
    return 0


if __name__ == "__main__":
    sys.exit(main())
