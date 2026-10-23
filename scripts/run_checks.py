#!/usr/bin/env python3
"""Run one CI job's checks, as the registry in checks/ lists them (#229).

    python3 scripts/run_checks.py --job check

CI's `check` job is its setup and this one step, so it runs the pull request's own
registry, as it follows the pull request's own ci.yml (docs/WORKFLOW.md, section 8). The
pre-flight does not run this: it runs origin/main's registry, read out of Git
(scripts/safe_push.py; docs/decisions/2026-10-22-check-registry.md).

The worktree's registry (scripts/registry.py, which refuses one that breaks its rules,
naming the file) gives the entries of the job, in order. Each runs in the repository's
root, with this environment, as a group of its own in the log, named for the check:
GitHub's `::group::` lines under GitHub Actions, a `==>` line elsewhere. A first word
"python3" is the interpreter that runs this script. An entry with `empty = true` runs
`git status --porcelain`, prints what it prints, and fails when that is anything at all.
The first check that fails stops the run, with its name; none after it runs.

Exit 0 when every check of the job passed; 1 when one failed, or the registry could not be
read; 2 for a usage error. Standard library only; scripts/test_safe_push.py tests it.
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import registry  # noqa: E402

ROOT = registry.ROOT
USAGE = "usage: run_checks.py --job JOB"


def group(name: str) -> None:
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"::group::{name}", flush=True)
    else:
        print(f"==> {name}", flush=True)


def end_group() -> None:
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print("::endgroup::", flush=True)


def run(entry: registry.Entry) -> tuple[bool, str]:
    """Run one check in ROOT; whether it passed, and why not."""
    argv = entry.argv(sys.executable)
    if entry.empty:
        done = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
        sys.stdout.write(done.stdout)
        sys.stderr.write(done.stderr)
        sys.stdout.flush()
        if done.returncode != 0:
            return False, f"exit {done.returncode}"
        if done.stdout:
            return False, "it printed what is listed above, and must print nothing"
        return True, ""
    try:
        done = subprocess.run(argv, cwd=ROOT)
    except OSError as error:
        return False, f"could not be run: {error}"
    return done.returncode == 0, f"exit {done.returncode}"


def main(argv: list[str]) -> int:
    if len(argv) != 2 or argv[0] != "--job":
        print(USAGE, file=sys.stderr)
        return 2
    job = argv[1]
    try:
        entries = registry.of_job(registry.load(ROOT), job)
    except (registry.RegistryError, OSError) as error:
        print(f"run_checks.py: the registry could not be read: {error}", file=sys.stderr)
        return 1
    if not entries:
        print(f"run_checks.py: no check of the job {registry.shown(job)!r} in "
              f"{registry.FOLDER}/; the jobs are {', '.join(registry.JOBS)}", file=sys.stderr)
        return 2
    print(f"run_checks.py: {len(entries)} checks of the job {job}, from "
          f"{registry.FOLDER}/", flush=True)
    for i, entry in enumerate(entries, 1):
        group(f"{i}/{len(entries)} {entry.name}")
        started = time.time()
        ok, why = run(entry)
        sys.stdout.flush()
        sys.stderr.flush()
        end_group()
        seconds = time.time() - started
        if not ok:
            print(f"run_checks.py: FAILED: {entry.name} ({entry.path}): {why}, after "
                  f"{seconds:.1f} s; the {len(entries) - i} checks after it did not run",
                  file=sys.stderr, flush=True)
            if os.environ.get("GITHUB_ACTIONS") == "true":
                print(f"::error title=A check failed::{entry.name} ({entry.path}): {why}",
                      flush=True)
            return 1
        print(f"ok {entry.name}  ({seconds:.1f} s)", flush=True)
    print(f"run_checks.py: all {len(entries)} checks of the job {job} passed", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
