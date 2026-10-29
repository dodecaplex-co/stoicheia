# The checks

Each file here is one check of CI's `check` job, the sequence that
[WORKFLOW, section 8](../docs/WORKFLOW.md#8-validation-on-the-integrated-revision) asks
of every revision delivered. The files are the one list of those checks:
`scripts/run_checks.py` runs them in CI, from the pull
request's own copy of this folder; `scripts/render.py` writes section 8's first command
block from them; and the pre-flight, `git safe-push`, runs origin/main's copy of them,
read out of Git, never the copy of the commit it checks
([the decision](../docs/decisions/2026-10-22-check-registry.md)).
`scripts/registry.py` is the one reader, and refuses the whole
folder, naming the file, when any file breaks the rules below. The reader and
`scripts/run_checks.py` are of risk class R5, the landing tool and CI, and the reader
stays one self-contained file of the standard library, since the pre-flight runs it
alone.

## What a file holds

A file is named `<NN>-<slug>.toml`: digits, then lower-case letters and digits joined by
hyphens. It holds these fields, and no others:

| Field | What it holds |
|---|---|
| `order` | A number. The checks run in its order, whatever the files are called. |
| `name` | The check's name, as the pre-flight reports it: the command's words joined by spaces, or `git status --porcelain is empty` for the entry with `empty`. |
| `job` | The CI job that runs it. `check` is the only job the registry holds, and any other is refused. |
| `command` | The command, as a list of words, run with no shell. A first word `python3` stands for the interpreter that runs the check. |
| `empty` | `true`, in place of `command`: `git status --porcelain`, over the whole worktree, must print nothing. |
| `section8` | The line section 8's command block shows for it. |
| `concurrent` | `true`: the pre-flight may run the check beside the other concurrent checks next to it in order (below). |
| `after` | With `concurrent` only: a list of earlier checks' names, each of which must have ended before this one starts. |

`order`, `name`, `job` and `section8` are required, and exactly one of `command` and
`empty`; `concurrent` and `after` may be left out. No two files share a name or an order,
and the folder holds nothing but the checks and this README, which the reader passes over,
as it does a Finder `.DS_Store`. A comment (`#`) says what the check is for, as a CI step's
name and comment did, and a line of it says why the check is concurrent or runs alone.

## Concurrent checks

`concurrent = true` is a promise about the check, and the reader accepts `true` alone. The
check:

- writes nothing in the worktree but Python's ignored bytecode (`__pycache__`);
- reads nothing that a check which may run beside it writes;
- has no limit timed by the clock tight enough to fail when the machine is busy;
- does not itself fill the machine.

A check without the field runs alone: after every earlier check has ended, and before any
later one starts. So every new check runs alone until a reviewed change declares it. The
check with `empty` judges the whole worktree, and is never concurrent. `after` names a
check's own test, so that a rule read wrongly stops the sequence before the check's
verdict, as it did when they ran one after another.

The pre-flight (`git safe-push`, step 4) runs concurrent checks that come next to each
other in order as a group: up to `STOICHEIA_CHECK_WORKERS` of them at once, each in its
own process, and never more than half the machine's cores. The variable unset, empty or 1
runs them one at a time, as before. Their lines and logs come in the registry's order, each
as it would be run alone, and a failure refuses at the first failing check in that order.
Interrupted, or refused, the pre-flight waits for the checks already running to end before
it cleans or removes the worktree. Around each group, however many run at once, the
pre-flight takes the worktree's state: HEAD, the index's entries, and every file that
`git status` or `git ls-files -o` lists, ignored files with them but Python's bytecode,
each file's bytes hashed but under `.lake/` and `model/.lake/`, where its size,
modification and change times, inode and mode are compared. A group that changes it fails
the step "concurrent checks left the tree as they found it", naming its checks and what
changed. CI's `scripts/run_checks.py` runs every check one after another, as before.

## Adding a check

1. Add one file, with an `order` that puts the check where it belongs: between two others,
   an order between theirs (`35` between `30` and `40`), and no other file renamed. The
   number in its name is for people listing the folder; the order decides.
2. Run `python3 scripts/render.py`, which writes the new line into section 8's block, and
   commit the file and the regenerated block together.
3. Name the new file, in a sentence of its own, in the train's decision entry, as for any
   protected path ([WORKFLOW, section 10](../docs/WORKFLOW.md#landing-work-pull-requests),
   "Protected paths"). Removing a check, or changing its command, job, order,
   `concurrent` or `after`, is the same: one file, named in the entry.

A check declared concurrent that is to write in the worktree loses its `concurrent` first,
in a train of its own. The commit's pass runs the commit's own scripts under origin/main's
declarations, so a train that makes such a check write is refused by the guard until the
train that undeclares it has landed.

A change to `checks/` is of risk class R3, and touches neither `scripts/safe_push.py` nor
the CI workflow. Its pull request's CI runs its own registry, the new check with it, and
that run is a required check of the pull request, so the change does alter checks that
judge it there. Three things keep that safe:

- Every train that touches `checks/` is R3 or above, so its pre-flight runs origin/main's
  whole registry on it, in both passes, whatever its CI runs.
- The change is protected: each file is named in a decision entry, and the pull request
  carries `security-review`.
- The change judges later trains only once it has merged: the check joins the pre-flight
  then.
