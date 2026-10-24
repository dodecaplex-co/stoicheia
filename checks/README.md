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

`order`, `name`, `job` and `section8` are required, and exactly one of `command` and
`empty`. No two files share a name or an order, and the folder holds nothing but the
checks and this README, which the reader passes over, as it does a Finder `.DS_Store`. A
comment (`#`) says what the check is for, as a CI step's name and comment did.

## Adding a check

1. Add one file, with an `order` that puts the check where it belongs: between two others,
   an order between theirs (`35` between `30` and `40`), and no other file renamed. The
   number in its name is for people listing the folder; the order decides.
2. Run `python3 scripts/render.py`, which writes the new line into section 8's block, and
   commit the file and the regenerated block together.
3. Name the new file, in a sentence of its own, in the train's decision entry, as for any
   protected path ([WORKFLOW, section 10](../docs/WORKFLOW.md#landing-work-pull-requests),
   "Protected paths"). Removing a check, or changing its command, job or order, is the
   same: one file, named in the entry.

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
