- **Main's checking policy runs in CI as a shadow, on each push to main, beside the local
  pre-flight, which it replaces nowhere (tooling,
  [#574](https://github.com/dodecaplex-co/stoicheia/issues/574)).** The pre-flight's step 4 is
  not only a repeat of CI. It runs every check twice when a change touches the checks' inputs,
  once with origin/main's copies put in place and once with the commit's own, and `keep_apart`
  refuses a commit that weakens a check together with what the check would catch, while it
  passes over stale pages and values pinned to their content. CI's `check` job runs only the
  pull request's own registry. So before CI can stand in for step 4, CI must run main's
  policy itself, and be seen to agree with the local run. On 27 October 2026 the owner chose,
  of the options put to them, "Adopt the revision (Recommended)", the revised plan for #574,
  whose first step this is (#574 is the coordinator's record of it): a shadow run of main's
  complete checking policy in CI, `keep_apart` included, with no local check removed, proved
  on planted cases.

  What it does. A workflow of its own runs main's `scripts/safe_push.py --dry-run`, taken out
  of git at the base commit, against an origin pinned to that base, on the commit that
  landed. It is main's own code, so the secret scan, the step 3 guards, both passes,
  `keep_apart` at steps 3 and 4, the full checks and the negative tests are main's, never a
  second copy. What needs a branch name is not run, as the dry run is given none: the kind
  label, the public names, a train branch's check and its body. A driver writes
  `verdict.json`, the raw outcome of every step and the policy's verdict, with the commits,
  the pull request's head and its tree when the push is its merge, the policy's blobs and
  the runtime versions, and CI keeps it as an artifact. A verdict is read from its run, a
  push to main by this workflow at the tested commit, never from an artifact's name alone.
  The repository's name is read from the event, never written in. The policy runs on push
  to main because the pre-flight's watch of a pull request's CI counts every check,
  required or not, so a shadow on pull requests would hold every landing; and not inside
  the post-merge workflow, whose failure starts the bounded revert, and whose runs alone the
  merge reads for main's health. Its self-test and planted cases run on a pull request that
  changes the shadow itself, whose landing they hold as any check does, and on demand on
  main: a clean control, a weakened check_fidelity.py with a
  stale record, a loosened renderer with the stage it lets in, a dropped check of the
  registry with a broken link, a weakened check_links.py with the same link, and a renderer's
  change with content, which passes as a legitimate exception. Each mirrors a case the
  pre-flight's own tests hold.

  Its limit, stated: the verdict counts only while the workflow GitHub runs still calls
  main's driver and main's harness, as queue-integrity's does. The pre-flight runs the
  pushed commit's own code in the same job, which could rewrite the verdict or steer the
  steps after it, so a verdict is evidence of agreement on honest work, not a defence
  against a hostile commit. Protecting the verdict, and then signing it from a definition
  the candidate cannot change, are later trains of the plan; nothing is signed, required or
  removed here. Nor may the workflow be required as it stands: its jobs skip by event, and
  a required workflow whose jobs all skip counts as passed. Actions are pinned by commit,
  and elan by its release's checksum.

  The files, each a protected path:
  - .github/workflows/shadow-policy.yml, new: the workflow, its triggers, pins and jobs.
  - scripts/shadow_policy.py, new: the driver, its planted cases and its self-test. It is
    the landing tool's and CI's, as scripts/run_checks.py is, so it is R5.
  - scripts/risk.py: classes scripts/shadow_policy.py R5, beside scripts/run_checks.py.
  - tests/test_risk.py: a row for it among the paths a broader, lighter rule also matches.
  - scripts/test_safe_push.py: the workflow's contract among the workflow contracts of #259,
    which refuse a workflow with none. The self-test and the planted cases hold a pull
    request that changes the shadow, so they are held whole. The policy job runs on a push
    to main alone, where no landing reads it, so it is named with its reason, and held to
    where it runs, its time limit, when it runs and its token's permissions.
