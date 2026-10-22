- **origin/main's pass of the pre-flight's full checks is cached by exact tree
  ([#224](https://github.com/jackChallis/stoicheia/issues/224)).** On 21 October 2026 the
  owner chose, of three options put to them, "A: cache by exact tree" (the coordinator's
  record of it is [#224](https://github.com/jackChallis/stoicheia/issues/224)). Option B,
  running origin/main's pass over the judged changes only, was not chosen. The coordinator
  then ruled the details, which this entry records.

  Why. When a commit changes a check input, step 4 of the pre-flight
  ([WORKFLOW](../WORKFLOW.md), section 10) runs every check and the negative tests twice:
  first with origin/main's copies of the check inputs laid over the commit's tree, then
  with the commit's own. The first pass turns on the exact tree it runs on, not on main
  alone: the 168 pre-flight records kept on the machine that lands the trains had 168
  different base trees, so a cache keyed by main's commit alone would be wrong as well as
  useless. But one train is pre-flighted several times at one head against one main: by
  its ship's dry run, by the yard and by the lane's push. The train at `af9ecc28` on main
  at `2e8aecf8` spent 7.7, 11.5 and 18.1 minutes in origin/main's pass over three such
  runs, and the train of #242 8.6 and 8.8 minutes over two. The cache takes away those
  repeats among the runs that pass the flag.

  What changed. `git safe-push` takes a new flag, `--main-checks-cache`, for the
  pre-flight alone, with or without `--dry-run`. The coordinator ruled that only the
  yard's run and the lane's push pass it, and a ship's own dry run does not: not as a
  security boundary, but so that fewer runs can leave anything in the cache. Without the
  flag nothing reads or writes the cache, and its directory is never made. With it:

  - The cache lives at `~/.cache/stoicheia/main-checks/`, outside every worktree, made by
    the harness with mode 0700, and used only while it is a real directory, owned by the
    user running the pre-flight, of mode 0700 exactly, and reached through no symbolic
    link.
  - Before any check runs, the harness tries macOS's `sandbox-exec` with a profile that
    allows everything but a write to that directory: a command must run under it, and a
    write into the directory must fail and leave no file. From then on every command the
    harness starts runs under that profile, wrapped in the one function that starts
    commands, so Git, the guards' `check_fidelity.py` and `render.py`, every step of both
    passes, and `gh` all do. Only the harness's own Python writes an entry. Without the
    sandbox (not macOS, no `sandbox-exec`, or a run already inside a sandbox) there is no
    cache that run, the run says why, and the pre-flight is otherwise as before.
  - An entry's name is the SHA-256 of a canonical JSON key the harness computes: a format
    version; origin/main's full commit; the exact base tree, made in a temporary index
    and tested to equal the tree the pass lays down; the harness's blob, with no caching
    when the harness running is not origin/main's; the toolchain (the tree's
    `lean-toolchain`, `lean --version` and `lake --version` in the worktree, and the real
    path of the `lean` that elan resolves); the Python, its real path, the platform, Git's
    version, the checks' `PATH`, and each variable whose name begins `STOICHEIA_`, `LEAN`
    or `LAKE`, but the four that are the harness's own plumbing and that no check reads
    (`STOICHEIA_HARNESS`, `STOICHEIA_PUSH_LOG`, `STOICHEIA_SAFE_PUSH_LAUNCHER` and
    `STOICHEIA_PYTHON`), so that a run handed over from a worktree and a run of the
    launcher share keys; and the lists of checks and negative tests.
  - Only origin/main's pass of step 4 is cached, both its loops. Step 3's pass (a few
    seconds) and the commit's own pass run every time. A miss runs the pass as before,
    and writes an entry only when both loops finished in that run, under the sandbox,
    with the harness unchanged: through a temporary file in the directory, synced, then
    renamed into place, mode 0600. A hit puts the recorded steps in the report with their
    recorded outcomes, "ok" or "note", each marked as reused from the cache with its entry
    and the time it was written, writes their logs among the run's own, and runs none of
    them; `keep_apart` then reads them exactly as it reads a pass that ran. One line of
    the report, which reaches the pull request's record, names the hit or the miss and
    why.
  - An entry is used only if it reads as JSON; its key fields are this run's exactly and
    hash to its name; its digest, over the rest of it, matches; its harness is the one
    running; its steps are origin/main's pass, each once and in order, each "ok" or
    "note"; and it is a regular file, not a symbolic link, of the user's, mode 0600. On
    any doubt the pass runs again, the run says why, and a bad entry is replaced only
    after the pass has finished.

  Two details are stricter than the ruling's words, and stay. The key
  holds the commit's own tree beside the base tree: the checks compare the tree they run
  on with the commit's (`git status --porcelain`, and `git ls-files` in `check_style.py`
  and `negative_tests.py`), so two commits with one base tree could see different
  outcomes, and the cache must never let one stand for the other. And the sandbox's
  profile also refuses a write to each directory above the cache, as a literal path: with
  the directory's own rule alone, a trial on macOS showed that a command could
  rename `~/.cache/stoicheia`, write an entry in the moved directory, and rename it back;
  with the rules for the directories above, the renames fail, and files can still be
  made beside the cache.

  What it does not do. The digest is no signature, and the sandbox protects the cache
  from train code the pre-flight runs, not from code run as the same user outside it: a
  contributor's own run of a train's tests, say, or a job that such code leaves with the
  system's services, which the sandbox does not stop, to run later. That is the same
  exposure the `--merge` step-4 record already has. A cache owned by another Unix user,
  which would close it, is for the owner to decide. The first pre-flight of a train
  against a given main still runs both passes, so the card's target for a
  one-proposition train at 465 propositions is not met by this alone, and the time per
  train before and after is still to be measured on the trains that use the flag.

  This entry approves the changes to `scripts/safe_push.py`, the harness, which gains the
  flag, the sandbox and the cache.

  It approves the launcher's usage lines in `scripts/hooks/safe-push`, which name the new
  flag and change nothing it does.

  It approves as well the new tests of the cache in `scripts/test_safe_push.py`, the class
  `MainChecksCache`, which need no Lean and no network.
