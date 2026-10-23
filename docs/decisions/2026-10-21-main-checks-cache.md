- **origin/main's pass of the pre-flight's full checks is cached by exact tree
  ([#224](https://github.com/jackChallis/stoicheia/issues/224)).** On 21 October 2026 the
  owner chose, of three options put to them, "A: cache by exact tree" (the coordinator's
  record of it is [#224](https://github.com/jackChallis/stoicheia/issues/224)). Option B,
  narrowing main's pass, was not chosen. The coordinator then ruled the details, which
  this entry records.

  Why. When a commit changes a check input, step 4 of the pre-flight
  ([WORKFLOW](../WORKFLOW.md), section 10) runs every check and the negative tests twice:
  first with origin/main's copies of the check inputs laid over the commit's tree, then
  with the commit's own. The first pass turns on the exact tree it runs on, not on main
  alone: the 168 pre-flight records kept on the machine that lands the trains had 168
  different base trees, so a cache keyed by main's commit alone would be wrong as well as
  useless. But one train is pre-flighted several times at one head against one main: by
  its ship's own dry run, by the coordinator's dry run of the train, and by its push. The
  train at `af9ecc28` on main at `2e8aecf8` spent 7.7, 11.5 and 18.1 minutes in
  origin/main's pass over three such runs, and the train of #242 8.6 and 8.8 minutes over
  two. The cache takes away those repeats among the runs that pass the flag.

  What changed. `git safe-push` takes a new flag, `--main-checks-cache`, for the
  pre-flight alone, with or without `--dry-run`. Only the runs that land a train pass it
  (the coordinator ruled): the coordinator's dry run of the train and its push; a ship's
  own dry run does not. Without the flag nothing reads or writes the cache, and its
  directory is never made. Since the pre-flight was scaled to risk
  ([checks by risk](2026-10-22-checks-by-risk.md)), the cache serves only a train of R3
  and above landed from a branch not named `train/*` (since #383, below), whose
  pre-flight still runs step 4 in full: for R0 to R2, which leave step 4
  to CI, the flag makes, reads and writes nothing and sets no sandbox, and the run says
  so (should the check inputs overrule a low class, origin/main's pass runs uncached).
  With it, for R3 to R5:

  - The cache lives at `~/.cache/stoicheia/main-checks/`, outside every worktree, made by
    the harness with mode 0700, and used only while it is a real directory, owned by the
    user running the pre-flight, of mode 0700 exactly, reached through no symbolic link,
    and on the device of the directory above it, so that nothing mounted over it stands
    in for it.
  - Once the class is read, the harness loads origin/main's count-marker reader and its
    dependencies, and retains that reader for the exact repository and base. Then,
    before any of the commit's code or any check runs, it tries macOS's `sandbox-exec`
    with a profile that allows everything but a write to that directory or to a
    directory above it: a command must run under it, a write into the directory must fail
    and leave no file, and a harmless write to the directory above it (`touch -c`, which
    makes nothing) must fail with the sandbox's own refusal, "Operation not permitted",
    so that a profile that has lost the rules above the cache is caught, and a write that
    fails for another reason passes nothing. From then on every command the harness
    starts runs under that profile, wrapped in the one function that starts commands, so
    Git, the guards' `check_fidelity.py` and `render.py`, every step of both passes, and
    `gh` all do. The class comes first: origin/main's `risk.py` runs outside that
    function, with a time limit. The Git read and module load of origin/main's
    count-marker reader follow it, also outside the sandbox, but neither runs the
    commit's code.
    Once the sandbox is set, nothing else in the harness starts a process, nor imports a
    module but a builtin (`atexit`), which no path holds: Python would look for any other
    first in the harness's own directory, one a sandboxed command may write. At first,
    `platform.mac_ver()` imported `plistlib`, with `xml.parsers.expat`, when the key was
    first computed, after step 3 had run the commit's code, and the allow-list imported
    `tomllib` in step 2; both are now imported with the rest at the top. A `train/*`
    branch's train check ([#383](https://github.com/jackChallis/stoicheia/pull/383))
    loads origin/main's `check_train.py` into the harness's own process with
    `importlib`, after the guards have run the commit's code; so for a train the flag
    sets no cache and no sandbox, and the run goes on as without it, and the train check
    refuses to run should a sandbox be set. `importlib` is used nowhere else in the
    harness, and two tests hold both (`test_every_import_is_at_the_top` and
    `test_the_flag_for_a_train`), with a flagged dry run of a `train/*` branch end to
    end. The `tomllib` import is unconditional at module load,
    so an unsupported interpreter can fail before the harness reaches its controlled
    version refusal. Tests check this as they run,
    by Python's own record of each process started and each module imported, any import
    but a builtin's being refused: one over the key and
    origin/main's pass, missed and hit, in the test's own process; one over the same in a
    fresh interpreter, so that nothing the tests have loaded can hide a late import,
    which also parses the allow-list with `tomllib` forgotten from the module cache,
    shows the watch refusing a module imported late, and on macOS `plistlib`, imported as
    `environment()` once imported it; and one over a flagged dry run of the pre-flight
    (steps 1 to 3 and 5, step 4 being the internal test flag's skip) and its push. A
    runtime test observes classification finishing before the count-marker reader is
    loaded, the reader being retained before sandbox activation, the commit checks
    starting after it, and a child of those checks going through the sandbox. A fresh
    interpreter also exercises counted prose and judged content after activation: a
    sandboxed child can plant a `dataclasses.py` beside the harness, but the retained
    reader does not load it and the refused run writes no cache entry. The
    harness first read the platform with `platform.platform()`, which starts `uname -p`
    and `file -b`, found on the `PATH`, outside the sandbox; it now reads `os.uname()` and
    macOS's version file. Only the harness's own Python writes an entry. Without the
    sandbox (not macOS, no `sandbox-exec`, a run already inside a sandbox, or a profile
    that fails the trial) there is no cache that run, the run says why, and the
    pre-flight is otherwise as before.
  - An entry's name is the SHA-256 of a canonical JSON key the harness computes: a format
    version; origin/main's full commit; the exact base tree, made in a temporary index,
    which a test checks equals the tree the pass lays down; the harness's blob, with no
    caching when the harness running is not origin/main's; the toolchain (the tree's
    `lean-toolchain`, `lean --version` and `lake --version` in the worktree, and the real
    path of the `lean` that elan resolves); the Python, its real path, the platform (its
    system, release, machine and macOS version), Git's version, the checks' `PATH`, the
    variables `LANG` and `LANGUAGE`, and each variable whose name begins `STOICHEIA_`,
    `LEAN`, `LAKE`, `PYTHON` or `LC_`, but three that are the harness's own plumbing
    (below) and the terminal's `LC_TERMINAL` and `LC_TERMINAL_VERSION`, which iTerm2 sets
    to name itself and are no locale (keyed, a dry run and a push from two terminals
    would never share an entry); and the lists of checks and negative tests. `LANG` is
    keyed by its name, not as a prefix, so that no unrelated variable whose name merely
    begins with it is written into an entry.
  - Only origin/main's pass of step 4 is cached, both its loops. Step 3's pass (a few
    seconds) and the commit's own pass run every time. A miss runs the pass as before,
    and writes an entry only when both loops finished in that run, under the sandbox,
    with the harness unchanged: through a temporary file in the directory, synced, then
    renamed into place, mode 0600. A hit puts the recorded steps in the report with their
    recorded outcomes, "ok" or "note", each marked as reused from the cache with its entry
    and the time it was written, writes their logs among the run's own, a note pointing to
    that copy of its log, and runs none of them; `keep_apart` then reads them exactly as
    it reads a pass that ran. One line of the report, which reaches the pull request's
    record, names the hit or the miss and why.
  - An entry is used only if it reads as JSON; its key fields are this run's exactly and
    hash to its name; its digest, over the rest of it, matches; its harness is the one
    running; its written time has the exact emitted form `YYYY-MM-DD HH:MM UTC`, with a
    valid calendar date and time; its steps are origin/main's pass, each once and in
    order, each "ok" or "note", each with a time a step could take (none, or up to a week)
    and a detail and a log the run can write as UTF-8 and print; and it is a regular file,
    not a symbolic link, of the user's, mode 0600, no larger than 16 MiB (the one measured
    below is 156,119 bytes). A larger entry is refused unread, and no more than 16 MiB and
    a byte is ever read, so that a sparse file of a tebibyte cannot hang the run. On any
    doubt, and on any error at all in reading it, the pass runs again, the run says why,
    and a bad entry is replaced only after the pass has finished.

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

  One detail departs from the ruling's words in the looser direction, and is recorded
  here for the coordinator: the ruling keys each variable whose name begins
  `STOICHEIA_`, and three of them are left out of the key, as the harness's own
  plumbing. `STOICHEIA_HARNESS` is set by the hand-over to origin/main's harness and not
  by the launcher; `STOICHEIA_PUSH_LOG` places the log, and with it the cache itself; and
  `STOICHEIA_PYTHON` picks the interpreter, whose real path the key holds. No check
  reads any of them: a search of the repository finds them only in the harness, the
  launcher, the pre-push hook, their tests and the pages that describe them. Keyed, a
  run handed over from a worktree and a run of the launcher would never share an entry.

  What the key leaves out, as low risk. Git's own settings (the `GIT_` variables,
  `~/.gitconfig`, `.git/config`, `info/exclude`, `core.excludesFile`), which
  `check_links.py`, `check_style.py`, `render.py` and `negative_tests.py` read through
  Git: in a fresh worktree of the commit they change what the checks see only through
  files Git ignores or does not track, and two runs that share an entry run on one
  machine as one user.
  The toolchain's binaries beyond their versions and the real path of the `lean` that
  elan resolves, which change only when a toolchain of the same version is installed
  afresh. And time limits under load (`check_style.py`'s 900-second Lean probes,
  `test_certificate.py`'s 120 seconds): a hit keeps the one outcome its run had of a
  limit that turns on the machine's load. A note kept that way errs towards refusing, and
  names its entry, which can be deleted; an "ok" kept that way is what a lighter load
  gave.

  What it does not do. The digest is no signature, and the sandbox stops only this: the
  commands a flagged run starts writing the cache directly. It does not stop a run
  without the flag, a ship's own dry run among them, which starts its commands with no
  sandbox, nor a flagged run of a `train/*` branch, which sets none; nor anything code
  run as the same user does outside a flagged run; nor anything a flagged run's code
  leaves for a later command to run before its sandbox starts: the launcher in `.git/stoicheia/`, `alias.safe-push` in `.git/config`, a
  program earlier on the `PATH`, the harness copy in `~/.cache/stoicheia/harness/`, a
  module in the harness's own directory, which Python searches first, or in Python's
  standard library (the user's own under Homebrew), or Python's start-up files; since
  no module is imported once the sandbox is set, such a module runs only in a later
  run, before its sandbox. That is the exposure the `--merge` step-4 record already has,
  a local file any code run as the user can write. A profile that allows writes only
  where the checks need them, or a cache owned by another Unix user, could narrow it;
  either is for the owner to decide. The first flagged pre-flight of a train against a
  given main still runs both passes, and a train that changes no check input, a
  one-proposition train among them, has no pass with origin/main's copies to reuse, so the
  card's target for a one-proposition train at 465 propositions is not met by this, and is
  left to a card of its own.

  Measured on the machine that lands the trains, three dry runs of `tooling/lock-header`
  at one head against one main, before the pre-flight was scaled to risk. Before, with
  origin/main's harness (`af90d71e`'s): 21.5, 18.9 and 18.7 minutes, of which
  origin/main's pass, in steps 3 and 4 together, took 11.4, 9.6 and 9.5. After, with
  this change's harness as first written (`9bb2d002`) and the flag, against a simulated
  origin whose main holds it: the first run, a miss, took 18.2 minutes, 9.2 of them in
  origin/main's pass in steps 3 and 4, and wrote its entry; each later run, a hit, spent
  4 seconds there (step 3's pass, which is not cached), its own checks running in full:
  9.4 minutes for the second run, and 25.7 for the third, which shared the machine with
  other test runs. They were not measured again at the delivered head.

  This entry approves the changes to `scripts/safe_push.py`, the harness, which gains the
  flag, the sandbox and the cache.

  It approves the launcher's usage lines in `scripts/hooks/safe-push`, which name the new
  flag and change nothing it does.

  It approves the whole of the change to `scripts/test_safe_push.py`: the class
  `MainChecksCache`, the stand-in for `sandbox-exec` (`FAKE_SANDBOX`), `sandbox_usable`,
  `CheckRun`, the watch on the processes a run starts and the modules it imports
  (`PROCESS_EVENTS`, `WATCHING`, `watch_hook`, `watch_processes`, `WATCH_SITECUSTOMIZE`
  and `STEP4_WATCH`, the script of the fresh interpreter), the imports of `platform` and
  `stat`, and the docstring's bullet for the cache; none of it needs Lean or the
  network.
