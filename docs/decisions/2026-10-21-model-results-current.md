- **The model's results and the overlap screen say what they were made from, and the
  release makes both again
  ([#160](https://github.com/jackChallis/stoicheia/issues/160)).** Apart from its
  self-test, which runs `run.py --full --write` on a made-up harness in a git repository
  of its own, `python3 -I tests/model/results_check.py` runs no harness. It fails,
  naming each file, when the files in `tests/model/results/` are not exactly those
  `--write` writes, each a regular file that reads; when a file names no commit or
  harness, or one twice, or `summary.txt` no Python or date, or one twice; when a file
  names its commit without "(harness files as committed)", so that its run read other
  harness files; when a file names a harness hash other than the harness's now, computed
  by the code that writes the results' headers (`harness_hash`, which `provenance`
  calls); when the files name more than one commit or harness; when the counts in
  `tests/model/MODEL.md` are not one block naming the results' commit; or when
  `summary.txt` and those counts are not what `--write` makes of the runs' output in
  `results/`. It fails, too, when the runs' output is what `run.py`'s `judge` refuses; a
  results file records no exit status, so each run is taken to have exited 0. Its
  self-test runs first: it writes results as `--write` does, from made-up runs, into a
  temporary folder, plants each of those faults in a fresh copy, and checks that each is
  caught and that the results unchanged pass. It reads what a run wrote, so it cannot
  tell a header written by hand from a run's; the security review, which every change
  under `tests/` gets, reads the results' diff. It is not a file of the harness
  (`HARNESS` in `tests/model/run.py`), so a later fix to it needs no new run and can
  land on its own, as a change to a check does. Of the check, `run.py` keeps only the
  helpers it shares with `--write`: `harness_hash`, `written`, `result_file`,
  `short_commit` and the names of what `--write` writes. `--write` writes each file
  through a new one renamed over it, so that a symbolic link in its place is replaced,
  not followed. CI's `model` job runs the check after `--fast`, so a pull request that
  changes the harness commits the change, runs `--full --write` on it and commits what
  it writes, in the same pull request: generated facts are refused when stale (WORKFLOW,
  section 10, step 8, Tier 1). `scripts/safe_push.py` does not run the check yet, and
  WORKFLOW, section 8, says so until the command joins its `CHECKS`.
- **Where `--write` runs.** It writes nothing unless the harness files are a commit's,
  as committed, when it begins, and the commit, their state and their hash are the same
  when it ends. It copies `HARNESS` out of git's objects at that commit into a private
  temporary folder, checks that the copy hashes as the checkout does, and runs from it,
  so a harness changed and changed back during the run is not written as the commit's.
  It makes the copy before it imports any other file of the harness, so that of the
  checkout's harness only `run.py` itself runs. The run from the copy takes the
  checkout's root and the provenance from `MODEL_HARNESS_SNAPSHOT` only when it runs as
  a script, not when it is imported, and writes nothing when it runs in the checkout it
  would write to, so the variable set by hand cannot make a run in place write. It is no
  lock against someone who sets it on purpose: pointed at another checkout's root, it
  lets a run that is not from a copy write that checkout's results, as a header written
  by hand could, and the security review, which reads the results' diff, is the guard
  there. SIGTERM, SIGHUP or SIGINT stops the run from the copy and the harness it is
  running, and removes the copy. The run from the copy replaces its files as one
  publication, with the three signals held back until every file is replaced or every
  file is back, and checks the harness's provenance again once they are replaced; a
  signal, two at once among them (a Ctrl-C at a terminal reaches both processes of a
  `--write`, and the first then sends the second SIGTERM), or a harness found changed,
  puts every file back as it was, a link as a link and a file that was not there removed,
  so a `--write` stopped while it runs or publishes writes nothing.
  SIGKILL, which no process can catch, ends only the process it is sent to: sent to the
  first, it leaves the run from the copy to finish and write what passes the guards, and
  leaves the copy in the temporary folder. The results check's self-test runs `--write`
  for real on its made-up harness: changed and changed back while it runs, which writes
  the commit's output; changed and left, or changed from the start, which writes
  nothing; and, where there are POSIX signals, sent SIGTERM partway, which writes
  nothing and leaves no copy and no harness running. It stops publication too, with
  SIGTERM, with SIGHUP and with SIGINT, after a file is moved to its backup, after a
  replacement, after the first check for a pending signal, while the old files are
  removed and after they are; with SIGINT and SIGTERM together, as a Ctrl-C at a terminal
  reaches a `--write`, and with SIGHUP and SIGTERM together; and changes a harness file
  and leaves it changed during publication. Each time the earlier files must all return,
  with no temporary file left. The two-signal case was found by the independent review
  TT-results-cr7, with our thanks, which wrote and tested the fix.
- **The screen's record.** The overlap screen gains `--write`, with which a run that
  ends with every known row closed by a rule records, in `Audit/screen-run.toml`, the
  commit, the number of statements in `facts.json` and a sha256 of each part of what
  decides its result; and `python3 -I Audit/screen.py --check-current`, which computes
  the parts again without Lean and fails, naming each part that changed, when the record
  is missing or the inputs differ. The parts are more than the statements, the rules and
  the script. Every file of tries imports `Elements`, so the library's notation, in
  which the screen's own lemmas are written, decides the result too, and so do its
  instances: `grind`'s AC solver, on by default, looks for `Std.Associative` and
  `Std.Commutative`, which `Elements/Figure/Areas.lean` gives the sum of magnitudes. So
  the record pins `facts.json`'s statements (name, reference, kind and statement), rules
  (modules and statements) and words (`vocabulary`), every Lean file of the library, the
  toolchain's files, and `Audit/screen.py` without its docstring, which records the run
  and so is written after it (code on the docstring's last line is pinned with the
  rest), together with any other Python module under `Audit/`, which a run without `-I`
  could import in place of a standard one; every command for the screen is written with
  `-I`. `--write` records only a run on a commit's inputs as committed, never through a
  symbolic link in the record's place, and `--check-current` refuses a record that does
  not name a commit's 40 hex digits in that state. An ignored file among the input files
  counts, and the inputs are then not a commit's; ignored files outside the inputs, and
  modules under `__pycache__`, do not count. No input file, nor any folder on its path,
  may be a symbolic link, since git commits the link and the run would read its target:
  `--write` stops before the run and records nothing, and `--check-current` fails,
  naming the links. `--check-current` fails, too, when the inputs hash as recorded but
  are not now a commit's. Every try imports the build, not the sources, so a run reads
  the commit and its inputs before `lake build --no-build Elements` and again after it,
  stops before any Lean when the build is stale or the two readings differ, and records
  the first reading. Before `--write` records a completed run, it checks the build
  again, after every try and retry, and reads the commit and the inputs again; a failed
  check leaves the record as it was. Checks at the two ends of a run cannot show that
  nothing changed and changed back in between. The screen's check needs no Lean, but any
  change to the library makes it fail, and only a run, with Lean and about an hour and a
  half of processor time, may make it pass again; so it is a release step, not one of
  CI's. The check reads the record, not the run, so it cannot tell a record written by
  hand from a run's, and the security review reads the run's closing lines, which the
  pull request quotes. Until the screen runs on the candidate, `--check-current` fails,
  as it should, and nobody writes the record by hand. `tests/test_screen.py` gains the
  cases of the record, of what stops a run before Lean and of what stops a run from
  recording. WORKFLOW, section 10, step 10, lists both runs, made at the head of the
  release's pull request before `--merge`, both checks and when each runs, and the files
  the release's decisions entry names; section 8 lists the new command.
- **The run here.** The screen is not run again here. The model's full run is, because
  `tests/model/run.py` is a file of the harness:
  `python3 -I tests/model/run.py --full --write` was made at the commit that carries the
  change, 4cc96bc0, with its harness files as committed, after main's C7-C6c
  ([#331](https://github.com/jackChallis/stoicheia/pull/331)) was merged in, and what it
  wrote was committed after it. It replaces two earlier runs of this change, at a1144ad6,
  made after main's centre rule ([#240](https://github.com/jackChallis/stoicheia/pull/240)),
  and at 819119e7, made after main's C7-C6b
  ([#319](https://github.com/jackChallis/stoicheia/pull/319)), since C7-C6b and then
  C7-C6c each wrote new results of its own. Its counts were compared with main's own run, at
  df6f901c ([#331](https://github.com/jackChallis/stoicheia/pull/331)): every count is
  the same, and only the headers and the timings are new. What it wrote is named here
  file by file. At 4cc96bc0 the angle check wrote `tests/model/results/angle_check.txt`.
  At 4cc96bc0 the exhaustive harness wrote `tests/model/results/exhaustive.txt`.
  At 4cc96bc0 the grid check wrote `tests/model/results/grid_check.txt`.
  At 4cc96bc0 the hyperbolic check wrote `tests/model/results/hyperbolic.txt`.
  At 4cc96bc0 the fifteen mutations wrote `tests/model/results/mutations.txt`.
  At 4cc96bc0 the search with its first seed wrote `tests/model/results/search-seed1.txt`.
  At 4cc96bc0 the search with its second seed wrote `tests/model/results/search-seed2.txt`.
  At 4cc96bc0 the search with its third seed wrote `tests/model/results/search-seed3.txt`.
  At 4cc96bc0 the structured harness wrote `tests/model/results/structured.txt`.
  At 4cc96bc0 the run's table went to `tests/model/results/summary.txt`, and its counts
  to [`tests/model/MODEL.md`](../../tests/model/MODEL.md). The protected
  files changed are `tests/model/run.py`; `tests/model/results_check.py`, which is new;
  `tests/test_screen.py`; `tests/model/MODEL.md`, its counts and how a change to the
  harness carries a new run; the ten files of results above; `.github/workflows/ci.yml`;
  `Audit/screen.py`; and `scripts/safe_push.py` (two comments: one said that no check
  reads the model's results, and the one above `CHECKS` now names `results_check.py` as
  the command of CI's `model` job it does not yet run). `Audit/screen-run.toml` joins them
  when the screen first writes it.
- **Open.** A hardening not made here: when git has the commit the results name, the check
  could confirm that it is an ancestor of `HEAD` and that its harness files hash to the
  hash named, and say in a shallow clone that it could not.
