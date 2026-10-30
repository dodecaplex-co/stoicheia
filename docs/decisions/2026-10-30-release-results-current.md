<!-- entry: id=release-results-current cards=701 line="The release gate's script gains a mode that refuses the model's results when they name a commit with changes since, outside the release steps' own outputs." -->
- **The release gate asks whether the model's results are the head's own (tooling,
  [#701](https://github.com/dodecaplex-co/stoicheia/issues/701)).** The coordinator's
  orders of 30 October 2026, card #701, assign this change; this entry claims no decision
  or approval of the owner's.

  Why. Step 10 of [WORKFLOW](../WORKFLOW.md#10-how-a-book-is-made-and-released), section
  10, has the model's full run made again at the release's head, after every other change,
  and what it writes committed. Nothing checked that it was: `tests/model/results_check.py`
  holds the results to the harness, not to the library, so results run on an older commit
  pass it however much the library has changed since. One of the card's conditions is that
  a release's pull request refuse "results that name a commit with changes since, outside
  the release steps' own outputs". This change gives that refusal its script and its
  planted cases; putting it in the `release-gate` job is a later train of the card's, and
  this one touches no workflow and no page of the guides.

  What it judges. `python3 scripts/check_release_gate.py --results-current` reads a head,
  H, given by `--rev` (HEAD by default), of the repository at `--repo-dir` (this folder by
  default). Each results file at H names a commit where `tests/model/run.py` writes it,
  on line 4 of each run's file and line 1 of `summary.txt`. They must all name one commit,
  C, each with its harness files as committed; the counts in MODEL.md must name C by its
  first 12 digits; C must be an ancestor of H; and each change from C to H, as
  `git diff --name-status --no-renames` lists it, must be one the release steps make. Those
  are a results file added or modified, which then names C; MODEL.md modified inside its
  block of counts alone; the screen's record added or modified; the screen modified with
  the code it hashes of itself unchanged, by the screen's own rule, `without_docstring`,
  which the script restates rather than imports; the catalogue of overlaps or the
  acceptance report modified; and one decisions entry added, named in the form that
  `safe_push.py` reads as an entry. Any other change is refused, a deletion among them, and
  so is a second entry added, or an older one changed. The mode exits 0 when the results
  are current; 1 when they are not, naming each path and why, with any character a
  terminal could take for a command written as an escape; and 2 when it cannot judge: no
  commit at the revision, no results at H, a header not in the form `run.py` writes, or a
  C the repository lacks. Given with `--issues-json` or `--repo`, it is a usage error, and
  the issue check itself is as it was.

  How it reads. Git's objects alone (`rev-parse`, `ls-tree`, `cat-file`, `merge-base
  --is-ancestor` and `diff`), with `GIT_NO_REPLACE_OBJECTS=1` and every `GIT_` variable of
  its environment removed, so that no replacement and no variable can put other objects in
  place of H's. It never imports, runs or reads the working tree of the repository it
  judges, so that main's copy can judge a release's pull request without running any of
  it. Run on main at `973375348f02`, it refuses, as it should: the results there name
  `089badbd8463`, and of the 312 changes since, 299 are no release step's output, the
  library's among them.

  Its tests. A new class of cases builds a git repository of its own in a temporary
  folder, as the self-test of `results_check.py` builds one, with git's environment cleared
  and no configuration of the person running read. Its commits hold the library and the
  pages, then a change to the library, the results naming that change, the screen's
  record, the decisions entry and the acceptance report. The head's own fresh run passes,
  at each of the last four; results naming an older commit fail and name the library's
  file, as does a change to the library made after the run. Each refusal above is planted
  and its path named, as is each case of exit 2, a path holding an escape character, a
  `GIT_DIR` and its kin pointing at another repository, and a `git replace` of a stale
  head by the fresh one; the command line's three exits and its usage errors run as a
  subprocess. One case imports `run.py`, as `results_check.py` does but in a process of
  its own, and pins to it the script's copies of `COMMITTED`, `COUNTS_FROM` and `COUNTS`,
  and of the line where a header names its commit. Each rule was checked by mutation: with
  it removed, at least one new case failed. The existing cases pass unchanged.

  This entry approves the change to `scripts/check_release_gate.py`, which gains the mode
  `--results-current`, its two options and the code that judges it, beside the issue
  check, and a paragraph on it in its docstring; nothing it did before is loosened.

  This entry approves the change to `tests/test_release_gate.py`, which gains the class
  `ResultsCurrent` between `Fixtures` and `UnfinishedWork`, with the helpers that build its
  repository; no existing case is changed or loosened.

  This entry approves the change to `checks/10-test-release-gate.toml`, in its comment
  alone, which now says that the results' cases run git for real in a repository of their
  own; its command and its other fields are unchanged, and no check is loosened.
