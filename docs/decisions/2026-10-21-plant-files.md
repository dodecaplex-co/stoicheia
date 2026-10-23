- **Each negative test's plant is a file of its own
  ([#205](https://github.com/jackChallis/stoicheia/issues/205)).** The protected file
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) numbered its plants in one
  docstring and called each from one list in `main()`, so two branches that each added a
  plant took the same next number and edited the same list. On 21 October that happened
  three times (#172 against #158 against #168, and F2's #150 chain against #172), each
  resolved by hand. The issue quotes the owner's words of that day: "I'd like to prevent
  the problems we KNOW we have." Each plant is now a file in `scripts/negative/`, named for
  it, holding its description as the module docstring (what it plants, which check must
  refuse it and what that check must say), `BUILDS`, True for the four that run
  `lake build`, and `plant()`, which reaches the shared helpers as `nt.<name>`. The suite
  lists that folder, never Git's index, so the pre-flight's pass with origin/main's checks,
  which takes out the files a commit adds, runs main's plants. It runs every plant that
  does not run `lake build`, by name, then every one that does, by name, naming each with
  its file before it and timing each after it, restoration included; the closing list
  gives each failure, in its old words, under the plant that added it. Adding a plant is
  adding one file, with no number to choose and no list to edit. `--plant NAME` runs the
  plants named, inside the same Git bracket and with the same closing check of the
  unplanted tree, and exits 2 on a name it does not know; `--counts-only` keeps its
  meaning. The loader is checked too: a missing or empty folder; an entry that is not a
  regular file with a plant's name (a symbolic link or a directory among them), apart
  from a `__pycache__` folder and a `.DS_Store` file, which are passed over; a file that
  does not load; and one with no description, no `BUILDS` of True or False, or no
  `plant()` callable with no arguments: each fails the run, named, before anything is
  planted. A plant that records no refusal and adds no failure fails the run by its name.
  To count refusals, `expect_failure` records one where it printed "caught", through a
  new `refused` that prints the same line, and stale_page, the one plant that judges its
  refusal by hand, calls `refused` with the words it printed. That guard catches a plant
  that runs no check, or returns before its first; it does not catch one that calls
  `refused` with no check behind it, nor one that drops some of its cases.

  Every one of main's 42 plants is carried over unchanged in behaviour: the same changes
  planted and the same refusals expected. Each `plant()`'s syntax tree is its old
  function's, with `nt.` read as the bare name, apart from stale_page's printed refusal,
  which now goes through `refused` in the same words, and ill_typed_proof's docstring,
  below; continuation lines were re-aligned, which changes whitespace only. The constants
  and helpers that one plant alone used move into its file with their comments:
  `PLANTED_COMMANDS`, `PLANTED_FILES` and `BOOK_ZERO` into forbidden_commands and
  `toml_blocks` into undeclared_run, for example. Those that several plants use, or that
  `tests/test_negative_tests.py` reads, stay in `negative_tests.py`: `rules_in` and
  `scratch_plants`, the source scan on a tree of its own and the scratch copy of I.1 that
  the source-scan plants share, and `BOOK_ZERO_SPELLINGS` and `BOOK_ZERO_TEXT`, which the
  tests of the Book Zero rule read. The order departs on
  purpose from the issue's "by name": the 38 plants that do not run `lake build` go first,
  so that a fault in one shows before the four that do, each of which saves and restores
  `.lake/build`. `BUILDS` only orders the plants, so a wrong value moves a plant and skips
  none.

  The evidence of equivalence: the old suite, at e604deb0, and the new, at 2a39c2b7, were
  run on the same main under a recording harness, which logged every check call, file
  write and command, plant by plant. Both caught 68 planted changes, missed none and passed
  16 expected successes, and each plant made the same check calls, with the same verdicts,
  and ran the same commands. In what they wrote, 28 of the 29 plants match exactly, once
  two things that follow from the tree, not the code, are set aside: the order of three
  loops that put back files from a set (the same paths and the same bytes), and the 29 new
  files, which count_markers and merge_conflict_markers copy with every other tracked
  file. merge_conflict_markers differs besides only in the line numbers it expects,
  because this change lengthens CONTRIBUTING.md, to which it appends; rebuilt from each
  commit's own files, they match exactly. A plant file that refuses nothing, one that runs
  no check, one that does not compile, one with a bad name and one without `BUILDS` each
  failed the run. Main's two plants that landed after that comparison, missing_files and
  ill_typed_proof (#158), were converted the same way. missing_files' `plant()` has main's
  function's syntax tree, with `nt.` read as the bare name; so has ill_typed_proof's,
  apart from its docstring's pointer to item 15, which no longer exists, now "as
  corrupt_olean restores it". Each, run alone with `--plant`, caught what it planted and
  left the tree clean. The ten that landed after those, with #197, #200, #207, #209, #234,
  #256 and #77, were converted the same way when origin/main was merged at e5028ffc:
  book_zero_imports, carriage_return_comment, closed_up_commands, edited_note,
  guard_error_pins, guard_msgs_drop, guard_msgs_substring, queue_repeated_heading,
  secret_behind_a_replacement and set_option_spellings. Each `plant()`, and each constant
  and helper that moved into its file, has main's syntax tree, with `nt.` read as the bare
  name, and each description is its numbered item's text, with "Likewise" written out and
  a pointer to another item's number now that plant's name. The same merge brought main's
  changes to two plants already converted, the four commands added to forbidden_commands'
  list and stale_page's status over the whole worktree, and its two new regressions before
  the plants, the risk classes' and the axiom lock's, which join the list the runner runs.
  slashed_remark (#206), which landed after that, was converted the same way when
  origin/main was merged at c9411ece, and main's tests of the comment reader the scripts
  share join `tests/test_negative_tests.py` as they are.

  Two rounds of review then hardened the suite. It compiles each plant from its file's
  text, and, run as a script, registers itself under the name the plants import rather
  than importing its own file again, so no bytecode in a `__pycache__` runs in place of a
  plant or of the runner. The loader refuses a plants' folder that is, or passes through,
  a symbolic link, which would take every later plant off the protected paths, and passes
  over Finder's `.DS_Store`, naming it. The entry Git status is taken first of all, before
  the regressions that precede the plants (restoration, count, decision entry, risk class
  and lock),
  since the restoration regressions, `tests/test_negative_tests.py`, load the real plants'
  folder; so a file that a plant's file writes as it loads shows in the closing
  comparison. `--counts-only` keeps no bracket, as before. The names of the runner and of
  the modules the plants reach through it (check_fidelity, check_kernel,
  generated_counts, heath and subprocess) are noted before any plant's file is read, and
  a file that changes one, as it loads or as it runs, fails the run, named, with the name
  put back; the names are looked at once more after the closing check of the unplanted
  tree, where a change fails the run "after the closing check". The failures and refusals
  recorded before a plant only grow, so a `plant()` that changes them fails by its name,
  and they are put back as they were, with any it added after them kept. A `plant()` that
  raises SystemExit fails the run by its name, and the run goes on to the next. A run
  that ran fewer plants than it chose fails too: its loop ends early only when the list of
  the plants chosen changes as it runs. A run that `--plant` narrows closes by saying how
  many of the plants it ran, while a full run gives its count before its closing tick.

  These guards catch a mistake, not a file written to deceive: a plant's file runs in the
  runner's process with its full power, so the security review reads each plant's file
  as code of the runner. They do not see a shared object changed in place other than
  those two lists (a helper's `__code__` replaced, a dict of a helper module changed);
  and a file that ends the process itself (`os._exit`, a signal) is not caught in
  process, and leaves with the status it chooses. Review reads each plant's file for
  them. Running each plant in a child process of its own, which would contain both, is
  left for a later change.

  The protected test file
  [`tests/test_negative_tests.py`](../../tests/test_negative_tests.py) keeps every test,
  reaching the plants through the loader, and every assertion but one. That one is in
  main's test that a failed regression stops the run before any plant: it asserted that
  the regression was the last command run, and now asserts the whole list, the entry Git
  status, the regression and the closing Git status, since the bracket now opens before
  the regressions. The file gains `LoaderTests`, twenty tests of the loader and of
  `main()` around it, all on temporary folders without Lean or Git but one, which loads
  the real folder with no fault: the order; each kind of fault, a linked folder and a
  linked `scripts/` among them, each failing the run with nothing planted; a
  `__pycache__` folder and a `.DS_Store` file passed over, and bytecode beside a plant
  not read; a `plant()` that raises SystemExit, a run that stops short of its plants, a
  file that changes a shared name as it loads or runs, a name changed by the closing
  check, a `plant()` that clears the failures or pops a refusal recorded before it, and a
  file written as a plant loads, each failing the run; a warning recorded against the
  runner, passed over; the entry Git status taken before the regressions; a plant that
  refuses nothing, one whose check passes and one that records a refusal; and `--plant`
  and `--counts-only`. It gains `ScriptTests` too, which runs the suite as a script in a
  temporary copy and sees that a plant's `nt` is the running module and that bytecode
  beside the runner and a plant is not run. The loader's tests expect the bracket's two
  Git status calls even when loading fails or a name is unknown, since the bracket opens
  before loading; each asserts that nothing was planted and the closing check did not
  run. [WORKFLOW](../WORKFLOW.md), section 8, and CONTRIBUTING say how to add a plant,
  what the guards catch and what they do not, and that the pull request that adds,
  changes or deletes a plant's file, which is under `scripts/`, names it in a decision
  entry and carries `security-review`. CI's `negative` job and `scripts/safe_push.py`
  are unchanged. No check, plant or expected value is weakened.

  The protected files this changes are `scripts/negative_tests.py` and
  `tests/test_negative_tests.py`, and the 42 plants, each new:
  `scripts/negative/broken_link.py`,
  `scripts/negative/certificate_constructor_counting.py`,
  `scripts/negative/changed_audit_pin.py`, `scripts/negative/changed_word.py`,
  `scripts/negative/circle_dependencies.py`, `scripts/negative/circle_proved.py`,
  `scripts/negative/circle_renamed.py`, `scripts/negative/corrupt_olean.py`,
  `scripts/negative/count_markers.py`, `scripts/negative/figure_names_and_arcs.py`,
  `scripts/negative/forbidden_commands.py`, `scripts/negative/heath_word.py`,
  `scripts/negative/ill_typed_proof.py`, `scripts/negative/lake_links.py`,
  `scripts/negative/merge_conflict_markers.py`, `scripts/negative/missing_files.py`,
  `scripts/negative/model_lake.py`, `scripts/negative/native_decide.py`,
  `scripts/negative/placement_called.py`, `scripts/negative/placement_named.py`,
  `scripts/negative/planted_assumptions.py`, `scripts/negative/primitive_not_opaque.py`,
  `scripts/negative/remark_ends_run.py`, `scripts/negative/stale_lean.py`,
  `scripts/negative/stale_page.py`, `scripts/negative/stale_statement.py`,
  `scripts/negative/style_error.py`, `scripts/negative/symbolic_links.py`,
  `scripts/negative/undeclared_run.py`, `scripts/negative/weakened_postulate.py` and
  `scripts/negative/wrong_radii.py`. The merge of origin/main at e5028ffc adds ten of
  those protected files, each new: `scripts/negative/book_zero_imports.py`,
  `scripts/negative/carriage_return_comment.py`, `scripts/negative/closed_up_commands.py`,
  `scripts/negative/edited_note.py`, `scripts/negative/guard_error_pins.py`,
  `scripts/negative/guard_msgs_drop.py`, `scripts/negative/guard_msgs_substring.py`,
  `scripts/negative/queue_repeated_heading.py`,
  `scripts/negative/secret_behind_a_replacement.py` and
  `scripts/negative/set_option_spellings.py`. The merge of origin/main at c9411ece adds
  one more, new: `scripts/negative/slashed_remark.py`.
