# What the checks read (30 October 2026)

*Measured on main at e0ec6df2b, on 30 October 2026 from 20:42 to 21:13 UTC, on a cloud virtual machine of the kind
that checks changes before they land. A dated report: it is right as of that commit.*

A check that runs on every change costs every change its minutes. One that runs only on the changes that can alter its
verdict costs only those. To know which is which, each check and test was run once while the files it read were
recorded. Then a few dated reports and decision entries were deleted or changed, to see which verdicts moved.

The words used here:
- a **unit** is one thing that runs and passes or fails: a check, a test function or a negative plant;
- a **negative plant** puts one known fault into a copy of the repository and expects its check to fail on it
  ([WORKFLOW](../WORKFLOW.md), "Negative tests run in isolation");
- a unit's **verdict** is its pass or fail, and a verdict **moved** if a change turned one into the other;
- the **trace** is the first step: running every unit once while recording what it reads;
- the **strain** is the second: changing files on purpose and running again the units that read them.

## What was run

- **The trace,** from 20:42 to 21:07 UTC. Every unit below ran once under strace, a Linux tool that recorded the
  files it opened, listed or looked for, the programs it started and any network connection. The units were:
  - each check in `checks/` with a command of its own;
  - each test function in `tests/`;
  - the three quickest tests of each test class in `scripts/test_safe_push.py`, by its recorded times;
  - each of the 53 negative plants;
  - the formal model's two steps in CI.

  Where one file holds many tests, a marker written at each test's start and stop told their reads apart. In all,
  1,614 units ran in 157 batches on 24 workers: 25 minutes on the clock, and 283 minutes if each unit's time is added
  up.
- **The strain, for dated reports and decision entries,** from 21:08 to 21:13 UTC.
  - The Markdown files of `docs/reports/` and `docs/decisions/` fall into two groups by which units read them: a
    large group of more than 200, and the three gap reports, `docs/reports/gaps-book-I.md` to `gaps-book-III.md`.
  - Three files stood in for them: `docs/reports/routes-book-III.md` and
    `docs/decisions/2026-10-28-repository-address-check.md` from the large group, and
    `docs/reports/gaps-book-III.md` from the gap reports.
  - The three were changed together, in three rounds, each committed as a pull request's change would be: first
    deleted; then edited, with a word added to a line of running text a reader sees; then changed in bytes only, with
    a comment that does not show on the page added at the end.
  - 70 units read these files: 5 checks (named below), 12 tests and all 53 plants. Each round ran again the 5
    checks, the 12 tests and 5 of the plants, those in `scripts/negative/broken_link.py`, `count_markers.py`,
    `path_faults.py`, `retired_rule_used.py` and `style_error.py`: 22 units. It also ran 6 units that read none of
    the files, as controls, to show that a verdict did not move for some other reason. That is 28 units in each of
    three rounds, 84 runs in all.

## What it found

How far each unit's reads reach. Reads inside `scripts/`, `tests/`, `checks/` and `.github/`, the code of the checks
and tests, are not counted. An area is one book's pages and records, the reports and guides, the figures, the Lean
proofs, or the standard parts the proofs share.

| Reads, outside the code of the checks and tests | Units | Minutes of unit time, one run of each |
|---|---|---|
| Nothing outside that code, only the fixtures it builds | 0 | 0 |
| Files of one area | 1,329 | 45 |
| Files of several areas | 160 | 8 |
| More than 500 files: most of the repository | 125 | 230 |

- **No unit that ran reads only code and its own fixtures.** Each read at least one file outside those four folders, so
  a change to such a file can, in principle, reach it.
- **The units that read most of the repository take most of the time.** They are 8% of the units and 81% of the
  minutes, though the 56 tests below include 55 that failed (see Limits):
  - the 53 negative plants, 213 minutes in all: each copies the repository, plants its one fault, then runs its check;
  - 56 tests of `tests/test_jev_questions.py`, 14 minutes;
  - 5 checks: `check_fidelity.py`, `check_style.py`, `render.py`, `check_links.py` and `check_address.py`, all in
    `scripts/`;
  - 11 tests, of `tests/test_generated_counts.py` (5), `tests/test_check_acceptance.py` (2),
    `tests/test_check_style.py` (2) and `tests/test_decision_entries.py` (2).
- **The units that read several areas** are, for 98 of the 160, two test files: `tests/test_certificate.py` (52 units)
  and `tests/test_check_superposition_pins.py` (46).

**The strain.**
- Deleting the three files moved one verdict only, the link check's (`scripts/check_links.py`), because other
  documents link to them.
- The edit and the change of bytes moved none.
- No control moved.

So, of the units run again, the only one whose verdict these three files decided was the link check, and only when
they were deleted.

## Limits

- **One run, on one commit and one machine.** strace slows what it watches, so the minutes show where the time goes
  rather than what a run takes.
- **Some units were sampled.** Three tests a class of `scripts/test_safe_push.py` ran, not all 552, and they were the
  quickest, so its minutes here are low.
- **55 of the 56 tests of `tests/test_jev_questions.py` in the last row failed under the trace,** as did 6 more of
  that file; the cause was not looked into. A failing test may stop before it reads all that it would, so their reads
  may be incomplete. They are 14 of the 230 minutes.
- **The code of the checks and tests is not counted.** A test that reads another check's code still counts as reading
  nothing in the table.
- **The strain is narrow.** Three files stood in for more than 200; a file of the large group that the units treat
  differently would not show. The other 48 plants also read these files, since each copies the repository, but they
  were not run again, so the strain says nothing about them.
- **A harmless edit that moves no verdict shows only that these units do not depend on that kind of edit.** A check
  that judges a document's words would stay green on it. Faults of the kinds the style, link and entry checks look
  for, planted in these files, are the next probe.
- **The trace sees files, not functions.** Which code a test runs is a question for a coverage run.

## Proposals

These follow from the findings; none is decided.

- **Tests that build what they need.** A test that reads the working tree must run again whenever any file it reads
  changes, related or not. Built from a small fixture in a temporary folder, it depends only on what it tests.
- **Plants local to their check.** Each plant can put its fault in a small fixture and run the one check it guards,
  rather than copying the repository.
- **Declared inputs.** Each test file names the files it reads, as the checks in `checks/` do, and an audit refuses
  one that reads more. A change then runs only the tests whose inputs it touches.
- **One test where two areas meet.** A test that reads several areas becomes a test in each area, and one small test
  of what they share.
