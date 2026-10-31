# What the checks read (30 October 2026)

*Measured on main at e0ec6df2b, on the yard VM. A dated report: it is right as of that commit.*

A check that runs on every change costs every change its minutes. One that runs only on the changes that can alter its
verdict costs only those. To know which is which, each check and test was run once while its reads were recorded, and
then the files of one sort were deleted or changed to see which verdicts moved.

## What was run

- **The trace.** Every unit ran once under `strace`, recording the files it opened, listed or looked for, the
  programs it started and any network connection. A unit is one of these:
  - each check in `checks/` with a command of its own;
  - each test function in `tests/`;
  - the three quickest tests of each class in `scripts/test_safe_push.py`, by its recorded times;
  - each of the 53 negative plants;
  - the formal model's two CI steps.

  A unit's tests were told apart by a marker at each test's start and stop. In all, 1,614 units ran as 157 jobs, in
  25 minutes on 24 workers.
- **The strain, for dated reports and decision entries.** The files of `docs/reports/` and `docs/decisions/` fall
  into two groups, by the units that read them. One file of each group was deleted, then edited where a reader would
  see it, then changed in bytes only, each change committed as a pull request's would be. Every unit that read any
  of those files ran again, with six units that read none of them as controls.

## What it found

How far each unit's reads reach beyond its own code and fixtures:

| Reads | Units | Minutes, one run of each |
|---|---|---|
| Only its own code and the fixtures it builds | 0 | 0 |
| Files of one area (one book's pages, the reports, the figures) | 1,329 | 45 |
| Files of several areas | 160 | 8 |
| More than 500 files: most of the repository | 125 | 230 |

- **No unit is wholly local.** Every one reads at least one file of the working tree beyond its own code, so a change
  anywhere can, in principle, reach it.
- **The units that read most of the repository take most of the time.** They are 8% of the units and 81% of the
  minutes:
  - the 53 negative plants, each of which copies the tree to plant its one fault;
  - 56 tests of `tests/test_jev_questions.py`;
  - a few checks;
  - a few tests of `tests/test_check_style.py` and `tests/test_generated_counts.py`.
- **The units that read several areas** are mostly two test files: `tests/test_certificate.py` (52 units) and
  `tests/test_check_superposition_pins.py` (46).
- **One test file cannot be repeated from the files alone.** 55 tests of `tests/test_jev_questions.py` need an
  outside service.

**The strain.**
- Deleting the dated reports and decision entries moved one verdict only: `scripts/check_links.py`'s, because other
  documents link to those files.
- A visible edit and a change of bytes moved none.
- No control moved.

So the only check that depends on a dated report or a decision entry, as these probes measure it, is the link check,
through the documents that link to it.

## Limits

- **Some units were sampled.** Three tests a class of `scripts/test_safe_push.py` ran, not all 552.
- **An edit that moves nothing shows independence only from that edit.** A check that judges a document's words would
  stay green on a harmless edit. Faults of the kinds the style, link and entry checks look for, planted in these
  files, are the next probe.
- **The trace sees files, not functions.** Which code a test runs is a question for a coverage run.

## What follows

- **Tests that build what they need.** A test that reads the working tree changes whenever an unrelated file does.
  Built from a small fixture in a temporary folder, it depends only on what it tests.
- **Plants local to their check.** Each plant can put its fault in a small fixture and run the one check it guards,
  rather than copying the tree.
- **Declared inputs.** Each test file names the files it reads, as the checks in `checks/` do, and an audit refuses
  one that reads more. A change then runs only the tests whose inputs it touches.
- **One test where two areas meet.** A test that reads several areas becomes a test in each area, and one small test
  of what they share.
