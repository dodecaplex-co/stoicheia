# Acceptance

When does a book meet the standard? This page is the one checklist that answers it, for
Books I–III now and for every later book. A book is accepted when every item below passes
for each of its propositions, for the book and for the edition, with no failures; then the
independent audit and a cold outside reading follow ([Beyond the checklist](#beyond-the-checklist)).
For Books I–III, acceptance gates the consolidation release of
[brief 0005, stage 6](briefs/0005-astra-review.md#stage-6-acceptance-the-checklist-that-says-books-iiii-meet-the-standard).

Each item is one of two kinds:

- **[machine]**: `scripts/check_acceptance.py` checks it, on every proposition, every book
  and the whole edition, from the files as they are.
- **[review]**: a reviewer's verdict, recorded in a record the script reads ([Recording a
  review item](#recording-a-review-item)). The script checks that the verdict is there,
  that it is `pass`, and that the record names who gave it and at which commit; whether the
  verdict is right is the reviewer's, and the independent audit's, to answer.

The checklist merges the criteria of brief 0005's stage 6, Astra's measure of 95/100, with
the release criteria of [WORKFLOW](WORKFLOW.md#9-release-criteria-and-severity), section 9,
and with what has changed since both were written: the kernel replay, the stricter rule for
runs of `--` lines, review stamps tied to a commit, companions as certificate entries,
stage 4b's goal of a full statement for every record, and Staging. [Where the older
criteria went](#where-the-older-criteria-went) traces each one here.

## Running it

```sh
export PATH=$HOME/.elan/bin:$PATH
lake build
lake build Audit
lake env lean Certificate/Facts.lean
python3 scripts/check_acceptance.py           # every item, in about two minutes
python3 scripts/check_acceptance.py --quick   # the kernel replay and the model tests not run
python3 scripts/check_acceptance.py --json verdicts.json   # every verdict as JSON as well
python3 scripts/check_acceptance.py --compare main.json verdicts.json   # no check run
python3 scripts/check_acceptance.py --check-current   # no check run: the committed report
```

It writes [the report](reports/acceptance-books-I-III.md): a table of items by book, a table
of every proposition against every item, and every failure, each with what to do about it.
It changes no other file, save the verdicts `--json` asks for. It exits 0 only when every
item passes and every check ran; 1 when anything fails or was not run (a check not run is
not a pass); and 2 when it cannot begin. To pass every item it needs Python 3.11 or later,
`lake` on the PATH, and the commits the records name, so a full clone rather than a shallow
one. Before any check runs it asks Lake, with `lake build --no-build Elements Audit`,
whether the build is current, since the Lean the checks ask is the build and not the
sources; when Lake says it is not, by its exit 3, the script says why and what to build,
and exits 2 with nothing written; and when Lake cannot answer (any other exit, a toolchain
or lakefile problem, say), it says so, and exits 2 as well. If there is no `lake`
executable, it keeps the earlier path: the run continues, and each check that needs Lean
reports that it could not ask it.

The script stands on the checks already in place rather than restating them:
`check_fidelity.py`'s functions, `check_style.py`, `check_links.py`, `check_kernel.py`,
`heath.py` and the model tests, each run as CI runs it, with each finding sorted to the
proposition or book whose file it names; and `render.py`'s functions, which regenerate the
pages in memory to compare them with the files. An item passes only when the checks it
names pass for that proposition, book or edition.

`--json` writes every item's verdict, `pass`, `fail` or `not run`, with each failure's
messages or the reason an item was not run, to the path given. `--compare` runs no check:
it reads two such files, main's first, and compares their verdicts by the rule below
([In CI](#in-ci)). It exits 0 when every pass holds under that rule; 1 for a regression,
listing each; and 2 when a file cannot be read in the verdict format, or the two name
different copies of the script by their hashes. CI uses both options.

`--check-current` runs no check and needs no Lean: it reads the report as HEAD holds it,
and exits 0 when that report is a run of every item on a commit that HEAD descends from
and differs from in nothing but the report, with no staged, unstaged or untracked change
Git reports in the worktree and no tracked file marked assume-unchanged or skip-worktree;
1, giving each reason, when it is not; and 2 when it cannot begin. It asks Git with
replacement objects disabled, and reads the report, not the run that wrote it. It is a
release step, not one of CI's ([In CI](#in-ci)).

## In CI

CI's required `acceptance` job runs on pull request events and is skipped on pushes.
Its executable definitions are [the workflow](../.github/workflows/ci.yml),
[`scripts/check_acceptance.py`](../scripts/check_acceptance.py) and
[`scripts/copy_acceptance_checks.sh`](../scripts/copy_acceptance_checks.sh). It fetches
the whole history (`fetch-depth: 0`) for the records' commits. Until the consolidation
release, `ACCEPTANCE_GATE` is `ratchet`: **a pass on main may not turn into a fail on the
pull request**, save the staging exception below. The
[report committed on main](reports/acceptance-books-I-III.md) records failures
at the revision it names; CI recomputes the individual verdicts for comparison on each
run. The ratchet allows the checklist's exit 1, then weighs its verdicts. The checker's
tests and the builds must also pass; a checker exit of 2 or more, or verdicts that cannot
be compared, fail the job. In three steps:

1. After its comparison tests, the builds of `Elements` and `Audit`, and the computation
   of the certificate, the script checks every item on CI's checked-out revision,
   normally the pull request's test merge commit, and writes its verdicts with `--json`.
2. It checks main in a worktree beside it: the checkout's first parent if it has two
   parents, otherwise the pull request's recorded base commit. Main is built and its
   certificate computed with the pull request's own checks copied in (`scripts/`, `tests/`,
   `Certificate/`, `review/SCHEMA.md` and `review/terms.toml`), so that one copy of the
   checks judges both. Main keeps its own values pinned to its content:
   `Certificate/axioms.lock`, `tests/certificate_expectations.json`,
   `tests/model/lock.sha256`, `tests/model/laws.toml`, `tests/model/MODEL.md` and
   `tests/model/results/` ([WORKFLOW](WORKFLOW.md#landing-work-pull-requests), section 10,
   the pre-flight's step 4, "The full checks"). The formal model's `model/` directory is
   not copied. An updated definition or expected count must not make unchanged main fail
   and so hide a pull request's failure. A stricter check, which lands in a pull request
   of its own before the content it judges
   ([WORKFLOW](WORKFLOW.md#landing-work-pull-requests), section 10), judges both revisions.
   An item it fails on main is reported but does not hold the pull request back.
   Main's run is `--quick`: the kernel replay and the model tests (E1 and E4) are recorded
   as `not run`, so the comparison does not hold them. The pull request's checklist run
   runs them, and CI's `check` and `model` jobs require them to pass.
3. `--compare` sets main's verdicts beside the pull request's, and fails for each item that
   passes on main and does not pass on the pull request (a fail, a check not run, or an
   item missing), save a staging item (P10 or E6) that turns into a fail, which it lists.
   Both staging items read `Staging/` alone, where a statement that a stage adds or changes
   is staged before its proof ([WORKFLOW](WORKFLOW.md#2-briefs-before-proofs), section 2).
   A staging item that was passing and is now `not run` or missing still fails the
   comparison.

The run's artifact is named `acceptance`: the pull request's `report.md` and
`verdicts.json`, and, when main is checked, its `main-report.md` and `main.json`. The
upload step runs even after a failure and keeps whichever of these files were produced.

**The full gate.** The consolidation release's pull request switches it on: it sets
`ACCEPTANCE_GATE`, in the CI workflow, from `ratchet` to `full`, a change to a protected
file with its decisions entry; from then on the job skips main and the comparison, and
any failing item or check not run fails it, the staging items included. That is step 9
of [WORKFLOW](WORKFLOW.md#10-how-a-book-is-made-and-released), section 10: the checklist
passes in CI with no failures. Any other value fails the job before the checklist runs,
so that no misspelling turns the gate off. At the release candidate the report is
regenerated on a freshly built tree and committed, and `--check-current` passes, as step
10 of [WORKFLOW](WORKFLOW.md#10-how-a-book-is-made-and-released), section 10, says.
Every pull request's job has the build and the run, but only the release candidate is
held to committing the regenerated report, so an ordinary pull request is not held to
`--check-current`.

The distinction between GitHub's five required checks and the merge gate's local presence
test, including what a skipped job means, is in
[WORKFLOW](WORKFLOW.md#8-validation-on-the-integrated-revision), section 8.

## For each proposition

All 99 of Books I–III, each with its porism and its companions.

| # | Item | Kind | What passes |
|---|---|---|---|
| P1 | Proved | machine | The proposition, its porism and every companion that facts.json attaches to it are `proved`: no `sorry` stands in them or beneath them, so no `sorryAx` is in their dependencies. The page's table under "What it rests on" has a column, the certificate, for each attached entry. Each companion is listed in the record's `companions`, so that the scope counts it. |
| P2 | A current record | machine | The record reads against [review/SCHEMA.md](../review/SCHEMA.md) and is at the stage `full`, so it classifies every substantive passage and names its run and a reviewer with a role. Its stamps are current: its `fingerprint` matches the statements in facts.json, its `lean` the Lean file and its `text` the record's own text (`check_fidelity.py`). Its `commit` is a commit of this repository, in the history of the revision checked. Its `[review] items` use only the keys of P11 to P16. |
| P3 | Full | machine | The statement's scope is `full`, but for the limitations allowed below, each carrying its tag; and the route is Euclid's or `modified`, never `alternative`. |
| P4 | Disclosed | machine | On the committed page, the line under the enunciation, the field table under "In Lean" and, for a statement in part, the clause map are exactly those that `render.py` makes from the record, so every scope, route, representation and overlap exception the record declares stands in the page's top line and field table. A record with an `unformalized` passage has a `[coverage]` clause map. No sentence of the mishnah says that our statement or the Lean leaves something of Euclid's out (restricts, excludes, omits, leaves out, does not prove or cover, adds an extra hypothesis) when the record declares no departure at all: a scope short of full, a route not Euclid's, an overlap, a scope tag or `hypothesis-dropped`, a `different` or `unformalized` passage. |
| P5 | Policies | machine | For the proposition, its porism and its companions (`check_fidelity.py`): no later citation; superposition used directly only by I.4 and I.8; nothing before I.29 resting on Postulate 5 or a rule of `Elements.Tacit.Euclidean`; no axiom and no forbidden command in its Lean file. Its entries pass `check_fidelity.py`'s checks of them: each porism Heath prints has its entry, word for word, and each porism and companion is tied to this proposition. Placement is cited only by III.24 and the theorems on arcs: no other file of `Elements/` names it. The lock is E2's. |
| P6 | Runs | machine | Every run of `--` lines with no Lean beneath it, before the next run, is declared as a passage (`check_fidelity.py`, by the rule made stricter on 18 October: a `/- … -/` remark ends a run and carries none). Each passage begins at one of Euclid's sentences and names a helper that is declared, and each passage's note is on the page. |
| P7 | Text | machine | The docstring is Heath's enunciation and the `--` lines are Heath's proof, word for word (`check_fidelity.py`); the record's quotations are Heath's (P2). Heath's letters are plain and the quotation marks straight (`check_style.py`, S9 and S8). The reading line links only works that [docs/reading.md](reading.md) gives (S17). Every relative link of the page, the mishnah and the reading line resolves (`check_links.py`). Heath's source note names the scan leaves, so the page links his page images; the links themselves go to the Internet Archive, and are not fetched. |
| P8 | Figures | machine | Euclid's figure and the figure at a glance exist, and pass the figure rules (S13 to S16, S20, S21 and S26): Heath's letters, all and only his, in both figures and at every point the figure at a glance shows; each letter drawn once (once in each of Heath's figures where two or three stand side by side) and clear of every stroke; the palette, the strokes, the captions and the titles. A figure of the modern way, where the page has one, passes S24 and S25: it has a matching modern way paragraph, meets the canvas, palette and stroke rules for Euclid's figures, uses only letters drawn in its companion, and gives the paragraph's own names their mathematical style. S26 applies to Euclid's figure and the figure at a glance, not to the modern figure. When the theorem covers several cases (a `case` passage, or a companion), the record's `[figure]` gives the `case` its caption names. |
| P9 | Style | machine | The hard rules of `check_style.py` hold in the mishnah, the reading line, the notes of the record that its page shows and the Lean notes of the proposition's file, S12 among them (every Lean name in the mishnah, the reading line and the record's notes is one Lean knows); the mishnah exists; and the committed page is exactly what `render.py` makes. |
| P10 | Out of Staging | machine | No declaration under `Staging/` is for this proposition (a name with `PropN` under `Book<book>`, or in a file that imports that book's `PropN`): a statement once proved has moved to `Elements/`, and its staged copy is deleted ([WORKFLOW](WORKFLOW.md#2-briefs-before-proofs), section 2). |
| P11 | Statement | review | The statement says what Euclid's enunciation says, or its qualification is exact. Quantifiers, conclusions, hypotheses and cases have been checked, by the questions of [FORMALIZATION](FORMALIZATION.md#coverage-does-it-say-what-euclid-says), section 2. |
| P12 | Passages | review | Each substantive passage is carried, or its helper, grouping, case, alternative or omission is named truly. There are no dummy citations, no artificial hypothesis uses and no helpers that conceal a whole conclusion. |
| P13 | Representations | review | The representations used here (`rect` and `sq`, arcs, segments, figures given by their corners) have their bridge theorems, placed correctly in the dependency order. `n/a` when the proposition uses none of them. |
| P14 | Commentary | review | The commentary is accurate, specific to this proposition and in the common voice, explains the hardest block, and quotes and attributes exactly ([STYLE](STYLE.md), sections 3 and 5). |
| P15 | Figures | review | The figures agree with the proof's geometry and its scope: each case drawn is one the theorem covers, the caption names it, and a caption that says every case is drawn is exhaustive. |
| P16 | Sign-off | review | A reviewer other than the author signs off: the reviewer wrote, prompted and edited none of the claims judged ([WORKFLOW](WORKFLOW.md#1-roles), section 1), and the record names the reviewer, with the role, the run and the commit read. |

## For each book

| # | Item | Kind | What passes |
|---|---|---|---|
| B1 | Pages | machine | The book's index (with its introduction) and front matter, and README.md's completion summary for the book, are exactly what `render.py` makes. They are generated from facts.json and the records, so the summary is true to them. The introduction, the index and the front matter pass `check_style.py` (S18 and S19 among its rules), and their links resolve. |
| B2 | Catalogues | machine | The gap catalogue, `docs/reports/gaps-book-<book>.md`, passes `check_style.py`, and every Lean name it gives in backticks is one that Lean knows, asked of Lean with `Elements`, `Elements.Book<book>` and `Elements.Tacit` open (a pattern's placeholder `PropN`, a field of facts.json and a tactic aside). Every record of the book with an `[overlap]` has a row of its own in [the overlap catalogue](reports/overlaps.md), its first cell the reference alone, naming its rules; and no such row is for a proposition whose record declares none. The rows on a rule's use in other proofs (I.13's upper bound on an angle, used in I.47, for example; or its now-proved right-angle rule, used in 17 proofs from II.1 on, 16 calling it themselves) are read by no record, and not counted. |
| B3 | Read-through | review | Read straight through, the book flows, and the voice is common. |
| B4 | Limitations | review | The remaining limitations are deliberate, few and stated plainly where they occur: the overlaps of III.2's kind, and any allowed below, where none is now. I.45 and II.14 have been full since 22 October 2026, through their outline companions, which take a figure given by its outline alone (#116). |

## For the whole edition

| # | Item | Kind | What passes |
|---|---|---|---|
| E1 | Kernel | machine | `check_kernel.py --self-test` passes, as CI runs it: Lean's kernel replays the whole environment of `Elements` from nothing, and nanoda checks every declaration of the export, admitting only the locked axioms and Lean's three, and fails, as it must, with Postulate 5 withheld. |
| E2 | Certificate | machine | `check_fidelity.py`'s checks of the whole: the axiom lock (every axiom's statement and every word of the statements), every axiom in `Elements/Foundations/`, the primitive words opaque, the entries, for their findings that name no one proposition (a finding that names one goes to that proposition: P5, or P8 or P9 for a missing figure or mishnah), and the facts pinned in `tests/certificate_expectations.json`; any finding of these checks that names no one proposition; no shared file citing placement; and every Lean name the overlap catalogue gives (its rules, its audit lemmas) one that Lean knows, with `Audit` built. |
| E3 | Contracts | machine | `heath.py` passes: references, porisms, review terms and every record, against their contracts. |
| E4 | Model | machine | `tests/model/run.py --fast` passes, as CI's `model` job runs it. |
| E5 | The edition's pages | machine | CERTIFICATE.md, GRAPH.md and PROGRAM.md's status table are exactly what `render.py` makes, and the style rules and links hold in the files that belong to no proposition or book (README.md, the generated pages, the notes of the shared Lean modules, the overlap catalogue, the other reports and `review/terms.toml`). |
| E6 | Nothing else staged | machine | No file under `Staging/` declares anything that P10 does not already assign to a proposition: every staged statement, definition and shared step has moved to `Elements/`, or been retired; and no staged file that declares anything holds an import the scan cannot read for certain (#200). |

## The limitations allowed

P3 allows a statement short of full only when this table names it, with the tag that says
why; the table names none now. P3 also fails a full record that the table still names,
so a row goes when its record becomes full. The list in the script (`ALLOWED_LIMITS` in
`scripts/check_acceptance.py`) changes with this table, in a change to the check of its
own.

| Proposition | Scope | Tag | Why |
|---|---|---|---|

I.45 and II.14 were allowed restricted, with `figure-with-dissection`, until their outline
companions were proved and reviewed (#116). III.16 and III.31 were allowed partial, with
`mixed-angles-omitted`, until their mixed-angle clauses were stated and proved
([brief 0011](briefs/0011-mixed-angles.md), issue #57). All four records are full, their
rows have gone, and P3 now refuses any of them short of full.

An overlap is no limitation of scope: it is a disclosure, declared in the record's
`[overlap]` and the overlap catalogue, and P4 and B2 check that it is.

## Recording a review item

**In a proposition's record,** under `[review]`, as [review/SCHEMA.md](../review/SCHEMA.md)
foresees:

```toml
[review]
stage = "full"
commit = "…"
lean = "sha256:…"
reviewer = "…, its role"
run = "brief …, stage …, workflow …"

[review.items]
statement = "pass"
passages = "pass"
representations = "pass"       # or "n/a", when the proposition uses no such representation
commentary = "pass"
figures = "pass"
signoff = "pass"
```

Each item is `"pass"`, `"fail"` or `"n/a"`; only P13 may be `n/a`. An item counts only in
a record at the stage `full` whose stamps are current and which names a reviewer with a
role and its commit, one in the history of the revision checked (P2), so a record read
again for a changed Lean file is assessed again. The reviewer records only their own
reading, and never records an item for a claim they wrote, prompted, or edited.

**For a book,** in `docs/reports/acceptance/book-<book>.toml`, a table for each review
item, each with its verdict, the reviewer and role, the commit read, and the report the
verdict rests on (a read-through report, say), a file the repository tracks, given by its
path from the repository's root:

```toml
[read-through]
verdict = "pass"
reviewer = "…, its role"
commit = "…"
evidence = "docs/reports/read-through-02.md"

[limitations]
verdict = "pass"
reviewer = "…, its role"
commit = "…"
evidence = "docs/reports/…"
```

## Where the older criteria went

Brief 0005's stage 6, item by item:

| Brief 0005 | Here |
|---|---|
| 1. Displayed declarations proved, certificates shown, no `sorryAx` | P1 |
| 2. Fingerprint and Lean hash match a record at `full`, naming its commit | P2 |
| 3. Exceptions in the top line and field table; clause maps; no disclosure only in the mishnah | P4 |
| 4. Superposition, placement, later citations, Postulate 5, the lock | P5, E2 |
| 5. Every `--` run carried or declared; passage notes rendered | P6 |
| 6. Heath's text; quotations; plain letters; reading links; scan links | P7 |
| 7. Figure letters, palette and strokes; `[figure].case` | P8 (the letters of the figures at a glance, as decided on 18 October) |
| 8. Style hard rules; pages regenerated clean | P9, B1, E5 |
| 9 to 14. Statement, passages, representations, commentary, figures, sign-off | P11 to P16 |
| Per book: completion summary generated and true | B1 |
| Per book: gap and overlap catalogues current | B2 |
| Per book: read straight through | B3 |
| Per book: limitations deliberate, few, plain | B4, with P3 |

WORKFLOW, section 9, criterion by criterion:

| WORKFLOW, section 9 | Here |
|---|---|
| 1. Reviewed brief and final statements agree | P11, and P10 (nothing left in Staging) |
| 2. Every clause and porism proved or exactly qualified | P1, P3, P11 |
| 3. Cases covered; construction inputs and outputs right | P11 |
| 4. Representations with their correspondence results | P13 |
| 5. Route accurate; every exception visible | P4, P12 |
| 6. Dependency closure, axiom boundaries and certificate cover every claim | P1, P5, E1, E2 |
| 7. Quotations, attributions and commentary checked | P7, P14 |
| 8. Figures and page inspected | P8, P15 |
| 9. The required checks pass on the integrated revision | E1 to E5, with the rest of the [machine] items |
| 10. A reviewer other than the author, named with the commit | P2, P16 |

What has changed since: the kernel replay is E1; the stricter rule for runs of `--` lines
is P6; review stamps tied to a commit are P2; companions, certified and counted, are P1;
stage 4b's goal of a full statement for every record ([brief 0007](briefs/0007-stage-4b.md))
is P3; and Staging, which holds statements only until they are proved, is P10 and E6.

## Beyond the checklist

Acceptance asks for three things ([WORKFLOW](WORKFLOW.md#10-how-a-book-is-made-and-released),
section 10, step 9): the checklist with no failures, the independent audit, and a cold
outside reading. The checklist is this page. The independent audit, by a model family that
wrote none of the work, reads the [review] items afresh (brief 0005, stage 6), and its
evidence goes under `docs/reports/acceptance/`. The cold outside reading scores the
release candidate's exact pull-request head commit, identified by its full SHA; how the
measurement is made, and its gate, are in the [review rubric](RUBRIC.md). On that pull request
all five required checks are green, with `acceptance` under its full gate. The separate release
gate, including the two readings and the owner's approval of the notes, is
[WORKFLOW](WORKFLOW.md#10-how-a-book-is-made-and-released), section 10, steps 8 and 10.
The final release tag is made after acceptance and the owner approves the release notes, as
step 10 requires.

The check that every Lean name a catalogue gives is declared, by asking Lean itself (B2,
E2), follows Patrick Massot's [leanblueprint](https://github.com/PatrickMassot/leanblueprint),
whose `checkdecls` checks that every Lean declaration a blueprint names exists in the
project. We are grateful for the idea, and for the blueprints it has made easier to trust.
