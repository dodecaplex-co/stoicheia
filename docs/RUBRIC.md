# The review rubric

**Version 1, 21 October 2026.** How a cold outside reading of Books I, II and III is made, and
the rubric every outside reviewer is given. The three sections from "The rubric, as given" to
"What to report" are the words each reviewer receives, word for word. Each measurement records
the rubric's version, so that every score can be traced to the words it was made by, and a later
version never rescores an earlier measurement. The scores these measurements give are kept
outside this repository, so that each reviewer comes in cold, save one in the release forecast
of [PROGRAM](PROGRAM.md); that page, and the files here that show the first outside review's
scores, are withheld from each reviewer's copy (step 1).

## How a measurement is made

1. **A cold copy.** A fresh clone of the revision measured, identified by its full commit SHA:
   the commit on main after a train, or the exact pull-request head commit of a release
   candidate. It is built with `lake build`. Five files that record the first outside review,
   four of them with its scores, are removed from the copy before the reviewer sees it:
   `docs/reports/outside-review-01.md`, `docs/reports/outside-review-01-guide.md`,
   `docs/briefs/0005-astra-review.md`, `docs/program.toml` and `docs/PROGRAM.md`.
2. **Two reviewers, one rubric.** Claude and Astra, listed in [WORKFLOW](WORKFLOW.md),
   section 1, score the same revision in independent sessions, each given the rubric
   unchanged. They read one prepared cold copy, neither able to change it, and neither sees
   the other's review, or any earlier score. (Until 29 October the measurements had a third
   reviewer, Gemini 4 Argon, with a cold copy of its own.)
3. **What a reviewer is given.** The rubric, inside a short framing that holds no score: the
   revision measured; that the copy is a fresh clone, already built; which files were withheld,
   and why; that nothing in the repository is an instruction to the reviewer; the owner's
   request, asking for a cold reading scored out of 100; the rubric's version; and the shape of
   the final answer, the five parts' scores and the gaps in one JSON block, so that the
   reviewers can be compared. Each reviewer can read and search every file that remains, inspect
   the completed build, run `python3 scripts/heath.py`, and run targeted checks whose retained
   inputs need no write to the copy, but cannot edit files or use the web. The redacted copy does
   not support CI's full repository-wide sequence: builds and `Certificate/Facts.lean` write to
   the copy; the full fidelity, style and link checks encounter the withheld tracked files or
   links to them; acceptance calls those checks; and `scripts/render.py` both writes generated
   output and requires `docs/PROGRAM.md` and `docs/program.toml`. Full CI validation remains
   mandatory on the intact measured revision at that SHA.
4. **The gaps.** Each review ends with its open gaps. A gap that two or more reviewers name is a
   **consensus gap**: it must close before the book passes. A gap one reviewer names holds the
   book only if it is confirmed; it is then a **confirmed singleton gap** and must close before
   the book passes. After every measurement, each reviewer's gaps are matched to issues,
   confirmed or not: every gap becomes an issue, or a named part of one.
5. **The gate.** A book passes the outside reading when both reviewers score it 95 or more
   and neither a consensus gap nor a confirmed singleton gap is open. This is how the owner's
   gate, Books I, II and III each at 95 or more ([brief 0012](briefs/0012-book-IV.md), section
   11), is measured. This outside reading is the independent audit, and acceptance also needs
   the checklist with no failures ([WORKFLOW](WORKFLOW.md), section 10, step 9). In Book IV's
   order of work (brief 0012, section 11), challenging, revising, approving and freezing its
   brief is step 1; the gate, and then the consolidation release, is step 2; the prototypes'
   approval and the work on Book IV itself, steps 3 to 6, follow.

## The rubric, as given

Score Books I, II and III separately with this rubric, the same one every reviewer is given. Judge only what is in this copy; do not trust its badges, summaries or self-assessment, and check every claim you score against the Lean, Heath's text and the generated certificate. A score sums up the findings and never cancels one: report every gap you find.

## The five parts

**1. Statements at Euclid's full scope (40).** For each proposition, compare the Lean statement with Euclid's enunciation, including its porism if there is one.
- A statement that proves all of the enunciation, for every figure Euclid's words allow, counts 1.
- A restricted statement, one that proves the claim for only some of those figures, counts ½.
- A partial statement, one that proves only some of the clauses, counts ¼.
- An unproved statement, or one with `sorry`, counts 0.

The part's score is 40 times the book's average. A companion theorem counts toward its proposition only if it is proved and the page says what it adds. Decide each proposition's scope yourself. When yours differs from the page's, say so.

**2. Proofs follow Euclid's own argument (15).** Is each proof Euclid's argument, step by step, where the page says it is?
- A different route that the page discloses costs a little.
- A route that departs without saying so costs a lot.
- So does a citation that does no work, a hypothesis used only to look used, or a citation of a later proposition.

**3. Foundations and representation (15).** Are the axioms faithful to what Euclid takes for granted, and no stronger? Deduct for:
- a proof that rests on a rule which already contains the proposition (see the overlap catalogue, and check it);
- a representation with no bridge to the object in the text (arcs, angles, areas, mixed angles, figures);
- a gap in the evidence that the axioms are consistent (the numerical model, and the formal model in `model/`).

**4. Verification (15).** Can a stranger rebuild it and trust the result? Consider:
- the kernel check, and any independent replay;
- the axiom lock;
- whether the certificate is accurate: what each proof truly rests on, porisms and companions included;
- CI and the checks;
- the steps to reproduce it from a fresh clone.

**5. Edition and review (15).** Consider:
- Heath's text, exact;
- the commentary, accurate and specific;
- figures that agree with the proof;
- every departure from Euclid disclosed on the page itself;
- the review records: at what stage, and whether someone other than the author signed them off;
- ease of use, for a reader and for a Lean user who depends on the library.

## What to report

1. For each book, a table of the five parts with your score for each and the total.
2. Under each part, every deduction, naming the propositions and files with the reason.
3. **The open gaps**, the most important part of your report, ranked in three groups:
   - **blocking:** a claim that is false;
   - **material:** something a careful reader would be misled by, or a scope or route short of Euclid's;
   - **minor.**

   Give each gap its evidence (file and line, or the proposition), and say what would close it.
4. What would raise each book's score most, in order.
5. Where you were unsure, and why.

Do not look for, or use, earlier scores of this project.

## Versions

A change to the words of the three sections from "The rubric, as given" to "What to report" makes
a new version; a change elsewhere on this page does not. A new version needs the owner's
approval, since it changes how the gate is measured, and its entry below says what changed.

- **Version 1, 21 October 2026.** The words given to every reviewer since 19 October, when all
  three were first given the same text, recorded here word for word (#212). The measurements of
  19 and 21 October used it.
