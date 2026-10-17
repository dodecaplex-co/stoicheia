# The programme: thirteen books at one standard

This page holds the state of the whole project and what we have learned making it. It
is updated at the end of every stage and every book. The rules themselves live in
`WORKFLOW.md`, `FORMALIZATION.md` and [STYLE.md](STYLE.md);
this page says where we are against them, and why they are what they are.

## 1. The standard

We aim at about 95/100 for every book, in the sense of [Astra's outside
review](reports/outside-review-01.md). A reader of any page should be able to answer four
questions at once:

1. What does Euclid claim?
2. What does the formal theorem prove?
3. How does each substantive step of his argument appear in the Lean?
4. What has the formalization added, changed or left out?

A book meets the standard when its acceptance checklist (`ACCEPTANCE.md`)
passes with no failures, an independent audit by a model family that wrote none of it
agrees, and a cold outside reading scores it about 95. A few deliberate limitations are
allowed when they are stated plainly where they occur: in Book III, the mixed angles of
III.16 and III.31, and the places where a System E rule already contains a proposition
(III.2).

## 2. How a book is made, in parallel

The detail is in `WORKFLOW.md`. In outline, with the crew sizes of Books I–III:

1. **Ground.** Heath transcribed and proofread; the book's brief settles its vocabulary,
   representations, construction inputs and expected exceptions. One first mate.
2. **Statements before proofs.** Every statement is written with `sorry`, translated back
   into plain words, challenged by adversarial readers, and approved before anyone proves
   it. A change later is a recorded brief revision, never a quiet edit.
3. **Sailing.** For each proposition two OpenAI Codex sailors, one at its usual reasoning
   and one at its highest, prove it independently; a Claude bosun checks both and keeps
   the better; Claude first mates review faithfulness; Claude captains enforce the voice.
   About two agents per proposition plus one per pair, in fleets of up to 45.
4. **One voice.** Range enforcers read the book straight through; blind readers, given
   pages mixed from every book, try to hear a second writer; a polisher fixes what they
   hear.
5. **Records.** A review record for every proposition, keyed to the commit it read; the
   gap and overlap catalogues; the book's introduction; further reading from the verified
   list only.
6. **Acceptance.** The checklist passes in CI, the independent audit agrees, a reader goes
   through the book start to finish.
7. **Release.** Release notes drafted from the generated summaries, approved by Jack, then
   the tag.

## 3. Status

| Book | Propositions | Stage | Records | Acceptance | Outside score | Release |
|---|---|---|---|---|---|---|
| I | 48 of 48 proved | precision pass | — | — | 90 (Astra, 676244a) | [book-I](https://github.com/jackChallis/stoicheia/releases/tag/book-I) |
| II | 14 of 14 proved | precision pass | — | — | 85 (Astra, 676244a) | [book-II](https://github.com/jackChallis/stoicheia/releases/tag/book-II) |
| III | 37 of 37 proved | precision pass | — | — | 80 (Astra, 676244a) | waiting on stage 1 |
| IV–XIII | not begun | — | — | — | — | — |

From stage 1 this table is generated from `facts.json`, `review/` and the acceptance
report, and CI checks it is current.

The work under way is [brief 0005](briefs/0005-astra-review.md):

| Stage | What | State |
|---|---|---|
| 0 | The review, this page, the brief | done |
| 1 | Precision: certificate, review records, wording, layout, evidence, overlaps, Book III's reading | next |
| 1b | Standards: AGENTS.md, STYLE, FORMALIZATION, WORKFLOW, templates | |
| — | Release of Book III | after 1 and 1b, notes approved by Jack |
| 2 | I.40, I.45, II.1, II.14 in full generality | |
| 3 | Arcs and segments; III.24 | |
| 4 | III.14, III.15, III.25 | |
| 5 | Consolidation review of all 99 | |
| 6 | Acceptance, then a consolidation release of Books I–III | |

## 4. Decisions later books depend on

- **Arcs and segments** (stage 3) are what Book IV will inscribe and circumscribe with;
  their definitions and `Circumference.add` must be settled first.
- **Construction inputs.** A construction receives only what the problem gives; its
  correctness may quantify over more (stage 4, III.25). Book IV's brief adopts this.
- **Proportion** (Book V): Eudoxus's definition taken literally, the Archimedean property
  as an axiom; one hard statement (V.18's fourth proportional) prototyped before any
  fleet.
- **Numbers** (Books VII–IX): what Euclid assumes, decided by brief; VII.16 proved without
  borrowing commutativity; prototyped first.
- **Incommensurables** (Book X): X.1 prototyped first.
- **Solids** (Books XI–XIII): planes as primitives; one statement prototyped first.
- **A formal model** of the axioms in Lean with Mathlib, as a separate package.

## 5. Lessons

- **16 Oct. The highest reasoning setting wins best-of-two.** Kept 15 of 16 times in
  Book I's fleet, 14 of 14 in Book II, 33 of 37 in Book III.
- **16 Oct. Captains enforcing five pages each do not make one voice.** Range enforcers
  reading a book straight through, and blind readers across books, do
  ([voice-01](reports/crew/voice-01.md), [voice-02](reports/crew/voice-02.md)).
- **16 Oct. A style rule can cause the drift it guards against.** Asking every commentary
  to explain every extra citation produced the same paragraph on twelve pages; a generated
  line under the certificate does the job once.
- **16 Oct. Agents read the message that launched them.** A relayed "Ignore" made a fleet
  stand down; every crew order now opens with a note on what the user's latest message
  means.
- **17 Oct. Our promises outran our coverage.** The outside review found claims of
  "complete", "sentence by sentence" and "never need" broader than the statements and
  checks behind them. Statements and representations are now reviewed before proofs, and
  every page shows its own scope.
- **17 Oct. A porism is a claim too.** It needs its own certificate and every check.
- **17 Oct. The fidelity check checks wording, not meaning.** Meaning needs a review
  record, tied to the commit it read.
- **17 Oct. An independent model is cheap.** Jev answered a scope question and three
  figure questions correctly in under a fifth of a second each; on the scope question it
  was right but only moderately confident, so its disagreements go to an adjudicator.

## 6. Cost and time

Claude agents and tokens per workflow (Codex sailors' tokens are logged by their bosuns
in the voyage logs).

| Work | Agents | Tokens | Wall time |
|---|---|---|---|
| Book III, first fleet (III.1–19) | 45 | 7.3M | 66 min |
| Book III, second fleet (III.20–37) | 42 | 6.8M | 125 min |
| Books I–II in one voice | 27 | 7.0M | 205 min |
| Book III in one voice | 8 | 2.4M | 88 min |
| Read-through (finish, after a network failure) | 8 | 2.3M | 149 min |
| Follow-ups (Common Notions, held fixes, Book III's introduction) | 6 | 1.0M | 136 min |
| Book III close-out (I.23, logs, catalogue, status) | 8 | 1.6M | 48 min |
| Pre-release checks | 6 | 1.4M | 57 min |
| Book III references research | 11 | 2.5M | 65 min |
