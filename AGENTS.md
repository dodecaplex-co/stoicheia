# Stoicheia: for agents

Stoicheia is a reader's edition of Euclid's *Elements*: Heath's text, synthetic proofs in
plain Lean 4.35 (no Mathlib), two figures, a certificate of what each proof rests on, and
commentary, for Books I–III so far. It is Jack Challis's friendly, public, personal
project. Read this file on every task. It is short on purpose: each rule lives in one
place, and this file links to it.

## Priorities

**Preserve the source, state the mathematics accurately, follow the declared route, explain
clearly; stylistic defaults serve those obligations.**

So a necessary hypothesis stays even when it makes the modern way three sentences long; a
historical uncertainty stays even when the voice is confident; an omitted clause is
disclosed even when the page is less tidy for it.

## The ten rules

1. Read the whole enunciation and proof before working on the formalization.
2. Have the formal statement reviewed and approved before its proof is assigned.
3. Preserve every substantive quantifier and conclusion, or record the precise
   qualification.
4. Follow Euclid's argument where the page promises it, and label any other route.
5. Give each represented object a justified connection to the object in the text.
6. Keep Heath's words, our explanations and Lean declarations distinguishable.
7. Treat a Lean check, a transcription check and a semantic review as different kinds of
   evidence.
8. Give each file and shared interface one owner during parallel work.
9. Tie review and validation to the revision actually delivered.
10. Prefer accurate, proposition-specific explanation to mechanical prose quotas.

The rules and the priorities are Astra's, from the
[outside review](docs/reports/outside-review-01.md), adopted with thanks.

## Requirements and defaults

| Requirements: always | Defaults: usually, and a departure has a reason |
|---|---|
| Accurate statements, with their scope stated ([FORMALIZATION](docs/FORMALIZATION.md), section 2) | A mishnah of 250–450 words in three to five paragraphs ([STYLE](docs/STYLE.md), section 3) |
| Exact quotations, with checked attribution (STYLE, section 5) | Short, proposition-specific bold leads |
| An accurate account of the route (FORMALIZATION, section 5) | Four Lean names at most in a mishnah |
| Omitted or reformulated clauses visible on the page (STYLE, section 2) | "The modern way" as a short last paragraph |
| Valid dependency and certificate claims (FORMALIZATION, sections 8 and 9) | "We" where it comes naturally, with no count |
| Figures that agree with the argument (STYLE, section 7) | The exact stroke weights of a figure |

## Reading order

1. This file.
2. For Lean, [docs/FORMALIZATION.md](docs/FORMALIZATION.md). For anything a reader sees,
   [docs/STYLE.md](docs/STYLE.md). For tasks, ownership, review and release,
   [docs/WORKFLOW.md](docs/WORKFLOW.md).
3. The book's brief: [Book I](docs/briefs/book-I.md), [Book II](docs/briefs/book-II.md),
   [Book III](docs/briefs/0004-book-III.md).
4. Your task: its orders or proposition brief; `heath/<book>/NN.md`; the Lean file; the
   proposition's review record, `review/<book>/NN.toml` ([schema](review/SCHEMA.md)).
5. [docs/examples.md](docs/examples.md) for judgment, and
   [docs/templates/](docs/templates/proposition.md) for the forms.

People start at [CONTRIBUTING.md](CONTRIBUTING.md); the state of the work is in
[docs/PROGRAM.md](docs/PROGRAM.md).

## Scope and ownership

- Work only in the files your task names: one writer per file. The integrator owns the
  generated output; the coordinator owns the foundations (`Elements/Foundations/`),
  `Certificate/axioms.lock`, the decisions page, PROGRAM.md and CI; your orders name the
  owner of everything else.
- Need something outside your files? Ask its owner in your handback, with a concrete
  proposal. For a shared lemma: its type, purpose, a proof or plan, where it may live, and
  who will use it.
- An interface wrong? Stop work on what depends on it, propose a correction (the case that
  fails, the current and proposed declarations, the reason, the consumers), and go on with
  the work it does not affect.
- Commit your files by name; never `git add -A` in a tree others use.

## Never

- Add an `axiom`, or anything that gets round the kernel: `native_decide`,
  `decide +native`, `set_option debug.…`, `run_cmd`, `elab`, `macro`, `implemented_by`,
  `extern`, `unsafe`.
- Change a statement, a porism's statement or a definition without approval; change the
  words of a `--` line; change `heath/` except against the page image.
- Add a dummy citation (a call made only to match Heath's references) or an artificial
  hypothesis use (a mention made only to silence a warning); hide a whole conclusion inside
  a helper; cite a later proposition.
- Weaken, skip or edit a check, test, expected value, lock or schema to let a change pass.
- Commit generated files (`facts.json`, `book/`, `CERTIFICATE.md`, `GRAPH.md`) unless you
  are the integrator.
- Publish: push, merge into main, tag, release, write release notes, change the GitHub
  description, or send anything outside the repository. Each needs Jack Challis's OK.
- Invent a quotation, a page or a reference; put crew talk where readers look; write
  anything competitive.

No guide, this one included, grants authority to change the foundations, weaken a check or
publish.

## Commands

```sh
export PATH=$HOME/.elan/bin:$PATH
lake build
lake env lean Certificate/Facts.lean
python3 scripts/check_fidelity.py
python3 scripts/render.py          # a preview; only the integrator commits its output
python3 scripts/negative_tests.py  # in a disposable worktree only: it plants breaks
```

No `lake update` or `lake clean`.

## The handback

End every task with a short, factual handback
([template](docs/templates/proposition.md)):

- **status:** ready for review, provisional (on unfinished dependencies), or blocked;
- **what changed:** the revision delivered, and the files and declarations, porisms and
  companions included;
- **coverage and route:** what is proved, every qualification and where the reader sees it,
  and the review-record entries you propose;
- **dependencies:** helpers added; citations beyond Heath's references, each with the step
  that brings it in; hypotheses not used; pending proof roots; requests for owners;
- **checks:** each command run, its outcome, and the revision it ran on. A check not run is
  not a pass;
- **open items:** the exact failing goal or problem, and the next step.

If your sandbox cannot write to `.git`, leave your files uncommitted and say so.
