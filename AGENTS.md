# Stoicheia: for agents

Stoicheia is a reader's edition of Euclid's *Elements*: Heath's text, synthetic proofs in
plain Lean 4.35 (no Mathlib), two figures, a certificate of what each proof rests on, and
commentary, for Books I–III so far. It is a friendly, public project. Read this file on
every task. It is short on purpose: each rule lives in one place, and this file links
to it.

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
| Accurate statements, with their scope stated ([FORMALIZATION](docs/FORMALIZATION.md), section 2) | A mishnah as long as its proposition needs, with no count of words or paragraphs ([STYLE](docs/STYLE.md), section 3) |
| Exact quotations, with checked attribution (STYLE, section 5) | Bold leads only where a hook helps, each proposition-specific |
| An accurate account of the route (FORMALIZATION, section 5) | Four Lean names at most in a mishnah |
| Omitted or reformulated clauses visible on the page (STYLE, section 2) | "The modern way" only where it helps, as a short last paragraph |
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
  generated output (`facts.json`, `book/`, `CERTIFICATE.md`, `GRAPH.md`, README.md's rows
  between the `<!-- scope:… -->` markers and PROGRAM.md's status table between the
  `<!-- status -->` markers, and inline `count:` values) and the companions list
  (`Elements/Companions.lean`); WORKFLOW section 8's first command block between the
  `<!-- checks -->` markers is generated from `checks/` too, but a part that changes
  `checks/` commits it regenerated with `render.py`; the coordinator owns the foundations
  (`Elements/Foundations/`), `Certificate/axioms.lock`, the toolchain (`lean-toolchain`,
  `lakefile.toml`, `lake-manifest.json`), the decisions page and `docs/decisions/`,
  PROGRAM.md and CI; your orders name the owner of everything else
  ([WORKFLOW](docs/WORKFLOW.md), section 4).
- Need something outside your files? Ask its owner in your handback, with a concrete
  proposal; a shared lemma is asked for with form 6 of the
  [templates](docs/templates/proposition.md).
- An interface wrong? Stop work on what depends on it, and propose a correction as
  WORKFLOW, section 2, says; go on with the work it does not affect.
- Commit your files by name; never `git add -A` in a tree others use.

## Never

Each rule has one home, linked; this list only points to it.

- Add an `axiom`, or anything that gets round the kernel (the forbidden commands are in
  [FORMALIZATION](docs/FORMALIZATION.md), section 7).
- Change a statement, a porism's statement or a definition without approval
  (WORKFLOW, section 2); change the words of a `--` line; change `heath/` except against
  the page image (STYLE, section 5).
- Add a dummy citation or an artificial hypothesis use, hide a whole conclusion inside a
  helper, or cite a later proposition (FORMALIZATION, section 5).
- Weaken, skip or remove a check, test, expected value, lock or schema to let a change pass
  (FORMALIZATION, section 1).
- Commit generated files unless you are the integrator (WORKFLOW, section 4), save the
  `<!-- checks -->` region, which a part that changes `checks/` commits regenerated.
- Push, or open, merge or approve a pull request: agents never do. The coordinator lands
  work on main only as a pull request, through `scripts/safe_push.py` (WORKFLOW, section
  10, "Landing work: pull requests").
- Publish: tag, release, write release notes, change the GitHub description, or send
  anything outside the repository. Each needs the repository owner's OK (WORKFLOW,
  section 1).
- Invent a quotation, a page or a reference; put crew talk where readers look; write
  anything competitive (STYLE, sections 1 and 5).

No guide, this one included, grants authority to change the foundations, weaken a check or
publish.

## Commands

The full list, exactly as CI runs it, is in [WORKFLOW](docs/WORKFLOW.md), section 8. A
contributor runs this much:

```sh
export PATH=$HOME/.elan/bin:$PATH
python3 scripts/check_paths.py      # the paths staged: git add a new file first
lake build                          # the whole library: the certificate imports it all
lake env lean Certificate/Facts.lean
python3 scripts/check_fidelity.py
python3 scripts/check_style.py
python3 scripts/render.py           # a preview; only the integrator commits its output
```

On your branch, a changed Lean file makes its review record stale: that is expected. List
the records made stale in your handback, and never stamp a record you did not review
(WORKFLOW, section 6). No `lake update` or `lake clean`.

## The handback

End every task with a short, factual handback, in the shape of form 3 of the
[templates](docs/templates/proposition.md), its one home: status, what changed, coverage
and route, the record entries you propose, the records made stale, dependencies, the checks
run with their outcomes and revision (a check not run is not a pass), and open items.

If your sandbox cannot write to `.git`, leave your files uncommitted and say so.
