# Templates for a proposition

Six short forms for the work records of one proposition: the brief that settles its
statement, the task that assigns it, the handback that returns it, the review that reads it
(as a report, and as its record in `review/`), a correction to a frozen brief, and a request
for a shared lemma. The rules behind them are in [WORKFLOW.md](../WORKFLOW.md) and
[FORMALIZATION.md](../FORMALIZATION.md); the record's fields are defined in
[review/SCHEMA.md](../../review/SCHEMA.md), and these forms use its words.

Fill them with exact declarations, paths and commits. "None" is a good answer for an
exception, and most entries of a routine proposition are one line. Link an existing brief
rather than copy it. For an editorial task (a sentence, a figure, a quotation), the task
form's first block and its checks are enough.

Fleet orders, for a proof stretch, a statement wave, or a companion proof or a
restatement's, have [their own template](orders.md).

## 1. Proposition brief

The statement contract. Approved by the coordinator before any proof work; each later
change is a new revision (form 5).

```markdown
## Brief <Book>.<N>, revision <r>

Base commit:
Approved by, and when:
Heath: heath/<Book>/NN.md (vol. <v>, pp. <a>–<b>; scan leaves n<x>–n<y>)
Book brief: docs/briefs/<book brief>

Declarations (exact Lean, with any porism and companions):
    theorem PropN …
    theorem PropN.porism …

In plain words (the statement read back, to set beside the enunciation):

Coverage: full / restricted / partial
- Extra hypotheses, each excluding a case Euclid's words admit (in words, then the Lean
  condition: STYLE, section 1, "Hypotheses in words"):
- Clauses left out, quoted exactly from Heath:
- Hypotheses of Euclid's left out, so that the statement claims more:
Cases the statement admits (boundary positions, equality, order, orientation, coincidence,
greater and less), and how each is covered:
Construction: what is given; the operations; what is returned; what shows it solves the
problem:
Representation: tags from review/terms.toml; bridge theorems needed, and where they sit in
the dependency order:
Route: Euclid's main construction and inferences, the propositions he uses, and any
departure approved:
Dependencies: declarations and shared steps available (and what each brings in); pending
ones:
```

## 2. Task

```markdown
## Task <Book>.<N>

Role and result:
Base commit:
Brief and revision:
Owned files:
Owners of shared files touched:
Reviewer:

Sources: Heath's file and pages; the definitions, book brief and examples that apply.

Contract: link the brief; restate only what this task changes.

Finish:
- Deliverables.
- Checks to run, and the review evidence wanted.
```

## 3. Handback

Facts, not celebration. Paste no exploratory logs unless they show an unresolved problem.

```markdown
## Handback <Book>.<N>

Status: ready for review / provisional dependencies / blocked
Revision delivered:
Brief and revision:
Changed files and declarations:

Coverage and route:
- Clauses and cases proved; porism and companions included.
- Qualifications that remain, and where the reader sees them.
- Changes to the contract, with their approval.

Proposed record entries (review/SCHEMA.md):
- [statement] scope, hypotheses, omitted, note, short:
- [route] kind, note:
- [representation] tags:
- [overlap] rule, also, kind (states / gives / step, always named), note (required for a step):
- [[passage]] at, kind (helper / grouped / case / given / different / unformalized), helper, note, unused (bindings that stand for Euclid's words and are not used again):
- [figure] case, every_case or some_cases, and note (a line for under the figure, where
  the drawing departs from Heath's, or, with some_cases, naming the cases not drawn):

Records made stale: the review records whose Lean file or statement this change touched,
even by a comment, and those whose own text it edited; their owner reads and stamps them
(WORKFLOW.md, section 6).

Dependencies:
- Helpers added or changed, with their signatures.
- Citations beyond Heath's references, each with the step that brings it in.
- Pending proof roots.
- Requests for a shared owner (form 6).
- Hypotheses the proof does not use, and why.

Checks (exact commands, outcomes, and the revision checked; the full list is
WORKFLOW.md, section 8):
- lake build
- lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py
- python3 scripts/check_style.py
- Figures rendered and looked at; quotations checked against the scan.

Open items:
- The exact failed goal or unresolved issue, the next step proposed, and the work it
  affects.
```

## 4. Review

### The report

The reviewer begins from Heath and the formal statement, each read on its own, before the
author's account.

```markdown
## Review <Book>.<N>

Revision reviewed:
Brief and revision:
Reviewer, and what was reviewed:

Statement and cases:                    pass / changes needed
Representation and constructions:       pass / changes needed / not applicable
Correspondence with the text, and route: pass / changes needed
Text, attribution and commentary:       pass / changes needed
Figures and the rendered page:          pass / changes needed
Proof and certificate closure:          pass / provisional / changes needed

Findings:
- Severity (blocking / material / editorial), place, defect, correction required.

Disposition:
- Ready / ready with named published limitations / return for correction.
- Checks or sources not reviewed.
```

An accepted limitation names a deliberate boundary of scope. It never stands in for a
defect nobody has looked into.

### The record

What the review leaves in the repository: `review/<book>/NN.toml`, read by
`heath.load_review`. The stamps (`fingerprint`, `commit`, `lean`, `text`) are written by
`scripts/review_stamp.py`, never by hand. Delete the sections that have nothing to say;
`[statement]`, `[route]` and `[review]` are always present.

```toml
# review/<Book>/NN.toml
[statement]
scope = "full"                 # or "restricted", "partial"
# hypotheses = ["in words (`the condition`)"]   # restricted; STYLE, section 1
# omitted = ["quoted exactly from Heath"]       # partial
# note = "One line, at most 160 characters."    # unless full
# short = "a few words for beside the badge"    # unless full; 70 characters at most
# companions = ["<Book>.<N> general"]
fingerprint = "sha256:…"

[route]
kind = "euclid"                # or "modified", "alternative", with a note

[representation]
tags = []                      # from review/terms.toml
# note = "…"

# [overlap]
# rule = "Tacit.…"
# also = ["Tacit.…"]           # any rules that contain it, or supply its step, only with `rule`
# kind = "states"              # required: or "gives", "step", the catalogue's kind of its row
# note = "…"                   # required for a step: which step, in which proof

# [coverage]                   # required when partial
# checked = ["…"]
# explains = ["…"]
# text_only = ["quoted exactly from Heath"]

# [[passage]]
# at = "first words of the passage, quoted exactly"
# kind = "helper"              # carried, helper, grouped, case, given, different, unformalized
# helper = "PropN.something"
# note = "One or two plain sentences, shown on the page."
# unused = ["FC", "this"]      # bindings for Euclid's words, not used again; not shown

# [figure]
# case = "the case the figure shows"
# every_case = true            # only when the figure draws every case the theorem covers
# some_cases = true            # when it draws more than one case, but not every one;
#                              # then the note names the cases it does not draw
# note = "where our drawing places a point otherwise than Heath's, and why"

[review]
stage = "exceptions"           # or "full"
commit = "…"
lean = "sha256:…"
text = "sha256:…"
reviewer = "…"                 # from stage "full": the model or person, and the role
# run = "brief …, stage …, workflow …"   # from stage "full"
# [review.items]               # acceptance (brief 0005, stage 6), in a "full" record
# Keys fixed by docs/ACCEPTANCE.md, P11 to P16:
# statement, passages, representations, commentary, figures, signoff = "pass" / "fail" / "n/a"
# The reviewer records only their own reading, never records an item for a claim they wrote, prompted, or edited.
# Acceptance requires "pass"; representations alone may be "n/a" when P13 does not apply.
# Omitted or empty items are valid under the schema, but do not pass acceptance.
```

## 5. Correcting a frozen brief

```markdown
## Brief correction <Book>.<N>, from revision <r>

The case that fails, or the discrepancy:
Current declaration:
Proposed declaration:
Reason:
Consumers affected (propositions, records, pages, figures):
Work that can go on meanwhile:
```

## 6. Requesting a shared lemma

```markdown
## Shared lemma request

Proposed name and type:
Purpose (the step of Euclid's it supplies):
Proof, or a plan:
Where it may live (what it cites, and so its place in the dependency order):
Who will use it:
```
