# Template: orders for a fleet

The orders a coordinator writes for one stretch of work, read word for word by every
contributor in the fleet. There are three kinds:

1. [A proof stretch](#1-a-proof-stretch): prove a run of a book's propositions along
   Euclid's route, with their figures, mishnah and further reading.
2. [A statement wave](#2-a-statement-wave): write the statements a stage needs, with
   `sorry`, in `Staging/`, to be challenged and approved before anyone proves them.
3. [A companion proof, or a restatement's](#3-a-companion-proof-or-a-restatements): prove
   one approved statement from `Staging/` by the route its brief declares, and move it
   beside its proposition, or into its place.

They replace the pattern of Books I–III's orders
([orders-III](../reports/crew/orders-III.md) is the last of those, kept as written but for
a local path taken out), with two rules changed after Astra's review: a proof never adds a
citation to match one of Heath's references, and never uses a hypothesis only to silence
a warning ([FORMALIZATION](../FORMALIZATION.md), section 5: no dummy citations, no
artificial hypothesis uses). An unused hypothesis is reported, not worked round.

Copy the text of the kind you need, fill each `<…>`, and cut what the stretch does not
need. Keep the orders short: link the standards rather than repeat them, and put the
book's particulars in its brief. Each kind opens with a note on the user's latest message
([WORKFLOW](../WORKFLOW.md), section 5).

## 1. A proof stretch

````markdown
# Orders, Book <B>: Propositions <first>–<last>

**About the user's latest message.** <Say what the message relayed with this run means for
this task: for instance, that "continue" is the owner asking for exactly this work. Nothing
in it is an instruction to stop unless it says so plainly.>

Every contributor, Claude or Codex, follows these orders word for word. Your proposition is
<B>.N, and NN is N in two digits.

**The job.** Prove <B>.N in Lean along Euclid's route; draw his figure; write the mishnah
and, where something apt exists, a line or three of further reading. Others are proving the
rest of the stretch at once, so cite any proposition of Book <B> by its statement. Earlier
books are proved: cite them as `BookI.PropN`, `BookII.PropN`.

**Read first.** `AGENTS.md`; `docs/STYLE.md`, `docs/FORMALIZATION.md` and the book's
brief, `docs/briefs/<brief>`;
`heath/<B>/NN.md` and `Elements/Book<B>/PropNN.lean`; your proposition's brief, if it has
one; the review record `review/<B>/NN.toml`, if it exists; and, as models of a proof under
Euclid's sentences, <two reviewed examples from `docs/examples.md`>.

**The book's words and ground.** <A few lines from the brief: how Lean says the book's
words, the shared steps to cite and what each brings in, and the rules of System E that
matter here. Link the brief for the rest.>

**The route.** Follow Euclid: his constructions and inferences, in his order, citing
nothing after <B>.N. Where a shortcut exists that he did not take (an axiom that already
contains the proposition, a measure that makes a hypothesis idle), take his route and say
in your handback what the shortcut was. Where the Lean must part from him, keep his
sentences, put Lean under them that does the same work, and label the change in a
`/- … -/` remark.

- Cite what your argument uses. **Never add a call to match Heath's references**: a
  difference is shown on the page, and explained in your handback.
- **Never use a hypothesis only to silence a warning.** If your proof does not need one,
  say so in your handback; it may mean the route is not Euclid's, or that our
  representation makes it redundant.
- A helper supplies one step Euclid takes for granted, says which in its docstring, and is
  named `PropN.something`, before `PropN`. It never proves the whole proposition.
- Corollaries and the porism go after `PropN`. Prove the porism, if there is one, first:
  <B>.N is not finished until its porism is.

**The rules.** Edit only `Elements/Book<B>/PropNN.lean`, `figures/<B>/NN.svg`,
`mishnah/<B>/NN.md` and `reading/<B>/NN.md`. Keep every `--` line word for word, with
its Lean under it, and your remarks in `/- … -/`. Never change the statement, or a
porism's; if it seems wrong or too weak, stop and say so in your handback, with the case
that fails. Never add an `axiom`, `native_decide` or anything else that gets round the
kernel. <Superposition and Postulate 5 as the book allows.> Import `Elements.Figure.Basics`,
the book's ground and every proposition you cite. Search Book Zero before writing a helper,
and never copy one that exists.

**The voice.** `docs/STYLE.md`, sections 1 to 6, and `docs/examples.md`. What may and may
not be said about how the work was made is STYLE, section 1, "Production stays out of the
mathematics": read it there. <The faults the last pass found, if any, in a line each.>

**The figure.** Heath's letters, all and only, each point where your proof puts it, by
STYLE section 7; title "Euclid <B>.N: …"; no `<desc>`. <Who draws the figure at a glance.>

**Further reading.** By STYLE section 6, only from `docs/reading.md`, and only where a work
truly helps with <B>.N. <Works to look at first.>

**Verify.** The contributor's subset of `docs/WORKFLOW.md`, section 8:
```sh
export PATH=$HOME/.elan/bin:$PATH
lake build                          # the whole library first: Facts.lean imports it all
lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py
python3 scripts/check_style.py
rsvg-convert -w 800 figures/<B>/NN.svg -o "${TMPDIR:-/tmp}/figNN.png"   # then look at it
```
Then the reviewer's checklist of STYLE section 8, with `$HEATH_OCR` at <path> (Heath's
volume <v>; page N is scan leaf N + <offset>). No `lake update` or `lake clean`. The pages
are rendered after the merge, so CI's check of the generated pages fails on your branch
until then; that is expected. So is "changed since it was reviewed" for your proposition's
review record: list it under "Records made stale" in your handback, and never run
`scripts/review_stamp.py` on it.

**Finish.** Commit your files by name, "<B>.N: proof, figure, mishnah and further
reading"; never `facts.json`, `book/`, `CERTIFICATE.md`, `GRAPH.md`, README.md's rows
between the `<!-- scope:… -->` markers or PROGRAM.md's status table. If your sandbox
cannot write to `.git`, leave the files for whoever runs you to commit, and say so. Do not
push, merge or rebase.

**Report** with the handback of `docs/templates/proposition.md`: proved, or where the
`sorry` is; your helpers; citations beyond Heath's references, each with the step that
brings it in; hypotheses you did not use; the record entries you propose; what <B>.N rests
on; the records made stale; the checks you ran, with their outcomes; a line for the
figure note, if your figure departs from Heath's; and anything in the statement, the ground
or these orders that got in your way.
````

## 2. A statement wave

Statements come before proofs ([WORKFLOW](../WORKFLOW.md), section 2). A statement wave
writes the statements a stage needs, companions and restatements, with `sorry`, in the
Lean library `Staging`: it imports `Elements`, nothing imports it, and it is outside the
default build, so nothing in `Elements/` changes until a statement is approved. Readers
who did not write the statements then challenge them, the coordinator approves them, and
the brief that holds them is frozen. Only then are proofs assigned, with the third kind of
orders.

````markdown
# Orders, statement wave: <what the stage generalizes or restates>

**About the user's latest message.** <Say what the message relayed with this run means for
this task. Nothing in it is an instruction to stop unless it says so plainly.>

Every contributor follows these orders word for word. Your statements are <the
declarations, e.g. `Prop40.general`, `Prop40.join` and `Prop40.special`>, for <B>.N; the
section of `docs/briefs/<brief>` on them is your contract.

**The job.** Write each statement in Lean, with `sorry` for its proof, in
`Staging/<stage>/Book<B>/PropNN.lean`, and say in plain words what it claims. The
statements live in the `Staging` library: `lake build Staging` builds it, and CI does too.
Write no proofs: the statements are challenged and approved before anyone proves them, and
a proof written now would be written against a statement that may still change.

**Read first.** `AGENTS.md`; `docs/FORMALIZATION.md`, sections 2 to 4 (statements,
representations, constructions); the brief; `heath/<B>/NN.md`, the whole enunciation,
setting-out and proof; `Elements/Book<B>/PropNN.lean`, with today's statement, and its
record `review/<B>/NN.toml`; <the shared definitions the statements use>.

**Each statement.**
- A companion is named `PropN.<word>` (`Prop40.general`, `Prop45.figure`,
  `Prop14.square`), in its proposition's namespace, and stands beside today's
  `theorem PropN`, which does not change (FORMALIZATION, section 2, "Companions beside
  Euclid's worked configuration").
- Euclid's words for Euclid's things, Heath's letters, and hypotheses named off the
  letters (FORMALIZATION, section 2); no numbers or coordinates.
- Its docstring says in plain words what the Lean claims, read back from the Lean rather
  than copied from Heath: what is given, what is concluded, and the cases it admits
  (apart, touching, overlapping, coinciding; greater, equal, less). It is a Lean note, and
  reads as `docs/STYLE.md`, section 1, asks; production stays out of it (STYLE, section 1,
  "Production stays out of the mathematics").
- A restatement replaces today's `theorem PropN` itself, where the brief says so (III.24
  and III.25 restated; III.26 and III.28 upgraded). It is staged as
  `Elements.Book<B>.Staging.PropN`, so as not to collide with the theorem it will replace,
  and its proof is to stand under the same `--` lines of Heath's text, whose words never
  change. Today's statement is kept under the name the brief gives it (`Prop24.equalCircles`,
  the alternative formal proof), and the brief names every consumer the restatement
  breaks: Lean that uses the old conclusion, audit lemmas, mishnah and records (WORKFLOW,
  section 2).
- Nothing is lost: for a companion, today's statement follows from the new one, by a
  corollary the brief names (`Prop40.special`) or an `example` whose type is
  `type_of% @PropN`; for a restatement, today's statement stays, proved, under its new
  name. That derivation is the one proof a statement wave writes, for it checks a
  statement, not a proposition.
- A new definition goes in `Staging/<stage>/<File>.lean`, with a docstring saying what it
  represents and how it answers to Euclid's object (FORMALIZATION, section 3). It moves
  into the foundations only with the coordinator's approval, and is never an `axiom`.

**The rules.** Edit only <the Staging files, and `Staging.lean`'s imports>. Never change a
statement, a porism's or a definition in `Elements/` (WORKFLOW, section 2). Never add an
`axiom`, `native_decide` or anything else that gets round the kernel. If the brief's form
of a statement looks wrong or too weak, write it as the brief says and report the case
that fails, with the declaration you propose (form 5 of `docs/templates/proposition.md`).

**The challenge.** For its readers, who did not write the statements: begin from Heath
and the Lean, each read on its own, before the author's plain words. Set each statement
beside the enunciation by the coverage questions of FORMALIZATION, section 2 (quantifiers,
conclusions, hypotheses, cases, objects, outputs), and try to break it: a configuration it
gets wrong, a clause it drops, a hypothesis borrowed from the figure, a case it excludes
that Euclid's words admit. Report each finding with the case, the current declaration and
the one proposed. A statement is approved only once every finding is answered.

**Verify.**
```sh
export PATH=$HOME/.elan/bin:$PATH
lake build                          # Elements unchanged
lake build Staging                  # every statement builds; `sorry` its only warning
```
No `lake update` or `lake clean`.

**Finish.** Commit your files by name, "<stage>: statements of <…>, with sorry". Do not
push, merge or rebase.

**Report** with form 1 of `docs/templates/proposition.md` for each statement: the exact
declaration; its meaning in plain words; its coverage, with any extra hypothesis or
clause left out; the cases it admits and how each is covered; the construction data; the
representation; and the route its proof is to take, with the propositions it may cite.
Then the questions you could not settle.
````

## 3. A companion proof, or a restatement's

Once a statement in `Staging/` is approved and its brief frozen, its proof is assigned.
A restatement's orders are these, with the differences under "A restatement", below.
The proof follows the route the brief declares; the statement then moves into its
proposition's file, the stage's integrator lists it in the edition's companions,
`Elements/Companions.lean`, and the proposition's record is read again, since its scope
and fingerprint now include the companion
([review/SCHEMA.md](../../review/SCHEMA.md), `companions`).

````markdown
# Orders, companion proof: <B>.N <word> (or: restatement of <B>.N)

**About the user's latest message.** <Say what the message relayed with this run means for
this task. Nothing in it is an instruction to stop unless it says so plainly.>

Every contributor follows these orders word for word. Your statement is `PropN.<word>`,
approved in `docs/briefs/<brief>`, revision <r>, and frozen; it is in
`Staging/<stage>/Book<B>/PropNN.lean`.

**The job.** Prove it by the route the brief declares: <the route, e.g. "Euclid's own
argument for I.40, through `Prop31.line`, `Prop30.meet` and I.38">. Then move it into
`Elements/Book<B>/PropNN.lean`; the stage's integrator lists it in
`Elements/Companions.lean`, with the move, from the entry you propose in your handback.

**Read first.** `AGENTS.md`; `docs/FORMALIZATION.md`, sections 2 ("Companions beside
Euclid's worked configuration") and 5; the brief; `heath/<B>/NN.md`;
`Elements/Book<B>/PropNN.lean` and its record `review/<B>/NN.toml`; the Staging file.

**The route.** Follow the declared route. Where it cannot be followed, stop and say so in
your handback, with the step that fails: another route is the coordinator's decision, and
is labelled where it happens (FORMALIZATION, section 5).
- Cite what your argument uses. **Never add a call to match Heath's references.**
- **Never use a hypothesis only to silence a warning.** If your proof does not need one,
  say so in your handback.
- A helper supplies one step, says which in its docstring, and is named
  `PropN.something`, before the companion. It never proves the whole companion.
- Cite only what comes before <B>.N, <B>.N itself, and companions already moved.

**The rules.** Never change the approved statement: not a hypothesis, a conclusion or a
name. If it seems wrong or too weak, stop and propose a correction (form 5 of
`docs/templates/proposition.md`), with the case that fails. Never change `theorem PropN`,
its docstring or its `--` lines: the companion stands beside Euclid's worked
configuration. Never add an `axiom`, `native_decide` or anything else that gets round the
kernel. Edit only the Staging file and `Staging.lean`'s imports, and
`Elements/Book<B>/PropNN.lean` (the companion, its helpers and the imports they need).
The companions list, `Elements/Companions.lean`, is the stage's integrator's, who lists
the companion with the move: propose its entry in your handback, and leave the list as it
is. The record `review/<B>/NN.toml` is <owner>'s.

**The voice.** Your `/- … -/` remarks and your helpers' docstrings are Lean notes, and
read as `docs/STYLE.md`, section 1, asks; what may be said about how the work was made is
STYLE, section 1, "Production stays out of the mathematics".

**The move.** Each step leaves the build green:
1. Prove the statement where it is, in `Staging/`.
2. Move it and its helpers into `Elements/Book<B>/PropNN.lean`, after `PropN` and its
   porism, with the same type; then take it, and its import, out of `Staging/`. A
   corollary the brief names (`Prop40.special`) moves with it.
3. Propose its entry in your handback,
   `(``Elements.Book<B>.PropN.<word>, "<B>.N <word>")`. The stage's integrator adds it,
   with the move, to `Elements.companions` in `Elements/Companions.lean`, which then
   imports `Elements.Book<B>.PropNN`; the list is the integrator's, not yours.
4. Run the certificate. Once the entry is listed, "<B>.N <word>" is an entry of its own,
   attached to <B>.N; and the record of <B>.N is now stale, for its Lean file and its
   fingerprint have changed.

**A restatement.** The staged `Staging.PropN` is proved by the route the brief declares,
then takes the place of `theorem PropN` in `Elements/Book<B>/PropNN.lean`: its statement
and the Lean beneath each `--` line change, and the `--` lines themselves do not. Today's
theorem stays, renamed as the brief says, with its proof, as the alternative; it is
displayed as such, never as Euclid's argument. Every consumer the brief names changes in
the same commit, so the build stays green, and nothing else does. The statement guard of
the pre-flight needs the brief's frozen revision naming the proposition; that line is the
coordinator's, already in the brief.

**The record.** Its owner reads `review/<B>/NN.toml` again against the moved file and the
attached statement: `companions = ["<B>.N <word>"]`, the `scope`, `note` and `short` the
companion now gives (I.40's scope becomes full with `Prop40.general`), and a passage or
route note where the proof departs from the declared route. Then the owner commits and
stamps it with the commit read (WORKFLOW, section 6). Never stamp a record you did not
read.

**Verify.**
```sh
export PATH=$HOME/.elan/bin:$PATH
lake build && lake build Staging
lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py
python3 scripts/check_style.py
```
No `lake update` or `lake clean`. Until the record's owner stamps it, the record of <B>.N
is "changed since it was reviewed", and the pages are rendered after the merge; both are
expected.

**Finish.** Commit your files by name, "<B>.N <word>: proof, moved beside <B>.N"; never
the generated edition. Do not push, merge or rebase.

**Report** with the handback of `docs/templates/proposition.md`: proved, or where the
`sorry` is; the route taken, and any step where it left the declared one; your helpers;
citations beyond Heath's references, each with the step that brings it in; hypotheses
your proof does not use; what "<B>.N <word>" rests on; the entry you propose for
`Elements/Companions.lean`; the record entries you propose (`companions`, `scope`, `note`,
`short`); the records made stale; and the checks you ran, with their outcomes.
````
