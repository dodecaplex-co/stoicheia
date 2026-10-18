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
Write no proof of your statements themselves: they are challenged and approved before
anyone proves them, and a proof written now would be written against a statement that may
still change. The proofs `Staging/` may hold, the derivation under "Nothing is lost" among
them, are listed in WORKFLOW, section 2, "What proofs `Staging/` may hold", the rule's one
home. A scratch proof that tests a statement, where its route is in doubt, is welcome: it is
committed unbuilt in `docs/reports/crew/scratch-<B>/`, never in `Staging/` (WORKFLOW,
section 2).

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
- A companion's docstring says in plain words what the Lean claims, read back from the Lean
  rather than copied from Heath: what is given, what is concluded, and the cases it admits
  (apart, touching, overlapping, coinciding; greater, equal, less). It is a Lean note, and
  reads as `docs/STYLE.md`, section 1, asks; production stays out of it (STYLE, section 1,
  "Production stays out of the mathematics").
- A restatement replaces today's `theorem PropN` itself, where the brief says so (III.24
  and III.25 restated; III.26 and III.28 upgraded). It is staged as
  `Elements.Book<B>.Staging.PropN`, so as not to collide with the theorem it will replace,
  and its proof is to stand under the same `--` lines of Heath's text, whose words never
  change. Its docstring is Heath's enunciation, exactly, as for every `theorem PropN`
  (FORMALIZATION, section 2, "Writing one"); its plain words go in your report. Today's
  statement is kept under the name the brief gives it (`Prop24.equalCircles`, the
  alternative formal proof), and the brief names every consumer the restatement breaks:
  Lean that uses the old conclusion, audit lemmas, mishnah and records (WORKFLOW,
  section 2).
- Nothing is lost: for a companion, today's statement follows from the new one, by a
  corollary the brief names (`Prop40.special`) or an `example` whose type is
  `type_of% @PropN`; for a restatement, today's statement stays, proved, under its new
  name. That derivation checks a statement, not a proposition, and so may be written in
  `Staging/` (WORKFLOW, section 2, "What proofs `Staging/` may hold").
- The definitions the statements share are in `Staging/<stage>/<File>.lean`, each with a
  docstring saying what it represents and how it answers to Euclid's object
  (FORMALIZATION, section 3). A definition moves into the foundations only with the
  coordinator's approval, and is never an `axiom`. One that an approved statement uses
  moves into `Elements/Foundations/`, the coordinator's, before or with that statement's
  move: nothing in `Elements/` ever imports `Staging/`. It joins the vocabulary of
  `Certificate/axioms.lock` in the commit where an entry's statement in `Elements/` first
  uses it, which is the move, with `check_fidelity.py --write-lock`, a decisions entry,
  and the model brought to the new lock as `tests/model/MODEL.md`, "Changing the axioms",
  says (WORKFLOW, section 2, item 1; FORMALIZATION, section 7).

**The rules.** Edit only your statements' files, `Staging/<stage>/Book<B>/PropNN.lean`,
and your scratch proofs. `Staging.lean`'s imports, which are for readers, and the shared
definitions, `Staging/<stage>/<File>.lean`, are the integrator's (WORKFLOW, section 4):
propose in your handback any definition you need that is not there, with its type and
docstring (WORKFLOW, section 4, "Ask for a shared lemma with a proposed type"); leave
both files as they are. Never change a statement, a porism's or a definition in
`Elements/` (WORKFLOW, section 2). Never add an `axiom`, `native_decide` or anything else
that gets round the kernel. If the brief's form of a statement looks wrong or too weak,
write it as the brief says and report the case that fails, with the declaration you
propose (form 5 of `docs/templates/proposition.md`).

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
lake build                                  # Elements unchanged
lake build Staging.<stage>.Book<B>.PropNN   # your file; `sorry` its only warning
lake build Staging                          # every file under Staging/, yours included
```
`lake build Staging` builds every file under `Staging/`, whether or not `Staging.lean`
imports it. No `lake update` or `lake clean`.

**Finish.** Commit your files by name, "<stage>: statements of <…>, with sorry". Do not
push, merge or rebase.

**Report** with form 1 of `docs/templates/proposition.md` for each statement: the exact
declaration; its meaning in plain words; its coverage, with any extra hypothesis or
clause left out; the cases it admits and how each is covered; the construction data; the
representation; and the route its proof is to take, with the propositions it may cite.
Then, for the integrator, the shared definitions you propose; your scratch proofs, if
any; and the questions you could not settle.
````

## 3. A companion proof, or a restatement's

Once a statement in `Staging/` is approved and its brief frozen, its proof is assigned.
A restatement's orders are these, with the differences under "A restatement", below.
The proof follows the route the brief declares; the statement then moves into its
proposition's file, the integrator lists it in the edition's companions,
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
`Elements/Book<B>/PropNN.lean`, for the integrator to commit, as "The move" says below.

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
- Cite only what comes before <B>.N, <B>.N itself, and the companions of <B>.N already
  moved.

**The rules.** Never change the approved statement: not a hypothesis, a conclusion or a
name. If it seems wrong or too weak, stop and propose a correction (form 5 of
`docs/templates/proposition.md`), with the case that fails. Never change `theorem PropN`,
its docstring or its `--` lines: the companion stands beside Euclid's worked
configuration. Never add an `axiom`, `native_decide` or anything else that gets round the
kernel. Edit only the Staging file and `Elements/Book<B>/PropNN.lean` (the companion, its
helpers and the imports they need). Nothing in `Elements/` ever imports `Staging/`: a
staged definition the statement uses moves into the foundations, `Elements/Foundations/`,
the coordinator's, before or with your move. It joins the vocabulary of
`Certificate/axioms.lock` in the commit where an entry's statement in `Elements/` first
uses it, which is the move, with `check_fidelity.py --write-lock`, a decisions entry,
and the model brought to the new lock as `tests/model/MODEL.md`, "Changing the axioms",
says (FORMALIZATION, section 7). If the move would need an import from `Staging/`, stop and ask the
coordinator in your handback. `Staging.lean`'s imports, which are for readers, and the
companions list, `Elements/Companions.lean`, are the integrator's (WORKFLOW, section 4):
propose the companion's entry in your handback, and leave both files as they are. The
record `review/<B>/NN.toml` is <owner>'s.

**The voice.** Your `/- … -/` remarks and your helpers' docstrings are Lean notes, and
read as `docs/STYLE.md`, section 1, asks; what may be said about how the work was made is
STYLE, section 1, "Production stays out of the mathematics".

**The move.** Each commit leaves the build green:
1. Prove the statement where it is, in `Staging/`, and commit the proof there.
2. Move it and its helpers into `Elements/Book<B>/PropNN.lean`, after `PropN` and its
   porism, with the same type and no import from `Staging/`, and delete the staged file.
   A corollary the brief names (`Prop40.special`) moves with it. Leave the move
   uncommitted.
3. Propose in your handback the line that goes with the move, the companion's entry,
   `(``Elements.Book<B>.PropN.<word>, "<B>.N <word>")`, for `Elements.companions` in
   `Elements/Companions.lean`, which then imports `Elements.Book<B>.PropNN`. The
   integrator commits the move with it, in one commit, and takes out of `Staging.lean`
   any import of the deleted file, so that `lake build Staging` stays green and the
   listing travels with the proof (WORKFLOW, section 4).
4. Run the certificate on the move. The companion is not in it until the integrator lists
   it, so find what it rests on from `#print axioms Elements.Book<B>.PropN.<word>`, in a
   scratch file outside the build that imports `Elements.Book<B>.PropNN`
   (`lake env lean "${TMPDIR:-/tmp}/rests.lean"`), and from its citations. Once the entry
   is listed, "<B>.N <word>" is an entry of its own, attached to <B>.N, and the integrator
   confirms what it rests on from the certificate. The record of <B>.N is now stale, for
   its Lean file and its fingerprint have changed.

**A restatement.** The staged `Staging.PropN` is proved by the route the brief declares,
then takes the place of `theorem PropN` in `Elements/Book<B>/PropNN.lean`: its statement
and the Lean beneath each `--` line change; its docstring, Heath's enunciation, and the
`--` lines themselves do not. Today's theorem stays, renamed as the brief says, with its
proof, as the alternative; it is displayed as such, never as Euclid's argument. Every
consumer the brief names changes in the move, so the build stays green, and nothing else
does: those files are yours for this task, save the records, which are their owners'. A
restatement is not a companion, so it proposes no entry in step 3.
Its commits are "<B>.N restated: proof, in Staging" and the integrator's "<B>.N restated,
in place of PropN"; its record entries are the `scope`, the `[route]` and the
`[[passage]]` entries, with no `companions` entry.
The pre-flight's statement guard passes a changed `theorem PropN` only if the push adds a
new line to `docs/briefs/` naming <B>.N; an old line, or one edited in place, does not
count (WORKFLOW, section 10, "Landing work: pull requests"). So the restatement's pull
request adds that line, which is the coordinator's: a revision of the brief, or an entry
in the decisions page.

**The record.** Its owner reads `review/<B>/NN.toml` again against the moved file and the
attached statement: `companions = ["<B>.N <word>"]`, the `scope`, `note` and `short` the
companion now gives (I.40's scope becomes full with `Prop40.general`), and a passage or
route note where the proof departs from the declared route. Then the owner commits and
stamps it with the commit read (WORKFLOW, section 6). Never stamp a record you did not
read.

**Verify.**
```sh
export PATH=$HOME/.elan/bin:$PATH
lake build && lake build Staging      # step 1, the proof in Staging/
lake build && lake build Staging      # then the move
lake build Audit                      # a restatement: the audit lemmas its move changes
lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py
python3 scripts/check_style.py
```
No `lake update` or `lake clean`. `lake build Staging` builds every file under `Staging/`,
whether or not `Staging.lean` imports it, so it still passes after the move; a failure
there is real, and goes in your handback, unless it is only `Staging.lean`'s own import
of the deleted file, which the integrator takes out. These are expected: until the
record's owner stamps it, the record of <B>.N is "changed since it was reviewed"; the
pages are rendered after the merge; and, for a restatement whose statement uses a
definition moved into the foundations, `check_fidelity.py` finds that word missing from
the lock until the move's commit adds it. Name the word in your handback.

**Finish.** Commit the proof in `Staging/` by name, "<B>.N <word>: proof, in Staging", and
leave the move for the integrator, who commits it as "<B>.N <word>: proof, moved beside
<B>.N"; never the generated edition. Do not push, merge or rebase.

**Report** with the handback of `docs/templates/proposition.md`: proved, or where the
`sorry` is; the route taken, and any step where it left the declared one; your helpers;
citations beyond Heath's references, each with the step that brings it in; hypotheses
your proof does not use; what "<B>.N <word>" rests on, found as step 4 says; the entry
you propose for `Elements/Companions.lean`; the record entries you propose (`companions`,
`scope`, `note`, `short`); the records made stale; and the checks you ran, with their
outcomes.
````
