# Template: orders for a fleet

The orders a coordinator writes for one stretch of a book, read word for word by every
contributor in the fleet. They replace the pattern of Books I–III's orders
([orders-III](../reports/crew/orders-III.md) is the last of those, kept as written), with
two rules changed after Astra's review: a proof never adds a citation to match one of
Heath's references, and never uses a hypothesis only to silence a warning. An unused
hypothesis is reported, not worked round.

Copy the text below, fill each `<…>`, and cut what the stretch does not need. Keep the
orders short: link the standards rather than repeat them, and put the book's particulars
in its brief.

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
