# The review rubric

**Version 1, 21 October 2026.** The rubric every outside reviewer is given, word for word, when
they score Books I, II and III. It is kept here so that every score can be reproduced: a
measurement names the rubric's version, and a later version never rescores an earlier
measurement. The scores themselves are not kept in this repository, so that each reviewer comes
in cold ([WORKFLOW](WORKFLOW.md), section 10, step 9).

## How a measurement is made

1. **A cold copy.** A fresh clone of the revision measured (main, or the release candidate),
   built with `lake build`. The files that record an earlier outside review and its scores
   are removed from the copy before the reviewer sees it.
2. **Three reviewers, one rubric.** Three models from three families score the same copy
   independently, each given this rubric unchanged: at present Claude, GPT-6 Astra (Codex)
   and Gemini Argon. None sees another's review, or any earlier score.
3. **The gaps.** Each review ends with its open gaps. A gap that two or more reviewers name is
   a **consensus gap**: it must close before the book passes. A gap one reviewer names is
   weighed on its merits. Every gap becomes an issue, or a named part of one.
4. **The gate.** A book passes when all three reviewers score it 95 or more, and no consensus
   gap is open. No work on the next book begins before then.

## The rubric

Score each of Books I, II and III separately, out of 100, in five parts. A score sums up the
findings. It never cancels one, so report every gap you find, whatever it costs in points.
Come in cold. Judge only what is in the copy you were given; do not trust its badges, summaries
or self-assessment. Check every claim you score against the Lean, Heath's text and the
generated certificate.

**1. Statements at Euclid's full scope (40).** For each proposition, compare the Lean statement
with Euclid's enunciation, including its porism if there is one.
- A statement that proves all of the enunciation, for every figure Euclid's words allow,
  counts 1.
- A restricted statement, one that proves the claim for only some of those figures, counts ½.
- A partial statement, one that proves only some of the clauses, counts ¼.
- An unproved statement, or one with `sorry`, counts 0.

The part's score is 40 times the book's average. A companion theorem counts toward its
proposition only if it is proved and the page says what it adds. Decide each proposition's
scope yourself; where yours differs from the page's, say so.

**2. Proofs follow Euclid's own argument (15).** Is each proof Euclid's argument, step by step,
where the page says it is? A different route that the page discloses costs a little; one that
departs without saying so costs a lot. So does a citation that does no work, a hypothesis used
only to look used, or a citation of a later proposition.

**3. Foundations and representation (15).** Are the axioms faithful to what Euclid takes for
granted, and no stronger? Deduct for a proof that rests on a rule which already contains the
proposition (see the overlap catalogue, and check it); for a representation with no bridge to
the object in the text (arcs, angles, areas, mixed angles, figures); and for a gap in the
evidence that the axioms are consistent (the numerical model, and the formal model in
`model/`).

**4. Verification (15).** Can a stranger rebuild it and trust the result? Consider the kernel
check and any independent replay; the axiom lock; whether the certificate is accurate about
what each proof truly rests on, porisms and companions included; CI and the checks; and the
steps to reproduce it from a fresh clone.

**5. Edition and review (15).** Consider Heath's text, exact; the commentary, accurate and
specific; figures that agree with the proof; every departure from Euclid disclosed on the page
itself; the review records, at what stage, and whether someone other than the author signed
them off; and ease of use, for a reader and for a Lean user who depends on the library.

## What a review reports

1. For each book, a table of the five parts with the score for each, and the total.
2. Under each part, every deduction, naming the propositions and files, with the reason.
3. **The open gaps**, the most important part of a review, ranked in three groups: blocking (a
   claim that is false), material (something a careful reader would be misled by, or a scope
   or route short of Euclid's) and minor. Each gap gives its evidence (a file and line, or the
   proposition) and says what would close it.
4. What would raise each book's score most, in order.
5. Where the reviewer was unsure, and why.

## Change log

- **Version 1, 21 October 2026.** The rubric in use since 19 October, when all three reviewers
  were first given the same text, recorded here unchanged (#212).
