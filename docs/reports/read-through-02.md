# Read-through 02: Books I to III

*29 October 2026. A draft. Books I and II were read at main
3938eacc7eb378465aa2c0fcae1cbfbfe1a0a756, on 29 October. A section for Book III follows,
read when Book III's queued trains have landed (#34). The state of each finding is given as
at main 559237731, the head when this draft was written; "Since the read" lists what changed
in the paths read between the two.*

*This file held an earlier read of Books I and II, made at 2e8aecf8 on 21 and 22 October; it
stands in the history at 4baf973fe. [Read-through 03](read-through-03.md) is the read of 25
and 26 October. Neither one's verdicts were used here: the readers below were told not to
open either report, and none did, save for one line noted under "The pilot editor".*

## Who read what

Every reader is Claude Opus 5.5, working as an independent reader, and none wrote, prompted
or edited any of the pages it judged. Each read the tree pinned at 3938eacc7, checked the
commit itself, and changed nothing in it.

| Role | Read | At |
|---|---|---|
| Reader of I.1 to I.12 (RD-r1) | Book I's index with its introduction, its front matter, the table of names, and I.1 to I.12 | 3938eacc7 |
| Reader of I.13 to I.24 (RD-r2) | I.13 to I.24 | 3938eacc7 |
| Reader of I.25 to I.36 (RD-r3) | I.25 to I.36 | 3938eacc7 |
| Reader of I.37 to I.48 (RD-r4) | I.37 to I.48 | 3938eacc7 |
| Reader of II.1 to II.7 (RD-r5) | Book II's index with its introduction, its front matter, and II.1 to II.7 | 3938eacc7 |
| Reader of II.8 to II.14 (RD-r6) | II.8 to II.14 | 3938eacc7 |
| Book I's flow reader (RD-f1) | Book I's index, introduction and front matter, then for I.1 to I.48 in order the top of each page, its notes, its commentary, its further reading and its figure at a glance | 3938eacc7 |
| Book II's flow reader (RD-f2) | Book II's index, introduction and front matter, then II.1 to II.14 whole, in order, with every figure; and, as a reader arriving from Book I meets them, Book I's introduction and the commentary of I.46 to I.48 | 3938eacc7 |
| Pilot editor (RD-p) | book/II/01.md, book/I/45.md and book/II/14.md, one after another | 3938eacc7 |
| Director of the read and writer of this report (RD) | An AI reading ship, Claude Opus 5.5, with no part in writing these pages. It wrote the readers' orders, checked each material finding against the sources named below, and wrote this report and the card drafts; it read no page as a reader and mended nothing | 3938eacc7 and 559237731 |

**How they read.** The six readers of ranges read every rendered page of their range top
to bottom, as a visitor meets it on GitHub, each against its sources: Heath's text in
heath/, the review record, the commentary, the further reading, the Lean and facts.json.
They rendered every figure to an image and looked at it beside the proof, all 162 figures
of the two books, and three of them, with the pilot editor, compared Euclid's figures with
Heath's printed ones on the page images of his first volume. They checked every Heath quotation's words and page against the
OCR of that volume, and many against the page images (leaves n297 to n430 among them); the
OCR keeps no italics, and the italics left unchecked are listed under "Doubts". The flow
readers read for what only a reader of a whole book sees, and the pilot editor for what the
three pilot pages pass on to every other page. No reader ran Lean: none graded a finding
blocking, so none needed to.

## How the findings are graded

By [WORKFLOW](../WORKFLOW.md) section 9, "Release criteria and severity". Blocking is an
invalid or wrongly scoped formal claim presented as full, an unresolved dependency presented
as closed, an unapproved change to the foundations, or a materially false certificate.
Material is an unmarked alternative argument, a hidden omission of a clause, an unsupported
claim about a representation, a misleading figure, or a wrong quotation or attribution.
Editorial is what "does not change the meaning". A sentence that a reader sees and that is
false is therefore graded material here when it is not blocking: it changes the meaning, so
it cannot be editorial.

## What they found

| Book | Blocking | Material | Editorial | All |
|---|---|---|---|---|
| I | 0 | 2 | 41 | 43 |
| II | 0 | 3 | 16 | 19 |
| Books I and II | 0 | 5 | 57 | 62 |

The counts are of distinct findings: a finding that several readers made counts once. The
readers made 87 in all, 6 of them material; the pilot editor's 12 notes, all editorial, are
counted among these. A finding that spans both books (the line in the "Reviewed" row, the
terms of I.45 and II.14) is counted with Book I. The editorial findings are listed under
their card drafts, below.

### The material findings

| # | Page | Finding | Readers | State at 559237731 |
|---|---|---|---|---|
| M1 | I.8 | The commentary says two of the laws I.8 cites have proofs that "draw circles and straight lines too"; the certificate puts only Postulate 3 beneath them | RD-r1 1; RD-f1 2 | Open: card draft RD-C1 |
| M2 | I.13, I.47 | Metric 5 supplied a step of I.47's proof that is a consequence of I.13, and I.13's status line did not say so | RD-f1 1 | Resolved at 559237731 (pull request #699): I.47 now takes the step from I.13 itself |
| M3 | Book II's introduction | "Two enunciations are wider than the case Euclid's proof draws": II.5's and II.9's are wider too | RD-r5 1 | Open: card draft RD-C2 |
| M4 | Book II's introduction | "We prove each once": II.5 and II.14 prove the right angle beside a right angle again, in their own Lean | RD-f2 1 | Open: card draft RD-C2 |
| M5 | II.9, II.10 | The captions at a glance give a reason in areas that is not Euclid's, without the label II.8's caption gives | RD-f2 2 | Open: card draft RD-C3 |

**M1. I.8's commentary, on what the cited laws' proofs draw.** mishnah/I/08.md:5
(book/I/08.md:363) says: "The same is true of two of the three other laws I.8 cites, that a
straight line equal to one with distinct ends has distinct ends, and Savile's argument from
I.4 that on a ray only one point lies at a given distance from its start: their proofs draw
circles and straight lines too, and only Metric 3 is proved with no construction." facts.json
gives, for I.8's `cited_laws`, `"construction_rules": ["Postulate3"]` for both `neOfLen` and
`rayUnique`; only the law `prop7` has `Postulate1` and `Postulate2` beneath it. The page's own
table of the laws cited inside the placement says the same (book/I/08.md:351-352). So these
proofs describe a circle and draw no straight line, and "and straight lines" is false. The
sentence stands unchanged on main at 559237731. *What it should say:* "... from its start:
their proofs draw a circle too (Postulate 3), and only Metric 3 is proved with no
construction." facts.json is computed from the Lean and checked against it by
`check_fidelity.py`; `#print axioms Elements.Superposition.Cited.holds_neOfLen` and
`#print axioms Elements.Superposition.Cited.holds_rayUnique` would show it again.

**M2. The overlap at I.13.** At 3938eacc7 the catalogue's table of current overlaps had the
row "| I.13, a consequence used in I.47 | Metric 5 (`angle_le_two_right`) | Supplies a step:
the upper bound on an angle | I.47 | None |" (docs/reports/overlaps.md:74), and
review/SCHEMA.md:120-125 gives this very overlap as its example of the kind `step`, which
"the page words ... in the line under the enunciation". No Book I record carried it, and
I.13's status line read only "proved, as Euclid states it · Euclid's argument"; I.47's page
told it in a passage note alone. Pull request #699, merged as 559237731, makes I.47 rule out
AD beyond B by I.13's bound (`Prop13.angle_lt_two_right`), so no entry rests on Metric 5 and
the row has moved to the catalogue's former overlaps. Nothing is left to mend. One sentence of
[ACCEPTANCE](../ACCEPTANCE.md), item B2, still names "I.13's upper bound on an angle, used in
I.47" as a row "read by no record"; that is for the owner of ACCEPTANCE.md to bring up to
date, and is on card draft RD-C10.

**M3. "Two enunciations are wider".** mishnah/intro/II.md:5 (book/II/index.md:13): "Two
enunciations are wider than the case Euclid's proof draws; there the main theorem keeps his
case and companions take the rest." II.5's enunciation is wider too: its record's `case`
passage says "Euclid's figure puts D between C and B" and "covers D between A and C by
exchanging A and B" (review/II/05.toml:12), its figure note says "Drawn for one case: D
between C and B" (book/II/05.md:23), and Heath writes that "Euclid's figure corresponds to one
only of the two solutions" (vol. 1, p. 384). docs/briefs/book-II.md:84-86 says the same of
II.9. There the main theorem itself takes the wider enunciation, so the sentence understates
the Lean rather than overstating it, but as a count it is false. *What it should say:* "In two
propositions the main theorem keeps the case Euclid's proof draws, and companions take the
rest of the enunciation. Elsewhere the main theorem meets a wider enunciation itself: II.5
and II.9 let D fall on either side of C, though Euclid's figure puts it between C and B."

**M4. "We prove each once".** mishnah/intro/II.md:7 (book/II/index.md:15): "Page after page,
Euclid takes the same few things for granted. We prove each once, in `Rectangles.lean` or,
for one of them, in I.13's file", the one being the right angle beside a right angle
(`Tacit.adjacent_eq_of_right`). II.5's note says "the right angle HDA is proved in place, for
the angles BDH, HDA on the straight line AB make two right angles by I.13", and II.14's "The
Lean proves it in place". The Lean bears them out: Elements/BookII/Prop05.lean:138 and
Prop14.lean:165 and :291 call `BookI.Prop13` directly, and neither file names
`adjacent_eq_of_right`; the overlap catalogue says as much ("after II.5 and II.14 came to
prove their right angles in place", docs/reports/overlaps.md:202 at 559237731). *What it
should say:* either II.5 and II.14 call `Tacit.adjacent_eq_of_right`, and their notes say so
in a clause, or the introduction says: "We prove each in one place, in `Rectangles.lean` or,
for one of them, in I.13's file, and the line under each page's table names those its proof
calls on; II.5 and II.14 take the right angle beside a right angle from I.13 in their own
Lean."

**M5. The captions of II.9 and II.10 at a glance.** figures/II/09-idea.svg:3: "Cut AB in half
at C, and unequally at D: the squares on AD, DB (left) are twice the squares on AC (yellow)
and CD (blue), for the red and black pieces make a second yellow and blue."
figures/II/10-idea.svg:3 ends "for the red and black make a second blue and yellow." The
"for" clause is a reason, and not Euclid's: his proof of II.9 draws no square, as II.9's own
commentary says ("Euclid proves II.9 without drawing a single square", mishnah/II/09.md:1),
and as Heath says ("the method of demonstration by showing in the figures the various
rectangles and squares to which the theorems relate is here abandoned", vol. 1, p. 394). The
figure's source names the squares "the squares of the reading in areas, which Heath's figure
does not draw" (figures/II/09-idea.svg:5), but nothing the reader sees does. II.8's caption
labels the same kind of departure: "as in Heath's second alternative proof, not Euclid's
nine cells" (figures/II/08-idea.svg:3). *What it should say:* each caption ends "...: a
reading in areas, not Euclid's proof." (II.9's then has 45 words, within STYLE section 7's
50.)

## The pilot editor

The pilot editor (RD-p), which wrote, prompted and edited none of the three pages, read
book/II/01.md, book/I/45.md and book/II/14.md consecutively, each whole and top to bottom
with its figures, at 3938eacc7. It read every part of the three pages save the bodies of the
14 `Fitted.fan` helper lemmas in I.45's folded listing (book/I/45.md:360-860), whose notes
and docstrings it read. It compared the figures with Heath's (leaves n365, n395 and n429)
and checked every quotation on the three pages against the page images, italics included.
III.24 joins the set when Book III's queued trains have landed.

It made 12 notes: none blocking or material, 12 editorial. Once, a search of docs/reports/
for a chapter title returned a line of the earlier read in this file, on II.14's further
reading, already mended; it read nothing else of it, and no note rests on it.

| Note | Pages | What | For STYLE or examples | Card draft |
|---|---|---|---|---|
| P1 | I.45, II.14, II.1 | The statement notes split the scope three ways, in three orders and three vocabularies; "a triangle more" cannot be followed; "lists of triangles" makes checked divisions read as unchecked | An example for docs/examples.md: a statement note whose scope is full through a companion names first the declaration that carries the whole enunciation, then what the main theorem keeps, then each other companion by what it takes | RD-C6 |
| P2 | I.45, II.14, Book I's introduction | "Independence", "content" and "outline" are never glossed; on II.14 the debt to Hilbert hangs on "constructs a square", as if the construction were his | STYLE section 4, "A figure given with its triangles": the debt to Hilbert said in one form (the proof that every division gives one sum; the construction is Euclid's), and "content" glossed where it first stands on a page | RD-C6 |
| P3 | II.14 | "The content theorem (`area_eq`)" names a different declaration from the one the term names on I.45 and in Content.lean (`Apart.area_eq_of_same_region`) | None | RD-C6 |
| P4 | II.14 | A dated change-log in a passage note ("until 26 October 2026 ...") | A second example under STYLE section 4, "Change-logs on the page"; a reported check for a dated phrase in a review note or the commentary, proposed as a card of its own | RD-C4 |
| P5 | I.45, II.14 | "The older companions" and "stay beside" tell the order in which the declarations were written | STYLE section 4: these companions are named by what they take, never "older", and nothing says that they "stay" | RD-C4 |
| P6 | II.14 | In the Representation row "It represents" reads as `Prop14.square`, though it means the main theorem; the cell runs to about 190 words | None: section 2's "a short table" covers it | RD-C6 |
| P7 | I.45, II.14 | Each page tells the outline route in its Argument row and again in a passage note; II.14's note retells I.45's | An example for docs/examples.md: "A table tells a route once; a passage note gives it a clause." | RD-C5 |
| P8 | I.45, Book I's introduction | The figure given by its outline is told in full in both, word for word, and the ray rule in two forms | STYLE section 3, "Told once": I.45 tells the figure given by its outline; Book I's introduction gives it a sentence and a link | RD-C5 |
| P9 | I.45 | The main theorem leaves bare two steps (KF and ML not one straight line, for I.30; F and L on one side of KM, for I.33) that `Prop45.append` and II.1 explain | A line for the reviewer's checklist: a step noted in a companion is noted in the main theorem too | RD-C10 |
| P10 | I.45 | `Prop45.outline` names its parallelogram KPLM, where Heath's is KFLM | None | RD-C7 |
| P11 | All three | Each "Reviewed" row links its commit through the repository's former path | None | RD-C9 |
| P12 | II.14 | "written out again so as not to cite II.14" records a writing choice, not mathematics | None | RD-C4 |

Its verdict: "pass, once the named findings are mended." It adds that notes P1, P2, P4 and
P5 "are exactly the cross-page differences of term and the process words these pilot pages
would pass on to every other page. They should be mended before the pilot pages serve as the
model." Each note's fix, or the change it makes to docs/STYLE.md or docs/examples.md, is to
be named here as #34 asks; none is made yet.

## The books read straight through

Each verdict is quoted from the reader's output.

### Book I

- **Flow reader (RD-f1):** "pass once the named findings are mended. The book flows and the
  commentary's voice is common. The two material findings (1 and 2) must be mended before
  the claim is presented as complete. The editorial findings in the notes are what keep the
  voice from being common across the whole page." Its material findings are M2, resolved,
  and M1, open.
- **I.1 to I.12 (RD-r1):** "pass once the named findings are mended. ... What stands between
  it and a clean pass is the false sentence on I.8 and the process voice in five pages' "How
  the Lean follows the text" notes." That is M1 and card draft RD-C4.
- **I.13 to I.24 (RD-r2):** "pass once the named findings are mended. All five are
  editorial, and none affects a formal claim or a quotation."
- **I.25 to I.36 (RD-r3):** "pass, once findings 2 and 3 are mended": the join refrain (RD-C5)
  and the change-log words (RD-C4).
- **I.37 to I.48 (RD-r4):** "pass. The ten findings are editorial mends that would tighten
  the records and two captions. None breaks the flow or the common voice."

The readers agree on where the second voice lives: not in the commentary, which every one of
them found in one plain and warm voice, but in the "How the Lean follows the text" notes,
with their change-log words ("now proved", "the retained axiom", "since the second axiom
retirement", "Until 26 October 2026") and two sentences repeated across eight records. Every
reader found the scope told truthfully, save M1 and M2, and the depth even, following the
difficulty of each proposition.

### Book II

- **Flow reader (RD-f2):** "pass once the named findings are mended. Read straight through,
  Book II flows and its voice is common. The two material findings ... are small, local
  mends that leave the flow and voice as they are." They are M4 and M5.
- **II.1 to II.7 (RD-r5):** "Pass once the named findings are mended: finding 1 (material)
  and findings 2 to 7 (editorial). The pages read straight through, the book flows, and the
  voice is common." Finding 1 is M3.
- **II.8 to II.14 (RD-r6):** "pass once the named findings are mended. All seven findings are
  editorial, and none affects a claim's truth or scope. Findings 1 to 3 are the voice lapses
  B3 asks about": II.14's change-log (RD-C4), II.10's notes copied from II.9 and II.8's
  commentary retelling its notes (RD-C5).

### Book III

To come: read once Book III's queued trains have landed, with III.24 for the pilot editor.

## The card drafts

The editorial findings, grouped as the drafts in captains/RD-cards.md group them for the
coordinator to file. Each gives the source to mend, the rendered line where a reader meets
it, and the readers who made it. The text quoted, the evidence and the wording proposed for
each are in the readers' outputs, which the card drafts carry.

**RD-C4: production history where readers look** (STYLE section 1, "Production stays out of
the mathematics"; section 4, "Change-logs on the page").

1. I.4: "since the second axiom retirement" and "(brief 0009, question 4)", review/I/04.toml:25
   (book/I/04.md:80). RD-r1 3; RD-f1 3.
2. "now proved", "the retained axiom", "remains an axiom" and "the forbidden reversed order"
   in the notes of I.2, I.5, I.11, I.12, I.27, I.31 and I.35, and I.22's "Until 26 October
   2026 the lemma called the rule, whose proof then used Circle 1." (review/I/02.toml:35,
   05.toml:23 and :34, 11.toml:13, 12.toml:13, 22.toml:26, 27.toml:13, 31.toml:16,
   35.toml:30). RD-r1 4; RD-r2 1; RD-r3 3; RD-f1 4.
3. II.14: "now proved in `Elements/Figure/RuleBase.lean` ... until 26 October 2026 that rule
   was proved from Postulate 3 and `circle_eq`", review/II/14.toml:38 (book/II/14.md:87).
   RD-r6 1; RD-p P4; RD-f2 3.
4. I.45 and II.14: "The older companions" and "stay beside", review/I/45.toml:14,
   mishnah/I/45.md:5, review/II/14.toml:60. RD-p P5.
5. II.14: "written out again so as not to cite II.14", review/II/14.toml:9 and the docstring
   at Elements/BookII/Prop14.lean:209. RD-p P12.
6. Book I's introduction: "Intersection 2, though proved, has no user in the published
   proofs", with the sentence on I.12 after it, which answers no part of the paragraph's
   question, mishnah/intro/I.md:13 (book/I/index.md:21). RD-f1 10.

**RD-C5: told twice: refrains and retellings** (STYLE section 1, "the note says how, the
mishnah says why"; section 3, "Told once"; section 4, the habits removed).

7. The join refrain, "The join is drawn in the text and is not needed by the formal proof",
   in the records of I.5, I.11, I.16, I.20, I.22, I.26 (twice), I.39 and I.40, and "Neither
   his proof nor ours uses it again", 15 times in 8 records, 5 of them I.26's. RD-r1 9; RD-r2
   2; RD-r3 2; RD-r4 4; RD-f1 5.
8. `produce_longer` and Postulate 3 retold in full on I.16, I.20 and I.22 (review/I/16.toml:13,
   20.toml:13, 22.toml:20), where STYLE section 3 gives it a clause. RD-r2 2.
9. I.44: "for which Heath gives no reference here" three times in one page's notes,
   review/I/44.toml:14, :20, :32. RD-r4 2.
10. I.44: the note, the commentary and the docstring each tell that Euclid moves I.42's
    parallelogram and we build an equal one, review/I/44.toml:14, mishnah/I/44.md:3,
    Elements/BookI/Prop44.lean:32-34. RD-r4 3; RD-f1 7.
11. I.5: the note, the commentary, the Lean comment and Book I's introduction each tell how
    I.5 still rests on Postulate 2, review/I/05.toml:17, mishnah/I/05.md:5,
    Elements/BookI/Prop05.lean:29, mishnah/intro/I.md:7. RD-r1 5 and 6; RD-f1 6.
12. I.13's commentary retells its notes on where BA and BE fall, mishnah/I/13.md:1. RD-r2 4.
13. I.27's commentary retells the figure note on how Heath's figure bends BG and DG,
    mishnah/I/27.md:5, where STYLE section 7 puts a departure from Heath's figure in the
    figure note, "not in the mishnah". RD-r3 4.
14. I.31's commentary restates the table's `Prop30.unique`, mishnah/I/31.md:3. RD-r3 6.
15. II.6's commentary restates its table's "D lies beyond B"; II.10 makes the same choice in
    its statement and its table says only "The whole enunciation.", mishnah/II/06.md:1,
    review/II/06.toml:3, review/II/10.toml:1-2. RD-r5 4; RD-f2 4.
16. II.8's commentary retells its listing note and its docstring on the points in order and
    `Prop8.cell`, mishnah/II/08.md:1 and :3. RD-r6 3.
17. II.10's four notes repeat II.9's prose, one verbatim and three with angle names changed,
    review/II/10.toml:46, :53, :65, :71 against review/II/09.toml:41, :48, :54, :60. RD-r6
    2; RD-f2 5.
18. II.12's note retells its commentary's argument for where D falls, review/II/12.toml:13
    against mishnah/II/12.md:1. RD-f2 6.
19. I.45 and II.14 each tell the outline route in the Argument row and again in a passage
    note; I.45's commentary tells its condition on A and C twice, review/I/45.toml:31,
    review/II/14.toml:15, mishnah/I/45.md:3 and :5. RD-p P7.
20. Book I's introduction and I.45 give the figure given by its outline word for word, with
    the ray rule told two ways, mishnah/intro/I.md:11 and mishnah/I/45.md:3. RD-p P8.

**RD-C6: terms, glosses and one name for one thing** (STYLE section 4).

21. "Division existence", "division independence", "theory of content", "independence" and
    "content proof", unglossed in Book I's introduction (mishnah/intro/I.md:11) and on I.45
    (mishnah/I/45.md:3); on II.14 "outline" unglossed and the Hilbert clause hung on the
    construction (mishnah/II/14.md:1). RD-r1 7; RD-r4 8; RD-r6 4; RD-f1 9; RD-p P2.
22. The statement notes of I.45 and II.14 tell the same split in different orders and words;
    "sums or a triangle more" and "Euclid shows two triangles", review/I/45.toml:4 and :10,
    review/II/14.toml:3. RD-r4 7; RD-p P1.
23. II.14: "the content theorem (`area_eq`)" names another declaration than on I.45,
    Elements/BookII/Prop14.lean:474-477. RD-p P3.
24. II.14's Representation row: "area-sum theorem" and "the other side forms", and an "It"
    whose antecedent reads wrong, review/II/14.toml:60. RD-r6 5; RD-p P6.
25. II.1: `Prop1.two` cuts at one point beside a main theorem that cuts at two, with nothing
    to say that "two" counts segments, review/II/01.toml:3. RD-r5 6.
26. Book II's introduction uses "unchecked" before saying what it means, mishnah/intro/II.md:5
    and :13. RD-f2 8.
27. Book II's introduction defines the gnomon by "the parallelograms about the diameter" and
    "the complements", I.43's terms, unglossed and unlinked, mishnah/intro/II.md:3. RD-r5 5.
28. The front matter's "III.25 kind" in double quotes, which mark Heath's words, and
    unexplained, scripts/render.py:2224-2229 (book/I/front.md:31). RD-r1 8.
29. The front matter's `Apart` "triangles that lie apart" and "the triangles it is cut into",
    and I.35's "cut into", where STYLE section 4 asks for "do not overlap, no point inside two
    of them" and "divided, not cut", scripts/render.py:2214 and :2230, mishnah/I/35.md:3.
    RD-f1 12.
30. The figure put on the side of a given point is worded six ways on I.1, I.11, I.22, I.23,
    I.44 and I.46, and only I.1 says it is more than Euclid asks, review/I/01.toml:4 and the
    other five at :4. RD-f1 13.
31. I.12: `Definition15` called "a rule we assume", which on these pages means a tacit rule;
    the table and the front matter call it an axiom, review/I/12.toml:24. RD-r1 11.
32. "Heath prints no bracket" and "Heath's bracket at this step" on I.16, I.20 and I.22, where
    STYLE section 4 says "Heath's references", review/I/20.toml:13, 16.toml:13, 22.toml:20,
    and the note at Elements/BookI/Prop20.lean:46. RD-r2 3.
33. I.35: "Proclus's", where every other page writes "Proclus'", review/I/35.toml:12. RD-r3 7.
34. I.7: "Charles Dodgson" in the commentary, "Charles L. Dodgson" in the reading line,
    mishnah/I/07.md:3. RD-r1 13.
35. Book I's introduction: "never use", where STYLE section 1 prefers "do not use", as the
    summary above it says, mishnah/intro/I.md:9. RD-f1 11.
36. I.31: "used beneath the joining of AD", review/I/31.toml:22. RD-r3 5.
37. I.39: "discharging the supposition ... The final step returns this conclusion",
    review/I/39.toml:38. RD-r4 4.
38. I.47: "Book II separately restates I.47 ... for later citations", naming neither
    `BookI.Prop47.sq` nor its users, review/I/47.toml:56. RD-r4 9. (Pull request #699 changed
    this record; the line still stands at 559237731.)
39. I.24: "by a tacit rule of magnitude", where the Lean uses a Book Zero theorem proved from
    the tacit rules, mishnah/I/24.md:3. RD-r2 5.

**RD-C7: figures** (STYLE section 7).

40. I.26's figure note says "Drawn for one case" and names two, and leaves out the exchanged
    suppositions the Lean also refutes; by review/SCHEMA.md:214 it is `some_cases`,
    review/I/26.toml:79-81. RD-r3 1.
41. I.37's modern figure draws two heights the paragraph never speaks of,
    figures/I/37-modern.svg:12-13 and :21-22. RD-r4 5.
42. I.43's caption at a glance names the yellow complements but not the blue and red
    parallelograms about the diameter, figures/I/43-idea.svg:3. RD-r4 6.
43. I.47's Euclid's figure is titled "the square on the hypotenuse", a modern word on
    Euclid's figure, figures/I/47.svg:2. RD-f1 15.
44. I.45: `Prop45.outline` and its docstring call the parallelogram KPLM, where Heath's is
    KFLM, Elements/BookI/Prop45.lean:957-959 and :965-967. Renaming the binder changes a
    statement's text and needs approval (WORKFLOW section 2); a clause in the docstring does
    not. RD-r4 10; RD-p P10.

**RD-C8: "Carried." where a helper does the step** (review/SCHEMA.md:158-163).

45. Passages of kind `carried` with no `helper` and no `unused`, each naming the lemma or
    proposition that does the step: I.36 (review/I/36.toml:26-28), I.42 (42.toml:38-41), I.44
    (44.toml:40-53, three) and I.45 (45.toml:16-19). The page shows a bare "Carried." where
    every neighbouring note says "Done by". RD-r3 8; RD-r4 1.

**RD-C9: the repository's former path in every "Reviewed" row.**

46. The constant REPO in scripts/render.py:80 is the repository's former path, under the owner's
    personal account, and every "Reviewed" row on every page links its commit through it
    (62 pages of Books I and II); everything else links the organisation's path. GitHub
    redirects the old path today (an HTTP 301, checked on 29 October), so no link is broken;
    but the account name stands on every page, and WORKFLOW section 10 lists the owner's name
    among the defects never on main. Whether the account name counts is the coordinator's
    ruling. RD-r1 2; RD-r5 7; RD-p P11; doubts of RD-r4, RD-f1 and RD-f2.

**RD-C10: precision, references and depth.**

47. I.4's commentary: "The proofs of those last two may even draw a straight line through
    that corner" hedges a fact the record states, mishnah/I/04.md:7. RD-f1 8.
48. II.1: "Heron did: he proved the propositions after it as its consequences" drops Heath's
    "It would appear that Heron was the first" (vol. 1, p. 373), mishnah/II/01.md:3. RD-r5 2.
    (The pilot editor read Heath's hedge as bearing on "first" only, and made no note; the
    commentary's owner decides.)
49. II.4: "cuts the square on AB into four pieces with the diameter BD", though BD bounds none
    of the pieces, mishnah/II/04.md:1. RD-r5 3.
50. II.13's modern way calls II.12 and II.13 together the law of cosines, which needs I.47 for
    a right angle too, mishnah/II/13.md:5. RD-r6 6.
51. I.11: De Morgan's words reach us through Heath (vol. 1, p. 269), and the sentence names
    neither the chain nor the page, mishnah/I/11.md:3. RD-r1 10.
52. II.12: "Gregory of St. Vincent", where Heath writes "St Vincent" (vol. 1, pp. 401 and 404,
    and his index), mishnah/II/12.md:3. RD-r6 7; RD-f2 9.
53. II.3: "the third of the identities Heath lists for Book II", with no volume or page; the
    list is on vol. 1, p. 372, mishnah/II/03.md:5. RD-f2 7.
54. I.36's reading line gives 1963 beside a link to Dover's volume of 2007, where STYLE section
    6 asks for the year of the edition linked, reading/I/36.md:2. RD-r3 9.
55. 18 of Book I's 48 reading lines hang on "the modern way", in a few repeated frames ("the
    modern way leans on", "the cosine of the modern way"), reading/I/18.md:1, 20.md:1,
    24.md:1, 25.md:1, 37.md:1, 40.md:2. RD-f1 14.
56. Book I's introduction gives "Forty-two remain axioms; forty-one are now proved" as
    literals, where STYLE section 4 asks for count markers, mishnah/intro/I.md:5. Both are
    right today. RD-r1 12.
57. I.45's main theorem leaves without a note the two steps its companion and II.1 explain,
    Elements/BookI/Prop45.lean:161 and :168. RD-p P9.

Card draft RD-C10 also carries one line of ACCEPTANCE.md, under M2.

## Doubts the readers left

None of these is a finding; each says what would settle it.

- **Italics.** The OCR keeps none, so the italics inside about forty quotations across Books I
  and II stand unchecked against Heath: on I.1, I.2, I.4, I.5, I.8 to I.12, I.14, I.15, I.17,
  I.19, I.21, I.24, II.10, II.12 and II.13. The pilot editor and the readers of I.25 to
  I.48 and II.1 to II.7 checked theirs on the page images. The leaves named in the readers'
  outputs settle the rest; this is the italics audit #34's comment asks after.
- **I.7's "in order to make it intelligible" (p. 259)**, where the OCR is garbled: leaf n279.
- **I.14's "I. 28" in Todhunter's remark**, which the OCR reads "i. 38": leaf n297.
- **I.35, whose words "the height of the parallels, which remains the same" are**: Heath's
  pp. 330-331 set them inside Proclus' report of Geminus citing Chrysippus. Proclus, in
  Friedlein p. 395, settles it.
- **I.33, "still following Proclus"**: whether the explanation after "as Proclus says (p. 385,
  5)" is Proclus' or Heath's. Proclus p. 385 settles it.
- **II.12 and II.13, "is proved" in the Statement row** of a betweenness the proof shows but
  the statement does not state: `#check @Elements.BookII.Prop12` shows the conclusion; the
  records' owner decides whether to add "within the proof".
- **I.37 at a glance**, which colours as equal two pieces I.37 does not state equal, though
  Common Notion 3 gives them at once: for the figures' owner, under STYLE section 7.
- **I.36's quotation from vol. 1, p. 22**, which stops mid-list with no mark: STYLE section 5
  does not say whether a cut at a quotation's end needs one.
- **Book II's introduction, "with no letter in Heath's figure" and "we prove it once"**
  (mishnah/intro/II.md:9), refrains STYLE section 3 retires "nowhere" in a proposition's
  commentary: whether an introduction is covered is for STYLE's owner.
- **I.46's figure**, where C need not lie beyond D and the figure note names no case: a
  freedom of the construction, or a case for `[figure]`.
- **Chapter titles** in some reading lines (Martin, Kedlaya, Steele, Miller, Courant and
  Robbins, Fowler, Richeson, Nelsen, Artmann, Stillwell), Mueller's edition on Open Library,
  Hilbert's numbering in Townsend's translation, Klein on betweenness, and Byrne's plate for
  I.45: their tables of contents or the books themselves settle them.

## Since the read

Main moved from 3938eacc7 to 559237731 while this draft was written. `git log --first-parent
--oneline 3938eacc7..559237731` gives two landings:

- 511fb5fe5 (pull request #698), a change to the renderer's notes; it changes nothing in the
  paths read.
- 559237731 (pull request #699), a batch of four trains. In the paths read it changes
  Elements/BookI/Prop47.lean, Elements/BookI/OutlineBound.lean and review/I/47.toml (I.47
  bounds its angle by I.13, not by Metric 5, #515), and regenerates 27 pages: book/I/02.md,
  06, 07, 09 to 13, 15, 16, 18, 20, 21, 26, 28, 30, 31, 40, 43, 47 and 48, and book/II/09.md
  to 14. It resolves M2.

`git diff --name-only 3938eacc7 559237731 -- book/I book/II mishnah Elements/BookI
Elements/BookII figures review/I review/II reading` lists those 30 files. No commentary,
figure or reading line of Books I and II changed. The dated addendum #34 asks for reads each
of these changes, and every later one to these paths, before the release.

## What #34 and B3 still need, for Books I and II

1. The four open material findings, M1 and M3 to M5, mended on main (card drafts RD-C1 to
   RD-C3), each naming here the commit that resolves it.
2. The readers' conditions on B3: every verdict passes once its named findings are mended,
   and the voice lapses they name are card drafts RD-C4 and RD-C5. These two are steps of the
   release gate; the others (RD-C6 to RD-C10) are editorial, and the readers did not make B3
   wait on them.
3. The pilot editor's notes, each with the commit that fixed it or the change it made to
   docs/STYLE.md or docs/examples.md, and III.24 read with the three pages once Book III's
   trains have landed.
4. The dated addendum that "Since the read" asks for.
5. The Book III section.
6. For B3, a `[read-through]` table in docs/reports/acceptance/book-I.toml and book-II.toml
   that cites this report, once each book's conditions are met, and the acceptance report
   regenerated ([ACCEPTANCE](../ACCEPTANCE.md)).
