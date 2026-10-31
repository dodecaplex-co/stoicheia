# Read-through 02: Books I to III

*29 October 2026. A draft. Books I and II were read at main
3938eacc7eb378465aa2c0fcae1cbfbfe1a0a756, on 29 October. The state of each of their findings
is given as at main 559237731, the head when their part was written; "Since the read" lists
what changed in the paths read between the two. Book III was read the same day, before its
queued trains had landed, at d4d65c48639fbafb50b2668603f82cd2be4d5334: main at 3938eacc7
with the 25 trains then queued merged, Book III's among them, and the generated output
rendered, the forecast of
the edition a reader will meet. That commit is a local forecast and not in main's history,
so Book III's findings are given as at d4d65c48, and the dated addendum (#34) reads every
page that changes between it and the release candidate.*

*This file held an earlier read of Books I and II, made at 2e8aecf8 on 21 and 22 October; it
stands in the history at 4baf973fe, [as it was then](https://github.com/dodecaplex-co/stoicheia/blob/4baf973fe/docs/reports/read-through-02.md).
[Read-through 03](read-through-03.md) is the read of 25 and 26 October. Neither one's
verdicts were used here: the readers below were told not to open either report, and none
did, save for one line noted under "The pilot editor". Other places still mean that earlier
read when they say "read-through 02": the decisions entry
[2026-10-25-book-i-front-definitions](../decisions/2026-10-25-book-i-front-definitions.md)
(its line 10, on I.17 and I.18), [STYLE](../STYLE.md) section 4 (its line 312),
[read-through 03](read-through-03.md) (its count of "read-through 02's 19 pilot notes", line
101), [figures against scans](figures-against-scans.md) (its opening paragraph, line 3, which
names 2e8aecf8; its two status notes of 21 October, lines 5 and 33; and two rows' dated
notes, lines 65 and 88), a comment in tests/test_jev_questions.py (line 1262), and the `run`
lines of 55 review records. The dated notes, the comment and the `run` lines record what was
true then and stand. The first four should link the earlier read at 4baf973fe; each belongs
to its own owner.*

## Who read what

Every reader is Claude Opus 5.5, working as an independent reader, and none wrote, prompted
or edited any of the pages it judged. Each read the tree pinned at its commit, 3938eacc7 for
Books I and II and d4d65c48 for Book III, checked the commit itself, and changed nothing in
it.

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
| Reader of III.1 to III.12 (RD-r7) | Book III's index with its introduction, its front matter, and III.1 to III.12 | d4d65c48 |
| Reader of III.13 to III.25 (RD-r8) | III.13 to III.25 | d4d65c48 |
| Reader of III.26 to III.37 (RD-r9) | III.26 to III.37 | d4d65c48 |
| Book III's flow reader (RD-f3) | Book III's index, introduction and front matter, with Books I and II's introductions for what carries over, then for III.1 to III.37 in order the top of each page, its notes, its commentary, its further reading and its figure at a glance | d4d65c48 |
| Pilot editor, second round (RD-p2) | book/II/01.md, book/I/45.md, book/II/14.md and book/III/24.md, one after another | d4d65c48 |
| Director of the read and writer of this report (RD) | Claude Opus 5.5, the instance that directs this read, an AI reading ship with no part in writing these pages. It wrote the readers' orders, checked each material finding against the sources named below, and wrote this report and the card drafts; it read no page as a reader and mended nothing | 3938eacc7, 559237731 and d4d65c48 |

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

Book III was read in the same way. Its three readers of ranges read every page of their
range whole, rendered every figure of III.1 to III.37 to an image and looked at it beside the
proof (Book III has no modern figures), and checked Heath's quotations against the OCR of his
second volume; the italics it does not keep are listed under "Doubts". The flow reader read
the book in order for what crosses pages, and rendered every figure at a glance. The pilot
editor read the three pilot pages again with III.24 after them.

## How the findings are graded

By [WORKFLOW](../WORKFLOW.md) section 9, "Release criteria and severity". Blocking is an
invalid or wrongly scoped formal claim presented as full, an unresolved dependency presented
as closed, an unapproved change to the foundations, or a materially false certificate.
Material is an unmarked alternative argument, a hidden omission of a clause, an unsupported
claim about a representation, a misleading figure, or a wrong quotation or attribution.
Editorial is what "does not change the meaning". A sentence that a reader sees and that is
false in what it tells of the mathematics, the source, the formal claim or a figure is
therefore graded material here when it is not blocking: it changes the meaning, so it cannot
be editorial.

Two grades need a word. I.26's figure note, which its reader graded editorial, is graded
material here (M6): "Drawn for one case" is false of a figure that draws two of Euclid's
suppositions, and the note does not say which cases the Lean covers that the figure leaves
undrawn. II.4's sentence (item 49) stays editorial. It says the square on AB is cut "into four
pieces with the diameter BD", though BD bounds none of the four pieces: the parallels through
G cut them. The phrase is loose rather than false, since "with the diameter BD" names the line
by which Euclid finds G, and what the sentence says of the pieces, two squares and two equal
complements, is true.

In Book III two findings that their readers graded editorial are graded material here. M11
(item 81) is a sentence of Elements/Foundations/DefinitionsIII.lean, which Book III's
introduction links, false of III.29's statement and out of date in its terms on III.27's. M12
(item 82) is III.13's caption at a glance, which gives one reason for both kinds of contact,
"the straight line through the two centres (black) runs to the point of contact, so there is
only one": for contact within that is the germ of Euclid's argument, but for contact without
it is the method Heath says Euclid "might also have" used (vol. 2, p. 34), not his, which
ends by III.2. That is an argument not Euclid's, at a glance and unmarked, as in M5.

Three findings stay editorial though each touches a claim. Book III's index says
"In III.5 and III.6 our tacit rules contain the propositions too, but our proofs never use
those rules" (item 80): "our proofs" may be read as every proof of the book, which would be
false, but the sentence opens on III.5 and III.6, and the next one ("In III.1 ... our proof
rests on it") uses "our proof" for its own proposition in the same way, so read as the
proofs of III.5 and III.6 it is true. III.28's commentary names `angleAtCentre.semicircle` for a true fact its proof
takes from another lemma (item 84): the reference misleads a reader who looks for it in the
listing, but nothing it says of the mathematics is false. III.37's "As De Morgan says of
I.48, the appeal to I.8 only hides one to I.7, on which I.8 is founded and which Euclid
proves indirectly" (item 85) adds a true clause of ours to De Morgan's remark; it is no
quotation, and the clause can be read as ours, so the attribution is loose rather than wrong.

## What they found

| Book | Blocking | Material | Editorial | All |
|---|---|---|---|---|
| I | 0 | 3 | 40 | 43 |
| II | 0 | 3 | 16 | 19 |
| Books I and II | 0 | 6 | 56 | 62 |
| III | 0 | 6 | 33 | 39 |
| The pilot editor's second round, on pages of Books I and II | 0 | 0 | 2 | 2 |
| All | 0 | 12 | 91 | 103 |

The counts are of distinct findings: a finding that several readers made counts once. Books
I and II's readers made 87 in all, 7 of them material as graded here (6 as the readers graded them); the pilot editor's 12 notes, all editorial, are
counted among these. A finding that spans both books (the line in the "Reviewed" row, the
terms of I.45 and II.14) is counted with Book I. The editorial findings are listed under
their card drafts, below.

Book III's readers made 78, the pilot editor's 18 among them, 5 of them material as they
graded them, which are 4 distinct findings; graded here, 6 are material (M7 to M12). Where
readers made one point on several pages (a refrain, a word STYLE retires), the pages are one
finding, as for Books I and II; and, as there, an item sometimes groups a few small points
of one kind (items 74 and 76 to 78), so the editorial count is of items as grouped. The pilot editor's
second round made 18 notes, all editorial: seven repeat findings of the first round, two are
new findings on pages of Books I and II (items 93 and 94), counted on a row of their own so
that the first round's counts stand, and the other nine are counted with Book III, two of
them (items 89 and 90) on all four pages.

### The material findings

| # | Page | Finding | Readers | State |
|---|---|---|---|---|
| M1 | I.8 | The commentary says two of the laws I.8 cites have proofs that "draw circles and straight lines too"; the certificate puts only Postulate 3 beneath them | RD-r1 1; RD-f1 2 | Resolved at 1f5769ca9 (pull request #752): their proofs draw a circle too (Postulate 3), and only Metric 3 is proved with no construction |
| M2 | I.13, I.47 | Metric 5 supplied a step of I.47's proof that is a consequence of I.13, and I.13's status line did not say so | RD-f1 1 | Resolved at 559237731 (pull request #699): I.47 now takes the step from I.13 itself |
| M3 | Book II's introduction | "Two enunciations are wider than the case Euclid's proof draws": II.5's and II.9's are wider too | RD-r5 1 | Resolved at 32eebe4ba (pull request #750): the introduction says that II.5 and II.9 let D fall on either side of C |
| M4 | Book II's introduction | "We prove each once": II.5 and II.14 prove the right angle beside a right angle again, in their own Lean | RD-f2 1 | Resolved at 32eebe4ba (pull request #750): the introduction says that we prove each in one place, in Rectangles.lean or, for one of them, in I.13's file |
| M5 | II.9, II.10 | The captions at a glance give a reason in areas that is not Euclid's, without the label II.8's caption gives | RD-f2 2 | Resolved at 1f5769ca9 (pull request #752): both captions end "a reading in areas, not Euclid's proof" |
| M6 | I.26 | The figure note says "Drawn for one case" of a figure that draws two, and leaves undisclosed the cases the Lean covers that the figure does not draw | RD-r3 1 (graded editorial by its reader) | Resolved at 1f5769ca9 (pull request #752): review/I/26.toml marks the figure `some_cases`, and its note says which cases the figure does not draw |

Book III's, at d4d65c48:

| # | Page | Finding | Readers | State |
|---|---|---|---|---|
| M7 | III.7, III.8 | Three of Euclid's conclusions are labelled "Proved separately" by a companion, though the main theorem proves them | RD-r7 1 | Open: card draft RD-C11 |
| M8 | III.22 | "As in III.21, we prove that AC and BD cut one another": III.21 proves no such thing; the step is III.20's | RD-r8 1; RD-f3 1 | Resolved at abb6b35f4 (pull request #746): mishnah/III/22.md:5 says "As in III.20, we prove that AC and BD cut one another", and the note at Elements/BookIII/Prop22.lean:30 says "as in III.20"; review/III/22.toml was read in full and stamped by an independent reader after it (6a656e53f) |
| M9 | III.22 | "The first half is Heron's proof, which Heath gives under III.20": Heath credits Heron with the extension of III.20, and gives no proof of III.22 as his | RD-f3 2 | Resolved at abb6b35f4 (pull request #746): mishnah/III/22.md:7 says "The first half is not Euclid's route: it is the one Heath points to under III.20", where III.22 "will follow immediately" (vol. 2, p. 47) |
| M10 | III.29 | Our own step, taking reflex angles from four right angles, is referenced to Heath's page 60, which says nothing of it | RD-r9 1 | Open: card draft RD-C13 |
| M11 | Book III's introduction, by its link to DefinitionsIII.lean | The linked note says III.29 needs equal circles and speaks of III.27 in equal measures: both statements take circumferences that coincide, and their records call the equal circles redundant | RD-r7 8 (graded editorial by its reader) | Mended on main since the read, by pull request #720 (89118233a8a9cc2c90569c10220e64170f248f2b, #474), which d4d65c48 did not hold; the addendum confirms it (card draft RD-C20, a check) |
| M12 | III.13 | The caption at a glance gives, for contact without, a reason that is not Euclid's, unmarked | RD-r8 20 (graded editorial by its reader) | Resolved at 1f5769ca9 (pull request #752): figures/III/13-idea.svg:3 reads "they meet at the point of contact and nowhere else, and the straight line through the centres (black) runs to it" |

**M1. I.8's commentary, on what the cited laws' proofs draw.** mishnah/I/08.md:5
(book/I/08.md:363) says: "The same is true of two of the three other laws I.8 cites, that a
straight line equal to one with distinct ends has distinct ends, and Savile's argument from
I.4 that on a ray only one point lies at a given distance from its start: their proofs draw
circles and straight lines too, and only Metric 3 is proved with no construction." facts.json
gives, for I.8's `cited_laws`, `"construction_rules": ["Postulate3"]` for both "neOfLen" and
"rayUnique"; only the law "prop7" has `Postulate1` and `Postulate2` beneath it. The page's own
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
the row has moved to the catalogue's former overlaps. Nothing is left to mend. The grade rests on
SCHEMA and STYLE section 2, which put an overlap of this kind in the status line, against
ACCEPTANCE's item B2, which named this row as one "read by no record, and not counted"; the
disclosure in I.47's passage note did not reach I.13's page, where a reader looks for it.
That sentence of [ACCEPTANCE](../ACCEPTANCE.md), item B2, still names "I.13's upper bound on an angle, used in
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

**M6. I.26's figure note.** review/I/26.toml:79-81 (book/I/26.md:21 and :23): "Drawn for one
case: AB supposed greater than DE, with G between B and A, and separately BC supposed greater
than EF, with H between B and C; both suppositions appear on one triangle, as in Heath's
figure." The note announces one case and names two: the figure draws both of Euclid's parts,
the side adjoining the equal angles (G) and the side subtending one of them (H). It does not
draw the exchanged suppositions, DE greater than AB and EF greater than BC, which the Lean
also refutes, applying Euclid's argument again with the triangles exchanged (the `case`
passages, review/I/26.toml:41-43 and :69-71). review/SCHEMA.md:214 gives such a figure
"some_cases": its caption then reads "Drawn for some of its cases: ...", and its note says
which cases the figure does not draw. The record is unchanged on main at 559237731 (only the
page's moved anchors changed). *What it should say:* the record takes `some_cases = true`,
keeping its `case`, and its note adds "It does not draw DE greater than AB or EF greater than
BC, which the Lean rules out by exchanging the triangles."

**M7. "Proved separately" on III.7 and III.8.** review/III/07.toml:64-66 gives the passage
"Therefore FA is greatest, FD is least, and FB is greater than FC" `kind = "carried"` with
`helper = "Prop7.general"`, which the page renders "**Proved separately, as
`Prop7.general`.**" (book/III/07.md:123); review/III/08.toml:59-61 and :99-101 do the same for
"therefore DA is greatest, while DE is greater than DF" and "therefore DG is least, while DK
is less than DL" (book/III/08.md:136 and :143). The main theorems prove these clauses
themselves: Elements/BookIII/Prop07.lean:160 assembles them, `refine ⟨hgreatest, hleast,
hnearer, ?_⟩`, and `Prop7.general` takes them from `BookIII.Prop7` (:329, `obtain ⟨hgreatest,
hleast, hnearer, hpartner⟩ := Prop7 ...`); `Prop8.general` takes them from `BookIII.Prop8` in the
same way (Prop08.lean:550). So the page tells a reader that Euclid's conclusions live in a
companion when they are in the theorem. *What it should say:* each passage `kind =
"grouped"`, rendered "Carried together", with a note such as "Euclid's summary of the
comparisons just proved; the Lean gathers them as the theorem's first three conclusions. Its
companion `Prop7.general` compares two of the rest on opposite sides of AD as well." (RD-r7
gives the wording for III.8's two.)

**M8. "As in III.21" on III.22.** mishnah/III/22.md:5 (book/III/22.md:226): "As in III.21, we
prove that AC and BD cut one another, putting DB within the angle ADC so that its two parts
add up"; the note at Elements/BookIII/Prop22.lean:29-31 (book/III/22.md:82) says "as in
III.21: AC and BD cut one another." III.21's proof proves no crossing:
Elements/BookIII/Prop21.lean never names `between_of_inside_chord`, and, after taking a point
across BD and the centre, its proof is two uses of III.20 and `Magnitude.eq_of_add_self_eq`
(Prop21.lean:55, :59, :61). The step is III.20's
(Prop20.lean:91 and :305; its commentary, mishnah/III/20.md:7). *What it should say:* "As in
III.20, ..." in both places. The Lean note is a `/- -/` comment, not a `--` line, but changing
it makes III.22's record stale.

**M9. Heron and III.22.** mishnah/III/22.md:7 (book/III/22.md:228): "The first half is
Heron's proof, which Heath gives under III.20, not Euclid's." Heath's note on III.20 (vol. 2,
p. 47) says that the early editors "gave the extension of this proposition to the case where
the segment is less than a semicircle"; that with it "iii. 22 will follow immediately from
the fact that the sum of the "angles at the centre" for two segments making up a whole circle
is equal to four right angles"; and that "all the editors referred to were forestalled in
this matter by Heron", whose extension serves "the next proposition (about the equality of
the angles in any segment)", III.21. Heron's is the extension of III.20; Heath gives no proof
of III.22, and credits none to Heron. III.20's own commentary reports Heron's extension
rightly. *What it should say:* "The first half is not Euclid's route: it is the one Heath
points to under III.20, where, with angles at the centre of any size, III.22 "will follow
immediately" (vol. 2, p. 47)."

**M10. III.29's reference to Heath's page 60.** review/III/29.toml:35 (book/III/29.md:64):
"... which must be subtracted from four right angles before I.4 applies (Heath, vol. 2,
p. 60)", and :41 (book/III/29.md:65): "... supply the ordinary angles by subtraction before
I.4, an additional step within the statement (Heath, vol. 2, p. 60)." Page 60 holds the end
of III.28, Heath's note on a straight line through the centre, and III.29's text, which takes
the angles BKC and ELF at the centres by III.27 and applies I.4 with no subtraction; it says
nothing of angles at the centre greater than two right angles. Heath's only note on III.29,
on p. 61, is on semicircles and the same circle. The reference reads as Heath's support for
a step that is ours. *What it should say:* at :35, "... before I.4 applies, a step not in
Euclid's text (Heath, vol. 2, p. 60)"; at :41, "... an additional step within the statement,
not in Euclid's text (Heath, vol. 2, p. 60)", so that the page names III.29's text and the
step is said to be ours. RD checked both of Book III's Heath findings, M9 and M10, against the
OCR of his second volume.

**M11. The note on equal circles that Book III's introduction links.** The introduction sends
the reader to [`DefinitionsIII.lean`](../../Elements/Foundations/DefinitionsIII.lean) for Book
III's words (mishnah/intro/III.md:5). Its note on the measure of circumferences says (lines
96-101 at d4d65c48): "III.27 holds for any two circles as stated: equal measures give equal
angles whatever the radii, and its proof keeps the equal circles only along Euclid's route.
III.26, III.28 and III.29 need them: ... and in III.28 and III.29 the measures are tied to
straight lines in the circles." That was true of the statements in measures. At d4d65c48
`BookIII.Prop27` and `BookIII.Prop29` take circumferences that coincide (`Arc.Congruent`), not equal measures
(facts.json); both records are tagged `redundant-hypothesis` and call the equal circles
redundant in `BookIII.Prop27` and `BookIII.Prop29` (review/III/27.toml:13, 29.toml:13), as the introduction
itself says ("In III.27 and III.29, which take circumferences that coincide, it adds
nothing", book/III/index.md:15). So the reader who follows the link meets, on III.29, the
contrary of the page; on III.27 the note is true of the statement, but speaks of it in
measures.
*What it should say* (RD-r7's wording): "III.27 and III.29 hold for any two circles as
stated, since circumferences that coincide lie in equal circles already, and their proofs keep
the equal circles along Euclid's route; of their companions, which take circumferences equal
in measure, III.29's needs them, for there the measures are tied to straight lines. III.26 and
III.28 need them: ...". Main already says so: pull request #720 (b17478e5f, 29 October),
which d4d65c48 did not hold, brought commit 89118233a8a9cc2c90569c10220e64170f248f2b (#474), and DefinitionsIII.lean:96-104
on main now reads "III.27 and III.29 take circumferences that coincide (`Arc.Congruent`,
below), and those lie in equal circles already, so their statements do not need the equal
circles". The addendum confirms the page a reader meets.

**M12. III.13 at a glance.** figures/III/13-idea.svg:3 (book/III/13.md:15 and :17): "Let a
circle touch the blue one from inside (red) or from outside (yellow): the straight line
through the two centres (black) runs to the point of contact, so there is only one." Euclid
gives the two kinds of touching two proofs, as III.13's commentary says
(mishnah/III/13.md:1). For contact within, the straight line joined from G to H "will fall on
B, D. [III. 11]" (heath/III/13.md:11), and the caption's reason is the germ of his. For
contact without, Euclid joins AC and ends by III.2 (heath/III/13.md:37); the figure draws no
AC, and draws instead the straight line on to the yellow centre, which its own source says
"Heath's proof does not take" (figures/III/13-idea.svg:10 and :13). Heath names that route
as one Euclid did not take: "Euclid might also have proved the second part by the same
method as that which he employs for the first part" (vol. 2, p. 34). So, for contact without,
the caption gives at a glance an argument that is not Euclid's, unmarked, as M5's captions
did. *What it should say* (RD-r8's wording): "Let a circle touch the blue one from inside
(red) or from outside (yellow): they meet at the point of contact and nowhere else, and the
straight line through the centres (black) runs to it."

## The pilot editor

The pilot editor (RD-p), which wrote, prompted and edited none of the three pages, read
book/II/01.md, book/I/45.md and book/II/14.md consecutively, each whole and top to bottom
with its figures, at 3938eacc7. It read every part of the three pages save the bodies of the
14 `Fitted.fan` helper lemmas in I.45's folded listing (book/I/45.md:395-711), whose notes
and docstrings it read. It compared the figures with Heath's (leaves n365, n395 and n429)
and checked every quotation on the three pages against the page images, italics included.
III.24 joined the set in a second round, below.

It made 12 notes: none blocking or material, 12 editorial. Once, a search of docs/reports/
for a chapter title returned a line of the earlier read in this file, on II.14's further
reading, already mended; it read nothing else of it, and no note rests on it.

| Note | Pages | What | For STYLE or examples | Card draft |
|---|---|---|---|---|
| P1 | I.45, II.14, II.1 | The statement notes split the scope three ways, in three orders and three vocabularies; "a triangle more" cannot be followed; "lists of triangles" makes checked divisions read as unchecked | An example for docs/examples.md: a statement note whose scope is full through a companion names first the declaration that carries the whole enunciation, then what the main theorem keeps, then each other companion by what it takes | RD-C6 |
| P2 | I.45, II.14, Book I's introduction | "Independence", "content" and "outline" are never glossed; on II.14 the debt to Hilbert hangs on "constructs a square", as if the construction were his | STYLE section 4, "A figure given with its triangles": the debt to Hilbert said in one form (the proof that every division gives one sum; the construction is Euclid's), and "content" glossed where it first stands on a page | RD-C6 |
| P3 | II.14 | "The content theorem" is glossed area_eq, a different declaration from the one the term names on I.45 and in Content.lean, Apart.area_eq_of_same_region | None | RD-C6 |
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

**The second round, with III.24.** The pilot editor (RD-p2) read book/II/01.md,
book/I/45.md, book/II/14.md and book/III/24.md consecutively at d4d65c48, each whole with its
figures, and checked their quotations against the OCR. It made 18 notes, all editorial. Seven
repeat findings of the first round on the three pages, still standing at d4d65c48: P2 twice
(item 21), P4 (item 3), P5 (item 4), P6 (item 24), P8 (item 20) and the bare "Carried." on
I.45 (item 45). The other eleven are new:

| Note | Pages | What | For STYLE or examples | Item |
|---|---|---|---|---|
| Q1 | All four | The status line names a companion on III.24 alone, whose main theorem carries the whole enunciation, and says nothing on the three pages where companions carry the rest; "a companion" undercounts III.24's two | STYLE section 2: "through its companions" where the main theorem is Euclid's worked configuration; a badge that names companions counts them | 89 |
| Q2 | All four | The statement notes are in four moulds; "With its companions" means needed on II.1 and not on III.24 | review/SCHEMA.md, `note`: a full statement's note opens with the declaration that carries the whole enunciation | 90 |
| Q3 | III.24 | Nothing on the page says how "similar", the enunciation's first word, is read | docs/examples.md: the Representation row reads every word of the enunciation the Lean represents | 91 |
| Q4 | III.24 | The commentary retells the table and the notes, leads every paragraph in bold, and leaves thin the hardest step, the centre across AB in Heath's own figure | An example under STYLE section 4, "Retelling the Lean notes" | 71 |
| Q5 | III.24, Book III's introduction | The restriction on superposition is said in four forms | STYLE section 3, "Told once": one form, "our foundations allow superposition only in I.4 and I.8" | 92 |
| Q6 | III.24 | "shown on the page as the alternative" and "labelled so on the page" are asides for a checker | STYLE section 1, Avoid and Prefer | 64 |
| Q7 | III.24 against II.14 | "Heath prints no reference" in Book III's records, where Books I and II and STYLE say "gives" | A reported check of "prints no reference" | 74 |
| Q8 | III.24 | "map" and "image" are not glossed | STYLE section 4: glossed at first use outside the modern way | 72 |
| Q9 | III.24 | "[Post. 3]" and "Diagram-segments 3 and 4" in a note | A checked rule could refuse "[Post." in review notes | 74 |
| Q10 | I.45, II.14 | The parallel companions are titled "triangles that lie apart" on I.45 and "triangles that do not overlap" on II.14 | None: STYLE section 4 already says so | 93 |
| Q11 | II.1 | "the rectangles on its segments", where a rectangle is "contained by" | None: STYLE section 4 already says so | 94 |

Its verdict: "pass once the named findings are mended. There is no false claim and no scope
misstatement. The defects are inconsistencies of form and term that every later page would
copy from the pilot." It accepted III.24's route, `euclid` in its record, on the authority of #547's
decision, and left the doubts below on III.24's "and here he needs it", on italics and on
capitalised link anchors.

## The books read straight through

Each verdict is quoted from the reader's output. The readers' outputs, and the card drafts
made from them, are kept outside the repository, with the coordinator, who files the
cards.

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
reader found the scope told truthfully, save M1, M2 and M6, and the depth even, following
the difficulty of each proposition.

Book I was read straight through by its four readers of ranges, who between them read every
page whole and in order, with its commentary and every figure, each range ending where the
next begins; the flow reader then read the whole book in order for what crosses pages: the
top of each page, its notes, commentary and further reading, and its figure at a glance.
Euclid's proof, his figure and the Lean listing it left to the range readers.

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

On scope, the three readers found every status line true to its record, scope `full` and
route `euclid` on all fourteen pages, with each qualification visible in the table where the
reader meets it (II.1's and II.14's companions, the cases of II.5, II.6 and II.9, II.13's
dropped hypothesis), save M3 to M5: two false sentences of the introduction and two
captions. On depth, they found it even: the longer commentaries are those that carry Heath's
history (II.5, II.10, II.14), II.2 is short with reason, and each hard step (G where CF
crosses BD, the square CF counted twice in II.7, the two roots of II.5 and II.6) is explained
where it arises.

### Book III

Read at d4d65c48, the forecast head; the addendum reads what changes after it.

- **Flow reader (RD-f3):** "pass once the named findings are mended. The book flows and the
  voice is common. The two material findings, both on III.22, and the refrains in the notes
  are each small mends to a source file." They are M8 and M9.
- **III.1 to III.12 (RD-r7):** "pass once the named findings are mended. The pages read
  straight through and the commentary has a common voice. What breaks it is the record and
  Lean-note layer (findings 2–6), plus one false passage label (finding 1)." That is M7, with
  items 58 to 60, 66, 67, 75 and 76.
- **III.13 to III.25 (RD-r8):** "pass once named findings are mended. The book reads straight
  through and the commentary's voice is common. The false cross-reference (finding 1,
  material) must be fixed. The record and Lean-note register (findings 4 to 19) keeps the
  "How the Lean follows the text" sections from sharing that voice." That is M8, with items
  61, 63, 64, 66, 68, 69, 71 to 73, 76 and 78.
- **III.26 to III.37 (RD-r9):** "pass once named findings are mended. The book flows and the
  scope is truthful. The voice is common except where the mishnah repeats the table, and
  finding 1, which is material, must be mended before the claim is presented as complete."
  That is M10, and item 71.

The four readers agree with Books I and II's: the commentary is in one plain, warm voice from
III.1 to III.37, with leads proper to each proposition, and the second voice lives in the
"How the Lean follows the text" notes, the table rows and some Lean docstrings. There they
found dated history ("This was an assumption until 26 October 2026", "since 19 October
2026"), the equal-radii sentence 26 times on 12 pages, the centre by III.1's construction
told word for word on four pages, the record's own words ("so the route remains modified"),
and words STYLE section 4 keeps out of the prose ("chord", "arc", "bracket"). Eight
commentaries, III.24's and III.26's among them, retell the notes above them (item 71).

On scope, the readers between them found all 37 status lines true to their records: scope
`full` throughout, routes `euclid` save the four `modified` ones (III.21, III.26, III.27 and III.29),
every certificate table and "Lean cites" row matching facts.json, the three badges for the
measure of circumferences used consistently, and each figure note naming its case and each
impossible supposition. They found no page whose scope reads fuller than its status line,
save the doubts on the status lines of III.16, III.18, III.20 and III.31, below. The false
sentences are M7 to M11, and M12 a caption.

On depth, they found it following the difficulty: III.7, III.8, III.10, III.11, III.13,
III.16, III.20, III.24, III.25 and III.27 are rich because their gaps are real (De Morgan's,
Camerer's, contact, the cases of the angle at the centre); III.3, III.4, III.9, III.19 and
III.22 are short and complete. The uneven spots are bookkeeping: III.14 and III.15 trace a
rule's path no other page traces (item 69), and III.24 leaves its hardest step, the centre
across AB, to its notes (Q4).

Book III was read straight through by its three readers of ranges, each range ending where
the next begins, and then by the flow reader, as Books I and II were.

## The card drafts

The editorial findings, and M6 among the figures, grouped as the card drafts group them
for the coordinator to file. Each gives the source to mend, the rendered line where a reader meets
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
5. II.14: "written out again so as not to cite II.14", review/II/14.toml:9, and "written out
   again so that it need not cite II.14", the docstring at Elements/BookII/Prop14.lean:209.
   RD-p P12.
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

21. "division existence", "division independence", "theory of content", "independence" and
    "content proof", unglossed in Book I's introduction (mishnah/intro/I.md:11) and on I.45
    (mishnah/I/45.md:3); on II.14 "outline" unglossed and the Hilbert clause hung on the
    construction (mishnah/II/14.md:1). RD-r1 7; RD-r4 8; RD-r6 4; RD-f1 9; RD-p P2.
22. The statement notes of I.45 and II.14 tell the same split in different orders and words;
    "sums or a triangle more" and "Euclid shows two triangles", review/I/45.toml:4 and :10,
    review/II/14.toml:3. RD-r4 7; RD-p P1.
23. II.14 glosses "the content theorem" as area_eq, another declaration than on I.45,
    Elements/BookII/Prop14.lean:474-477. RD-p P3.
24. II.14's Representation row: "area-sum theorem" and "the other side forms", and an "It"
    whose antecedent reads wrong, review/II/14.toml:60. RD-r6 5; RD-p P6. In the second round
    the pilot editor adds that the row says the main theorem "represents Euclid's pictured
    division", though II.14's figure draws no diagonal ("A four-sided with no diagonal drawn,
    as in Heath's figure", review/II/14.toml:63): the division is I.45's. RD-p2 3. It stays
    editorial: the division Euclid pictures is I.45's, which the sentence names.
25. II.1: `Prop1.two` cuts at one point beside a main theorem that cuts at two, with nothing
    to say that "two" counts segments, review/II/01.toml:3. RD-r5 6.
26. Book II's introduction uses "unchecked" before saying what it means, mishnah/intro/II.md:5
    and :13. RD-f2 8.
27. Book II's introduction defines the gnomon by "the parallelograms about the diameter" and
    "the two complements", I.43's terms, unglossed and unlinked, mishnah/intro/II.md:3. RD-r5 5.
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

40. Material, M6, above. I.26's figure note says "Drawn for one case" and names two, and
    leaves out the exchanged suppositions the Lean also refutes; by review/SCHEMA.md:214 it is
    "some_cases", review/I/26.toml:79-81. RD-r3 1.
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

45. Passages of kind "carried" with no "helper" and no "unused", each naming the lemma or
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
55. The reading lines of 18 of Book I's 48 propositions hang on "the modern way", in a few repeated frames ("the
    modern way leans on", "the cosine of the modern way"), reading/I/18.md:1, 20.md:1,
    24.md:1, 25.md:1, 37.md:1, 40.md:2. RD-f1 14.
56. Book I's introduction gives "Forty-two remain axioms; forty-one are now proved" as
    literals, where STYLE section 4 asks for count markers, mishnah/intro/I.md:5. Both are
    right today. RD-r1 12.
57. I.45's main theorem leaves without a note the two steps its companion and II.1 explain,
    Elements/BookI/Prop45.lean:161 and :168. RD-p P9.

Card draft RD-C10 also carries one line of ACCEPTANCE.md, under M2.

Book III's card drafts, at d4d65c48. RD-C11 to RD-C13, RD-C20 and RD-C21 carry the material
findings M7 to M12 (RD-C11: M7; RD-C12: M8 and M9; RD-C13: M10; RD-C20: M11, item 81 of
RD-C17, a check, since main has mended it; RD-C21: M12, item 82 of RD-C17); the editorial
findings follow.

**RD-C14: production history where readers look, Book III** (STYLE section 1; section 4,
"Change-logs on the page").

58. III.2's Lean docstrings: "This was an assumption until 26 October 2026", "until 24 October
    2026", "an assumption until 19 October 2026, and was then proved from Circle 3",
    Elements/BookIII/Prop02.lean:193, :208, :216-217, :236-238, :263-265 (book/III/02.md:269
    to :341, in the folded listing). RD-r7 2.
59. III.5's and III.6's Overlap rows: "have been theorems since 19 October 2026", "Since 26
    October 2026 ...", and "Circle 4", named nowhere else on either page,
    review/III/05.toml:13, 06.toml:17. RD-r7 3; RD-f3 6.
60. III.11: "our foundations can now express neighbourhoods", mishnah/III/11.md:5. RD-r7 2;
    RD-f3 6.
61. "now proved" on III.14 and III.25, review/III/14.toml:15, 25.toml:43. RD-r8 8; RD-f3 6.
62. III.20: "as III.20 had before" and "the one III.20 had before", review/III/20.toml:3,
    mishnah/III/20.md:3. RD-f3 6.
63. III.25's docstrings: "Brief 0006 planned it for Book Zero", "III.25's statement before
    brief 0006 restated it", Elements/BookIII/Prop25.lean:313, :359-360, :376. RD-r8 4.
64. III.24: "and labelled so on the page, with Euclid's text in full under the main proof",
    Elements/BookIII/Prop24.lean:390, and "keeps the proof by the radii ..., shown on the
    page as the alternative", review/III/24.toml:9. RD-r8 5; RD-p2 Q6.
65. III.29: "so the route is modified" and "so the route remains modified", the record's
    word and its history, review/III/29.toml:9, mishnah/III/29.md:7. RD-r9 7; RD-f3 7.

**RD-C15: told twice, Book III** (STYLE section 1, "the note says how, the mishnah says
why"; section 3, "Told once"; section 4, "Refrains").

66. The equal-radii sentence ("The Lean obtains it from `Definition15`, Euclid's definition of
    a circle, which we assume as a rule", "the assumed rule for equal radii") 26 times on 12
    pages, III.7 four times and III.8 five; and "the rule we assume as System E,
    Diagram-segment 1" or "Intersections ..." bullet after bullet on III.14, III.15, III.17
    and III.20. III.36's record shows the short form ("`Definition15` again gives the equal
    radii FC and FB"). review/III/02, 03, 07, 08, 11, 14, 15, 16, 17, 20, 31, 35, 37 (.toml).
    RD-r7 5; RD-r8 7; RD-f3 3.
67. The centre by III.1's construction (`Prop1.of_circle`) told in the same words on III.2,
    III.4, III.8 and III.17, where III.32, III.34, III.36 and III.37 point to the
    introduction; III.35 names `Tacit.exists_centre` without that pointer,
    review/III/02.toml:19, 04.toml:14, 08.toml:21, 17.toml:16, 35.toml:26. RD-r7 5; RD-f3 4;
    RD-r9 12.
68. III.25: Heath's lack of a reference said ten times in nine notes, twice in the last, and
    the clause on `Prop25.complete` three times, review/III/25.toml:19 to :79. RD-r8 6.
69. III.14 and III.15 trace `Tacit.exists_centre`'s path through their proofs, which the
    certificate shows and no other page traces, review/III/14.toml:15, 15.toml:10. RD-r8 8;
    RD-f3 8.
70. III.26 and III.28 give the same sentence on `Circumference.whole`, which Book III's
    introduction tells, review/III/26.toml:35, 28.toml:34. RD-r9 4.
71. Commentaries that retell their table and notes: III.16 (mishnah/III/16.md:9), III.18 (:1
    and :5), III.21 (:7), III.24 (:1, :3 and :5, each with a bold lead, and the centre across
    AB left thin), III.26 (:1 and :5), III.27 (:3 and :7), III.28 (the last sentence of :3)
    and III.37 (:5 and :7). RD-r8 14 to 17; RD-p2 Q4; RD-r9 5, 6 and 8; RD-f3 16.

**RD-C16: terms, glosses and one name for one thing, Book III** (STYLE section 4).

72. Modern words outside the modern way: "chord", "arc", "disks" and "reflex" in the records,
    Lean notes and one commentary of III.13, III.24, III.25, III.26, III.28 and III.29, and
    III.28's figure case "non-diameter chords" (review/III/25.toml:3, 26.toml:8, :35 and :41,
    28.toml:34, :40 and :43, 29.toml:9 and :35, mishnah/III/29.md:7,
    Elements/BookIII/Prop13.lean:148, :315, :379, Prop24.lean:56, Prop26.lean:250-251 and
    :305); "map" and "image" unglossed on III.24 (review/III/24.toml:9 and :13). RD-r9 3;
    RD-f3 5; RD-r8 18 and 19; RD-p2 Q8.
73. "The names in brackets are System E's", on every page, for names in parentheses
    (scripts/render.py:727), and III.16's "Heath gives no bracket for drawing this
    perpendicular" (Elements/BookIII/Prop16.lean:116). RD-r8 11 and 12.
74. "Heath prints no reference", in 28 of Book III's records, where Books I and II and STYLE
    say "gives"; and "[Post. 3]" and "System E's Diagram-segments 3 and 4" in III.24's note
    (review/III/24.toml:19, :31, :37). RD-p2 Q7 and Q9.
75. Book III's introduction: "with background existence supplied inside its proof", and "None
    is restricted", which may be read as the three propositions just named,
    mishnah/intro/III.md:17. RD-r7 6; RD-f3 10.
76. Rules named loosely: "our radius rule", unglossed at its first use, and "Circle 1 ... for a
    centre, proved without that rule", on III.2 (review/III/02.toml:31); "The rule supplies
    both centres", before any rule is named, on III.10 (10.toml:12); "a rule we assume from
    Definitions I.15 and I.16" and "without citing III.1" on III.13, III.20, III.21 and
    III.25 (13.toml:20, 20.toml:19, 21.toml:20, 25.toml:9); Postulate 5 as "a rule we assume"
    on III.25 (25.toml:37); and the retired "a rule we assume ..., not a proof" on III.27
    (27.toml:42). RD-r7 4; RD-f3 11 and 12; RD-r8 9 and 10; RD-r9 14.
77. Sentences a reader cannot follow: III.18's "The order is Euclid's, III.18 and then
    III.16" (mishnah/III/18.md:7, Elements/BookIII/Prop18.lean:111); III.21's "the little
    argument met under I.37", a pointer in words alone (mishnah/III/21.md:1); III.1's modern
    way, whose a and b are never introduced (mishnah/III/01.md:9); and the rule bookkeeping of
    III.27's and III.31's notes (review/III/27.toml:25, 31.toml:54). RD-r8 2 and 3; RD-f3 13
    and 14; RD-r9 11.
78. Passage leads: III.28's "Euclid's. Euclid's argument: ..." (review/III/28.toml:8), and
    III.16's "Proved separately, as `Prop16.semicircle`" over a note on two other companions
    (16.toml:80-84). RD-r9 2; RD-r8 13.

**RD-C17: Book III's introduction and index, a foundations note, and figures** (STYLE
sections 3 and 7).

79. Book III's introduction tells the changed steps of III.21 and III.26 only, where its index
    lists four routes changed, III.27 and III.29 among them, mishnah/intro/III.md:17. RD-f3 9.
80. The index's "our proofs never use those rules", of III.5 and III.6, may be read as every
    proof of the book, though III.10, III.23, III.24 and III.26 to III.30 rest on
    `circle_eq`, with III.13's and III.25's companions (facts.json at d4d65c48),
    scripts/render.py:2062 and :2080 (book/III/index.md:5). RD-r7 7.
81. Material, M11, above: Elements/Foundations/DefinitionsIII.lean:96-101, linked from the
    introduction, describes III.27's and III.29's statements as they were before they took
    circumferences that coincide; mended on main by pull request #720 (card draft RD-C20, a
    check). RD-r7 8.
82. Material, M12, above: III.13 at a glance, "runs to the point of contact, so there is only
    one", for contact without a reason not Euclid's, figures/III/13-idea.svg:3 (card draft
    RD-C21). RD-r8 20.
83. III.31 at a glance: "cut the triangle ABC into two with equal sides", two of what,
    figures/III/31-idea.svg:3. RD-r9 13.

**RD-C18: references and further reading, Book III.**

84. III.28's commentary names `angleAtCentre.semicircle`, which its proof never calls; it
    takes the measures from `Circumference.semicircle`, mishnah/III/28.md:3,
    Elements/BookIII/Prop28.lean:115. RD-r9 10.
85. III.37: "As De Morgan says of I.48, ... on which I.8 is founded and which Euclid proves
    indirectly": Heath's De Morgan ends at "founded" (vol. 1, p. 369), mishnah/III/37.md:3.
    RD-r9 15.
86. III.26's further reading: Smith's "two of our present theorems" made "two of our
    theorems", so "our" means two things in one sentence, reading/III/26.md:1. RD-r9 9.
87. III.22's further reading repeats Pedoe's book without "(also on III.21)", the only such
    repeat in Book III, reading/III/22.md:2. RD-f3 15.
88. III.4's further reading on Velleman would fit any reductio, reading/III/04.md:1, where
    STYLE section 6 leaves out "a line that would fit any page of the book". RD-r7 9.

**RD-C19: the pilot editor's second round.**

89. Q1: the status line and companions, scripts/render.py:1105, on II.1, I.45, II.14 and
    III.24.
90. Q2: the statement notes in four moulds, review/II/01.toml:3, review/I/45.toml:4,
    review/II/14.toml:3, review/III/24.toml:3 (with item 22).
91. Q3: how III.24 reads "similar", review/III/24.toml:13.
92. Q5: the restriction on superposition in four forms, mishnah/III/24.md:3,
    review/III/24.toml:19, mishnah/intro/III.md:9.
93. Q10: "lie apart" on I.45 and "do not overlap" on II.14, Elements/BookII/Prop14.lean:341,
    review/I/45.toml:14.
94. Q11: "the rectangles on its segments" on II.1, review/II/01.toml:13.

## Doubts the readers left

None of these is a finding; each says what would settle it.

- **Italics.** The OCR keeps none, so the italics inside about forty quotations across Books I
  and II stand unchecked against Heath: on I.1, I.2, I.4, I.5, I.8 to I.12, I.14, I.15, I.17,
  I.19, I.21, I.24, II.10, II.12 and II.13. The pilot editor and the readers of I.25 to
  I.48 and II.1 to II.7 checked theirs on the page images. The leaves named in the readers'
  outputs settle the rest; this is the italics audit #34's comment asks after.
- **I.7's "in order to make it intelligible" (vol. 1, p. 259)**, where the OCR is garbled: leaf n279.
- **I.14's "I. 28" in Todhunter's remark**, which the OCR reads "i. 38": leaf n297.
- **I.35, whose words "the height of the parallels, which remains the same" are**: Heath's
  vol. 1, pp. 330–331, sets them inside Proclus' report of Geminus citing Chrysippus. Proclus, in
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

Book III's:

- **Italics.** The OCR of Heath's second volume keeps none, so the italics inside quotations
  on III.3, III.7, III.9 to III.12, III.16 to III.18, III.20, III.24, III.29, III.33, III.35
  and the index stand unchecked: the leaves named in the readers' outputs (n13 to n85) settle
  them.
- **Words that reach us through Heath.** Todhunter's "do not cut at all" (III.11) and De
  Morgan's remarks on III.7 and III.9 match Heath's report of them (vol. 2, pp. 3, 15 and
  22). Heath gives III.5's "same centre" sentence in his own words (p. 12). Todhunter's
  "should have been taken together" (III.5), his note on III.3 and De Morgan's "depending
  upon the eye" (III.8) are not in the OCR. Todhunter 1872, pp. 271-272, and De Morgan 1849,
  p. 10, settle whether the words are theirs.
- **Pages not tied to a running head:** the equal-circles quotation (vol. 2, p. 2) and
  Simson's note (1756, p. 363): the leaf and Simson's edition settle them.
- **Heath's printed figures,** where a page says what they show: III.4's "In Heath's figure
  EA lies within the angle FEB", and III.7's dotted EK (leaves n23 and n26).
- **III.10's "footnote"**, which the OCR sets among Heath's line notes: leaf n35.
- **III.25's quotation of Heath**, which cuts the clause "If the problem is solved after the
  manner of IV. 5," before "it is still desirable to state": leaf n68 settles whether the cut
  changes the sense.
- **III.24's "and here he needs it"**, which may read as Heath's words, where Heath says only
  "Euclid avoided this method wherever he could".
- **Status lines.** III.16, III.18 and III.31 say "as Euclid states it" for angle clauses read
  near the vertex (`mixed-angles-local`, which has no badge), and III.20 says "Euclid's
  argument" while its statement uses our angle at the centre (`angle-at-centre`, no badge):
  whether STYLE section 2 wants these readings beside the check is for the records' owner.
  III.20's "Euclid's argument" beside III.21's "one step changed", for the same reading,
  follows the records' logic (a case beyond the statement against a case within it), but a
  reader may see the two as at odds: FORMALIZATION section 5 settles it.
- **III.29's equal circles,** which M11 calls redundant in `BookIII.Prop29` on the authority of its
  record's tag and note: a scratch file stating `BookIII.Prop29` without `EqualCircles` and proving it
  from `BookIII.Prop29` and `Arc.congruent_iff`, checked with `lake env lean`, settles it in Lean.
- **"[III. 2]" and "[Post. 3]" in our notes,** III.25's (review/III/25.toml:9) as well as
  III.24's (item 74): STYLE section 4 keeps bracketed references for Euclid's text, and
  section 5 allows them in Lean remarks; whether a record's note counts is for STYLE's owner.
- **III.33 and III.34 at a glance,** which say the segment's angles "all equal" the given
  angle, where the Lean gives it at one point (III.21 gives the rest): for the figures'
  owner, under STYLE section 7.
- **III.19 at a glance,** which gives the letter F to the true centre, where Heath's F is a
  supposed one: the caption says so and the figure note does not.
- **The `segment-with-circle` tag's meaning,** which no page shows: where render.py prints a
  tag's meaning settles it.
- **Capitalised link anchors** such as `24.md#equalCircles`: clicking them on GitHub settles
  whether they resolve.
- **The further reading's works.** Of Smith's, only the III.26, III.31 and III.33 lines were
  checked (against Project Gutenberg), not his pp. 202, 203 and 209 or his III.14 and III.36
  lines; and none of the others' (Stillwell, Johnson, Loney, Yaglom,
  Mueller, Velleman, Hadamard, Ogilvy, Coolidge, Thomas, Maor, Aaboe, Courant and Robbins,
  Klein, Dunham, Casey, Chen, Andreescu and Andrica, and others): their pages and chapters
  settle them.
- **The records' stamps at d4d65c48,** which no reader checked: `python3
  scripts/check_fidelity.py` after `lake env lean Certificate/Facts.lean` settles them.

## Since the read

Main moved from 3938eacc7 to 559237731 while this draft was written. `git log --first-parent
--oneline 3938eacc7..559237731` gives two landings:

- 511fb5fe5 (pull request #698): the render-notes test and the stale-page plant now render
  once before they plant (#677), with its decisions entry; it changes nothing in the paths
  read.
- 559237731 (pull request #699), a batch of four trains. In the paths read it changes
  Elements/BookI/Prop47.lean, Elements/BookI/OutlineBound.lean and review/I/47.toml (I.47
  bounds its angle by I.13, not by Metric 5, #515), and regenerates 27 pages: book/I/02.md,
  06, 07, 09 to 13, 15, 16, 18, 20, 21, 26, 28, 30, 31, 40, 43, 47 and 48, and book/II/09.md
  to 14. Most of their changed lines are link anchors moved by a change to
  Elements/Figure/RuleBase.lean (#561); the rest are #515's: I.47's listing, its
  `Prop47.within` note and its Reviewed commit change, and it counts 37 tacit rules, not 38;
  I.48 and II.9 to II.14 count 38, not 39, with Metric 5 gone from their lists. facts.json and
  docs/reports/overlaps.md, which M1 and M2 cite, changed with them. It resolves M2.

`git diff --name-only 3938eacc7 559237731 -- book/I book/II mishnah Elements/BookI
Elements/BookII figures review/I review/II reading` lists those 30 files. No commentary,
figure or reading line of Books I and II changed. The dated addendum #34 asks for reads each
of these changes, and every later one to these paths, before the release.

Book III was read at d4d65c48, a forecast of the queue, not a commit of main. Its addendum
reads every page of Book III whose sources change between d4d65c48 and the release
candidate: the pages of the trains that land in another form than the forecast held, and
those of trains not in it, among them the circle-centre chain (#629, #630, #672) and the
train of #474 that pull request #720 landed, which mends M11.
`git diff --name-only d4d65c48 <candidate> -- book/III mishnah/III mishnah/intro/III.md
Elements/BookIII Elements/Foundations/DefinitionsIII.lean figures/III review/III reading/III`
lists them; DefinitionsIII.lean is there because the introduction links it (M11).

## What #34 and B3 still need, for Books I and II

1. The five material findings open at the read, M1 and M3 to M6, mended on main (card
   drafts RD-C1 to RD-C3, and item 40 of RD-C7), each naming here the commit that resolves
   it. Met on 30 October 2026: pull requests #750 and #752 mended them, and the table above
   names each commit.
2. The readers' conditions on B3. Every verdict but those of RD-r3 and RD-r4 passes "once
   the named findings are mended", all of its reader's findings; RD-r3 names its findings 2
   and 3, and RD-r4 passes as it stands. As written, then, Book I's B3 waits on RD-C1, on
   the Book I items of RD-C4, RD-C5, RD-C6, RD-C9 and RD-C10, and on items 43 and 44 of
   RD-C7, besides M6 (item 40); Book II's on RD-C2 and RD-C3, and on the Book II items of
   RD-C4, RD-C5, RD-C6, RD-C9 and RD-C10. Only RD-C8, and items 41 and 42 of RD-C7, hold
   neither. RD-C1 to RD-C3, and M6 (item 40), are met since (item 1). The pilot editor's
   second round passes on the same condition, so both books' B3
   also wait on items 89, 90 and 93 of RD-C19, on its pages of Books I and II, and Book II's
   on item 94. The verdicts
   single out the voice lapses of RD-C4 and RD-C5; whether the other editorial findings must
   be mended before B3 is recorded, or may go to the backlog, is for the coordinator to
   rule.
3. The pilot editor's notes, each with the commit that fixed it or the change it made to
   docs/STYLE.md or docs/examples.md; III.24 has now been read with the three pages (the
   second round, under "The pilot editor").
4. The dated addendum that "Since the read" asks for.
5. For B3, a `[read-through]` table in docs/reports/acceptance/book-I.toml and book-II.toml
   that cites this report, once each book's conditions are met, and the acceptance report
   regenerated ([ACCEPTANCE](../ACCEPTANCE.md)).

## What #34 and B3 still need, for Book III

1. The material findings M7 to M10 and M12 mended (card drafts RD-C11 to RD-C13 and RD-C21),
   each naming here the commit that resolves it; and M11, mended on main by pull request #720,
   confirmed on the page in the addendum (RD-C20). Met for M8, M9 and M12 on 30 October 2026:
   pull requests #746 and #752 mended them, and the table above names each commit. M7 and
   M10 (RD-C11 and RD-C13) are open.
2. The readers' conditions on B3. All five of Book III's verdicts, the pilot editor's
   included, pass once the named findings are mended ("once named findings are mended", in
   RD-r8's and RD-r9's words), all of their findings. As written, then, Book III's B3 waits on
   RD-C11 to RD-C18, RD-C20, RD-C21 and items 89 to 92 of RD-C19. RD-C12 and RD-C21 are met
   since (item 1). The verdicts
   single out the second voice of RD-C14, RD-C15 and RD-C16; whether the other editorial
   findings must be mended first, or may go to the backlog, is for the coordinator to rule,
   as for Books I and II.
3. The pilot editor's notes Q1 to Q9, each with the commit that fixed it or the change it
   made to docs/STYLE.md or docs/examples.md (Q10 and Q11 are on Books I and II's pages).
4. The addendum that "Since the read" asks for, read at the release candidate, which is a
   commit in main's history as B3's record requires; d4d65c48 is not.
5. For B3, a `[read-through]` table in docs/reports/acceptance/book-III.toml that cites this
   report, once its conditions are met, and the acceptance report regenerated.
