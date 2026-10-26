# Read-through 03: Books I to III

*26 October 2026. Books I and II were read at main bedbba23e, on 25 October, and Book III at main cf1591f14, on 26 October. The mends, and the state of every finding given here, stand on the branch text/read-through-03 at 4acc5ff2a, which has merged main at 110a01809, with the commits after it on the branch: the code review's fixes and two withdrawals (3918ef06d, 26eb5794c, ef949cd29) and a re-reader's correction of I.45's and II.14's run lines, each commit saying what it changes; they are not yet on main. The changes main had had by 41dc2a0ae since the commits read are listed under "Since the read"; the later ones are for the dated addendum.*

## Who read what

| Role | Model | Read or wrote | At |
|---|---|---|---|
| Reader of I.1 to I.12 (RT-b1a) | GPT-6 Astra (Codex) | I.1 to I.12, with Book I's index, introduction and front matter | bedbba23e |
| Reader of I.13 to I.24 (RT-b1b) | Claude Opus 5.5 | I.13 to I.24 | bedbba23e |
| Reader of I.25 to I.36 (RT-b1c) | GPT-6 Astra (Codex) | I.25 to I.36 | bedbba23e |
| Reader of I.37 to I.48 (RT-b1d) | Claude Opus 5.5 | I.37 to I.48 | bedbba23e |
| Book I's flow reader (RT-b1f) | GPT-6 Astra (Codex) | Book I's index, front matter and I.1 to I.48, in order | bedbba23e |
| Book II's reader (RT-b2a) | Claude Opus 5.5 | Book II's index, introduction, front matter and II.1 to II.14 | bedbba23e |
| Book II's flow reader (RT-b2f) | GPT-6 Astra (Codex) | Book II's index, front matter and II.1 to II.14, in order | bedbba23e |
| Reader of III.1 to III.9 (RT-b3a) | GPT-6 Astra (Codex) | III.1 to III.9, with Book III's index, introduction and front matter | cf1591f14 |
| Reader of III.10 to III.18 (RT-b3b) | Claude Opus 5.5 | III.10 to III.18 | cf1591f14 |
| Reader of III.19 to III.27 (RT-b3c) | GPT-6 Astra (Codex) | III.19 to III.27 | cf1591f14 |
| Reader of III.28 to III.37 (RT-b3d) | Claude Opus 5.5 | III.28 to III.37 | cf1591f14 |
| Book III's flow reader (RT-b3f) | Claude Opus 5.5 | Book III's index, introduction, front matter and III.1 to III.37, in order | cf1591f14 |
| Writer of Books I and II's mends | Claude Opus 5.5, the instance that directs this read-through | 34f15131a, 983b5fc35, 427854aef, 8bbeee79d and 2d2c6ab4f, from the readers' proposed wording, with 54df72583; e9d3b1f20 and 9353bbe7a, from the re-readers' findings; and 079318c04, from the pilot editor's | 560da15a2, the branch's base |
| Writer of Book III's mends (RT-w3) | GPT-6 Astra (Codex) | 07416606e, from the five Book III readers' findings, in the files no other work then held | 01ee9cc91 |
| Re-reader (RT-s1x) | GPT-6 Astra (Codex) | The records of I.4, I.16, I.20, I.22, I.23, I.27, I.45 and II.14, whole, stamping all but I.4's; seventeen other mends to Books I and II's commentary, captions, reading lines and figures | ece9c2d71 |
| Re-reader (RT-s2x) | Claude Opus 5.5 | The records of I.39, I.40, I.47, II.1, II.6, II.7 and II.10, whole, stamping all seven, though I.47's mend and stamp were withdrawn at the merge of main that brought #295, which rewrote and restamped that record; twenty-one other mends to Books I and II | 3caa7a252 |
| Re-reader (RT-s3x) | Claude Opus 5.5 | The records of III.1, III.4, III.8, III.9, III.12, III.16 and III.17, whole, stamping all seven; the mends to III.2 to III.17, the introduction and the two idea figures, and e9d3b1f20's | 07416606e |
| Re-reader (RT-s3y) | Claude Opus 5.5 | The records of III.23, III.29, III.30, III.32, III.34, III.36 and III.37, whole, stamping all seven; the mends to the commentary of III.22 to III.37 and the reading lines of III.19 to III.35, and 9353bbe7a's | 7b71d1782 |
| Re-reader (RT-s4x) | GPT-6 Astra (Codex) | The records of I.45 and II.14, whole, again, stamping both and correcting on their run lines the family clause of RT-s1x's reading; it made no finding | a973c8726 |
| Pilot editor (RT-p3) | GPT-6 Astra (Codex) | book/II/01.md, book/I/45.md, book/II/14.md and book/III/24.md, one after another | 52767c483 |
| Writer of this report (RT-rep) | Claude Opus 5.5 | This report, from the outputs above and the branch's commits; it read no page as a reader and wrote no mend | e7decb6ee |

None of the readers wrote, prompted or edited the pages they judged. The two families alternate: the range readers of Books I and III take turns, GPT-6 Astra (Codex) first; Books I and II's flow readers are GPT-6 Astra (Codex), and Book II's reader and Book III's flow reader Claude Opus 5.5. The branch changes 25 records; each was re-read whole and stamped by one of the re-readers listed above, of the family that did not write its proof, as its run line says (#220), save I.45 and II.14: their original proofs are Codex's, and their Codex re-reader is of the family that did not write their outline companions, which Claude's writers added, as a second Codex re-reader's correction on their run lines says. II.6's and II.7's mended records were stamped too, then withdrawn in 9303e9e15 for the cross-family train of #326, which held them; I.4's record mend was withdrawn in 3caa7a252, since its re-reader would not sign I.4 off (below). No Lean file changed.

The readers' outputs, the Book III writer's handback and the ledger of findings kept by the instance that directs this read-through are kept outside the repository, under the identifiers above. Each fate below was read from the diff of the commit named.

## What they found

The severities are the readers' own, by [WORKFLOW](../WORKFLOW.md) section 9. No reader graded a finding blocking.

| Book | Readers | Blocking | Material | Editorial | All |
|---|---|---|---|---|---|
| I | 5 | 0 | 7 | 44 | 51 |
| II | 2 | 0 | 1 | 20 | 21 |
| III | 5 | 0 | 3 | 64 | 67 |
| All three | 12 | 0 | 11 | 128 | 139 |

A finding that several readers made counts once for each: the line over every commentary is six of the editorial findings, and Definition I.19's "none" two of Book I's material ones. The four re-readers made 32 findings of their own (3 material, 29 editorial), and the pilot editor 8 ("The pilot editor").

The material findings, one row for each, with every reader who made it:

| Book | Page | Finding | Reader | Resolution |
|---|---|---|---|---|
| I | Front matter | Definitions I.2 and I.3 are given the Lean partner `Line`, a whole straight line, though Definition I.3 gives a line its extremities | RT-b1a 1 | Open: card draft C1, for the owner of scripts/render.py |
| I | Front matter | Definition I.19 gives multilateral figures "none", though `Figures.Outline` gives a rectilineal figure of any number of sides (I.45, II.14) | RT-b1a 2; RT-b1f 1 | Open: card draft C1 |
| I | I.4, I.8 | The folded heading "Before the theorem, 14 lemmas" (13 on I.8) lists inductive types and abbreviations; on I.4 none is a lemma | RT-b1a 5; RT-s1x 1 | Open: card draft C1 |
| I | I.24 | "Heath proves it under I.38": the proof there is Heron's, which Heath gives | RT-b1b 17 | Mended in 34f15131a |
| I | I.27 | The figure note did not say that the figure draws the impossible supposition | RT-b1c 2 | Mended in 34f15131a |
| I | I.40, III.12 | The status line says "as Euclid states it" of a proposition Heath prints in brackets as an interpolation | RT-b1d 1; RT-s2x 1 | Open: card draft C1 |
| II | II.5 | The problem's "two solutions" stood without their condition, which came a paragraph later | RT-b2f 2 | Mended in 2d2c6ab4f |
| II | II.9 | A re-reader's: the mend e9d3b1f20 said Heath leaves "four steps" without a reference, a count false of his text | RT-s3x 1 | Mended in 9353bbe7a |
| III | III.19, III.25, III.26 | Three reading lines give an earlier year beside a link to a later edition | RT-b3c 1 | Mended in 07416606e |
| III | III.24, III.25 | The status lines say "in our measure of circumferences", though III.24's main theorem says nothing of a measure and in III.25 only a companion uses one | RT-b3f 1; RT-p3 1 | Open: card draft C5, for the owners of scripts/render.py and review/terms.toml |
| III | III.25 | "Euclid's [III. 9]" gives Euclid Heath's reference | RT-b3f 2 | Mended in 07416606e |
| III | III.24 | The proof by the radii, `Prop24.equalCircles`, was told without its semicircle case, which goes by equal diameters | RT-p3 3 | Mended in 079318c04 |

Of the twelve, seven are mended on this branch and five are open: four on card draft C1 and one on C5. The card drafts are not yet filed.

**The editorial findings.**

| Book | Editorial | Mended | In part | To card drafts | Declined | On card draft C9 |
|---|---|---|---|---|---|---|
| I | 44 | 29 | 6 | 7 | 1 | 1 |
| II | 20 | 14 | 0 | 5 | 1 | 0 |
| III | 64 | 36 | 10 | 17 | 0 | 1 |
| All three | 128 | 79 | 16 | 29 | 2 | 2 |

The 79 are mended in 34f15131a (26), 427854aef (2) and 983b5fc35 (1) for Book I, in 8bbeee79d (12) and 2d2c6ab4f (2) for Book II, and in 07416606e (36) for Book III; 54df72583 brought four of the mended statement notes within the 160-character limit. Of the 16 mended in part, 11 have the rest on card drafts (C1 2, C2 2, C5 7), 4 have it on card draft C9 (RT-b1b 16, RT-b3d 19, RT-b3f 11, RT-b3f 16), and 1 has it declined. RT-b3d 19's part on III.28, mended in 07416606e, was withdrawn in the commit after 3918ef06d, since the train of #129 rewrites that commentary. The 29 sent whole to card drafts are in files this read-through did not own, or that other work held while it ran: 9 to C1, for the owner of scripts/render.py, six of them the line over every commentary; 6 to C2, for the owner of the Lean notes of Books I and II (Elements/BookI, Elements/BookII); 1 to C4, for the owner of II.6's and II.7's records, a mend made in 8bbeee79d and withdrawn in 9303e9e15; and 13 to C5, for the owners of Book III's held records, commentary and Lean notes. Every card draft is open. The two open on card draft C9 alone are RT-b1d 9, I.47's record note, mended in 34f15131a and withdrawn when main's #295 rewrote that record, and RT-b3c 3, III.21's record note, in a file held at the time, whose passage the move of #129 is to replace.

Declined, each with its reason:

- **RT-b1f 3.** I.5's paragraph on how its proof still rests on Postulate 2 stays: I.5's page is where a reader needs those paths, and the introduction only summarises them.
- **RT-b2a 11.** II.8's commentary and II.12's note repeat what stands beside them, but say nothing false, and the reader counted the finding among the polish that does not stand in B3's way.
- **RT-b1f 2, in part.** I.4's and I.8's history clause is gone (34f15131a); their inventories stay, since they say what the proofs of the laws cited in the placement draw.

Of the re-readers' 29 editorial findings, 8 are mended (e9d3b1f20, 9353bbe7a, and RT-s3y A1 and A2 in 3918ef06d), 1 in part (RT-s2x 5: II.9's reading line mended, II.3's on card draft C9), 18 are on card drafts (C1 1, C2 4, and 13 on C6, for the owner of the Book III records and pages it names), and 2 are on card draft C9: RT-s1x 6, "the retained axiom" and "now proved" in I.27's record, and RT-s2x 2, "The final step returns this conclusion" in I.39's.

## The pilot editor

The pilot editor (RT-p3), which wrote, prompted and edited none of the four pages, read book/II/01.md, book/I/45.md, book/II/14.md and book/III/24.md consecutively, each top to bottom with its figures, at 52767c483, the branch's head after the Book III mends and their stamps. It made 8 notes: none blocking, 2 material and 6 editorial.

| Note | Page | Severity | What | Fate |
|---|---|---|---|---|
| 1 | III.24 | material | The status line's "in our measure of circumferences" qualifies a main theorem that proves congruence; a rule for STYLE section 2 proposed | Open: card draft C5; the rule for the owner of docs/STYLE.md |
| 2 | II.14 | editorial | "Does the same" blurs that `Prop14.outline` constructs the square with its four corners; the Representation row's "It represents" | In part: the commentary in 079318c04; "It represents" on card draft C9 |
| 3 | III.24 | material | The proof by the radii told without its semicircle case | Mended in 079318c04 |
| 4 | I.45, II.14 | editorial | The tables tell one input, division and area in several rows; a rule for STYLE section 2 proposed | Open: for the owner of docs/STYLE.md |
| 5 | All four | editorial | The line over every commentary | Open: card draft C1 |
| 6 | II.1 | editorial | Four passage notes in a row lead "Done by"; "Again by" proposed for STYLE section 2 and render.py | Open: for the owner of docs/STYLE.md |
| 7 | III.24 | editorial | Bold leads on every paragraph before the modern way | Open: card draft C6 |
| 8 | I.45, II.14 | editorial | An example for docs/examples.md, "A construction completed by companions: I.45 and II.14" | Open: for the owner of docs/examples.md |

Of read-through 02's 19 pilot notes, it found 14 resolved, 2 holding in part and 3 holding still; its notes 4 to 8 carry those five on. No re-reader has read 079318c04.

Its verdict: "Verdict: yes, once notes 1–3 are mended." At 4acc5ff2a, note 3 is mended, note 2 is mended in part, and note 1 is open.

## The books read straight through

Each verdict is quoted from the reader's output, with the state at 4acc5ff2a of each finding it names.

### Book I

- **Flow reader (RT-b1f):** "B3 verdict: pass once findings 1–5 are mended." Finding 1, Definition I.19's "none", is open on C1. Finding 2 is mended in part and declined in part, and finding 3 declined (above). Findings 4 and 5 are mended in 427854aef. It asks for "a rereading of the affected passages before recording B3 as passed"; RT-s1x confirmed the mends to I.4, I.8, I.24 and I.44.
- **I.1 to I.12 (RT-b1a):** "B3 verdict for this range: pass once the named findings are mended." Finding 3 is mended in 983b5fc35. Findings 4 and 7 are mended in part (34f15131a, 983b5fc35): I.4's record waits on C1, and the notes of Prop06.lean and Prop07.lean are on C2. Findings 1, 2, 5 and 6 are open on C1.
- **I.13 to I.24 (RT-b1b):** "Verdict on B3: pass once the named findings are mended." Findings 1 to 9, 11, 12 and 17 are mended in 34f15131a. Findings 14 and 18 are mended in part, with the rest on C2 and C1, and 16 in part, with I.23's route note on card draft C9. Findings 10, 13, 15 and 19 are open on C2, and 20 on C1.
- **I.25 to I.36 (RT-b1c):** "B3 verdict for I.25–I.36: pass once the named findings are mended." All four are mended in 34f15131a.
- **I.37 to I.48 (RT-b1d):** "Verdict on B3: pass once the named findings are mended." Findings 2 to 8 and 10 to 14 are mended in 34f15131a, and 9, I.47's record note, is on card draft C9 since #295 rewrote that record. Findings 1, I.40's status line, and 15 are open on C1.

### Book II

- **Flow reader (RT-b2f):** "B3 verdict: pass once findings 1–3 are mended." All three are mended in 2d2c6ab4f. It adds, "The corrections should be reread at the revision delivered before recording a pass." RT-s1x confirmed the introduction's, and RT-s2x II.5's and II.12's.
- **Book II's reader (RT-b2a):** "Verdict on B3: pass once named findings are mended, namely findings 1 and 2." Finding 2, the praise words of the reading lines, is mended in 8bbeee79d. Finding 1, the line over every commentary, is open on C1.

### Book III

- **Flow reader (RT-b3f):** "Verdict on B3 for Book III: pass once the named findings are mended." Of its two material findings it writes, "By WORKFLOW section 9 they should be mended before the acceptance record is signed." Finding 2, "Euclid's [III. 9]", is mended in 07416606e; finding 1, the measure on III.24's and III.25's status lines, is open on C5. Its editorial findings it calls "polish that would make the read smoother; none of them blocks": 7 are mended in 07416606e, 4 in part there and 4 are on card drafts.
- **III.1 to III.9 (RT-b3a):** "B3 verdict for this range: pass once findings 1–3 are mended." Findings 1 and 3 are mended in 07416606e. Finding 2, the dated history in Prop02.lean's notes and in III.5's and III.6's records, is open on C5.
- **III.10 to III.18 (RT-b3b):** "Verdict on B3: pass once the named findings are mended." It adds, "The mends B3 depends on are the voice ones: findings 6, 16, 17, 22 and 23." Findings 16, 17 and 22 are mended in 07416606e. Finding 23 is mended there in five records and open in four on C5. Finding 6, III.11's change-log, is open on C5.
- **III.19 to III.27 (RT-b3c):** "B3 verdict: pass once findings 2, 3 and 4 are mended." It adds, "Finding 1 also needs correction before acceptance of the affected reading lines." Findings 1 and 2 are mended in 07416606e. Finding 4, Prop25.lean's history, is open on C5. Finding 3, III.21's record note, is open on card draft C9.
- **III.28 to III.37 (RT-b3d):** "Verdict on B3: pass once named findings are mended." It adds, "Finding 1 is the one that must be mended for the range to read in one voice, with findings 2, 4 and 8 alongside it." Findings 2 and 8 are mended in 07416606e. Findings 1 and 4 are mended there in part, with III.28's, III.31's and III.35's records, and for finding 4 Prop28.lean, on C5.

## Since the read

For Books I and II, `git log --oneline bedbba23e..41dc2a0ae -- book/I book/II mishnah/I mishnah/II mishnah/intro/I.md mishnah/intro/II.md Elements/BookI Elements/BookII figures/I figures/II review/I review/II reading/I reading/II` gives twelve commits:

- 9586abc0a: a merge of main at cf1591f14 into the branch of #326; in these paths it brings d66e8bfcf's text stamps.
- ec4b714c6: I.28's record, a correction to its run line.
- c8bd60954: I.28's record read in full by GPT-6 Astra (Codex) for #326: its stamp, reviewer and run line, and the page's "Reviewed" row.
- 9230de107: II.7's, the same.
- 7bad6fede: II.6's, the same.
- 2f156000b: II.13's, the same.
- 10c02b989: II.13's record: a note now says that the acute angles at B and C keep the foot D within CB, and the page follows.
- e5b76b9d6: II.12's, as c8bd60954.
- ff10462e1: I.42's, the same.
- c48f4cfc9: I.38's, the same.
- 87e04e74a: I.34's, the same.
- d66e8bfcf: a text stamp, the hash of the record's text and nothing else, written into each of the 63 records stamped before there were text stamps (#77).

For Book III, `git log --oneline cf1591f14..41dc2a0ae -- book/III mishnah/III mishnah/intro/III.md Elements/BookIII figures/III review/III reading/III` gives three:

- 2883dfbe0: a merge of main at cf1591f14 into the branch of #476; it brings nothing to these paths beyond the commit read.
- 0dddd7220: III.10's proof produces its perpendiculars by Postulate 2, where it called III.2 and Intersections 5; its record's notes and its page follow (#476).
- e88fa2be5: III.10's record read in full and stamped after that change (#476).

None of these is a mend of this read-through's. Before the release, a dated addendum to this report will read each of them, and every later change to these paths, as #34's done-when asks.

## What #34 and B3 still need

1. This branch on main: #34 asks each material finding to name the commit on main that resolves it, and the commits named here are on text/read-through-03.
2. The five open material findings, on card drafts C1 and C5, filed and their fixes landed on main.
3. The verdicts' other open conditions, on C1 (among them the line over every commentary, which Book II's reader names), C2 and C5, and on card draft C9: RT-b3c 3, which its reader's verdict names, RT-b1b 16, RT-b1d 9, RT-b3d 19, RT-b3f 11, RT-b3f 16, the pilot editor's note 2, RT-s1x 6, RT-s2x 2 and RT-s2x 5.
4. A re-reader for 079318c04, the mends to II.14's and III.24's commentaries.
5. The pilot editor's notes 4, 6 and 8, and note 1's rule: #34 asks for each the commit that fixed it or the change it made to docs/STYLE.md or docs/examples.md, and none is made.
6. I.4's record, whose history clause waits for C1's heading and a re-read of I.4.
7. The dated addendum that "Since the read" asks for.
8. For B3, a [read-through] table in docs/reports/acceptance/book-I.toml, book-II.toml and book-III.toml that cites this report, written once its book's verdicts' conditions are met, and the acceptance report regenerated to show B3 passing for each book ([ACCEPTANCE](../ACCEPTANCE.md)). B4 is the limitations review's ([limitations-01.md](limitations-01.md)): it passes Books I and II, whose [limitations] tables stand in the same commit as this report, and holds Book III on the measure of III.24's and III.25's status lines, the finding on card draft C5.
