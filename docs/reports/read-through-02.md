# Read-through 02: Books I and II

*21 October 2026. Read at main 2e8aecf8; the mends and their state as at b78e8ae5, then the head of this read-through's branch, with the second code review's mends in the commit after its merge of main at 2853075b, and the third code review's in the commit after its merge of main at b2c30b6d. This first part covers Books I and II. A second part reads the findings on pages that were held while the readers read, with the changes that have since landed on main, and a later part reads Book III once its moves into the edition land (#34).*

*Each part gives its counts and states as at the revision it names. The second addendum, of 22 October, at the end, says how they changed when this read-through merged the cross-family sign-off (#220) and was read again across families, and gives the stamps as this read-through lands.*

## Who read what

Seven readers read main at 2e8aecf8. Each was Claude Opus 5.5, working as an independent reader, and none of them wrote, prompted or edited the pages they judged. Their roles:

- **The reader of I.1 to I.12**, who also read Book I's index, its introduction and its front matter.
- **The reader of I.13 to I.24.**
- **The reader of I.25 to I.36.**
- **The reader of I.37 to I.48.**
- **The reader of Book II**: its index, its introduction, its front matter and II.1 to II.14.
- **The cross-page reader**, who read across both books for the further reading, the terms a reader meets on many pages, the two questions #34 asks, the figure titles, the figure records and the book pages (the indexes, the front pages, the table of names and the README).
- **The pilot editor**, who read book/II/01.md, book/I/45.md, book/II/14.md and book/III/24.md one after another, as #34 asks. The notes on III.24 are provisional, since III.24 is being restated with Book III's moves.

The five readers of ranges read every rendered page of their range from top to bottom, each against its sources: Heath's text in heath/, the review record, the mishnah, the reading lines and the Lean. They rendered every figure (the figures at a glance, Euclid's figures and the modern figures) and looked at each one. They checked every Heath quotation they met against the OCR of Heath's first volume, word and page, and some against the page images (leaves n295, n296, n297, n307, n316, n410 and n429, and n66 of the second volume). Two changes were in flight while they read, and the readers were given their diffs and judged the pages as those changes would leave them. Those findings are marked "in flight" below. The two changes are:

- **the superposition replacement**, which makes the superposition rule a restricted inference in System E's style (#75);
- **the notation train**, a train of Book I text (#48), which adds a paragraph on the modern way's notation to STYLE section 4, rewrites I.45's modern way and carries the record stamps of the pages it touches.

Both have since landed on main: the replacement at 17ae8e2a (pull request #191) and the notation train at 09bc89f3 (pull request #193). Heath's letters were set upright in every figure at ac6e5389 (pull request #194). This branch merged main, with all three, at 926e67d2.

The findings were then judged against the sources, and those found true and free to mend went to writers. The writers were other Claude Opus 5.5 instances, none of which was one of the readers. One writer took Book I from I.1 to I.36. A second took Book II and I.37 to I.48. A third began the reading lines, and a fourth finished them. A fifth took STYLE sections 5, 7 and 8, the report on figures against Heath's scans, and a dozen commentaries and records across both books. A sixth took what the first writers found on the way, with the pilot editor's notes on II.1 and II.14. Six more followed the re-readers and the code reviews: a seventh mended the first re-readers' findings, finishing what an interrupted run had begun; an eighth wrote the list of habits removed into STYLE section 4; a ninth told II.14's restriction in one set of words and mended the later re-readers' points; a tenth mended the first code review's; after the merge of main at 2853075b, an eleventh mended the second code review's; and after the merge of main at b2c30b6d, a twelfth mended the third's. Each writer checked each finding against Heath, the Lean and the reading list before mending it, and said why when it did not.

While the two changes were in flight, nothing they held was mended on this branch. What they held was what a change in flight was rewriting, with the checks under scripts/, the foundations, docs/STYLE.md section 4, docs/examples.md, the README, the overlap catalogue and all of Book III. One mend made to Elements/BookI/Prop23.lean, whose record was held, was left out of the commit. STYLE section 4 was changed only after the notation train had landed and been merged into this branch.

Seven re-readers, each Claude Opus 5.5 and none of whom wrote or prompted the mends, then read every changed page against Heath, the Lean and the reading list, and stamped the records: four at 206e3080, two at c814e8fb and one at 9b7dad70 ("Re-read and stamped", below). An independent code reviewer, another Claude Opus 5.5 instance, which wrote nothing on this branch and was none of its readers, reviewed the branch at 926e67d2 ("The code review", below). A second code reviewer, another Claude Opus 5.5 instance that wrote nothing on this branch, read its later commits, a third the commits after those, and a fourth the commit after that ("The code review", below). This report was written by a further Claude Opus 5.5 instance, which read no page as a reader and wrote none of the mends. It was brought up to date at b78e8ae5 by another, which likewise wrote no mend; after 2853075b by the eleventh writer and by the instance that directs this read-through, which added the account of the second code review; after b2c30b6d by the twelfth writer, which added the account of the third; and after 74e8ad1f by the instance that directs this read-through, which added the account of the fourth. None of them read a page as a reader. Each resolution below was checked against the diff of the commit it names.

The mends are twelve commits on the branch text/read-through-02:

- 1eda7896: Book I, I.1 to I.36;
- 307eb24f: Book II, I.37 to I.48, STYLE sections 5, 7 and 8, and the report on figures against Heath's scans;
- fe30d3f3: the reading lines of Books I and II;
- 206e3080: what the first mends found on the way;
- c814e8fb: the first re-readers' findings, with II.14's half of the pilot editor's notes 3, 4 and 7;
- b9245195: the list of habits removed, in STYLE section 4 (#46);
- a1ddfcf7: II.14's restriction told in one set of words, with Book II's introduction; the later re-readers' points; and three points not taken up before, I.43's "complements", I.6's axis "0" and a sentence for Book II's introduction;
- 9b7dad70: the first code review's findings;
- b78e8ae5: the last re-reader's point on the scans report;
- 4e9643cb: the second code review's points, in this report, the scans report and STYLE section 4;
- 74e8ad1f: the third code review's points, in this report and the scans report;
- a0bc7896: the fourth code review's point, in this report.

The re-readers' stamps are 4a7bc952, 787ea8ba, 44096af6 and 03676129.

## In short

Books I and II read as one book, in one voice, with their scope told truthfully at the top of every page and their depth even. No finding is blocking.

The readers made 191 findings: 172 from the six readers of ranges and pages, and the pilot editor's 19 notes. Of these, the readers graded 27 material and 164 editorial; one of the 27, I.7's, has since been found partly mistaken and is withdrawn as material (below). As the branch stands at b78e8ae5, by the counts first reported:

- **100 are fixed** by seven commits of this branch: the four first mends, the stamp commit 4a7bc952 (the pilot editor's note 15), c814e8fb and a1ddfcf7. One of them is I.7's, whose mend stands as an accurate rewording but corrected no misattribution.
- **25 are fixed in part.** The rest of each is for the next part of this read-through (23) or for the coordinator (2).
- **64 are open**: 44 for the next part, nearly all on pages that the two changes then in flight held; 11 for changes to scripts/render.py, proposed to the coordinator; 3 for Book III's read; 3 not taken up; 2 in files held for their owners; and 1, I.16's "a + 1", waiting on a font for digits proposed to the coordinator.
- **2 are resolved on main by other work.** Heath's letters, italic in two kinds of figure and upright elsewhere, are upright in every figure since ac6e5389 (pull request #194), and S15 and S20 have required it since cba27afa (pull request #196), both for #159.
- **Three were not taken up**, and need a writer or a decision: "applied" glossed two ways, the unused tags in review/terms.toml, and a record of which chapters were checked. They are among the 64 open.
- **None was declined.** The writers judged every finding they checked true, and in one they were wrong in part. I.7's finding held that Heath gives Proclus the view that I.7 serves only to prove I.8; but Heath writes of "the mistake made by those editors who regard I. 7 as being of no use except to prove I. 8" (vol. 1, p. 261), and his "apparently only required for I. 8" comes later, in his sentence on Proclus. So the old line, "Some editors used I.7 only to prove I.8", was broadly faithful. The finding's other half, that Heath calls ill-advised the editors who drop I.7, is true, and the rewording in 1eda7896 is accurate. Where a proposed wording was not, or would not pass a check, it was written otherwise (the rows for I.22, I.47, II.13 and the years of editions). Two mends to figures could not be made within the checks, I.1's "0" and I.16's "a + 1", and a font for digits is proposed to the coordinator ("Still open").

Of the 27 findings graded material, 11 were first reported fixed on this branch: I.7's attribution, I.18's "We prove both", I.21's condition, I.33's "in the same directions", the docstring of `Prop34.bisect`, I.43's modern figure, II.13's modern figure, I.18's reading line, the two findings on Postulate 5 in Book II, and II.14's figure note. With I.7's withdrawn, 26 material findings stand: 10 are fixed on this branch, and 16 are left: 3 fixed for II.14 and left for I.45, and 13 open. "The material findings left", below, names each with its owner and next step. So #34 is not yet done: each blocking or material finding must name the commit on main that resolves it.

The seven re-readers confirmed every mend, and 43 records now carry their stamps. They and the first code review found no blocking point and no material one that the readers had not already found; the second found one, the stamped records that work in flight also changes (seventeen by the fourth review's count), which wait for the coordinator's order of landing ("Re-read and stamped"). The third found that this summary and "Still open" left that point out; both now name it ("Still open", item 8). The fourth found six more stamped records, I.13, I.14, I.24, I.30, I.32 and I.43, that two sign-off branches for #220 also change; they too wait for the coordinator ("Still open", item 9). Their editorial points, with what became of each, are under "Re-read and stamped" and "The code review": most are mended (c814e8fb, a1ddfcf7, 9b7dad70, b78e8ae5, this report, and the commits after 2853075b and b2c30b6d); one was declined and one not taken up; the rest wait for the next part, the coordinator, the owners of the gap catalogues and Book Zero, or Book III's read.

## The material findings left

| Finding | What | Owner | Next step |
|---|---|---|---|
| I.1 to I.12, 1; I.13 to I.24, 2; across pages, 26 and 27 | The brief, README.md, FORMALIZATION, the overlap and gap catalogues and the rule's docstring would describe the old superposition rule once the replacement landed, and the overlap catalogue would keep rows for I.2, I.3 and I.23 that B2 refuses | Each file's owner; the coordinator for the foundations | The replacement has landed (17ae8e2a, #75). The next part reads these files as it left them, and sends any mend to the file's owner. All but the docstring are changed again by work in flight, the second axiom wave (#119) among it ("Still open", item 1) |
| I.37 to I.48, 3 | I.44's commentary and record would give two reasons for one step | The coordinator, who orders the next part (#34) | Read I.44 as the replacement left it; its commentary and record are now free |
| I.37 to I.48, 4 | The Lean notes of `Prop44.place` and `Prop46.side_eq`, and the rule's docstring on every page, describe the form the replacement retires | The coordinator, who orders the next part (#34) | Prop44.lean and Prop46.lean are free; the docstring is in the foundations |
| I.1 to I.12, 2 | I.4's figure note: Heath's figure also draws the bent base, and ours says nothing (#30) | The coordinator, who orders the next part (#34) | review/I/04.toml is held by the per-law superposition change (#150) and the second axiom wave (#119); write the line the scans report proposes once those land |
| I.25 to I.36, 2 | I.27's figure note does not say the figure draws the impossible supposition (#30) | The coordinator, who orders the next part (#34) | review/I/27.toml is held by the second axiom wave (#119); write the note and case the scans report proposes once that lands |
| I.1 to I.12, 4; across pages, 33 | Book I's front page maps Definitions I.2 and I.3 to `Line`, and lists `quadArea` for Definition I.14 | The coordinator | A change to scripts/render.py, proposed (#34) |
| I.37 to I.48, 1 | I.45's modern way needs A and C on opposite sides of DB | The coordinator, who orders the next part (#34) | mishnah/I/45.md is free; mend it with II.14's wording (#116) |
| Across pages, 16 (in part); pilot, 3 (in part) | I.45's half: the main theorem said to "take the figure", and the issue link read as the citation for Hilbert's proof | The coordinator, who orders the next part (#34) | Mend mishnah/I/45.md as II.14 now reads (c814e8fb, a1ddfcf7), #116 |
| Pilot, 4 (in part) | I.45's Statement and Extra hypotheses rows describe the companions in noun piles | The coordinator, who orders the next part (#34) | review/I/45.toml is held by the citation sweep (#32); mend it in II.14's words once that lands, #116 |
| Pilot, 1 | The notation train's I.45 record was cut from an older base, its stamp and Lean hash out of date | The coordinator, who orders the next part (#34) | The notation train has landed (09bc89f3); read I.45's record as it stands, and stamp it again once the citation sweep (#32) releases it |
| Pilot, 16 | III.24's caption claims more than its statement; two sentences will be false once it cites placement; its scope and route fail ACCEPTANCE P3 | The coordinator, for Book III's read (#34) | Read with III.24's restatement |

## The four answers

### 1. Is it one voice?

**Yes, in the mishnah; a second voice survived in the notes, the reading lines and one generated line, and most of it is now gone.** Every reader of a range heard one warm, exact writer in the commentary. Heath is quoted with his page, and the leads are the proposition's own ("Much greater.", "Who is so dull?", "A ladder to the square root of two."). No page reads like a ledger. The pilot editor heard one writer across II.1, I.45, II.14 and III.24.

The second voice was in four places:

- **The "How the Lean follows the text" notes.** "A rule we assume" and its kin ("not a proved lemma", "a rule we assume, not a proof") stood sixteen times on twelve pages of I.1 to I.12, and "a rule we assume, not a proof" eight times in four records of I.19 to I.22. "Now proved from I.13 and Common Notion 3 in `Elements/BookI/Prop13.lean`" stood eight times across Book II. Heath's missing reference was said three ways.
- **The reading lines.** Nine of the twenty-six lines of I.1 to I.12 carried "a [adjective], [adjective] book", and "friendly" stood in eight files of Book I.
- **Dated history on reader pages**, such as "This was an assumption until 19 October 2026 and is now proved" and "These corollaries retain the former rules' names and types".
- **The generated line over every commentary**, "Our commentary: what Euclid assumes, what Lean made us say out loud, and how the result looks by modern means." It echoes a lead that STYLE section 3 retires, and on the pages with no modern way it promises one.

The first three are mended on the pages no change in flight held (1eda7896, 307eb24f, fe30d3f3, 206e3080, c814e8fb); on the pages that were held, they are for the next part. The last is a change to scripts/render.py, proposed to the coordinator, and is open.

The readers also heard a logician's register coming in with the superposition replacement, in "represented derivations", "export" and "returned as constructed points". It came on the introduction, I.4, I.8 and I.23, as that change wrote them. The change has since landed (17ae8e2a), and the next part reads those pages.

### 2. Is it consistent?

**Mostly, and the seams the readers found are mended where their files were free.** The house terms hold across the four pilot pages: Heath's references, "the Lean", the rectangle contained, "Drawn for one case:" and the colours named in brackets. The seams were these:

- Captions said "line", "longer", "bigger", "smaller" and "diagonal", where Euclid's words are "straight line", "greater", "less" and "diameter" (I.9 to I.12, I.18 to I.20, I.34, I.43, I.44).
- Lean notes gave definitions without their book ("Definition 10", "Definition 23", "Def. 22").
- "Proclus's" stood beside "Proclus'".
- "Rule of magnitudes" stood beside "rule of magnitude".
- The rectangle was "contained by CA and AD" beside Heath's comma form.
- Book I's helpers were named on Book II pages without their book (`Prop43` for `BookI.Prop43`).
- People were first named on a page by surname alone: Heiberg and Savile on I.4, and Heiberg on I.15 and I.37, in notes that stand before the commentary; Pasch on I.10; and Byrne, Bolyai and Lobachevsky, Saccheri and Gauss in reading lines.

All of these are mended outside the files that were held; in those files they are for the next part. Three seams remain open:

- **The restriction of I.45 and II.14 went by several names**: "supplied" or "given", "non-overlapping" or "lie apart", an unglossed "outline", and a "tacit step". II.14's page and Book II's introduction now use one set of words: a figure "given with a checked division into triangles", and a figure "given only by its boundary" for "outline" (a1ddfcf7). I.45, Book I's introduction and the vocabulary the pilot editor proposes for STYLE section 4 are for the next part.
- **Joining.** Euclid's "let … be joined" is carried out on I.5 and I.11 but not on I.1, I.6, I.7 or I.12. The records of I.5 and I.11 are still held, by the citation sweep (#32) and the second axiom wave (#119).
- **"Applied"** is glossed one way on I.8 and another on I.44 (not taken up).

### 3. Does it say truly what it proves?

**Yes, at the top of every page. Lower down, a few sentences and figures claimed more than the Lean or the sources, and most of them are mended.**

- Every status line and statement row the readers checked says where our statement goes beyond Euclid's, and every certificate claim they checked agrees with facts.json.
- The cross-page reader found that "every proof follows Euclid's argument" matches all 62 records.
- The pilot editor found that I.45 and II.14 tell the restriction alike in substance, and as docs/ACCEPTANCE.md's table allows it: a figure given with its checked division into triangles, its area relative to that division, the outline proof to come (#116).

The claims that went beyond the Lean or the sources were these:

- **I.18 said "We prove both"** of two steps, one of which is the assumed rule `lt_trans` (1eda7896).
- **The docstring of `Prop34.bisect` said I.35 to I.47 cite I.34 for the halving** (1eda7896).
- **I.33 gave Heath the words "in the same directions"**, which are Euclid's (1eda7896).
- **I.21's and I.45's modern ways dropped a condition.** I.21's is mended in 1eda7896. I.45's is for the next part (#116).
- **Three modern figures printed conditions narrower than their paragraphs.** The labels were taken off II.12 and II.13 in 307eb24f, and off I.31 in 206e3080. STYLE section 7 now asks a modern figure to be drawn under the conditions its paragraph states (9b7dad70).
- **II.14's figure note promised two triangles over an undivided figure** (307eb24f).
- **The Book I front page maps Definitions I.2 and I.3 to `Line`**, which is whole and straight. This is open, in scripts/render.py.

This list first held one more, that I.7 credited editors with what Heath gives Proclus (1eda7896). That is withdrawn: Heath himself gives the view to editors (vol. 1, p. 261), so the old line did not go beyond the sources, and its rewording, which stands, corrected no misattribution ("In short").

The pilot editor's further point was that on I.45 and II.14 the mishnah said the main theorem "takes the figure", while the top rows described the companions. For II.14 this is mended: its Extra hypotheses and Representation rows, its commentary and Book II's introduction now say that the main theorem takes its two triangles unchecked (c814e8fb, a1ddfcf7). I.45's half is for the next part. It is the limitation B4 asks to be stated plainly ("Still open").

### 4. Is the depth even?

**Yes.** Each reader found the pages as deep as their propositions.

- I.3 and I.10 are the thinnest pages of I.1 to I.12, but they are simple propositions, and I.7's hard block has its paragraph.
- I.18 and I.19 are shorter, but they have Heath's datum and quaesitum and De Morgan's logic.
- The commentaries of I.25 to I.36 run to three or four paragraphs. I.25 is short because the proposition offers little.
- I.45 and I.47 are rich because they hold the hardest formal blocks, and I.41 and I.42 are short but each has its point.
- II.2 and II.3 are shorter because those propositions offer less.

The pilot editor measured the four pilot commentaries at 360, 662, 537 and 441 words, each with a paragraph on its hardest formal step. The unevenness is in the tables: the Representation rows of II.1, I.45, II.14 and III.24 ran to 100, 256, 207 and 46 words, and II.14 retold I.45's limitation in full. II.14's row now tells the main theorem's scope first and no longer repeats its Statement row, though it runs to 214 words (a1ddfcf7). I.45's is for the next part (notes 3 and 5).

## The two questions of #34

**(1) May a repeated page reference drop "vol. N"? No.** STYLE section 5, "Quoting Heath", now says this, in 307eb24f:

> Every reference to Heath keeps its volume, however close the one before it: "(vol. 1, p. 243)" after "(vol. 1, p. 242)", never "(p. 243)", since Heath's volumes share page numbers and each reference must be checkable on its own.

The cross-page reader counted the evidence for the rule:

- 93 references in Books I and II repeat the volume within a paragraph.
- 1 drops it: "(p. 316)" after "(Heath, vol. 1, p. 207)" in mishnah/intro/I.md:9.
- 1 gave no page at all: II.3's "(Heath, under II.2)", now "as Heath remarks under II.2 (vol. 1, p. 377)" (307eb24f). II.1's reference to the same note gained its page in c814e8fb.

So two bare page references still fail the rule, both in files that other work holds:

- **mishnah/intro/I.md:9**, "(p. 316)", to become "(vol. 1, p. 316)". The superposition replacement held the file while the readers read; the second axiom wave (#119) holds it now. It is for the next part.
- **mishnah/III/32.md:3**, "(p. 67)" after "(vol. 2, p. 66)", to become "(vol. 2, p. 67)". A writer found it; Book III is held for its moves, and it waits for Book III's read.

**(2) The italics audit, open since read-through 01's issue 9, is done for Books I and II.** The cross-page reader checked every italic span in the commentaries and introductions of Books I and II against the italic flags of the ABBYY data for the cited leaf.

- There are 126 spans: titles, foreign words and Heath's own emphasis.
- Three could not be read from the data: I.6's *logical* (p. 256, leaf n276), I.8's *partial* (p. 262, leaf n282) and I.46's *one* (p. 348, leaf n368). A writer viewed those three page images, and all three words are italic there.
- So all 126 are confirmed, and no italic has been added.
- One italic Heath printed was thought perhaps missing: II.14's "in the figure of II. 5" (p. 410, leaf n430). It is roman on the scan.
- The reading lines hold 122 more spans, all titles, with I.6's *reductio ad absurdum*. The record notes hold none.
- The audit covers Books I and II only. Book III's commentaries and reading lines are not yet audited; they wait for Book III's read.

The audit also found a disagreement between STYLE section 5 and the reviewer's checklist, item 10. Heath sets every enunciation in italic, but the pages quote an enunciation's words in roman (I.14, I.17, I.33, II.1). STYLE section 5 now says that this is Heath's setting, not his emphasis, so such words stay roman, while a theorem he states in italic in a note keeps its italic (Heron's converse, under II.12). Item 10 agrees (307eb24f).

## Findings

Each row gives a reader's finding:

- **Finding**: the reader's role and the reader's number. "Across pages" is the cross-page reader, and "pilot" the pilot editor, whose notes have their own section below.
- **Where**: the file and line at 2e8aecf8, or where a change then in flight put it.
- **Tier**: the tier of WORKFLOW section 10, step 8.
- **Severity**: by WORKFLOW section 9, the reader's own grade.
- **Resolution.** "Next part" marks a finding on a page that a change in flight held while the readers read: the superposition replacement, for I.4, I.8, I.23, I.44 and Book I's introduction, or the notation train, for I.5, I.11, I.20, I.27, I.29, I.35, I.37, I.39, I.40, I.43, I.45 and I.48. Both have landed on main, and this branch has merged them. The next part of this read-through, a second train under #34, reads these findings on the pages as they landed, with the dated addendum #34 asks for (see "Still open"), and until then they stay open. Where a file is still held by a change in flight, the row names it: the per-law superposition change (#150), the citation sweep (#32) or the second axiom wave (#119).

A finding several readers made has one row naming them all. The cross-page reader's fortieth item is not a finding: every relative link and anchor on the book pages resolves, the introduction's "Heath sees three sections in it" (vol. 1, p. 308) checks out against his "second section of the first Book", which "leads up to the third", and every record declares Euclid's route.

### Book I: introduction and front matter

| Finding | Where (file:line at 2e8aecf8) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| I.1 to I.12, 16 | mishnah/intro/I.md:3 | 2 | editorial | "Euclid's own figure" for a figure redrawn from Heath's; the page's order leaves out the "In Lean" table and the notes | Open: next part; the introduction is held by the second axiom wave (#119), #34 |
| I.1 to I.12, 7; across pages, 28 | mishnah/intro/I.md:7 (in flight), with I.4, I.8 and I.23 | 2 | editorial | The replacement's "represented derivations", "export", "returned" and "leaves the placement", four ways of saying one thing, none glossed | Open: next part; the introduction is held by the second axiom wave (#119), and I.4's and I.8's records and Lean by the per-law superposition change (#150) and the second axiom wave (#119), #75, #34 |
| Across pages, 3(a) | mishnah/intro/I.md:9 | 2 | editorial | "(p. 316)" after "(Heath, vol. 1, p. 207)", the one bare repeat | Open: next part; held by the second axiom wave (#119); STYLE section 5 now asks for "(vol. 1, p. 316)" (307eb24f), #34 |
| I.1 to I.12, 15 | mishnah/intro/I.md:13 | 2 | editorial | "Why does the Lean cite more?" ends on two asides about Intersections 2 and 3 | Open: next part; held by the second axiom wave (#119), #34 |
| Across pages, 14 | mishnah/intro/I.md:13 | 2 | editorial | "A bracket is Heath's pointer", where "brackets" alone are Heiberg's | Open: next part; held by the second axiom wave (#119), #34 |
| I.1 to I.12, 4; across pages, 33 | scripts/render.py:1777–1782 (book/I/front.md:15–16, :27) | 1 | material | The front page maps Definitions I.2 and I.3 to `Line`, which is whole and straight and has no ends, and lists `quadArea` among the kinds of figure for Definition I.14 | Open: scripts/render.py is not changed by this work; proposed to the coordinator, #34 |
| Across pages, 37 | scripts/render.py (book/I/front.md:62) | 1 | editorial | Book I's front page gives pp. 153–155 with no scan leaf, where Book II's links its leaf | Open: scripts/render.py, proposed to the coordinator, #34 |
| Across pages, 38 | scripts/render.py (book/I/index.md:7, book/II/index.md:7, book/names.md:9) | 1 | editorial | "whole", "restricted" and "in part" set in italic, being neither titles nor foreign words | Open: scripts/render.py, proposed to the coordinator, #34 |

### I.1 to I.12

| Finding | Where (file:line at 2e8aecf8) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| I.1 to I.12, 29 | reading/I/03.md:1, reading/I/05.md:2 | 2 | editorial | Kedlaya's line on I.3 and Wardhaugh's on I.5 would fit any page | Fixed in fe30d3f3: both dropped, and each work described in full at its first apt page, I.18 and I.40 |
| I.1 to I.12, 2; across pages, section 5 | review/I/04.toml (no [figure]) (book/I/04.md:21) | 2 | material | Heath's figure also draws the base bent below EF, for the bracketed scholium; ours leaves it out and says nothing | Open: next part; the record is held by the per-law superposition change (#150) and the second axiom wave (#119), #30 |
| I.1 to I.12, 5 | mishnah/I/04.md:3, :7 (in flight) | 2 | editorial | I.4's new paragraph in a logician's register, and without the answer to Peletier's danger | Open: next part; held by the second axiom wave (#119), #75, #34 |
| I.1 to I.12, 8 | review/I/04.toml:13, :19; review/I/08.toml:10, :17, :38 (in flight) | 2 | editorial | The new notes of I.4 and I.8 in the same register | Open: next part; both records are held by the per-law superposition change (#150) and the second axiom wave (#119), #34 |
| I.1 to I.12, 21; across pages, 24 (I.4) | review/I/04.toml:36; Elements/BookI/Prop04.lean:55 | 2 | editorial | Heiberg and Savile first named by surname alone, in notes that stand before the commentary | Open: next part; both files are held by the per-law superposition change (#150) and the second axiom wave (#119), #34 |
| I.1 to I.12, 10 | review/I/05.toml, review/I/11.toml (in flight); Elements/BookI/Prop05.lean:57–58; Prop11.lean:67 | 2 | editorial | Euclid's "let … be joined" carried out on I.5 and I.11, but not on I.1, I.6, I.7 or I.12, with no reason given | Open: next part; the files are held by the citation sweep (#32) and the second axiom wave (#119); one practice is to be chosen and told once in the introduction, #34 |
| I.1 to I.12, 24 | review/I/06.toml:44–45 | 2 | editorial | I.6's case and note say the figure draws AB greater than AC; it draws them equal, as Heath's does, with DB shorter | Fixed in 1eda7896; the scans report's I.6 row corrected in 307eb24f |
| I.1 to I.12, 3 | mishnah/I/07.md:3 | 2 | material (withdrawn) | "Some editors used I.7 only to prove I.8": Heath gives that remark to Proclus, and calls ill-advised the editors who drop I.7 | Reworded in 1eda7896, and the rewording stands; but the finding was partly mistaken, and is withdrawn as material. Heath gives the view to editors too, "those editors who regard I. 7 as being of no use except to prove I. 8" (vol. 1, p. 261), so the old line was broadly faithful; the finding's second half, "ill-advised", is true |
| I.1 to I.12, 14 | review/I/07.toml:9 | 2 | editorial | The route note names the audit's reverse derivation and an "overlap" a visitor is never told of | Fixed in 1eda7896 |
| Across pages, 18 | mishnah/I/07.md:7 | 2 | editorial | "Lean has no reader to leave cases to", kin of a retired refrain | Fixed in 307eb24f |
| I.1 to I.12, 6 and 9 | mishnah/I/08.md:3, :5 (in flight) | 2 | editorial | I.8's new paragraph in words written for a checker, and its third telling of "only I.4 and I.8" | Open: next part; held by the second axiom wave (#119), #34 |
| I.1 to I.12, 13 | Elements/BookI/Prop08.lean:33–37 | 2 | editorial | Heath's letters in backticks, and a meaning claimed for "applied" that the commentary calls our reading | Open: next part; held by the per-law superposition change (#150) and the second axiom wave (#119), #34 |
| I.1 to I.12, 26 | mishnah/I/08.md:5; reading/I/08.md:1 | 2 | editorial | David Hilbert "made side, angle, side an axiom": his axiom gives only the remaining angles, and he proves the rest | Fixed in fe30d3f3 for the reading line; open for mishnah/I/08.md (now :7): next part, with the first code review's wording; held by the second axiom wave (#119), #34 |
| I.1 to I.12, 19 | mishnah/I/09.md:3 | 2 | editorial | "Our proof has to be that objector": it answers him | Fixed in 1eda7896 |
| I.1 to I.12, 17; across pages, 24 (Pasch) | mishnah/I/10.md:1; reading/I/10.md:1 | 2 | editorial | "Pasch's rules" unglossed, and Moritz Pasch not named in full | Fixed in 1eda7896 |
| I.1 to I.12, 18 | mishnah/I/11.md:1 | 2 | editorial | "Isaac Todhunter's worry under I.14" never said | Fixed in 1eda7896 |
| I.1 to I.12, 11 | review/I/11.toml (in flight) | 2 | editorial | A new passage key renders "and let FC be joined;…" | Open: next part; held by the citation sweep (#32) and the second axiom wave (#119), #34 |
| I.1 to I.12, 20 | Elements/BookI/Prop11.lean:39 | 2 | editorial | "In Lean C may be any point": our statement's choice, not Lean's | Open: next part; held by the citation sweep (#32), #34 |
| I.1 to I.12, 12; across pages, 25 (I.12) | Elements/BookI/Prop12.lean:89 | 2 | editorial | "Definition 10" without its book | Fixed in 1eda7896 |
| I.1 to I.12, 23 | figures/I/09-idea.svg:3 to 12-idea.svg:3 | 2 | editorial | Captions say "line" for Euclid's straight line | Fixed in 1eda7896 |

### I.13 to I.24

| Finding | Where (file:line at 2e8aecf8) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| I.13 to I.24, 9 | review/I/13.toml:9; Elements/BookI/Prop13.lean:186, :242 | 2 | editorial | A change-log on the page: "These corollaries retain the former rules' names and types"; "This was an assumption until 19 October 2026" | Fixed in 1eda7896; the same file's "positivity" and "In Lean a right angle has one size" in 206e3080 |
| I.13 to I.24, 26; across pages, 25 (I.13) | Elements/BookI/Prop13.lean:117 | 2 | editorial | "Definition 10" without its book | Fixed in 1eda7896 |
| I.13 to I.24, 10 | figures/I/13-idea.svg:3 | 2 | editorial | "Heath's E … is not drawn" beside a drawn perpendicular | Fixed in 1eda7896 |
| I.13 to I.24, 5 | review/I/14.toml:33 | 2 | editorial | The figure note says the figure draws the supposition, then that it does not | Fixed in 1eda7896 |
| I.13 to I.24, 7 | mishnah/I/14.md:3 (in flight) | 2 | editorial | "as in I.4" will point to a name I.4's new commentary no longer gives | Open: next part, which reads I.14 against I.4 as the superposition replacement left it, #34 |
| I.13 to I.24, 20 | mishnah/I/14.md:5 | 2 | editorial | "Our Lean settled this in I.11": it is our Postulate 4 that makes every right angle the one right angle | Fixed in 1eda7896 |
| Across pages, 24 (I.15) | review/I/15.toml:19 | 2 | editorial | Heiberg first named by surname in the note that stands before the commentary | Fixed in 307eb24f; the commentary's second full name cut in 206e3080 |
| I.13 to I.24, 11 | mishnah/I/16.md:1; mishnah/I/17.md:5 | 2 | editorial | Riemann's geometry pointed to in words alone, chained from I.17 to I.16 to I.12 | Fixed in 1eda7896 |
| I.13 to I.24, 29 | figures/I/16-modern.svg:28 | 2 | editorial | "a + 1" in Georgia's old-style 1 may read as "a + i" at the page's width | Open: not possible within the checks, for Georgia has no lining figures to switch on and S24 and S25 accept no other font; a font for digits is proposed to the coordinator, #34 |
| I.13 to I.24, 19 | mishnah/I/17.md:1; mishnah/I/19.md:1 | 2 | editorial | I.17 retells the introduction's "similarly"; I.19 retells a Lean note | Fixed in 1eda7896 |
| I.13 to I.24, 21 | review/I/17.toml; review/I/20.toml:39 | 2 | editorial | I.17 names no case drawn; I.20's case ends "in Euclid's figure" under Euclid's figure | Fixed in 1eda7896 for I.17; open for I.20: next part, its record held by the citation sweep (#32), #30 |
| I.13 to I.24, 24 | reading/I/17.md:1–2 | 2 | editorial | Saccheri by surname alone; Bolyai and Lobachevsky named in full a second time | Fixed in fe30d3f3 |
| I.13 to I.24, 1 | mishnah/I/18.md:3 | 0 | material | "We prove both", where one of the two steps is the assumed rule `lt_trans`; and the figure spares Euclid's sentence, not our step | Fixed in 1eda7896 |
| I.13 to I.24, 13; across pages, 5 | reading/I/18.md:2 | 2 | material (I.13 to I.24: editorial) | "Euclid uses I.5 here without naming it": the references are Heath's | Fixed in fe30d3f3 |
| I.13 to I.24, 12 | figures/I/18-idea.svg:3 to 20-idea.svg:3 | 2 | editorial | "Longer", "bigger", "smaller", "shorter" for "greater" and "less" | Fixed in 1eda7896 |
| I.13 to I.24, 15 | mishnah/I/20.md:5 | 2 | editorial | The modern way never ties its u and v to the triangle | Open: next part, #34 |
| I.13 to I.24, 3 | mishnah/I/21.md:5; figures/I/21-modern.svg | 2 | material | The modern way's claim holds only on A's side of BC; the figure draws a point E the paragraph never uses | Fixed in 1eda7896 (the condition) and 206e3080 (E taken out) |
| I.13 to I.24, 27 | mishnah/I/21.md:1 | 2 | editorial | The commentary opens by restating the enunciation | Fixed in 1eda7896 |
| I.13 to I.24, 16 | review/I/22.toml:4 | 2 | editorial | "its third corner on P's side", P never introduced | Fixed in 1eda7896, without "as I.23 needs", which broke the 160-character limit for a statement's note |
| I.13 to I.24, 4 | mishnah/I/23.md, review/I/23.toml (in flight) | 2 | editorial | I.23's new paragraph and route note retell the rule's machinery in unglossed words, and answer a question the same change deletes | Open: next part, #34 |
| I.13 to I.24, 17 | Elements/BookI/Prop23.lean:42 | 2 | editorial | "(I.24, I.31)" leaves out I.42, which facts.json shows citing I.23 | Open: next part. The mend was made and then left out of 1eda7896, because I.23's record was held; it should then name I.44 too, #34 |
| I.13 to I.24, 6 | mishnah/I/24.md:1 | 2 | editorial | Heath's "We have already seen one instance in I. 7" quoted without its antecedent, beside our own "as under I.2" | Fixed in 1eda7896 |
| I.13 to I.24, 14 | figures/I/24-modern.svg | 2 | editorial | b and c stand on the sides opposite to I.18's names | Fixed in 1eda7896 |
| I.13 to I.24, 23 | reading/I/24.md:1 | 2 | editorial | "tables" twice, and the first half of I.4's Maor line word for word | Fixed in fe30d3f3 |

### I.25 to I.36

| Finding | Where (file:line at 2e8aecf8) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| I.25 to I.36, 13 | mishnah/I/26.md:1; docs/reports/figures-against-scans.md:36 | 2 | editorial | The commentary repeats the figure's case line; the scans report still calls I.26's note the owner's judgment | Fixed in 1eda7896 (the sentence) and 307eb24f (the report's dated note) |
| I.25 to I.36, 2; across pages, section 5 | review/I/27.toml:27; mishnah/I/27.md:5 | 2 | material | I.27's figure note does not say that the figure draws the impossible supposition, nor which way AB and CD meet | Open: next part; the record is held by the second axiom wave (#119), #30 |
| I.25 to I.36, 12 | mishnah/I/28.md:1; mishnah/I/31.md:5 | 2 | editorial | Why the angles are alternate, told at I.27, retold on both pages and in their own notes | Fixed in 1eda7896 |
| I.25 to I.36, 15; across pages, 25 (I.29) | Elements/BookI/Prop29.lean:91 | 2 | editorial | "Definition 23" without its book | Open: next part, #34 |
| I.25 to I.36, 20 | reading/I/29.md:2; reading/I/30.md:1 | 2 | editorial | "Playfair's" in quotation marks, beside the commentary's plain "John Playfair's axiom" | Fixed in fe30d3f3 |
| I.25 to I.36, 11 | mishnah/I/30.md:3 | 2 | editorial | A route stated and dropped, and the circle that rules it out never said | Fixed in 1eda7896 |
| I.25 to I.36, 21 | figures/I/31-modern.svg:24–25, with 01-, 06-modern.svg and II/12-, 13-modern.svg | 2 | editorial | "t < 0" reads "t < o" in Georgia's old-style zero | Fixed in 206e3080 (I.31), 307eb24f (II.12, II.13) and a1ddfcf7 (I.6's axis label "0" taken off, the axes' crossing showing the origin); I.1's "0" kept, for it is the paragraph's "A = 0" and the figure's only mark of the origin: open, with the font for digits proposed to the coordinator, #34 |
| I.25 to I.36, 9; across pages, 6 | reading/I/32.md:3 | 2 | editorial | The Lincoln line has no main verb, leaves "Charleston" unexplained and writes "3:186" | Fixed in fe30d3f3 |
| I.25 to I.36, 1 | mishnah/I/33.md:3 | 2 | material | "In the same directions" credited to Heath: the words are Euclid's, and Heath added only those in parentheses round them | Fixed in 1eda7896 |
| I.25 to I.36, 3 | Elements/BookI/Prop34.lean:95 | 2 | material | The docstring of `Prop34.bisect` says I.35 to I.47 cite I.34 for the halving: I.35 and I.36 cite it for other things | Fixed in 1eda7896 |
| I.25 to I.36, 16; I.37 to I.48, 28 | figures/I/34-idea.svg:3; 43-idea.svg:3; 44-idea.svg:3 | 2 | editorial | "Diagonal" for Euclid's "diameter", and "two equal halves"; I.43's caption never says "complements", the enunciation's word | Fixed in 1eda7896 for "diameter" and "in half", and in a1ddfcf7 for "complements": "the two pieces the diameter misses, EBGK and HKFD (yellow), which Euclid calls the complements" |
| I.25 to I.36, 4 | mishnah/I/36.md:7 | 2 | editorial | Heath's note printed under I.37 quoted on I.36, its point told a third time | Fixed in 1eda7896 |

### I.37 to I.48

| Finding | Where (file:line at 2e8aecf8) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| I.37 to I.48, 21; across pages, 24 (I.37) | review/I/37.toml:25 | 2 | editorial | Heiberg first named by surname in a note that stands before the commentary | Open: next part, #34 |
| I.37 to I.48, 20 | mishnah/I/38.md:1; mishnah/I/39.md:3 | 2 | editorial | "the little argument proved for I.37" and "its page tells why", pointers in words alone | Fixed in 307eb24f for I.38; open for I.39: next part, #34 |
| Across pages, 4 | reading/I/38.md:1 | 2 | editorial | Aigner and Ziegler's first appearance never says what the book is | Fixed in fe30d3f3 |
| I.37 to I.48, 16 | mishnah/I/39.md:5; mishnah/I/40.md:5 | 2 | editorial | I.39 and I.40 retell one reductio step by step, each repeating its own notes | Open: next part, #34 |
| I.37 to I.48, 24 | review/I/39.toml:7 | 2 | editorial | "so A and D are apart" reads as following from the conclusion, where it is the hypothesis | Open: next part; held by the citation sweep (#32), #34 |
| I.37 to I.48, 25 | review/I/40.toml:4 | 2 | editorial | "`Prop40.join` gives AD parallel", parallel to what not said | Open: next part; held by the citation sweep (#32), #34 |
| I.37 to I.48, 22 | review/I/40.toml:10; review/I/47.toml:7, :12, :53 | 2 | editorial | Lean names bare in notes, so S12 cannot check them | Fixed in 307eb24f for I.47 (in the figure's alt text, "its companion"); open for I.40: next part, held by the citation sweep (#32), #34 |
| I.37 to I.48, 17 | mishnah/I/41.md:1; 42.md:5; 48.md:1 | 2 | editorial | Three commentaries restate their own notes; I.42's "its arm, produced" is not always so | Fixed in 307eb24f for I.41 and I.42; open for I.48: next part, #34 |
| I.37 to I.48, 12 | reading/I/42.md:2 | 2 | editorial | The link opens Dover's reprint under another title, and I.42 does not say so | Fixed in fe30d3f3 |
| I.37 to I.48, 2 | figures/I/43-modern.svg:35–38 | 2 | material | "u" beside EB and "v" above HD read as those pieces, though u and v are the whole of AB and AD | Fixed in 307eb24f: EB and HD labelled (1 − s)u and (1 − t)v |
| I.37 to I.48, 3; across pages, 26 (I.44) | mishnah/I/44.md:3 (in flight) | 2 | material | After the superposition replacement, I.44's commentary and record would give two reasons for one step | Open: next part, which reads I.44 as the replacement left it (17ae8e2a), #34 |
| I.37 to I.48, 4 | Elements/BookI/Prop44.lean:22, :34; Prop46.lean:124; Elements/Foundations/Tacit/Superposition.lean:27 (in flight) | 2 | material (if left) | Lean notes of `Prop44.place` and `Prop46.side_eq`, and the rule's docstring on every page, describe the form the replacement retires | Open: next part for Prop44.lean and Prop46.lean; the rule's docstring is in the foundations, the coordinator's, #34 |
| I.37 to I.48, 5 | review/I/44.toml:14 (in flight) | 2 | editorial | The new note: "supplies" twice, a construction called "unproved", terms unglossed | Open: next part, #34 |
| I.37 to I.48, 13 | reading/I/44.md:1–2 | 2 | editorial | "before and after Euclid, back past the *Elements*" says one thing twice; two lines running "is the place to" | Fixed in fe30d3f3 |
| I.37 to I.48, 1; pilot, 3 (modern way) | mishnah/I/45.md:11 | 2 | material | The modern way's sum of two triangles is the figure's area only with A and C on opposite sides of DB, which the page itself says | Open: next part, with II.14's wording, #34, #116 |
| I.37 to I.48, 18; pilot, 3 (I.45) | mishnah/I/45.md:1 | 2 | material (pilot); editorial (I.37 to I.48) | The reason for avoiding AC reads as if DB were always safe, and the main theorem is said to "take the figure" | Open: next part, as II.14 now reads (c814e8fb, a1ddfcf7), #34, #116 |
| I.37 to I.48, 19; pilot, 5 (I.45) | review/I/45.toml:18 | 2 | editorial | The Representation row runs to about 260 words, with one sentence a reader cannot parse | Open: next part; the record is held by the citation sweep (#32), #34, #116 |
| I.37 to I.48, 29 | figures/I/45-idea.svg | 2 | editorial | The figure at a glance draws KFLM apart, H a point of its own, where Euclid's figure puts H on D | Fixed in 307eb24f: the caption says it is drawn apart, as Heath draws it |
| I.37 to I.48, 15 | mishnah/I/47.md:7 | 2 | editorial | "The right angle at A ensures this arrangement…" and "This transfer leaves…", written for a checker | Fixed in 307eb24f, without the proposed "the only way they can fall", which is false of a square described inward |
| I.37 to I.48, 30; across pages, 25 (I.48) | Elements/BookI/Prop48.lean:17 | 2 | editorial | "Def. 22" without its book | Open: next part, #34 |

### Book II: introduction and front matter

| Finding | Where (file:line at 2e8aecf8) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| Book II, 9; across pages, 19 | mishnah/intro/II.md:9 | 2 | editorial | II.7's "let the figure be drawn" called I.43's figure, where II.7's commentary and the lemma call it II.4's | Fixed in 307eb24f |
| Book II, 10; across pages, 15 and 34 | mishnah/intro/II.md:11 (book/II/index.md:5 against :13) | 2 | material (across pages); editorial (Book II) | "every proposition of Book II rests on Postulate 5", against the generated "Every proof uses the parallel postulate" on the same page; "II.10 cites the postulate by name", where Heath's reference names it | Fixed in 307eb24f (II.10's text calls on the postulate, and Heath's reference names it) and c814e8fb ("every proof in Book II uses Postulate 5") |

### II.1 to II.14

| Finding | Where (file:line at 2e8aecf8) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| Book II, 4; pilot, 9 | review/II/01.toml:49, :55; 03.toml:30; 04.toml:42; 05.toml:48; 09.toml:66; 11.toml:24; 14.toml:36, :48, :60 | 2 | editorial | "now proved from I.13 and Common Notion 3 in `Elements/BookI/Prop13.lean`" on seven pages, a dated history retold on each; II.14 glosses its tacit rules three times | Fixed in 307eb24f (once on II.1, "(I.13)" elsewhere), 206e3080 (II.14's glosses) and a1ddfcf7 (the pilot editor's sentence for Book II's introduction, in other words: "When a straight line set up on a straight line makes one right angle, the other angle it makes is right too, by I.13 and Common Notion 3") |
| Book II, 6 | review/II/04.toml:35; 09.toml:59; Elements/BookII/Rectangles.lean:28 | 2 | editorial | "Done by `Prop43`" and "`Prop47.sq`" on Book II pages, read as II.43 and II.47 | Fixed in 307eb24f: `BookI.Prop43` and `BookI.Prop47.sq` |
| Across pages, 3(a) | mishnah/II/03.md:3 | 2 | editorial | "(Heath, under II.2)" with no page | Fixed in 307eb24f: "(vol. 1, p. 377)" |
| Book II, 7 | mishnah/II/05.md:1 | 2 | editorial | The link to the introduction's "areas" for the gnomon, which the introduction does not explain | Fixed in 307eb24f: the link is to the definitions |
| Book II, 8 | mishnah/II/05.md:3 | 2 | editorial | "met under I.44", a pointer in words alone | Fixed in 307eb24f |
| Book II, 18 | reading/II/06.md:2 | 2 | editorial | "argues, lively and readable, that": adjectives with nothing to attach to | Fixed in fe30d3f3 |
| Book II, 12 | mishnah/II/07.md:1 | 2 | editorial | "though the proof never names those two": ours does; Euclid's text does not | Fixed in 307eb24f |
| Book II, 15 | reading/II/08.md:1 | 2 | editorial | II.8, an identity, said to be an inequality; "mean proportional" unglossed | Fixed in fe30d3f3 |
| Book II, 16; across pages, 3 | reading/II/09.md:2 | 2 | editorial | Klein's *Elementary Mathematics* at its first appearance in Book II, not described | Fixed in fe30d3f3 |
| Book II, 13 | mishnah/II/10.md:1 | 2 | editorial | "a point Heath's figure leaves unnamed": the figure does not draw it | Fixed in 307eb24f |
| Book II, 3 | figures/II/11-idea.svg:3 | 2 | editorial | The red AK is not named in the caption | Fixed in 307eb24f |
| Book II, 2 | figures/II/12-modern.svg:29 | 2 | editorial | "h > 0" narrower than the paragraph's condition, and the zero reads as "o" | Fixed in 307eb24f: the label taken off, since the paragraph states the conditions |
| Across pages, 22 | mishnah/II/12.md:1; mishnah/II/13.md:1 | 2 | editorial | "the rectangle contained by CA and AD", against Heath's comma form | Fixed in 307eb24f |
| Book II, 1 | figures/II/13-modern.svg:34–35 | 2 | material | "0 < d < a" and "h > 0" contradict the paragraph, which proves the identity whether D falls within CB or not | Fixed in 307eb24f: the labels taken off; S25 does not allow "≠" in a modern figure |
| Book II, 14; pilot, 2 | review/II/14.toml:67; figures/II/14.svg | 2 | material (pilot); editorial (Book II) | The figure note says "with the figure A of two triangles" over an A drawn whole, as Heath draws it | Fixed in 307eb24f, by the case rather than a drawn diameter: A is drawn four-sided as in Heath's figure, and the main theorem takes it as the two triangles a diameter divides it into |
| Book II, 17; across pages, 10 | reading/II/14.md:2 | 2 | editorial | "chapter 7", the only such form, with the number unchecked | Fixed in fe30d3f3: "in its chapter "Quadratures"" |

### Across pages

| Finding | Where (file:line at 2e8aecf8) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| I.1 to I.12, 1; I.13 to I.24, 2; across pages, 26 (README) and 27 | docs/briefs/book-I.md:55–60, :154–161; README.md:68; docs/FORMALIZATION.md:224; docs/reports/overlaps.md:13–16, :150–155, :209–212; docs/reports/gaps-book-I.md:256; Elements/Foundations/Tacit/Superposition.lean:16–22 (in flight) | 2, 3 (0 for the catalogue once the change lands) | material | After the superposition replacement these still describe the old rule, and the overlap catalogue keeps rows for I.2, I.3 and I.23, whose records will declare no overlap, which B2 refuses | Open: the replacement has landed (17ae8e2a); the next part reads these files as it left them, and any mend goes to each file's owner, the coordinator for the foundations; all but the docstring are changed again by work in flight, the second axiom wave (#119) among it, #75, #34 |
| I.13 to I.24, 8; I.25 to I.36, 14; I.37 to I.48, 27; Book II, 11; across pages, 35; pilot, 8 | scripts/render.py:1398 (every commentary's heading); README.md:23 | 1 (README: 2) | editorial | "Our commentary: what Euclid assumes, what Lean made us say out loud, and how the result looks by modern means": a retired refrain's kin, a triplet on every page, and a promise of a modern way on pages with none | Open: proposed to the coordinator for scripts/render.py, with README.md:23, #34 |
| I.1 to I.12, 22; I.13 to I.24, 18; I.25 to I.36, 17 | review/I/01.toml:14; 02.toml:34, :40, :46; 03.toml:18; 04.toml:13, :42; 05.toml:23, :29, :35; 06.toml:13; 08.toml:13; 09.toml:32; 11.toml:13; 12.toml:13, :24; 19.toml:13; 20.toml:31; 21.toml:25, :31, :37, :43; 22.toml:20, :26; 26.toml:26, :37; 27.toml:13; 29.toml:13, :24; 31.toml:16 | 2 | editorial | "a rule we assume, not a proof" and its kin, "not a proved lemma", pasted across the notes; I.21's six notes two identical pairs | Fixed in 1eda7896 at I.6, I.9, I.19, I.21, I.22, I.26 and I.31, and in 307eb24f at II.14, with I.21's second pair varied; the gloss "a rule we assume" itself is kept, and the introduction's sentence proposed to replace it waits for mishnah/intro/I.md, held by the second axiom wave (#119); open at I.4, I.8, I.20, I.27 and I.29, whose records were held: next part, #34 |
| Book II, 5; I.25 to I.36, 18; across pages, 23 | review/I/06:35, 09:20, 30:32, 36:28, 37:19, 38:19, 42:24, 44:14, :20, :32, 47:23; review/II/03:12, 05:18, :48, 11:30, :42 | 2 | editorial | Heath's missing reference said three ways ("which Heath does not cite here", "Heath prints no reference", "where Heath cites"), and II.11's clause three times in three notes | Fixed in 1eda7896 (I.36), 307eb24f (I.6, I.9, I.30, I.38, I.42, II.3, II.5, II.11) and 206e3080 (I.47, and the Lean notes of I.6 and I.30); open at I.37 and I.44: next part, #34 |
| I.13 to I.24, 28; I.25 to I.36, 19; I.37 to I.48, 23 | review/I/24.toml:19; 35.toml:12; 43.toml:8; 48.toml:44 | 2 | editorial | "Proclus's" beside the house "Proclus'" | Fixed in 1eda7896 at I.24; open at I.35, I.43 and I.48: next part, I.35's record held by the citation sweep (#32) and the second axiom wave (#119), #34 |
| Across pages, 21 | mishnah/I/18.md:3; mishnah/I/19.md:1; Lean notes and records | 2 | editorial | "a tacit rule of magnitudes" beside "tacit rules of magnitude" and the page's "Laws of magnitude" | Fixed in 307eb24f (the commentaries) and 206e3080 (the Lean notes of I.13, I.17, I.19 and I.25, the records of I.17, I.19 and II.14); I.6's wrapped Lean note in c814e8fb, with the records of I.6, I.25 and I.26; Prop29.lean:59 and I.29's record open: next part, #34 |
| Across pages, 17; pilot, 6 | mishnah/intro/I.md:11, mishnah/intro/II.md:5, mishnah/I/45.md:1, :3, mishnah/II/14.md:1, review/I/45.toml:4, review/II/14.toml:3 | 2 | editorial | I.45's and II.14's restriction said four ways: "supplied" or "given", "non-overlapping" or "lie apart", an unglossed "outline", a "tacit step" | In part: II.14's page and Book II's introduction say it in one set of words, a figure "given with a checked division into triangles", and "given only by its boundary" for "outline" (a1ddfcf7); I.45 and Book I's introduction: next part, I.45's record held by the citation sweep (#32) and the introduction by the second axiom wave (#119); the vocabulary goes into STYLE section 4 with them, #34, #116 |
| Across pages, 16; pilot, 7 | mishnah/I/45.md:3; mishnah/II/14.md:1 | 2 | material (across pages); editorial (pilot) | "David Hilbert proved it": he proved the second of the two unproved facts, and the issue link reads as the citation for his proof | Fixed for II.14 in c814e8fb and a1ddfcf7: the link now stands with what is not yet proved, and Hilbert is said to have proved the second of the two facts; open for I.45: next part, #34, #116 |
| I.25 to I.36, 22; I.37 to I.48, 26; across pages, 29 | docs/STYLE.md section 4 (in flight), against section 7 and S25; figures/I/27-, 29-, 40-, 43-modern.svg | 2 | editorial | After the notation train, a paragraph names a vector in bold while its figure must set it in italic | Open: next part; STYLE section 4 is free now that the notation train has landed, and should say how a modern figure names a vector, #34 |
| Across pages, 20 | mishnah/I/08.md:3; mishnah/I/26.md:7; mishnah/I/44.md:1 | 2 | editorial | "applied" glossed as laying one triangle on another and as building an area on a straight line | Open: not taken up in this part; I.8's commentary, then held, is now free, #34 |
| I.1 to I.12, 31; I.13 to I.24, 30 | figures/I/*.svg and *-idea.svg, figures/II/; scripts/check_style.py:175 | 2 | editorial | Heath's letters italic in the figures at a glance and Euclid's figures, upright in the prose and the modern figures | Resolved on main by other work: upright in every figure since ac6e5389 (pull request #194), and required by S15 and S20 since cba27afa (pull request #196), both for #159; the next part's addendum reads the pass |
| I.1 to I.12, 25; I.13 to I.24, 22; I.25 to I.36, 13 (report); across pages, 32 | docs/reports/figures-against-scans.md:23–36, :45, :48, :49, :54, :55, :65, :68 | 3 | editorial | Rows still say "nowhere yet" and "does not yet name" of lines the records now carry; I.6 misread | Fixed in 307eb24f: dated status notes, and the I.6 row corrected; the rows rewritten to how the records stand, with the commits read at, in 9b7dad70 |
| Across pages, 31 | docs/STYLE.md:488, :500, :569, and S14, S15 and S24 at :665, :666, :675; scripts/check_style.py:100–101 | 3 | editorial | The figure titles written for Book I alone (#145) | Fixed in 307eb24f, with examples from Books II and III; the script's own header still says "I.N": open, for the coordinator, #145 |
| Across pages, 30 | docs/STYLE.md section 5 against section 8, item 10 | 3 | editorial | Italics in an enunciation: section 5 and the checklist disagreed | Fixed in 307eb24f |
| Across pages, 36 | README.md:40 | 2 | editorial | The page's order leaves out the figure at a glance and the further reading | Open: README.md is held for its owner; for the coordinator, #34 |
| Across pages, 39 | review/terms.toml:18–28 | 3 | editorial | The tags two-triangles, three-pieces and adjacent-bases are used by no record | Open: not taken up in this part, #34 |
| Across pages, 13 | the reading lines; docs/references.bib | 3 | editorial | STYLE asks for a chapter "only where checked", and nothing records which were checked | Open: not taken up in this part; some chapters were checked against their contents and one dropped (fe30d3f3), but no record was written, #34 |
| Across pages, 7 | reading/I/02.md:1; 29.md:1; reading/II/11.md:3 | 2 | editorial | Byrne, Bolyai and Lobachevsky, and Gauss first named by surname alone | Fixed in fe30d3f3 |
| I.1 to I.12, 30; I.25 to I.36, 5, 6 and 7; I.37 to I.48, 6 and 7; across pages, 1 | reading/I/26.md:2; 27.md:2; 33.md:1; 40.md:2; 48.md:1 | 2 | editorial | "(also on …)" links a repeat, not the first appearance (#144) | Fixed in fe30d3f3 |
| I.13 to I.24, 25; I.25 to I.36, 8; I.37 to I.48, 8; across pages, 2 and 12 | reading/I/31.md:1; reading/I/39.md:2 | 2 | editorial | Repeats of Courant and Robbins and of Velleman with neither words nor a link; I.39 says `by_contra` where our Lean writes `Classical.byContradiction` | Fixed in fe30d3f3 |
| I.1 to I.12, 27; I.25 to I.36, 10; I.37 to I.48, 14; across pages, 11 | reading/I/ and reading/II/ | 2 | editorial | Moulds: stacked praise, "short" and "friendly" again and again, "a much-loved classic" for two books, "about eighty friendly pages" three times, Artmann's description word for word on four pages | Fixed in fe30d3f3 |
| I.1 to I.12, 28; I.37 to I.48, 9, 10 and 11; across pages, 8 and 9 | reading/I/04, 06, 09, 14, 23, 25, 46, 47; reading/II/09, 12 | 2 | editorial | The year given is the first edition's, where the link is a later one, and Nahin and Morrow were to be dated two ways | Fixed in fe30d3f3: the linked year, with the first publication's at a first appearance; Coxeter's and Loomis' as reprints of second editions, since "first published 1969" and "1940" would be false; Maor's *Trigonometric Delights* (I.4, I.25, II.12) in c814e8fb, "(2020 paperback; first published 1998)" at a first appearance; the first appearances of Nahin (I.11) and Morrow (I.20), held while the notation train was in flight: next part, #144 |

## The pilot editor's notes

The pilot editor read II.1, I.45, II.14 and III.24 one after another, at 2e8aecf8, as #34 asks. Five notes are material and fourteen editorial.

Notes 1, 3 to 7, 12 and 13 concern I.45 and II.14 together. II.14's half of notes 3 to 7 is mended (c814e8fb, a1ddfcf7): its page and Book II's introduction tell the restriction in one set of words, and its main theorem is said to take its two triangles unchecked. I.45's half was held for the notation train, which has landed; it is for the next part, which is to tell I.45 as II.14 now reads, in the parallel wording that the writers of c814e8fb and a1ddfcf7 drafted from II.14's. I.45's record is still held by the citation sweep (#32), and Book I's introduction by the second axiom wave (#119).

Notes 8 and 11 are changes to scripts/render.py, a protected file this work does not change. They are open, and proposed to the coordinator. Notes 16 to 18 are on III.24 and provisional. Note 19 is docs/examples.md, which is held for its owner.

| Note | Page | Grade | What | Resolution |
|---|---|---|---|---|
| 1 | I.45 | material | The notation train's hunk for review/I/45.toml was cut from an older base: it would stamp a commit that is not an ancestor of main, with the Lean hash of an older Prop45.lean | Open: next part. The notation train has landed (09bc89f3); I.45's record, held by the citation sweep (#32), is to be read as it stands and stamped again once that lands, #34 |
| 2 | II.14 | material | The figure note says "two triangles" over a figure that draws A whole | Fixed in 307eb24f, by the case rather than the line the note proposed (row above) |
| 3 | I.45, II.14 | material | Both commentaries say the main theorem "takes the figure", where it takes two triangles unchecked; I.45's reason for avoiding AC implies DB is safe; I.45's modern way needs A and C on opposite sides of DB | Fixed for II.14 in c814e8fb and a1ddfcf7; open for I.45: next part, #34, #116 |
| 4 | I.45, II.14 | material | The Statement and Extra hypotheses rows describe the companions, not the theorem shown, in noun piles ("outline coverage and independence of division remain unproved"), so the limitation is not stated plainly | Fixed for II.14: the Statement row in c814e8fb and a1ddfcf7, which names `Prop14.square`, and the Extra hypotheses row and the words beside its badge in a1ddfcf7; I.45's rows open: next part, its record held by the citation sweep (#32), #34, #116 |
| 5 | I.45, II.14 | editorial | Representation rows of 256 and 207 words, telling the main theorem's scope last and repeating the Statement row | In part: II.14's row now tells the main theorem's scope first and no longer repeats the Statement row, at 214 words (a1ddfcf7); I.45's open: next part, its record held by the citation sweep (#32), #34, #116 |
| 6 | I.45, II.14, both introductions | editorial | One limitation under several names; a vocabulary proposed for STYLE section 4 | In part: II.14 and Book II's introduction in one set of words (a1ddfcf7); I.45, Book I's introduction and STYLE section 4: next part, #34, #116 |
| 7 | I.45, II.14 | editorial | "David Hilbert proved it … (#116)": the link reads as the citation for his proof | Fixed for II.14 in c814e8fb and a1ddfcf7; open for I.45: next part, #34, #116 |
| 8 | all four | editorial | The generated line over every commentary | Open: scripts/render.py, proposed to the coordinator, #34 |
| 9 | II.1, II.14 | editorial | "now proved" eight times across seven records; II.14 glosses its tacit rules three times | Fixed in 307eb24f and 206e3080, and the sentence for Book II's introduction in a1ddfcf7 |
| 10 | II.1 | editorial | The caption says "each piece", where Heath's word is "segments" | Fixed in 206e3080; STYLE section 4 now allows Heath's segments of a straight line cut at a point, in Book II and III.35 (9b7dad70) |
| 11 | II.1 | editorial | Four notes in a row open "**Done by `Rectangle.of_right`.**"; proposed: render.py leads a repeated helper "Again by" | Open: scripts/render.py, proposed to the coordinator, #34 |
| 12 | I.45 | editorial | Two notes out of the house voice: "the Lean requests I.44's parallelogram", and "the representation note", a field a reader does not see | Open: next part; I.45's record is held by the citation sweep (#32), #34, #116 |
| 13 | I.45 | editorial | The figure note mentions only Heath, where the figure at a glance draws the parallelogram apart and Euclid's figure puts H on D | In part: the caption at a glance says it is drawn apart, as Heath draws it (307eb24f); the figure note open: next part, I.45's record held by the citation sweep (#32), #34 |
| 14 | II.14 | editorial | A docstring gives the reason the wrong way round: "written out again, for it does not cite II.14" | Fixed in 206e3080 |
| 15 | II.14 | editorial | The record's commit was restamped and its run left naming the older commit | Fixed in 4a7bc952: the record was re-read, and its commit and run stamped together |
| 16 | III.24 (provisional) | material | The caption claims the segments are equal while the statement leaves that in Euclid's words; two sentences will be false once III.24 cites placement; its scope and route fail ACCEPTANCE P3 | Open: Book III, for III.24's restatement, #34 |
| 17 | III.24 (provisional), and STYLE | editorial | No note names the case drawn; a STYLE section 7 sentence proposed for cases split by a lemma | Open: Book III; the STYLE sentence waits with III.24's record, #34, #30 |
| 18 | III.24 (provisional) | editorial | All four paragraphs before the modern way open on a bold lead | Open: Book III, #34 |
| 19 | docs/examples.md | editorial | No reviewed example of a restricted construction, and lines 123–124 are overtaken | Open: docs/examples.md is held for its owner; to be written once I.45 and II.14 tell the restriction alike, #34 |

## Further reading

**The rule, as now applied (#144).** In each book separately, and in page order:

- A work is described in full where it first appears in that book: what it is, and what this page's reader finds there.
- Each later line keeps a few words on what the work is, or links the page where it is described, "(also on [I.18](../../book/I/18.md))". The link goes directly to the first appearance in the same book, never to another repeat, and never to another book.
- No line points back in words alone.
- The author is named in full, and the title and the link are as docs/reading.md gives them.
- The year is the linked edition's. Where that edition is a later one, a first appearance adds the first publication, "(2019; first published 1994)", and a repeat gives the linked year alone.
- "Free online" stands where the list says **Free**.
- A chapter is given only where the list or a checked contents page gives it.
- The lines of a book do not fall into one mould.

This is STYLE section 6 read strictly. #144 also asks for a book-aware check with regression cases: a chain, a wrong target, an undescribed first appearance. That check would sit under scripts/, which this work does not change, so #144 stays open for it.

**The map.** This was built again from reading/ as it stood at 206e3080, and checked again at b78e8ae5: the later changes (c814e8fb, a1ddfcf7, and the notation train's two years on I.11 and I.20) change years and descriptions, not which works appear where or what each line links.

- **Book I.** 48 works make their first appearance, each described in full. There are 46 later mentions: 43 link the first appearance directly, and 3 keep a few words on the work instead (Hilbert on I.36, Descartes on I.39, Morrow on I.47).
- **Book II.** 26 works make their first appearance, each described in full. There are 3 later mentions: Nelsen on II.8 and Fowler on II.10 link theirs, and Heath's *History* on II.6 keeps a few words.
- No link goes to a repeat or crosses a book, and no line points back in words alone.
- The most-used work, Stillwell's *The Four Pillars of Geometry*, is on 6 of Book I's 48 pages.

| Work | Book I: first | Book I: later | Book II: first | Book II: later |
|---|---|---|---|---|
| Needham, *Visual Complex Analysis* | I.1 | I.13, I.16, I.32 | none | none |
| Hartshorne, *Geometry: Euclid and Beyond* | I.1 | I.22, I.35 | none | none |
| Rougeux, *Byrne's Euclid* | I.1 | none | none | none |
| Sanderson, *Essence of linear algebra* | I.2 | I.11, I.31, I.37, I.48 | none | none |
| Yaglom, *Geometric Transformations I* | I.2 | I.5, I.34 | none | none |
| Stillwell, *The Four Pillars of Geometry* | I.3 | I.12, I.17, I.19, I.27, I.40 | II.4 | none |
| Martin, *Transformation Geometry* | I.4 | I.15, I.33 | none | none |
| Maor, *Trigonometric Delights* | I.4 | I.25 | II.12 | none |
| Coxeter, *Introduction to Geometry* | I.6 | none | none | none |
| Velleman, *How to Prove It* | I.6 | I.25 | none | none |
| Descartes, *The Geometry*, tr. Smith and Latham | I.7 | I.39 (words) | II.13 | none |
| Dodgson, *Euclid and His Modern Rivals* | I.7 | I.29 | none | none |
| Hilbert, *The Foundations of Geometry* | I.8 | I.27; I.36 (words) | none | none |
| Klein, the Erlangen Programme | I.8 | I.34 | none | none |
| Hahn, *Complex Numbers and Geometry* | I.9 | I.14, I.23, I.46 | none | none |
| Klein, *Famous Problems of Elementary Geometry* | I.9 | I.45 | II.11 | none |
| Richeson, *Tales of Impossibility* | I.9 | I.42 | II.14 | none |
| Greenberg, *Euclidean and Non-Euclidean Geometries* | I.10 | I.16, I.26, I.29 | none | none |
| Klein, *Elementary Mathematics from a Higher Standpoint, II* | I.10 | I.35 | II.9 | none |
| Nahin, *An Imaginary Tale* | I.11 | I.46 | none | none |
| Van Brummelen, *Heavenly Mathematics* | I.12 | none | none | none |
| Avigad and others, *Theorem Proving in Lean 4* | I.14 | none | none | none |
| Heath, *A History of Greek Mathematics* | I.15 | I.44 | II.3 | II.6 (words) |
| Bonola, *Non-Euclidean Geometry* | I.17 | I.30 | none | none |
| Kedlaya, *Geometry Unbound* | I.18 | none | II.13 | none |
| Mueller, *Philosophy of Mathematics and Deductive Structure* | I.18 | I.38 | II.2 | none |
| Velleman, *How To Prove It with Lean* | I.19 | I.39 | none | none |
| Steele, *The Cauchy-Schwarz Master Class* | I.20 | none | II.8 | none |
| Morrow, Proclus' *Commentary* | I.20 | I.47 (words) | none | none |
| Manders, "The Euclidean Diagram" | I.21 | I.43 | none | none |
| Artmann, *Euclid: The Creation of Mathematics* | I.21 | I.28, I.33 | II.1 | none |
| Courant and Robbins, *What Is Mathematics?* | I.22 | I.31 | II.14 | none |
| Miller, *Euclid and His Twentieth Century Rivals* | I.23 | none | none | none |
| Van Brummelen, *The Mathematics of the Heavens and the Earth* | I.24 | I.26 | none | none |
| Wiedijk, "Formalizing 100 Theorems" | I.32 | none | II.10 | none |
| LaFantasie, "Lincoln, Euclid, and the Satisfaction of Success" | I.32 | none | none | none |
| Boltyanskii, *Equivalent and Equidecomposable Figures* | I.36 | I.42 | none | none |
| Chou, Gao and Zhang, *Machine Proofs in Geometry* | I.37 | none | none | none |
| Aigner and Ziegler, *Proofs from THE BOOK* | I.38 | none | none | none |
| Wardhaugh, *Encounters with Euclid* | I.40 | none | II.3 | none |
| Braden, "The Surveyor's Area Formula" | I.41 | none | none | none |
| Frederickson, *Dissections: Plane & Fancy* | I.41 | none | none | none |
| Nelsen, *Proofs Without Words* | I.43 | none | II.1 | II.8 |
| Høyrup, *Algebra in Cuneiform* | I.44 | none | II.5 | none |
| Høyrup, "What is 'geometric algebra'" | I.45 | none | II.2 | none |
| Maor, *The Pythagorean Theorem* | I.47 | none | II.9 | none |
| Loomis, *The Pythagorean Proposition* | I.47 | none | none | none |
| Stillwell, *Mathematics and Its History* | I.48 | none | II.10 | none |
| Fowler, *The Mathematics of Plato's Academy* | none | none | II.4 | II.10 |
| Casselman, "The oldest diagram from Euclid" | none | none | II.5 | none |
| Blåsjö, "In Defence of Geometrical Algebra" | none | none | II.6 | none |
| Unguru, "On the Need to Rewrite the History of Greek Mathematics" | none | none | II.7 | none |
| Christianidis (ed.), *Classics in the History of Greek Mathematics* | none | none | II.7 | none |
| Herz-Fischler, *A Mathematical History of the Golden Number* | none | none | II.11 | none |
| Markowsky, "Misconceptions about the Golden Ratio" | none | none | II.11 | none |

**The exceptions that remain:**

- **Nahin and Morrow.** Their first appearances, I.11 and I.20, were held while the notation train was in flight. It has landed with the long form, "(2010; first published 1998)" on I.11 and "(1992 paperback; first published 1970)" on I.20, and the next part reads them. Their repeats give the linked year: I.46 "(2010)" and I.47 "(1992 paperback)".
- **Repeats that keep words rather than a link**: I.36, I.39, I.47 and II.6. STYLE section 6 allows this.
- **The moulds.** "Friendly" now stands only on I.20, whose line the notation train held, and on II.10; "a much-loved classic" only at Courant and Robbins' first appearance in Book II; and Artmann's "walk through all thirteen books" only at his first appearance in each book.
- **Chapter checks.** Which chapters were checked against a contents page is still recorded nowhere (across pages, 13).

Three exceptions named when the map was first made are settled: Maor's *Trigonometric Delights* gives its linked year, "(2020 paperback; first published 1998)" on I.4 and II.12 and "(2020 paperback)" on I.25 (c814e8fb); the copied descriptions of Kedlaya on I.18, Wardhaugh on I.40 and Maor on II.12, and I.40's echo of I.19's Stillwell line, are in words of their own (c814e8fb, a1ddfcf7); and docs/reading.md marks LaFantasie's article **Free** (c814e8fb).

## The habits removed

For #46: the habits of machine-written prose that the language passes (pull requests #111, on I.1 to I.24, and #115, on I.25 to I.48 and Book II) and this read-through removed from Books I and II are now listed in STYLE section 4, "Tightening the language": thirteen habits, each with one example from the history of mishnah/, reading/, the records and the Lean notes (b9245195, with the I.41 example worded more exactly in 9b7dad70). The list there merges the twelve this report first proposed with the six habits, with eight examples, the notation train had given that paragraph:

- Both gave I.41 for a recap in threes, and the two are one bullet.
- For announcing sentences, the notation train's I.33 stands; this report's I.4 was dropped, since I.4's page was being changed by the superposition work and its wording might change.
- For a claim surer than its evidence, this report's I.18, "We prove both", replaces the notation train's example, which came from a Book III reading line.
- This report's change-log on a reader's page (I.13's docstring) and its dated "now proved" clause (II.3) are one bullet, with I.13's example.
- This report's mould in the reading lines is folded into "One opening for every reading line" and "Inflated praise", and its Coxeter example is dropped, since its "after" still praises.
- This report's aside written for a checker (I.47) is dropped: the mend there was chiefly a correction of fact, and section 1 already rules such asides out.
- The notation train's other examples, I.27's "The proposition is old" for announcing sentences and II.1's "does its multiplying" for padded phrases, are dropped, to keep one example for each habit.
- The notation train's two qualifications close the list: a list that supplies necessary cases stays, and so does a qualification that belongs to the claim.

The last re-reader found every "before" in the history and every "after" in the files as they stand. It noted that "The proof is short", I.33's example, was written and cut within one pull request, so it never stood on main; the example is still true as history.

Of the vague hedge that STYLE section 1 rules out ("note that", "strictly speaking", "it is worth noting"), no instance was left in Books I and II to remove: S4 refuses them. The commoner fault was the opposite, a claim surer than its evidence, such as I.18's "We prove both" of a step we assume. Faults of that kind are findings of fact, in the table above.

## Still open

The next part is the addendum below, read at 99359055 and 275ae830: it gives item 1's addendum, closes item 1's findings on pages now free and item 2's commentary, caption and vocabulary, and closes, of the rows of "The material findings left" that wait for it, those for I.44 (I.37 to I.48, 3 and 4), for I.45's modern way and commentary (I.37 to I.48, 1; across pages, 16; pilot, 3) and for the pilot editor's note 1, with the first row save Book I's gap catalogue; the findings on files still held, item 6's lines for I.4 and I.27 among them, stay open, as the addendum's own "Still open" says.

Every open item, with its issue.

1. **The next part of this read-through**, a second train under #34. It reads the changes that landed on main after 2e8aecf8 and the findings that were held; this part's findings on those pages stay open until then.
   - **The addendum.** #34's second condition asks that nothing under book/, mishnah/, Elements/ or figures/ change on main after the commit read, save this read-through's own fixes, or that a dated addendum read each later change. Four pull requests have changed Books I and II there between 2e8aecf8 and main at 8674bce2, the last main this branch has merged: the superposition replacement (#191, at 17ae8e2a, for #75), the notation train (#193, at 09bc89f3, for #48), the upright figure letters (#194, at ac6e5389, for #159) and train C6a (#240, at 8674bce2), a Book III train. In Books I and II, #240 adds a Book I helper, Elements/BookI/HelpersTriangles.lean (`Prop20.collinear_congr` and `Prop20.between_congr` among its four theorems), and changes the 62 proposition pages, book/I/01.md to 48.md and book/II/01.md to 14.md, by shifting their links into Elements/Foundations/Tacit/Constructions.lean; the books' front and index pages are unchanged. In the foundations they share, it adds a tacit rule of our own to Tacit/Constructions.lean, `exists_centre`, whose content is Definitions I.15 and I.16, and changes documentation: Definitions.lean's module note now names that rule, and Words.lean's docstring of `CirclesMeet`, which I.22 uses, now reads "Two circles that meet at two points". Book Zero, which every proposition file imports, also imports two new modules for Book III, Regions and Chords. The addendum reads their changes to Books I and II and to the foundations they rest on, and any later one that lands before the release. None of #240's changes has yet been read by this read-through; they wait for the second part.
   - **Findings on pages now free**, the two changes having landed:
     - from the superposition replacement: the new wording of I.23 and its unglossed terms; I.14's "as in I.4"; I.23's Lean note, the mend left out of 1eda7896; I.44's two reasons for one step (material), its new note and "Heath does not cite"; the Lean notes of `Prop44.place` and `Prop46.side_eq` (material); and the rule's docstring, which the replacement was to bring into line (material), for the coordinator, who owns the foundations;
     - from the notation train: I.20's modern way; the definitions without their book and the plural "magnitudes" in Prop29.lean and Prop48.lean, and I.29's record, with its "not a proof"; "Proclus's" at I.43 and I.48; I.37's notes, with "Heath does not cite" and Heiberg's first naming there; the commentaries of I.39, I.40 and I.48; I.45's commentary; STYLE section 4's vector names and the restriction's vocabulary; and the years of Nahin (I.11) and Morrow (I.20), with the first re-readers' two points on them.
   - **Findings on files still held** by a change in flight:
     - the per-law superposition change (#150), which holds Prop04.lean, Prop08.lean and the records of I.4 and I.8: I.4's figure note (material, #30), the notes of I.4 and I.8 and their stock tag, Heiberg's and Savile's first naming at I.4, and I.8's backticked letters;
     - the citation sweep (#32), which holds the records of I.5, I.6, I.10, I.11, I.12, I.16, I.20, I.21, I.22, I.26, I.33, I.34, I.35, I.39, I.40, I.45 and I.47 and of II.6, II.8, II.9 and II.10, with Book I's Prop10.lean, Prop11.lean and Prop45.lean and Book II's Prop06.lean and Prop08.lean: I.11's Lean note, I.20's case and stock tag, the notes of I.39 and I.40, I.45's record (the pilot editor's notes 1, 4, 5, 12 and 13), and "Proclus's" at I.35;
     - the second axiom wave (#119), which holds Book I's introduction, the commentaries of I.4, I.5, I.8 and I.12, Prop05.lean, the records of I.2, I.5, I.11, I.12, I.22, I.27, I.31 and I.35, and those of II.10 and II.14, and, having merged the per-law superposition change, that change's files too: the new wording of I.4 and I.8, and I.8's Hilbert sentence, in the first code review's words; the introduction's new wording from the superposition replacement, its bare "(p. 316)", its "bracket", its two asides, the order of the page it gives and the sentence proposed to replace the gloss "a rule we assume"; I.27's figure note (material, #30) and stock tag; and, with the citation sweep, I.5's and I.11's joins and I.11's passage key;
     - several changes at once, which hold the documents the superposition replacement was to bring into line (material), each for its owner: the second axiom wave (#119) changes the brief, README.md, FORMALIZATION and the overlap and gap catalogues; the citation sweep (#32) changes README.md and FORMALIZATION too, the per-law superposition change (#150) FORMALIZATION, and the change for #168, which rewrites a step of Prop14.lean, the overlap catalogue.
2. **I.45 told as II.14 now is** (#34, #116).
   - These are the pilot editor's notes 3 to 7, 12 and 13, with note 1 on I.45's record; the reader of I.37 to I.48's findings 1, 18 and 19; and the cross-page reader's findings 16 and 17. Four of them are material, and note 1 is material too.
   - II.14's page and Book II's introduction now tell the restriction in one set of words: a figure given with a checked division into triangles; the main theorem taking its two triangles unchecked; and what is not yet proved, that every rectilineal figure, given only by its boundary, has such a division, and that another division gives the same area (a1ddfcf7).
   - A writer has drafted the parallel wording for I.45's commentary, record, caption and Lean notes, and for Book I's introduction, to be applied in the next part. I.45's commentary and caption are free; its record and Prop45.lean are held by the citation sweep (#32), and the introduction by the second axiom wave (#119). The vocabulary goes into STYLE section 4 with them (note 6).
   - The limitation itself, the proof for a figure given only by its boundary, is #116.
3. **Book III's read** (#34).
   - The pages of Book III are read in a later part of this read-through, once its moves land.
   - The pilot editor's notes 16 to 18 on III.24 are provisional until then.
   - Points found along the way that wait for that read: mishnah/III/32.md:3's bare "(p. 67)"; mishnah/III/28.md:5's "where Heath cites"; Maor's "(1998)" for the 2020 paperback at reading/III/26.md:2 and III/28.md:2, and III.26's line in the reading list's own words; and III.28's "(also on [I.25])", which points outside its book (#144).
   - Book III's italics are not yet audited.
4. **Proposals to the coordinator**, since this work changes no file under scripts/ or tests/:
   - scripts/render.py (#34): the generated line over every commentary (note 8, with five readers' findings and README.md:23); "Again by" for a repeated helper (note 11); Book I's front page, which maps Definitions I.2 and I.3 to `Line` and lists `quadArea` for Definition I.14 (material); its pages with no scan leaf; and the italic "whole", "restricted" and "in part";
   - the header of scripts/check_style.py, which still writes "I.N at a glance" and "Euclid I.N: …" (#145);
   - a book-aware check of the reading lines, with regression cases for a chain, a wrong target and an undescribed first appearance (#144);
   - a font for digits in the modern figures (#34). Georgia's old-style figures make I.16's "a + 1" read "a + ı" and I.1's "0" read "o" at the page's width, and set the 1 of I.43's "(1 − s)u" and "(1 − t)v" the same way. Georgia has no lining figures to switch on, in either renderer tried, and S24 and S25 accept only Georgia, which STYLE section 7 also sets. The writer proposes allowing a font with lining figures, as Times New Roman has, on a modern figure's text that holds a digit, in S24, S25 and STYLE section 7.
5. **Files held for their owners:**
   - README.md:40's order of the page, and README.md:23's echo of the generated line (#34);
   - docs/examples.md's example of a restricted construction, to be written once I.45 and II.14 tell the restriction alike (note 19);
   - "tacit law of magnitudes" in the gap catalogue (docs/reports/gaps-book-I.md:114, :139, :188), and "laws of magnitudes" in Book Zero and the gap catalogues, against "rule of magnitude" on the pages, which the later readers found (#46).
6. **Points not taken up in this part** (#34). These need a writer or a decision:
   - "applied" glossed two ways (across pages, 20);
   - the three unused tags in review/terms.toml (across pages, 39);
   - a record of which chapters were checked (across pages, 13);
   - "cut" for figures: Book II's introduction (:13, :15) and I.34's caption say a diameter "cuts" a figure, where II.14's page now says "divides". A sweep to "divide" waits for the vocabulary the pilot editor proposes for STYLE section 4 (note 6);
   - II.11's caption, "(Drawn 89 to 144: no whole numbers fit.)", which the last re-reader would end "fit exactly" and judged harmless as it stands;
   - the lines the scans report proposes for I.4's and I.27's records (#30). They are material, and were not written in this part because both records were held; they still are, I.4's by the per-law superposition change (#150) and the second axiom wave (#119), and I.27's by the second axiom wave, and the lines go with the next part (item 1).
7. **The book acceptance records** (#156). On main at 8674bce2, docs/reports/acceptance/ holds neither book-I.toml nor book-II.toml, so neither book can yet record a pass.
   - **B3 (read-through)** needs:
     - this report on main;
     - every blocking or material finding resolved by a commit on main: once this branch lands, 10 of the 26 material findings that stand will be, and 16 will not ("The material findings left"); the readers graded 27 material, and I.7's is withdrawn ("In short");
     - the dated addendum of item 1, reading each change under book/, mishnah/, Elements/ or figures/ after 2e8aecf8 other than this read-through's own fixes;
     - the [read-through] table of each record, citing this report as its evidence.

     When this branch merged main, at 2853075b, main stood at e7ffaf68, fourteen pull requests after 2e8aecf8. Of them, only #191, #193 and #194 change book/, mishnah/, Elements/ or figures/. It merged main again at b2c30b6d, at 6e0cdd27, fifteen pull requests after 2e8aecf8; the fifteenth, #208, changes none of them. At cd5ad5c3 it merged main at 554dfb0f, eighteen pull requests after 2e8aecf8; the three new ones, #219, #232 and #239, change none of them. At e7faa2fd it merged main at 8674bce2, nineteen after 2e8aecf8; the nineteenth, #240, changes book/, mishnah/ and Elements/: for Books I and II, a new Book I helper, the links of the 62 proposition pages (not the front or index pages), a new tacit rule, `exists_centre`, and the documentation of Definitions.lean and Words.lean, all for the addendum (item 1).
   - **B4 (limitations)** needs I.45's limitation stated plainly where it occurs, as II.14's now is (the pilot editor's notes 3 and 4; item 2); a limitations review against docs/ACCEPTANCE.md, "The limitations allowed", for the record's evidence; and the limitation itself waits on #116.
   - Book III's record waits on Book III's read, and its B4 on #57 (III.16 and III.31) as well.
8. **The seventeen records shared with work in flight** (#34, #32, #119, #168). The records of I.6, I.10, I.12, I.16, I.21, I.22, I.26, I.31, I.33, I.34, I.47, II.5, II.6, II.8, II.9, II.10 and II.14 carry this read-through's stamps and are changed by the citation sweep (#32), the second axiom wave (#119) or the change for #168 (II.5's and II.14's). The coordinator sets the order of landing; whichever change lands second has each shared record re-read and stamped again (material).
9. **Six more stamped records shared with the cross-family sign-off** (#34, #220). Beyond the seventeen of item 8, the fourth code review found that two sign-off branches for #220 change the records of I.13, I.14, I.24, I.30, I.32 and I.43, which carry this read-through's stamps. The order of landing, and any independent re-reading it calls for, are the coordinator's.

## Re-read and stamped

Seven re-readers read the mends, each Claude Opus 5.5, and none of them wrote or prompted the mends. They read in three rounds, each at the commit that carried the mends it read, and each stamped the records it read that it was given to stamp, with the reviewer "Claude Opus 5.5, independent reader". A stamp names the revision its reader read. Main's changes merged into this branch after those revisions, the upright figure letters (pull request #194) among them, are read in this read-through's second part, a dated addendum on its own branch (#34); no record here was stamped by anyone but its reader.

### At 206e3080: four re-readers

Four re-readers read every mend of the first four commits at 206e3080. They covered:

- I.2 to I.19;
- I.20 to I.36;
- I.37 to I.48, with STYLE sections 5, 7 and 8 and the report on figures against Heath's scans;
- Book II, with its introduction and the module note of Elements/BookII/Rectangles.lean.

Each read the changed page against Heath's text and the OCR, against the Lean and against docs/reading.md and references.bib. They rendered every changed figure and looked at it, and set the changed figure notes against Heath's leaves. Among the things they checked:

- I.6's and I.14's figure notes against n275 and n296, and I.17's case against n302;
- I.43's new labels against the figure's coordinates;
- I.45's caption against n365;
- the eight example titles in STYLE against the figures' own titles;
- every dated note of the scans report against the records.

**Every mend was confirmed.** They stamped the 42 records whose page changed and which they were given to stamp, in 4a7bc952, with the run "brief 0005 stage 5, read-through 02 (#34), independent re-read of the mends at 206e3080". The records stamped are those of:

- I.6, I.7, I.9, I.10 and I.12 to I.19;
- I.21, I.22, I.24 to I.26, I.28, I.30 to I.34 and I.36;
- I.38, I.41, I.42, I.46 and I.47;
- II.1 and II.3 to II.14.

The pages whose records the two changes then in flight held were read and confirmed, and not stamped: I.2 to I.5, I.8, I.11, I.20, I.23, I.27, I.29, I.35, I.37, I.39, I.40, I.43 to I.45 and I.48. Five records the second axiom wave was already changing, I.12, I.22, I.31, II.10 and II.14, were stamped; the end of this section says what that asks. After the stamps, `lake build` succeeded, check_style passed, and check_fidelity reported that all 99 propositions quote Heath exactly and that the 99 review records hold.

The re-readers found no blocking or material point. Their nineteen editorial findings, at 206e3080:

| Finding | Where (file:line at 206e3080) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| Re-reader of I.2 to I.19, F1 | review/I/13.toml:9 | 2 | editorial | The route note leaves out that an angle of a triangle is greater than nothing (`Triangle.angle_pos`), which both helpers use | Fixed in c814e8fb |
| Re-reader of I.2 to I.19, F2 | Elements/BookI/Prop06.lean:62–63; review/I/06.toml:13 | 2 | editorial | "a tacit rule of magnitudes", missed because it wraps a line; I.6's note shaped unlike I.17's and I.19's | Fixed in c814e8fb |
| Re-reader of I.2 to I.19, F3; re-reader of I.20 to I.36, 3 (year) | reading/I/04.md:2; reading/I/25.md:1; reading/II/12.md:1 | 2 | editorial | Maor's *Trigonometric Delights* given "(1998)", where the link appears to be the 2020 paperback | Fixed in c814e8fb |
| Re-reader of I.2 to I.19, F4 | reading/I/18.md:1 | 2 | editorial | Kedlaya's line repeats docs/reading.md's sentence almost word for word | Fixed in c814e8fb |
| Re-reader of I.20 to I.36, 1 | mishnah/I/24.md:1 | 2 | editorial | "He said as much under I.2" can be read as Euclid or Simson | Fixed in c814e8fb |
| Re-reader of I.20 to I.36, 2 | mishnah/I/36.md:5 | 2 | editorial | Heath hedges, "Apparently the end of the former and the beginning of the latter are missing" (vol. 1, p. 332), and the new sentence does not | Fixed in c814e8fb |
| Re-reader of I.20 to I.36, 3 (chords) | reading/I/25.md:1 | 2 | editorial | "the Greek tables of chords", where STYLE section 4 keeps "chord" out of our prose | Fixed in c814e8fb |
| Re-reader of I.20 to I.36, 4 | docs/reading.md:93–96 | 3 | editorial | LaFantasie's article is free at its link, and the list does not mark it **Free** | Fixed in c814e8fb |
| Re-reader of I.37 to I.48, F1 | reading/I/11.md:2 | 2 | editorial | Nahin "(1998)" on I.11, where its repeat on I.46 now gives the linked "(2010)" | Open: next part; reading/I/11.md was held for the notation train, which has landed with "(2010; first published 1998)", #34 |
| Re-reader of I.37 to I.48, F2 | reading/I/20.md:2 | 2 | editorial | Morrow "(1970)" on I.20, where its repeat on I.47 now gives "(1992 paperback)" | Open: next part; reading/I/20.md was held for the notation train, which has landed with "(1992 paperback; first published 1970)", #34 |
| Re-reader of I.37 to I.48, F3 | mishnah/I/41.md:1 | 2 | editorial | The closing phrase repeats the Statement row word for word | Declined: the re-reader judged that the sentence earns its place by giving the reason, and asked for no change |
| Re-reader of I.37 to I.48, F4 | reading/I/40.md:1, :2 | 2 | editorial | Wardhaugh's line copies docs/reading.md word for word, with 21 words before its verb; I.40's Stillwell line echoes I.19's | Fixed in c814e8fb |
| Re-reader of I.37 to I.48, F5 | mishnah/intro/I.md:9; scripts/check_style.py:100–101 | 2, 3 | editorial | The new rule on volumes is not yet met at the introduction's "(p. 316)"; the script's header still says "I.N" | Open: the introduction for the next part, held by the second axiom wave (#119); the script for the coordinator, #34, #145 |
| Re-reader of I.37 to I.48, F6 | docs/reports/figures-against-scans.md:5 | 3 | editorial | "Two of Book I's lines are not yet carried", where line 27 and I.27's row call I.27 carried in part | Fixed in c814e8fb |
| Re-reader of Book II, F1 | review/II/09.toml:18, :60; review/II/11.toml:12 | 2 | editorial | "without a reference here" said of Euclid, not of Heath | Fixed in c814e8fb |
| Re-reader of Book II, F2 | mishnah/intro/II.md:11 | 2 | editorial | "every proposition of Book II rests on Postulate 5", the half of the cross-page reader's finding 15 not yet mended | Fixed in c814e8fb |
| Re-reader of Book II, F3 | mishnah/II/14.md:1; review/II/14.toml:7 | 2 | editorial (the pilot editor graded these material) | II.14's half of the pilot editor's notes 3, 4 and 7 and the cross-page reader's finding 16: the main theorem said to take the figure, the "tacit step" and the issue link, and the Statement row's noun pile | Fixed in c814e8fb, and told in one set of words in a1ddfcf7, for II.14; I.45's half: next part, #116 |
| Re-reader of Book II, F4 | mishnah/II/01.md:3 | 2 | editorial | "as Heath remarks under II.2" without the page that II.3 now gives for the same note | Fixed in c814e8fb |
| Re-reader of Book II, F5 | mishnah/II/12.md:1; mishnah/II/13.md:1 | 2 | editorial | "the piece the perpendicular cuts off", where Heath says "the straight line" and Book II keeps "piece" for an area | Fixed in c814e8fb |

### At c814e8fb: two re-readers

Two re-readers read the mends of c814e8fb at that commit:

- **The re-reader of Book I** read I.6, I.13, I.18, I.24, I.25, I.26 and I.36, with I.4 and I.40, whose records other work held, and the Lincoln paragraph of docs/reading.md. It checked the new wording on magnitudes against `Tacit.lt_trichotomy`'s docstring, I.13's route note against the two helpers that use `Triangle.angle_pos`, Kedlaya's line against his TeX source, I.24's "Heath said as much" against vol. 1, p. 246, I.36's hedge against p. 332, Maor's paperback against its ISBN, and I.40's Stillwell line against the book's contents.
- **The re-reader of Book II** read II.1, II.9, II.11, II.12, II.13 and II.14, with Book II's introduction and the status note at the head of the scans report. It checked II.1's page against the OCR's running head on p. 377, "Heath gives no reference here" against heath/II/09.md and heath/II/11.md, "the straight line … cuts off" against the enunciations, II.14's new sentences against Prop14.lean, and "every proof in Book II uses Postulate 5" against facts.json, where all 22 of Book II's entries carry `Postulate5`. It rendered II.14's two figures and read the six rendered pages.

**Every mend was confirmed.** They stamped thirteen records, with the run "brief 0005 stage 5, read-through 02 (#34), independent re-read of the mends at c814e8fb": I.6, I.13, I.18, I.24, I.25, I.26 and I.36 in 787ea8ba, and II.1, II.9, II.11, II.12, II.13 and II.14 in 44096af6. I.4 and I.40 were read and confirmed, and not stamped. After the stamps, check_style passed and check_fidelity reported that the 99 review records hold. They found no blocking or material point. Their editorial points, at c814e8fb:

| Finding | Where (file:line at c814e8fb) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| Re-reader of Book I, F1 | reading/I/40.md:1 | 2 | editorial | "a lively history of the book" may be read for a moment as Wardhaugh's book, not the *Elements* | Fixed in a1ddfcf7: "a lively history of Euclid's text" |
| Re-reader of Book I, open item 1 | docs/reports/gaps-book-I.md:188 | 3 | editorial | "the tacit law of magnitudes", which STYLE section 4 rules out | Open: the gap catalogue is not this work's file; for its owner, #46 |
| Re-reader of Book I, open item 2 | Elements/BookI/Prop29.lean:59; review/I/29.toml:13, :24 | 2 | editorial | The last of the old wordings on magnitudes, unlike I.19's | Open: next part, #34 |
| Re-reader of Book I, open item 3 | docs/references.bib:558 | 3 | editorial | Kedlaya's version dated 17 January 2006, where his site and TeX say 18 January | Fixed in a1ddfcf7, recording both, since the PDF's own title page says 17 January |
| Re-reader of Book II, F1 | review/II/14.toml:7 | 2 | editorial | The Statement row's note names no declaration, where review/SCHEMA.md asks it to say which declaration covers what | Fixed in a1ddfcf7: "`Prop14.square` squares a figure given with a checked division into triangles" |
| Re-reader of Book II, F2 | reading/II/12.md:1 | 2 | editorial | "a warm, story-filled history of trigonometry" is the reading list's own description | Fixed in a1ddfcf7 |
| Re-reader of Book II, F3 | mishnah/II/14.md:1 | 2 | editorial | "Its companions take a figure supplied with a checked division", where two of the six take none | Fixed in a1ddfcf7: "Four of its companions" |
| Re-reader of Book II, open item | mishnah/II/14.md:1; review/II/14.toml; mishnah/intro/I.md; mishnah/intro/II.md | 2 | editorial | "Outline" glossed nowhere on II.14 or in either introduction (the pilot editor's note 6) | Fixed in a1ddfcf7 for II.14 and Book II's introduction, "given only by its boundary"; Book I's introduction: next part, held by the second axiom wave (#119), #116 |

### At 9b7dad70: one re-reader

The last re-reader read the mends of b9245195, a1ddfcf7 and 9b7dad70 at 9b7dad70: I.6, I.28, I.43, II.11, II.12 and II.14; I.40's first reading line, whose record other work holds; STYLE section 4's list of habits and its sentence on "segment", and section 7's sentence on a modern figure's conditions; Book II's introduction; docs/references.bib; and the scans report. It found every "before" of the list in the history and every "after" in the files; checked the "segment" sentence against Heath, who writes segments of a straight line, in Books I to III, only in Book II and III.35; fetched Kedlaya's site and both his files; set every changed row of the scans report against the records; and read II.14 against the pilot editor's notes and docs/ACCEPTANCE.md, finding notes 3 to 7 and 9 carried out and the two unproved items given with #116.

**Every mend was confirmed.** It stamped six records in 03676129, with the run "brief 0005 stage 5, read-through 02 (#34), independent re-read of the mends at 9b7dad70": I.6, I.28, I.43, II.11, II.12 and II.14. After the stamps, check_style passed and check_fidelity reported that the 99 review records hold. It found no blocking or material point. Its four editorial points:

| Finding | Where (file:line at 9b7dad70) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| Last re-reader, F1 | figures/II/11-idea.svg:3 | 2 | editorial | "(Drawn 89 to 144: no whole numbers fit.)" leaves out "exactly" | Not taken up: judged harmless, the caption being true to its drawing |
| Last re-reader, F2 | review/I/43.toml:8; review/I/35.toml; review/I/48.toml | 2 | editorial | "Proclus's", where the pages write "Proclus'" | Open: next part, with the cross-page readers' finding above; I.35's record is held by the citation sweep (#32) and the second axiom wave (#119), #34 |
| Last re-reader, F3 | docs/reports/figures-against-scans.md:74 | 3 | editorial | I.27's row says its note tells "only" Heath's bend, where it also says ours keeps the lines straight | Fixed in b78e8ae5 |
| Last re-reader, F4 | docs/STYLE.md:313 | 3 | editorial (an observation) | "The proof is short" was written and cut within one pull request, so it never stood on main | The example is true as history, and is kept; STYLE section 4 now says it was caught in the passes' own reviews |

**In all, 43 records carry a stamp of this read-through:** 28 at 206e3080, 9 at c814e8fb and 6 at 9b7dad70. They are the 42 first stamped in 4a7bc952 and I.43, whose stamp at 9b7dad70 is its first from this read-through. Of the 42, thirteen were stamped again at c814e8fb and four of those again at 9b7dad70, with I.28 once more at 9b7dad70.

Seventeen of these records were also changed by work in flight at the revisions named here. A read-only trial merge (`git merge-tree`) of this branch, at 2853075b and again at b2c30b6d, with each change (text/sweep-I-II at 688c0f66, lean/retire-axioms-2 at 69357498, lean/ii14-own-step at cb01d567) conflicts in every one of them: I.6, I.10, I.12, I.16, I.21, I.22, I.26, I.33, I.34, I.47, II.6, II.8, II.9 and II.10 with the citation sweep (#32); I.12, I.22, I.31, II.10 and II.14 with the second axiom wave (#119); and II.5 and II.14 with the change for #168, which rewrites a step of Prop05.lean and of Prop14.lean. Of this branch and each of those changes, whichever lands second has each record they share re-read and stamped again, in the order the coordinator sets.

## The code review

An independent code reviewer, another Claude Opus 5.5 instance, which wrote nothing on this branch and was none of its readers, reviewed the branch at 926e67d2: against the repository's standards, and against #34, #30, #46, #144 and #145. It ran `lake build`, the certificate, check_fidelity, check_style and check_links, and all passed. It found every change to the Lean inside a comment or a docstring, no held file changed (the list of held files it was given named none of the sixteen records above), the merge of main clean, and every stamp current. It checked each new or changed quotation against the OCR, rendered the 20 changed figures, and found the reading lines' years, editions and **Free** marks as docs/reading.md gives them. Its verdict on both counts was a pass with minor findings. It graded its own points minor, which is editorial by WORKFLOW section 9; its Spec 2 and Spec 8 restated as material the readers' material findings still open:

| Point | Where (file:line at 926e67d2) | What | Resolution |
|---|---|---|---|
| Standards 1 | figures/II/11-idea.svg:3 | The caption gives the square on AB a colour, black, that only the straight line AB has; 46 words | Fixed in 9b7dad70, not in the reviewer's words, which would be false of the square on AH: "for each, with AK (red), equals the square on the black AB", in 40 words |
| Standards 2 | mishnah/I/08.md:7 against reading/I/08.md:1 | The commentary still says Hilbert "made side, angle, side an axiom", where the reading line now says truly what his axiom gives | Open: next part, with the reader's finding I.1 to I.12, 26; held by the second axiom wave (#119), #34 |
| Standards 3 | mishnah/I/28.md:1 | The mend named one of the two hypotheses the alternation rests on | Fixed in 9b7dad70: "B and D lie on one side of EF, and G lies between A and B" |
| Standards 4 | docs/STYLE.md:610 | STYLE asked a modern figure to show its paragraph's conditions, which no modern figure now prints | Fixed in 9b7dad70: "drawn under the conditions the paragraph states" |
| Standards 5 | figures/II/01-idea.svg:3 against docs/STYLE.md:298 | "Never … "segment" for a straight line", against Heath's "segments" in II.1 | Fixed in 9b7dad70: save Heath's segments of a straight line cut at a point, in Book II and III.35 |
| Standards 6 | docs/reports/figures-against-scans.md:5 | The change I.27's line waited for was not named | Fixed in 9b7dad70: both changes named, with the commits at which they landed |
| Spec 2 | this report | Each material item left should name its owner and next step | Done here: "The material findings left" |
| Spec 3 | review/II/14.toml:5 | The hypotheses row's unglossed "outline", describing only the companions | Fixed in a1ddfcf7 |
| Spec 4 | mishnah/intro/I.md:9; mishnah/III/32.md:3 | Two bare page references fail the rule on volumes | Named here ("The two questions of #34"); both files are held, the first by the second axiom wave (#119), the second for Book III |
| Spec 5 | this report | The italics audit's scope and result were recorded only in a writer's handback | Done here ("The two questions of #34") |
| Spec 6 | scripts/ and tests/; reading/III/28.md | #144's book-aware validator; III.28's link outside its book | Open: the validator proposed to the coordinator (#144); III.28 with Book III's read |
| Spec 7 | scripts/check_style.py:100–101 | The script's header still says "I.N" | Open: for the coordinator, #145 |
| Spec 8 | review/I/04.toml; review/I/27.toml; docs/reports/figures-against-scans.md | I.4's and I.27's lines not yet carried; the scans report named only its audit baseline and kept rows saying "not yet" | The report's rows fixed in 9b7dad70; the two lines, the readers' material findings: next part, #30 |
| Spec 10 | the records; scripts/render.py:1434; mishnah/intro/I.md; Book Zero and the gap catalogues | "a rule we assume" in many records; the generated heading; "bracket"; "laws of magnitudes" | Open: the gloss is kept until the introduction's sentence replaces it (#119 holds the introduction), with "bracket", for the next part; the heading proposed to the coordinator; "laws of magnitudes" for the catalogues' and Book Zero's owners, #46 |

Its Spec points 1 and 9 confirmed mends, and need nothing.

A second code reviewer, another Claude Opus 5.5 instance that wrote nothing on this branch, read its later commits, 926e67d2 to 2853075b: the habits list, the last mends, the stamps at 9b7dad70, this report, and the merge of main at 2853075b, whose one conflicted file, docs/STYLE.md, held three conflicts in sections 7 and 8; it redid them and found that neither side lost a word. It found one material point, the sixteen records shared with work in flight, which the last paragraph of "Re-read and stamped" now names, with the order of landing left to the coordinator. Its verdict was a fail on the standards, for that point, and a pass with minor findings on the spec. Its minor points (the scans report's account of who holds I.4's and I.27's records; a quotation of Heath's that was the introduction's words; the stamping sentences, the first code review's grades, a severity, the summary of editorial points, and this report's owners and dates; and the habits list's I.33 example and dropped examples) were mended in the commit after 2853075b.

A third code reviewer, another Claude Opus 5.5 instance that wrote nothing on this branch, read 2853075b to b2c30b6d: the commit after 2853075b, and the merge of main at b2c30b6d, which it found clean. It found the sixteen records missing from "In short" and "Still open", a material point now mended there (item 8), and twelve minor points, nine on the standards and three on the spec, all mended in the commit after b2c30b6d. Its verdict was a pass with minor findings on the standards, with the second review's material point still open with the coordinator, and a fail on the spec, for that one point, before the mend.

A fourth code reviewer, another Claude Opus 5.5 instance that wrote nothing on this branch, read that commit (74e8ad1f). It found one blocking point: the list of shared records left out II.5's, which the change for #168 had rewritten eleven minutes before; the list is now seventeen (item 8). Its other points are for the coordinator's order of landing: two sign-off branches (#220) since share six more stamped records (I.13, I.14, I.24, I.30, I.32 and I.43; item 9), and this read-through's own second part writes `mishnah/I/04.md` and `mishnah/I/08.md`, which the second axiom wave also changes.

## Addendum, 21 October: the changes landed since 2e8aecf8, and the held findings

*21 October 2026. Read at 99359055 and 275ae830, the second part's merges of the first part's branch; the branch head is 000d6791, which carries main at 554dfb0f. This is the dated addendum that #34's second condition asks for, for Books I and II.*

### Who read what

As in the first part, the writers and the readers were kept apart. Each was a Claude Opus 5.5 instance; no reader wrote a mend, and no writer stamped a record.

- **The list.** One instance, which wrote nothing, read every finding the first part left open against the branch at 926e67d2 and against the three changes landed on main, and gathered them into one list of 96: 5 already fixed by those changes, 44 on files then free, and 47 on files still held or owned elsewhere.
- **Five writers** mended what was free: the first, I.4 to I.29 (3d703e80); the second, I.37 to I.48, save I.45 (7d4e6866); the third, I.6's modern figure and I.23's statement note, which the first had left (956e01e4); the fourth, I.45's commentary, STYLE section 4, docs/reading.md, docs/references.bib, three reading lines and Book II's gap catalogue (5a41eb62); and the fifth, the readers' editorial findings below (0022c931). A one-line mend to STYLE section 4, by the instance that directs this read-through, which read no page as a reader, followed the last reader (47230b33), and the addendum's commit rewrapped that line (4cdd5cb2). Each writer checked each finding against its sources before mending it (Heath, the Lean, facts.json and the works cited), and said why where it wrote otherwise than proposed.
- **Four readers** read every page of Books I and II at 99359055, against everything that had changed on it since 2e8aecf8: the three landed changes, the first part's mends and this part's. Two of them read at 32c168fa, which differs from 99359055 only in the stamps of four records. They took, in turn:
  - Book I's index, introduction and front matter, with I.1 to I.16;
  - I.17 to I.36;
  - I.37 to I.48;
  - Book II, with its index, introduction and front matter, and the shared documents the mends changed: STYLE section 4, docs/reading.md, docs/references.bib and Book II's gap catalogue.

  They rendered all 162 figures of Books I and II and looked at each. They checked the quotations on the changed pages against the OCR of Heath's first volume, and some against the page images (n296 and n297 for I.14, n222 for I.29), and set each claim against the Lean, facts.json and the outside sources: Mueller's Open Library record, Hilbert's axiom IV, 6 and Theorem 10 in the Gutenberg text, and the publishers' chapter records at Crossref. A fifth reader, the last, read the fifth writer's mends at 275ae830.
- **This addendum** was written by a further Claude Opus 5.5 instance, which read no page as a reader and wrote no mend. It checked each count and each open finding against the readers' and writers' handbacks, the commits named and the files at 000d6791.

### What landed on main

At 554dfb0f, main stands eighteen pull requests after 2e8aecf8. Three of them change book/, mishnah/, Elements/ or figures/ (`git log --first-parent 2e8aecf8..origin/main -- book mishnah Elements figures`), and all three change Books I and II: the superposition replacement (#191, at 17ae8e2a, for #75), the notation train (#193, at 09bc89f3, for #48) and the upright figure letters (#194, at ac6e5389, for #159). No other merge since 2e8aecf8 touches those four directories. Four change docs/STYLE.md: #195, #196 and #202 in what the checks of sections 7 and 8 require, and #239 in where section 4's count markers may stand. None of the four changes what a page of Books I or II says. After 554dfb0f one more pull request changed those directories before this addendum was written: #240 (train/C6a, at 8674bce2), for Book III. On the 62 pages of Books I and II it changes only line anchors into Tacit/Constructions.lean; its new Elements/BookI/HelpersTriangles.lean and its changes under Elements/Foundations/ and Elements/Figure/ print on no page of Books I or II. It needs its own dated reading (item 7 of "Still open after the addendum").

### The superposition replacement (#191)

It made superposition a restricted inference in System E's style, which only I.4 and I.8 call on. In Books I and II it rewrote the Lean, the records and the commentaries of I.4 and I.8; I.23's route note and commentary; I.44's Lean notes and record; the introduction's sentence on the rule; and the rule's docstring, which prints in the list of what each proof rests on, on 44 of Book I's pages and on all 14 of Book II's. It retired the overlap rows of I.2, I.3 and I.23, and brought the brief, README.md, FORMALIZATION and the overlap catalogue into line.

**True.** The readers found the rule told truly wherever it is told. Only I.4 and I.8 call `Tacit.superposition`; I.20 rests on it through I.5 and I.4, and I.23 through I.8 and I.20, while I.22 does not rest on it (facts.json). No record of Books I and II now declares an overlap, and Book I's index no longer names overlaps at I.2, I.3 and I.23. I.4's four equalities and I.8's citation of I.7 inside the placement agree with Prop04.lean and Prop08.lean.

**In the voice.** The first readers heard a logician's register come in with this change: "represented derivations", "export", "returned as constructed points". It is gone from the commentaries of I.4, I.8, I.23 and I.44, from the records of I.23 and I.44, and from Prop44.lean, whose module note now says that the rule "lays a triangle down only in thought and hands back no point", and from Prop46.lean, which says that "no rule of ours carries a square to a new place" (3d703e80, 7d4e6866, 0022c931). I.4's commentary answers Peletier's danger again, and I.8's says truly what Hilbert's axiom gives. I.44's commentary now tells its "apply" apart from the "applied" of I.4 and I.8, and its caption says "apply" where it said "lay" (7d4e6866, 0022c931). The register remains in three places:

- the rule's docstring, Elements/Foundations/Tacit/Superposition.lean:44–47, "permits a restricted derivation of metric equalities … and exports no symbol of the placement": a new point, for the coordinator, who owns the foundations ("The readers' findings", below);
- Book I's introduction, mishnah/intro/I.md:7, "Its represented derivations draw nothing inside the placement, and no equality they export can name its hypothetical corners or side", held by the second axiom wave (#119);
- the records of I.4 and I.8 and the module notes of Prop04.lean and Prop08.lean, such as review/I/04.toml:13, "admits a derivation over symbols", and review/I/08.toml:10, "a proved statement asserting no existence", held by the per-law superposition change (#150) and the second axiom wave (#119).

**Consistent.** The two material findings the change left on I.44 and I.46, two reasons for one step and the notes of `Prop44.place` and `Prop46.side_eq`, are mended (7d4e6866), and both records are stamped. The one material point left is in Book I's gap catalogue, docs/reports/gaps-book-I.md:256, "Our Lean moves a figure only by superposition", which the second axiom wave (#119) holds. The reader of I.1 to I.16 added three editorial points to I.4's and I.8's held notes ("The readers' findings").

### The notation train (#193)

It added the paragraph on the modern way's notation to STYLE section 4 and set the modern ways of I.20, I.27, I.29, I.35, I.37, I.39, I.40, I.43, I.45 and I.48 by it, bold for a vector, with plain bars. It added the join passages to the records of I.5 and I.11 and "Definition I.10" to Prop11.lean, gave Nahin's and Morrow's first appearances, on I.11 and I.20, their linked years, and stamped the records it touched, I.45's among them.

**True.** The vector algebra of the modern ways is right (the reader of I.17 to I.36 checked I.20, I.27, I.29 and I.35), and I.5's join passage agrees with Prop05.lean:57–58, where FC and GB are joined and never used. I.45's record, which the pilot editor feared would be stamped from an older base (note 1, material), landed stamped at ef3ca8dd, an ancestor of main, with the Lean hash of Prop45.lean as it stands; that note is closed.

**Consistent.** The modern figures set in italic the names their paragraphs set in bold, and STYLE section 4 now says so: "the bold is the paragraph's mark of a vector" (5a41eb62; the reader of Book II found it true to section 7). Nahin's year on I.11, "(2010; first published 1998)", and Morrow's on I.20, "(1992 paperback; first published 1970)", agree with their repeats on I.46 and I.47, which settles the first re-readers' two points and the further reading's exception for them; "friendly" still stands on I.20's Steele line and on II.10, as the first part found. The definitions without their book and the plural "magnitudes" on the train's pages are mended: "Definition I.23" and "a tacit rule of magnitude" in Prop29.lean, "Def. I.22" in Prop48.lean, and I.29's two notes in I.17's words (3d703e80, 7d4e6866).

**Left on its pages**, all in held files: the joins of I.5 and I.11 against I.1, I.6, I.7 and I.12, and I.11's passage key, review/I/11.toml:22 (the citation sweep, #32, and the second axiom wave, #119); I.20's case and "not a proof", review/I/20.toml:39 and :31 (#32); I.27's figure note (material, #30) and "not proofs", review/I/27.toml:27 and :13 (#119); "Proclus's" at review/I/35.toml:12 (#32, #119); the notes of I.39 and I.40, review/I/39.toml:7 and review/I/40.toml:4 and :10 (#32); and I.45's record ("I.45 and II.14", below).

### The upright figure letters (#194)

It set Heath's letters upright in every figure at a glance and every one of Euclid's figures, as the prose and the modern figures already set them. The four readers rendered all 162 figures of Books I and II and looked at each: every letter is upright, clear of the strokes and Heath's own, and italic stands only in the modern figures. Since #196 (cba27afa), S15 and S20 require it, with the switch for upright letters on (scripts/check_style.py:176). The readers found nothing to mend.

### The held findings

The list counts what the first part left open on files then held, with the open points of its writers and re-readers: 96 in all, 14 of them material. A finding open in part counts once, by what is left of it. These are the first part's findings gathered again, not new ones, and they are not added to its 191.

| | Findings | Material |
|---|---|---|
| In the list, at 926e67d2 | 96 | 14 |
| Settled before this part's writers began | 15 | 3 |
| ... by changes landed on main (#191, #193, #195, #196) | 6 | 2 |
| ... by the first part's later mends (a1ddfcf7) | 9 | 1 |
| Mended in this part (3d703e80, 7d4e6866, 956e01e4, 5a41eb62) | 31 | 5 |
| Mended in part | 2 | 0 |
| Still held by work in flight | 30 | 4 |
| For owners outside this work | 18 | 2 |

- **Settled before, 15.** Six by changes on main: the replacement brought the shared documents into line and rewrote Prop08.lean's module note (#191); the notation train gave Nahin and Morrow their years and stamped I.45's record at an ancestor of main (#193); #195 answered a writer's point on the style check's list of files awaiting S12; and #196 turned on the switch for upright letters. Nine the first part had itself mended after the list was made, all in a1ddfcf7: I.43's "complements", I.40's "history of Euclid's text", II.14's commentary, Statement rows and Representation row, Book II's introduction and its sentence on I.13, Maor's line on II.12, and Kedlaya's date in docs/references.bib. They are counted there, not here.
- **Mended in this part, 31**, each confirmed by a reader. In Book I: I.4's and I.8's commentaries in a reader's words, with Peletier's danger answered and Hilbert's axiom told truly; I.14's lemma; I.20's vectors tied to the triangle; I.23's commentary and route note, and its callers, I.42 and I.44 among them, named in its commentary, Lean note and statement note (956e01e4); I.29's notes, and Prop29.lean's definition and "rule of magnitude"; the digit labels of the modern figures of I.1, I.6 and I.16; I.37's Heiberg and Proclus' "describers of countries"; the notes of I.37 and I.44 on I.30, for which Heath gives no reference; the commentaries of I.39, I.40 and I.48, and Prop48.lean's definition; I.44's commentary (material) and record, the Lean notes of Prop44.lean and Prop46.lean (material), and "applied" glossed on I.44; and I.45's commentary (material: its modern way, its main theorem and what is not yet proved). In the shared documents: STYLE section 4's words for the restriction, and its sentence joining a vector's bold and italic names; Mueller's edition on I.18, I.38 and II.2; Hilbert's axiom in docs/reading.md; and "Heath gives no reference" for "has no bracket" in Book II's gap catalogue.
- **Mended in part, 2.** "Proclus'" stands in the notes of I.43 and I.48 (7d4e6866), but the comment at review/I/43.toml:4, which no page shows, still says "Proclus's". And docs/references.bib now records the contents checked for the works whose chapters the reading lines give (5a41eb62, 0022c931), the first part's "record of which chapters were checked", save these: Courant and Robbins' chapters III and IV (docs/references.bib:981–990, given on I.22, I.31, II.14 and III.30), for which no contents page could be reached; Yaglom's section titles on I.2, I.5 and I.34, checked by the reader of I.1 to I.16 against the 1962 contents (p. vii) and not yet recorded; Coxeter's ch. 8 (I.6), Greenberg's ch. 3 and 4 (I.10, I.16, I.26), chapters 3 and 12 of *Theorem Proving in Lean 4* (I.14) and ch. 2 of Maor's *Trigonometric Delights* (I.25), which have no contents note yet; and Book III's works, for Book III's read.
- **Still held, 30**, by the work that holds each file:
  - the second axiom wave (#119), 13: Book I's introduction, seven points (mishnah/intro/I.md:3, "Euclid's own figure" and the page's order; :5, the sentence on names that begin `Tacit.`; :7, the rule's register; :9, "(p. 316)"; :11, I.45's old words; :13, the two asides on Intersections 2 and 3, and "A bracket is Heath's pointer"); I.27's figure note (material, #30), review/I/27.toml:27, with the sentence of mishnah/I/27.md:5 that waits on it, and its "not proofs" at :13; Book I's gap catalogue, three points (docs/reports/gaps-book-I.md:256, material; "the tacit law of magnitudes" at :114, :139 and :188; "has no bracket", fifteen times); and Book Zero's "the laws of magnitudes" (Elements/Figure/Lengths.lean:10, :49, Areas.lean:16, Sums.lean:12);
  - the per-law superposition change (#150), which the second axiom wave has merged, 3: I.4's figure note (material, #30: review/I/04.toml has no figure note, and Heath's figure also draws the bent base); the register of I.4's and I.8's records and module notes (review/I/04.toml:13, :19, :25, :52; review/I/08.toml:10, :16, :38; Prop04.lean:10–18; Prop08.lean:11–18); and Heiberg and Savile first named by surname (review/I/04.toml:41; Prop04.lean:159, :197);
  - the citation sweep (#32), 11: Prop11.lean:39, "In Lean C may be any point"; I.20's case, "in Euclid's figure" (review/I/20.toml:39), its "not a proof" (:31) and "Heath gives no bracket here" at Prop20.lean:46, a free file whose change would make I.20's held record stale; I.39's note (review/I/39.toml:7); I.40's two notes (review/I/40.toml:4, and :10, where `Prop40.general` stands without its code mark); and I.45's record, four points (below);
  - both the citation sweep (#32) and the second axiom wave (#119), 3: the joins of I.5 and I.11; I.11's passage key; and "Proclus's" on I.35.
- **For owners outside this work, 18**, in files this work does not change:
  - the coordinator, 8: scripts/render.py's line over every commentary (render.py:1508), Book I's front page mapping Definitions I.2 and I.3 to `Line` and listing `quadArea` for Definition I.14 (material), its italic "whole", "restricted" and "in part", and "Again by" for a repeated helper; the header of scripts/check_style.py (#145); a font for digits; "the tacit laws of magnitudes" in Elements/Foundations/CommonNotions.lean:14; and the three unused tags of review/terms.toml;
  - README.md's owner, 2: README.md:23's echo of the generated line, and README.md:40's order of the page. The citation sweep and the second axiom wave also change README.md;
  - heath/'s owner, 1: heath/I/front.md:1 gives pp. 153–155 with no scan leaves, so Book I's front page links none;
  - docs/examples.md's owner, 1: an example of a restricted construction, once I.45's record tells it as II.14's does;
  - Book III's read, 6: III.24's caption and commentary (material, provisional), its record's missing figure note and its bold leads; mishnah/III/32.md:3's "(p. 67)"; mishnah/III/28.md:5's "where Heath cites"; and the reading lines of III.26 and III.28 (Maor's year, a line in the list's own words, and a link out of Book III).
- **Not taken up.** Of the 44 the list found free, four are in files the second axiom wave (#119) changes, Book I's gap catalogue and Book Zero, and were given to no writer; they are counted above as held. No other was left untaken. Of the six points the first part did not take up ("Still open", item 6):
  - "applied" glossed two ways: mended (7d4e6866, 0022c931);
  - the three unused tags: still not taken up, a decision for the coordinator;
  - a record of which chapters were checked: in part (above);
  - "cut" for figures: in part. STYLE section 4 now says that in the restriction's sentences a figure is divided, not cut (5a41eb62), and I.45's commentary and caption say "divides" and "divide" (5a41eb62, 0022c931). Book II's introduction (mishnah/intro/II.md:13, :15) and I.34's caption (figures/I/34-idea.svg:3) still say "cuts"; the writer left a sweep of the edition for the owner's decision;
  - II.11's caption: mended, "(Drawn with AH to AB as 89 to 144: no whole numbers fit exactly.)" (0022c931);
  - the lines for I.4's and I.27's figure notes (#30): still held (above).

  Two points the writers found on the way were not taken up: Elements/BookI/HelpersParallels.lean:128, "(Def. 22)", in a docstring no page shows; and review/I/23.toml:4, whose statement note now names Book I's callers of I.23 but not Book III's six, which would take it past 160 characters (the writer of 956e01e4 offers "and Book III").

### I.45 and II.14

I.45's commentary now tells the restriction in II.14's words (5a41eb62, 0022c931). Both say that the main theorem takes Euclid's two triangles unchecked, and that they make his figure when the two corners off the diameter lie on opposite sides of it; that the companions take a figure "given with a checked division into triangles"; and, in one sentence, word for word: "Not yet proved ([#116](https://github.com/jackChallis/stoicheia/issues/116)): that every rectilineal figure, given only by its boundary, has such a division, and that another division gives the same area." Each then says that Euclid takes the second for granted and that Hilbert proved it, for his measure of area. I.45's modern way states its condition, and its caption divides the figure. STYLE section 4 now holds these words, "A figure given with its triangles", with a short form for a record's statement note (5a41eb62, 0022c931, 47230b33). The reader of I.37 to I.48 read I.45 and II.14 one after the other, and the last reader found their shared sentences the same, word for word.

What remains is in five files, each held, with the words they need, as the reader of I.37 to I.48 gives them, checked against Prop45.lean.

- **review/I/45.toml**, held by the citation sweep (#32): the pilot editor's notes 4 (material), 5, 12 and 13, and the first part's I.37 to I.48, 19.
  - :4, the status line: "figures given with a checked division into triangles".
  - :6, the Extra hypotheses: "The figure is given with a checked division into triangles that do not overlap, no point inside two of them (`Apart` or `Rectilineal`, or the division from one corner that `Prop45.fan` checks); the main theorem takes Euclid's two triangles, ABD and DBC, unchecked. A figure given only by its boundary is not yet covered."
  - :8, the statement's note, 157 characters: "`Prop45.apart` covers a figure given with a checked division into triangles. Not yet proved: that every figure has one, and that another gives the same area."
  - :18, the Representation note: "The main theorem takes Euclid's two triangles, ABD and DBC, unchecked, and they may overlap; they make Euclid's figure when A and C lie on opposite sides of DB, and that checked case is `Prop45.fan` for the corners D, A, B, C. Three companions take a rectilineal figure given with a checked division into triangles: triangles that lie apart, so the figure may have a hole (`Prop45.apart`); triangles glued edge to edge in a suitable order, for a figure with one boundary (`Prop45.figure`); or, as Euclid and Byrne divide it, triangles from one corner, each two neighbours on opposite sides of the straight line they share and their angles at that corner together less than four right angles, which `Fitted.fan` proves fit together (`Prop45.fan`). Equal to the figure means equal to those triangles together. The construction itself works for any triangles (`Prop45.sum`); the check is what makes their sum the figure's. The Lean does not state that the figure `Prop45.fan` makes is the one bounded by the closed line through its corners in order, though this is true in the plane. Not yet proved ([#116](https://github.com/jackChallis/stoicheia/issues/116)): that every rectilineal figure, given only by its boundary, has such a division, and that another division gives the same area. David Hilbert proved the second, for his measure of area."
  - :29: "Euclid applies I.14 because KH and HM do not lie on the same side of GH. The Lean makes it so: it applies I.44's parallelogram to GH on the side away from K, and `SameSideOf.trans_opposite` puts M on the other side of GH from K. I.14 then puts H between K and M (D for H in the Lean)."
  - :35: "as the representation note explains" becomes "as the Representation row explains".
  - :38, the case: "Euclid's figure ABCD, divided by DB into the two triangles ABD and DBC".
  - :39: "H is drawn on D, as the Lean has it; Heath draws the parallelogram apart, as the figure at a glance does."
- **Elements/BookI/Prop45.lean**, held by the citation sweep (#32). Lean notes only, after which I.45's record goes stale and is re-read:
  - :19, "ABCD, cut by DB into the" becomes "ABCD, divided by DB into the";
  - :29–30, "triangles that lie apart, no point inside two of them (`Apart`)" becomes "triangles that do not overlap, no point inside two of them (`Apart`)";
  - :52, "gives the same sum" becomes "gives the same area";
  - :355, "cut it into triangles" becomes "divide it into triangles".
- **mishnah/intro/I.md:11**, held by the second axiom wave (#119), the whole paragraph, with "I.45" linked to its page as now: "**From triangles to a parallelogram.** Our I.45 takes the two triangles of Euclid's proof, unchecked; three of its companions take a figure given with a checked division into triangles that do not overlap, no point inside two of them, and repeat Euclid's construction for each triangle in turn. Equal to the figure means equal to those triangles together. I.45 is restricted. Not yet proved ([#116](https://github.com/jackChallis/stoicheia/issues/116)): that every rectilineal figure, given only by its boundary, has such a division, and that another division gives the same area."
- **Elements/BookII/Prop14.lean:30–31 and :320**, changed by the change for #168: the first mention on II.14's page says "triangles that lie apart", where STYLE section 4 asks first for "triangles that do not overlap, no point inside two of them (`Apart`)", and the docstring's heading should read "for a figure given with triangles that do not overlap". It lands with Prop45.lean's notes, and makes II.14's record stale.
- **docs/reports/gaps-book-I.md:262**, held by the second axiom wave (#119), still says "cuts", "every cutting gives the same whole" and "another cutting".

The pilot editor's note 1 is closed (the notation train, above). B4 of the book acceptance record asks that I.45's limitation be stated plainly where it occurs: the commentary now does, and the record's Statement and Extra hypotheses rows (note 4) do not yet.

### The material findings left, as they now stand

| Finding | What | Now |
|---|---|---|
| I.1 to I.12, 1; I.13 to I.24, 2; across pages, 26 and 27 | The shared documents and the rule's docstring would describe the old rule; the overlap catalogue would keep rows B2 refuses | In part. The replacement itself brought the brief (docs/briefs/book-I.md:55–56), README.md:68, FORMALIZATION's table of rules (docs/FORMALIZATION.md:226) and the rule's docstring into line, and retired the catalogue's rows for I.2, I.3 and I.23 (docs/reports/overlaps.md:43); no record of Books I and II declares an overlap; I.44's half of across pages, 26 is mended (7d4e6866). Left: docs/reports/gaps-book-I.md:256, held by the second axiom wave (#119), #75 |
| I.37 to I.48, 3 | I.44's commentary and record gave two reasons for one step | Closed in 7d4e6866: the commentary gives the rule's reason, and the record says how `Prop44.place` builds an equal parallelogram; stamped at 99359055 and 275ae830 |
| I.37 to I.48, 4 | The Lean notes of `Prop44.place` and `Prop46.side_eq`, and the rule's docstring, described the retired form | Closed: the docstring by the replacement (17ae8e2a), the notes in 7d4e6866; I.44 and I.46 stamped. The docstring's register is a new editorial point |
| I.1 to I.12, 2 | I.4's figure note | Open: review/I/04.toml still has no figure note; held by the per-law superposition change (#150) and the second axiom wave (#119), #30 |
| I.25 to I.36, 2 | I.27's figure note | Open: review/I/27.toml:27; held by the second axiom wave (#119), #30 |
| I.1 to I.12, 4; across pages, 33 | Book I's front page | Open: scripts/render.py, for the coordinator, #34 |
| I.37 to I.48, 1 | I.45's modern way | Closed in 5a41eb62: "with A and C on opposite sides of DB, as in Euclid's figure" (mishnah/I/45.md:11) |
| Across pages, 16 (in part); pilot, 3 (in part) | I.45's half: the main theorem said to "take the figure", and the issue link | Closed in 5a41eb62 and 0022c931, in II.14's words (above) |
| Pilot, 4 (in part) | I.45's Statement and Extra hypotheses rows | Open: review/I/45.toml:4–8, held by the citation sweep (#32); the words are above, #116 |
| Pilot, 1 | I.45's record stamped from an older base | Closed by the notation train as it landed (09bc89f3): the record names ef3ca8dd, an ancestor of main, and the Lean hash of Prop45.lean as it stands. It is stamped again when the record is mended |
| Pilot, 16 | III.24 | Open: Book III's read, #34 |

So, of the 27 material findings, the first part fixed 11, and of the 16 it left, nine are now closed: I.13 to I.24, 2; across pages, 26 and 27; I.37 to I.48, 1, 3 and 4; across pages, 16 and the pilot editor's note 3, for I.45; and the pilot editor's note 1. Their commits are #191 (17ae8e2a) and #193 (09bc89f3) on main, and 7d4e6866, 5a41eb62 and 0022c931 on this branch, which reach main when it lands. Seven stay open: I.1 to I.12, 1 (in part), 2 and 4; across pages, 33; I.25 to I.36, 2; and the pilot editor's notes 4 and 16.

### The readers' findings

The readers found no blocking point and no new material one. Their new findings are nineteen, counting once the point three readers made on the rule's docstring and the one two made on Prop14.lean; they added four points to findings already held.

| Finding | Where (file:line at the revision read) | Severity | What | Resolution |
|---|---|---|---|---|
| Reader of I.1 to I.16, 1 | mishnah/I/01.md:7 | editorial | "explains beautifully", the inflated praise STYLE section 4 lists | Fixed in 0022c931 |
| Reader of I.1 to I.16, 3; reader of I.17 to I.36, N3; reader of Book II, X | Elements/Foundations/Tacit/Superposition.lean:44–47 | editorial | The rule's docstring, from the replacement, printed on 44 of Book I's pages and all 14 of Book II's, keeps the register the mends removed elsewhere | Open: the foundations are the coordinator's. Proposed: "A triangle may be laid down in thought on a given ray and side, keeping its sides and angles, to prove equalities of lengths, angles or areas about the figure already given. Nothing is drawn in the placement, each law it uses is cited, and no point of it comes back out.", #34 |
| Reader of I.1 to I.16, 4 | scripts/render.py:1898, :1902 (book/I/front.md:30–31) | editorial | Definitions I.17 and I.18 cite `Circumference.semicircle`, a theorem of Book III, without its book, so the name does not resolve in Book I | Open: scripts/render.py, proposed to the coordinator, `BookIII.Circumference.semicircle`, #34 |
| Reader of I.1 to I.16, 9 | mishnah/I/16.md:7 | editorial | With the label "a + 1" gone from the figure, its arrow from B to A is a vector the paragraph never names | Fixed in 0022c931: the paragraph names BA as a + 1, and says all three angles lie between 0 and π |
| Reader of I.17 to I.36, N1 | review/I/23.toml:9 | editorial | The route note retells why, which the commentary says | Fixed in 0022c931 |
| Reader of I.17 to I.36, N2 | Elements/BookI/Prop23.lean:22 | editorial | "the bracket in I.22's enunciation", where brackets alone are Heiberg's | Fixed in 0022c931: "Heath's reference" |
| Reader of I.37 to I.48, 1 | figures/I/44-idea.svg:3 | editorial | The caption "lays" the triangle on AB, where the commentary keeps "laid on" for I.4 and I.8 | Fixed in 0022c931: "To apply to AB (blue) a parallelogram equal to the triangle C (yellow) …" |
| Reader of I.37 to I.48, 3 | mishnah/I/38.md:1 | editorial | J. L. Heiberg named in full again, after the record's note | Fixed in 0022c931 |
| Reader of I.37 to I.48, 5 | figures/I/45-idea.svg:3 | editorial | "cut ABCD into triangles" | Fixed in 0022c931: "divide" |
| Reader of I.37 to I.48, 6 | mishnah/I/45.md:3; mishnah/II/14.md:1 | editorial | Byrne and Hilbert named in full again, after the record's rows | Fixed in 0022c931, on both pages, so that their shared sentences stay the same |
| Reader of I.37 to I.48, 7 | mishnah/I/45.md:3 | editorial | "taken together", where STYLE section 4 and II.14 say "together" | Fixed in 0022c931 |
| Reader of Book II, F1 | mishnah/intro/II.md:7 | editorial | "We prove each once, in Rectangles.lean", no longer true once the sentence on `Tacit.adjacent_eq_of_right`, which I.13's file proves, was added | Fixed in 0022c931 |
| Reader of Book II, F2 | figures/II/02-idea.svg:3 | editorial | "each piece", where II.1's caption now has Heath's "each segment" | Fixed in 0022c931 |
| Reader of Book II, F3; reader of I.37 to I.48 | Elements/BookII/Prop14.lean:30–31, :320 | editorial | The first mention on II.14's page says "lie apart" | Open: Prop14.lean is changed by the change for #168; to land with Prop45.lean's notes ("I.45 and II.14"), #34, #116 |
| Reader of Book II, F4 | docs/STYLE.md:369–380 | editorial | The new rule asked every text for the same words, which a record's 160-character note cannot give in full | Fixed in 0022c931: the texts named, and a short form for a record's statement note |
| Reader of Book II, F5 | docs/references.bib:981–990, :1104–1113 | editorial | Courant and Robbins' and Stillwell's *Mathematics and Its History* had no "Contents checked" note, though reading lines give their chapters | In part: Stillwell's note added in 0022c931, its titles checked at Crossref by the reader and the writer; Courant and Robbins' chapters wait for a contents page (above), #34 |
| Reader of Book II, F6 | figures/II/11-idea.svg:3 | editorial | "(Drawn 89 to 144: no whole numbers fit.)" no longer says what stands in that ratio; the last re-reader's F1 of the first part | Fixed in 0022c931 |
| Last reader, F1 | Elements/BookI/Prop23.lean:55–56 | editorial | I.22 is said to point to I.20 ("and points to I.20 for it"), where the docstring above now says "Heath's reference" | Open: for whoever next changes Prop23.lean, since the change makes I.23's record stale, #34 |
| Last reader, F2 | docs/STYLE.md:373–375 | editorial | The full words at first mention were asked of four kinds of text, not of the gap catalogues | Fixed in 47230b33 |
| Reader of I.1 to I.16, 5 (added) | review/I/04.toml:19, :25, :31, :47 | editorial | The notes use B', C' and DB'C', which the page never introduces | Open, with I.4's other notes: held by the per-law superposition change (#150) and the second axiom wave (#119) |
| Reader of I.1 to I.16, 6 (added) | Elements/BookI/Prop08.lean:16–17, against mishnah/I/08.md:5 | editorial | Two accounts of I.7's proof: "through I.5 and I.4", and "through I.5 and I.3 uses circles" | Open: held, as above |
| Reader of I.1 to I.16, 6 (added) | Elements/BookI/Prop08.lean:123 | editorial | "(Savile's argument)", the page's first mention of Henry Savile | Open: held, as above |
| Reader of I.1 to I.16, 7 (added) | review/I/05.toml:69 | editorial | `representations = "n/a"` beside a representation table, the only such pair in Books I and II; no page shows it | Open: held by the citation sweep (#32) and the second axiom wave (#119); "pass" at the next stamp |

Of the nineteen, fourteen are fixed (0022c931, 47230b33), one in part, and four open, one of them held.

The last reader read the fifth writer's twelve mends at 275ae830 and confirmed each. It checked I.16's three angles, I.23's record against the Lean line by line and its "through I.8 and I.20" against facts.json, I.44's caption against the figure's coordinates, the full names on the pages of I.38, I.45 and II.14, Book II's introduction against Prop13.lean and Rectangles.lean, and II.11's ratio against the figure, where AH is 89 and AB 144. One quotation added in this part, Proclus' "describers of countries" on I.37 (vol. 1, p. 332), was checked against the OCR by its writer and its reader, and not against the page image.

### Re-read and stamped

The readers were given twelve records to stamp, and stamped each with the reviewer "Claude Opus 5.5, independent reader":

- at 99359055, with the run "brief 0005 stage 5, read-through 02 (#34), part 2: the changes landed since 2e8aecf8 and the held findings' mends, read at 99359055": I.1, I.14, I.23 and I.29 in 32c168fa, and I.37, I.43, I.44, I.46, I.48 and II.2 in 55606178;
- at 275ae830, with the run "brief 0005 stage 5, read-through 02 (#34), part 2: the addendum readers' mends (0022c931), read at 275ae830": I.1, I.23, I.38, I.44, II.2 and II.11 in 4c83319a.

At 000d6791, six records carry the first stamp (I.14, I.29, I.37, I.43, I.46 and I.48) and six the second (I.1, I.23, I.38, I.44, II.2 and II.11). Seven are stamped by this read-through for the first time (I.1, I.23, I.29, I.37, I.44, I.48 and II.2), so 50 of the 62 records of Books I and II now carry its stamp. The twelve without it are I.2, I.3, I.4, I.5, I.8, I.11, I.20, I.27, I.35, I.39, I.40 and I.45: all held by work in flight but I.3, which the reader of I.1 to I.16 read and confirmed and was not given to stamp. Every mend and every landed change the readers read was confirmed true. No stamp was given over a blocking or material point; the editorial points stamped over are in the table above. The pages in book/ show the new stamps once the integrator renders them. Three of the 50, I.6 (9b7dad70), I.16 (206e3080) and II.14 (9b7dad70), were stamped before this part changed their figure or commentary (956e01e4; 3d703e80 and 0022c931; 0022c931). The readers confirmed each change; the records are held, and their re-reading under the first part's item 8 covers these changes too. A fourth, I.18 (c814e8fb), was stamped before 5a41eb62 changed its reading line; the readers confirmed that change too, and no work in flight holds I.18, so it is to be re-stamped with the next change to its record ("Still open after the addendum", item 5).

The checks, as the readers report them:

- after the first stamps, check_fidelity reported only I.44, I.46 and I.48, whose Lean notes had changed in 7d4e6866, until the reader of I.37 to I.48 stamped them; it then reported that all 99 propositions quote Heath exactly and that the 99 review records hold. check_style passed (S1 to S26).
- at 275ae830, `lake build Elements.BookI.Prop23` succeeded and check_fidelity passed. check_style failed at first, with three S12 failures because the tree was not built (no Prop24.olean), and passed after a full `lake build`. check_links found all 13771 relative links and anchors in 483 Markdown files resolving.

### Still open after the addendum

1. **Findings in files held by work in flight** (#34): the thirty above, four of them material (I.4's and I.27's figure notes, #30; I.45's Statement and Extra hypotheses rows, #116; Book I's gap catalogue at :256), with the readers' four additions and Prop14.lean. Each is mended, and its page read and stamped again, after the work that holds it lands: the citation sweep (#32), the second axiom wave (#119), with the per-law superposition change (#150) merged into it, and the change for #168.
2. **Files shared with work in flight**, for the coordinator's order of landing (#34):
   - mishnah/I/04.md:7 and mishnah/I/08.md:5, rewritten in this part (3d703e80) and by the second axiom wave (#119), as the fourth code review foresaw: whichever lands second merges the two and has both pages read again;
   - docs/reports/gaps-book-II.md, changed here (5a41eb62) and, near II.14's entry, by the change for #168;
   - the stamps. None of the twelve records stamped in this part is changed by the four changes in flight, so item 8's seventeen stand as they were. The cross-family sign-off (#220), not yet on main, restamps records that carry this read-through's stamps; its three branches were still moving as this was written, so the coordinator takes the full list from a trial merge at landing. At their heads at 18:13 on 21 October (873d1346, 5a2772dc, c67ed31d), eight of those records were stamped in this part (I.1, I.14, I.37, I.43, I.44, I.48, II.2 and II.11). Whichever lands second has each shared record re-read and stamped again.
3. **I.45 told as II.14 is** (#34, #116): its record, Prop45.lean, Book I's introduction, Book I's gap catalogue and Prop14.lean, in the words above; then docs/examples.md's example of a restricted construction (the pilot editor's note 19).
4. **For the coordinator** (#34): the rule's docstring; scripts/render.py, for the line over every commentary, Book I's front page (material), its `Circumference.semicircle`, its italics and "Again by"; the header of scripts/check_style.py (#145); a font for digits, which now concerns only I.43's "(1 − s)u" and "(1 − t)v", since the labels of I.1 and I.16 are gone (3d703e80); "the tacit laws of magnitudes" in Elements/Foundations/CommonNotions.lean:14; the three unused tags; and the book-aware check of the reading lines (#144).
5. **For other owners**: README.md:23 and :40; heath/I/front.md:1's scan leaves; Courant and Robbins' chapters, Yaglom's section titles, and Coxeter's, Greenberg's, *Theorem Proving in Lean 4*'s and Maor's chapters, to check and record in docs/references.bib; the comment at review/I/43.toml:4; Elements/BookI/HelpersParallels.lean:128; Prop23.lean:55–56, for whoever next changes that file; I.18's record, to re-stamp after its reading line's change (5a41eb62); and a sweep of "cut" for figures, for the owner's decision.
6. **Book III's read** (#34): the six points above, with reading/III/09.md's Mueller "(1981)", which by I.18's line should read "(2006; first published 1981)".
7. **The book acceptance records** (#156). B3 now has this addendum; it still needs this report on main, the seven material findings still open resolved by commits on main, and the [read-through] table of each record. B4 needs I.45's Statement and Extra hypotheses rows to state its limitation plainly, as its commentary now does. #34's second condition is met for Books I and II as main stood at 554dfb0f: each later change under book/, mishnah/, Elements/ or figures/ that lands before the release, #240 (8674bce2) first among them and the changes in flight above, needs its own dated reading.

## Second addendum, 22 October: read again across families

While this read-through waited to land, the cross-family sign-off (#220) landed in three parts, pull requests #272, #277 and #287, and a fourth, for #257, pull request #290. They re-stamp records that this read-through also changes. This addendum says what was done about it, on this branch, which now carries its second part as well (the two branches are one).

### The merges

This branch merged main four times on 22 October, after each part of the sign-off landed (dceb98ee, 01e0fe54, 09b32b47 and ddf3d618, the last with the figures' change, #289, as well). It also merged II.14's own step (#168; 5c03d00b), which lands before it, as posted for landing. Main had changed only the stamps of the records both sides change, with two exceptions. In II.4's and II.9's records the sign-off gave a helper its book, as this branch had already done, in the same words. In II.9's note on "But the square on EF is equal to the squares on EG, GF", the two sides worded Heath's missing reference differently, and this branch's "Heath gives no reference here", the pages' one phrase for it (STYLE section 4), is kept. II.14's own step rewrites one step of II.5's and II.14's records, the right angle each proves in place by I.13 and Common Notion 3, and Book II's gap catalogue's bullet on it; those take its side, and every other mend of this branch stays. So each shared record kept this branch's text, save those steps, and each was read again, as below. An independent code review checked each merge with `git show --cc` and found no text of either side lost.

### Why the stamps were read again

Every record of Books I and II carries, on main, the stamp of a reader from the family that did not write its proof: Claude wrote Book I's proofs except I.26, I.28, I.30, I.32 and I.33 to I.48, which are Codex's, as are Book II's (README.md, "How it was made"). This read-through's re-readers were all Claude Opus 5.5. Twenty of the records they stamped are of proofs that Claude wrote, and so those stamps would have undone #220's rule for those twenty. And the records the sign-off had stamped since this branch's readers read them carried text the sign-off's readers had not read.

So each record that this read-through stamps, whose page it changes, was read again in full, against Heath and the Lean, at a revision carrying everything it now shows: by GPT-6 Astra (Codex) for Claude's proofs, and by Claude Opus 5.5 for Codex's. I.41 and I.46, whose proofs have parts that Claude wrote (#257), are read by Codex alone. None of these readers wrote, prompted or edited anything on this branch. Each run line keeps the provenance the sign-off wrote and adds this reading. Each stamp names a commit in this branch's history.

| Reader | Family | Records | Read at | Stamped in | Verdict |
|---|---|---|---|---|---|
| RT-x1 | GPT-6 Astra (Codex) | I.9, I.10, I.15 | 01e0fe54 | 97205d2d | confirmed |
| RT-x2 | GPT-6 Astra (Codex) | I.22, I.31; I.21 and I.24 held back on three material findings | 01e0fe54 | b9cd9ad0 | confirmed |
| RT-x3 | GPT-6 Astra (Codex) | I.1, I.14 | b18bca18 | 05ea4b10 | confirmed |
| RT-y1 | GPT-6 Astra (Codex) | I.6, I.7, I.12, I.13, I.16 | b7b41f51 | 02559a6b | confirmed |
| RT-y2 | GPT-6 Astra (Codex) | I.17, I.18, I.19, I.21 | b7b41f51 | 02559a6b | confirmed |
| RT-y3 | GPT-6 Astra (Codex) | I.23, I.24, I.25, I.29 | b7b41f51 | 02559a6b | confirmed |
| RT-y5 | GPT-6 Astra (Codex) | I.41, I.46 (#257) | ddf3d618 | 02b285d2 | confirmed |
| RT-c1 | Claude Opus 5.5 | I.26, I.32, I.47 | 18e4e614 | 1145683c | confirmed |
| RT-c2 | Claude Opus 5.5 | I.37, I.43 | 387a590f | 30da0522 | confirmed |
| RT-y4 | Claude Opus 5.5 | I.30, I.34, I.44, I.48 | b7b41f51 | d69430d9 | confirmed |
| RT-c4 | Claude Opus 5.5 | II.1, II.3, II.4 | 09b32b47 | 5181f215 | confirmed |
| RT-c5 | Claude Opus 5.5 | II.8, II.9, II.10 | 09b32b47 | 5181f215 | confirmed |
| RT-c6 | Claude Opus 5.5 | II.2, II.11 | cf05b375 | 2bec4834 | confirmed |
| RT-y6 | Claude Opus 5.5 | II.5, II.14 | 5c03d00b | a1092c01 | confirmed |
Some of these records were read twice on 22 October. I.21 and I.24 were read again after the mends below. I.16, I.18 and the records whose Lean notes this branch changes were read again at b7b41f51, once the Lean notes were back on this branch (below), so that each stamp covers every file its page shows. A code review checked that, at each stamp's commit, the record, its Lean file, its commentary, its reading lines and its figures are those of the head.

**Every record was confirmed.** One Codex reader found three material points first. Each was mended in the sources (b9cd9ad0), and the records were read again after the mends:

| Finding | Where (file:line at 01e0fe54) | Tier | Severity | What | Resolution |
|---|---|---|---|---|---|
| Codex reader of I.21 to I.31, 1 | mishnah/I/21.md:3 | 2 | material | Proclus' illustration put D anywhere on BC of a triangle right-angled anywhere, where Heath's figure (vol. 1, p. 290; leaf n310) has the right angle at B and D between B and C; elsewhere DE may not be cut off at all | Fixed in b9cd9ad0 |
| Codex reader of I.21 to I.31, 2 | mishnah/I/21.md:3 | 2 | material | Pappus' fourth proposition, on a ratio less than 2 : 1, was joined to the scope of the first, "in any triangle but…"; in a given triangle neither line can be longer than the longest side, so it holds only in a triangle chosen to suit the ratio | Fixed in b9cd9ad0, and told as ours, after Heath's words, in b7b41f51 |
| Codex reader of I.21 to I.31, 3 | reading/I/24.md:1 | 2 | material | The reading line gave Hipparchus' table the standing of Ptolemy's, where Van Brummelen weighs scant evidence for it (pp. 41 to 44) | Fixed in b9cd9ad0, and "table of chords" made "table" in b7b41f51 |
| Codex reader of I.6 to I.17, 1 | mishnah/I/13.md:1 | 2 | editorial | "AB cannot lie along BE" holds only in the unequal case | Fixed in b9cd9ad0: "In the unequal case, …" |

The readers' other points are editorial, and none of them stopped a stamp. They wait for a follow-up under #34: the words of I.19's caption at a glance ("bigger", "longer"); the year given for Maor's book on I.25, which is the first edition's; I.21's ellipse, which passes through A (mishnah/I/21.md:7); the chapter of Van Brummelen's book on I.24; the letter of I.26's third angle in the modern way (mishnah/I/26.md:9); whose words I.32's quotation from Aristotle gives (mishnah/I/32.md:5); I.47's two reasons from Proclus, of which the page gives one (mishnah/I/47.md:1); I.37's Polybius, whom Heath gives after Cantor (mishnah/I/37.md:5); I.37's modern figure, which draws heights the paragraph does not use; "Proclus's" in a comment of I.43's record (:4); I.30's sentence on the straight line joined to the third (mishnah/I/30.md:3); `Prop44.place`'s docstring, which says Euclid moves the parallelogram "without a word" (Prop44.lean:32); I.34's caption at a glance, "the diagonal BC"; the years of Nahin's and Hahn's books on I.46, which are the first editions' where the links open later ones; a long line in Prop46.lean (:128); II.2's record (:24), which gives a reason as Euclid's; II.4's commentary (:3), where two other steps also go without a reference; II.10's commentary (:5), where "first printed in 1901" may be read of the whole commentary on the *Republic*; I.16's commentary (:1), where I.27 "draws" its parallels; I.44's record, where one clause on I.30 stands three times, and a straight line named K in `Prop44.place`; II.5's commentary (:3), where Heath's page follows the link to I.44; and, in II.5's and II.14's Lean notes, "(Common Notion 3)" beside Heath's "[I. 13]", plain letters in backticks, and `Prop45` names without their book.

### The Lean notes, apart and together again

On 22 October this branch's comment and docstring changes in sixteen Lean files, with the records of the fifteen propositions whose Lean they change, were moved to a branch of their own (fa4779ff, 3e583e4c), so that the text and the records could land apart from the Lean. An independent code review of both axes found that they do not stand alone. Those records carry reader-facing mends that the commentary and this report depend on: apart, II.14's page told its restriction two ways, reopening the pilot editor's notes 2, 4 and 6, and a STYLE example quoted a docstring the branch no longer had. So the two were merged back (0c004091), and the read-through lands as one change; the Lean files are again exactly as reviewed at 4248ed13. The stamps given on the other branch were given again here.

### The stamps now

50 of the 62 records of Books I and II carry a stamp of this read-through. 41 were given on 22 October by the readers above, each at a commit in this branch's history whose files are those of the head. Nine are from 21 October (I.28, I.33, I.36, I.38, I.42, II.6, II.7, II.12 and II.13), each a Claude reader's stamp on a proof Codex wrote, and their pages have not changed since. 22 carry a Codex reader's stamp: the twenty records of Claude's proofs, with I.41 and I.46. The twelve without one are those the first addendum lists (I.2, I.3, I.4, I.5, I.8, I.11, I.20, I.27, I.35, I.39, I.40 and I.45). Each of the 32 run lines the sign-off wrote on main (for #220 and #257) is kept, with this reading added.

### Still open after the second addendum

1. **The first part's items 8 and 9, and the addendum's item 2, on stamps shared with the sign-off, are settled** (#220): the sign-off's four parts are on main, and the shared records are read again above.
2. **Shared with work still in flight** (#34): the second axiom wave (#119) also changes the records of I.12, I.22, I.31 and II.10 and the commentary of I.4 and I.8, and lands after this; its readers read the shared records again. The citation sweep (#32) is not in flight as this is written; the first part's item 8 stands for it.
3. **The editorial points above**, for a follow-up under #34.
4. **The first part's items 1 to 7 and the addendum's items 1, 3 to 7 stand**, save that I.18's record is now stamped after its reading line's change (the addendum's item 5).
