# House style

How Stoicheia reads and looks: the voice, the page, the commentary, the words, the
quotations, the further reading and the figures. Everyone who writes for the project
works from it, people and agents alike. It grew out of the commentary on I.1–I.5, I.29
and I.47, the [read-through](reports/read-through-01.md) of Books I–III, the blind
readers' notes ([voice-01](reports/crew/voice-01.md), [voice-02](reports/crew/voice-02.md))
and Astra's [outside review](reports/outside-review-01.md), whose
[draft guide](reports/outside-review-01-guide.md) it adopts with warm thanks.

Each rule has one home. This page holds the reader-facing ones. The order of priorities,
the ten rules and what never to do are in [AGENTS.md](../AGENTS.md); statements,
representations, the Lean as an argument and what each check shows are in
[FORMALIZATION.md](FORMALIZATION.md); tasks, ownership, review and release are in
[WORKFLOW.md](WORKFLOW.md). Reviewed pages to learn from are in [examples.md](examples.md).

**Requirements and defaults.** A requirement holds on every page. A default is the usual
shape of a page, and a page may leave it for a reason a reviewer can see. A default never
justifies padding, and never hides a limitation: when one pulls against accuracy, accuracy
wins. A rule that a script checks is marked **[checked]**, and fails
`scripts/check_style.py`; a rule marked **[reported]** is listed by the script for a
reader to judge, and fails nothing. Section 8 gathers both lists.

## 1. Voice

**One warm, plain voice.** A friend who knows Euclid well, talking over his figure with a
curious reader, and interested in the mathematical step. Use concrete objects and verbs:
name the points, and say what is constructed, what is equal, where a point lies and why
the inference follows. Keep sentences short and plain. Three that have the voice:

- "So the tacit rule is doing real work: it says the plane has the square roots that ruler
  and compass need." (I.1)
- "Generations of schoolchildren knew it as the *pons asinorum*, the bridge of asses." (I.5)
- "Our statement gives the perpendicular, and our proof has to find its foot." (II.12)

**State facts directly; qualify uncertainty precisely.** A proved equality is said plainly.
A conjecture about the history of the text sounds like one, and says whose it is. A
necessary condition sits beside the claim it qualifies, not three paragraphs later.
Historical attribution, interpretation and the limits of a representation need the same
precision as a hypothesis. What this rules out is the vague hedge and the aside written
for a checker: no "note that", "strictly speaking" or "it is worth noting" **[checked]**.

**Who speaks.** "We" is the project: its statements, figures, choices and discoveries
("our I.1 lets the side be named"), and it may take the reader along ("Postulate 3 lets us
draw a circle"). Use it where it comes naturally; there is no count. "Euclid" is the
historical argument, "Heath" the translation and its notes, and "Lean" the language and
its checker ("Lean checks the formal derivation"); "the Lean" is our proof's code, where a
sentence needs it ("the Lean cites I.10"). No "I", "me" or "my" outside quotations
**[checked]**.

**Production stays out of the mathematics.** Readers meet Euclid, Heath and the proof, not
the people or agents who made the page. The mishnah, the captions, the reading lines, the
book introductions, the Lean comments, the review records' notes, the catalogues and the
README carry no crew talk **[checked]**: "Book Zero proves it once", not "the first mate
added it". Roles, model names and how the work was shared belong in
[WORKFLOW.md](WORKFLOW.md), [PROGRAM.md](PROGRAM.md), the briefs, `docs/reports/crew/` and
the README's "How it was made", which says plainly how the work is done. This paragraph is
the one home of that boundary between the crew and the reader: [AGENTS.md](../AGENTS.md),
the [orders](templates/orders.md) and every fleet prompt point here instead of restating
it, and `scripts/check_style.py` checks its words (S2, section 8).

**People by name,** spelled as Heath spells them (Proclus, an-Nairīzī, van Pesch). A
modern author in full at the first mention on each page, then by surname:
Augustus De Morgan, Henry Savile, Robert Simson, John Playfair, J. L. Heiberg, Paul
Tannery, Isaac Todhunter, David Hilbert, Christopher Clavius, Dionysius Lardner,
H. G. Zeuthen. Heath is Heath. Say who saw a gap first, where we know it, and call a find
new only when it is.

**Nothing competitive.** Nothing here is first, only, better or unlike anyone else's work,
and no page claims a novelty or a superiority it cannot support. Related work is cited
accurately and warmly: say what it does well, and link to it. "Only one triangle" is
geometry, and fine **[reported]**.

**Each paragraph earns its place.** It gives mathematics, historical evidence, a way into
the figure, or the reason for a formal choice. A paragraph that could be pasted unchanged
onto ten neighbouring pages belongs in the book's introduction, or nowhere.

**Punctuation.** No em dashes **[checked]**: a comma, colon or full stop does it. En dashes
for ranges (I.1–I.24, pp. 253–254). Straight quotation marks (section 5).

**Lean notes** (the `/- … -/` remarks and the docstrings of helpers) read as the mishnah
does. Each is a full sentence or two, and may say "we". Heath's letters are plain (AB, not
`AB`: the page shows the Lean in a code block, where backticks print), and so are the
letters of a step written once over any letters, as Book Zero's and the foundations' are,
the Lean's variables among them: the point P, the straight line PQ, the circle ABCD. A
code span of letters alone fails **[checked]**. Backticks are for Lean names and
expressions alone (`Prop30.meet`, `∠ A B C`), and hypotheses are said in words (below). A
shared step is explained once, where it is first used or in the book's introduction, and
pointed to elsewhere: "I.5 (`Prop5.base`)", "as in III.1 (`Prop1.perpendicular`)". A note
does not retell the mishnah: the note says how, the mishnah says why. Where the comments
go, and what the `--` lines are, is [FORMALIZATION.md](FORMALIZATION.md)'s business.

**Hypotheses in words.** This paragraph is the rule's one home. A hypothesis is said in
words, never by its local name: "the bases BC and CE meet at C", not `hBCE`, a name Lean
knows only inside its theorem. That holds wherever a reader meets one: in the mishnah, the
Lean notes, and a review record's notes, whose `hypotheses` the page shows as its extra
hypotheses ([review/SCHEMA.md](../review/SCHEMA.md)). Where it helps a Lean reader find
the condition in the listing, the condition may follow in backticks, as a Lean expression:
"the bases BC and CE meet at C (`Between B C E`)". In every text it reads (section 8), the
check fails a local name in backticks, alone or before its type (`hBCE : Between B C E`)
**[checked]**. A record's `#` comments, which no page shows and only its maintainers read,
may name a hypothesis as the Lean does.

### Avoid and prefer

The right-hand column gives sentence patterns, not quotations to copy.

| Avoid | Prefer |
|---|---|
| "Lean cannot represent a segment without its circle." | "Our representation of a segment includes its circle." |
| "This proposition needs Postulate 5." "I.1 to I.28 never need it." | "This proof uses Postulate 5." "The proofs of I.1 to I.28 do not use it." |
| "Euclid cites I.3 here." | "Heath's reference here is I.3." |
| "Lean verifies every word of Euclid." | "Lean checks the formal derivation; how it follows Euclid's argument is reviewed separately." |
| "The diagram is obviously valid." | "The two straight lines cross at X, between A and D, and that puts CB within the angle ACD." |
| "The remaining cases are analogous." | Name the symmetry, the exchange of letters or the shared lemma: "it is Euclid's figure with C and D exchanged". |
| "Euclid forgot to justify the step." | "The text gives no reason for the meeting; our proof uses the rule that two such circles cross." |
| "This elegant formulation reveals Euclid's deep intuition." | Say which construction or inference makes it useful, or which cases it covers. |
| "For completeness, it is worth noting that…" | State the fact, and say why it matters here. |
| "The first mate added a helper for this case." | Explain the case, and the fact the helper proves. |
| "Unlike earlier formalizations, this work…" | Say what this page does, and cite related work accurately and warmly. |

## 2. The page

Each proposition's page, `book/<book>/NN.md`, is generated by `scripts/render.py` from the
sources, and nobody edits it by hand. It always runs in the same order, so a reader knows
where to look:

1. **Navigation and title.** The book, the previous and the next proposition; the
   number, and a descriptive title in Euclid's words; then jump links to Euclid's proof,
   the Lean, what it rests on and the mishnah.
2. **Heath's enunciation,** complete.
3. **The status line.** One short line beside the badge answers three separate questions
   about the same declarations: is the formal proof finished; does the statement cover the
   whole enunciation, or a restricted case, or only some clauses; and is the argument
   Euclid's, Euclid's with a step done differently, or an alternative? It also says when
   an axiom already contains the proposition, or supplies a step of a proof of it, as the
   record's `[overlap]` names the kind. An exception shows here, in a few words,
   before the reader meets the green check, and never only in the mishnah; the detail is
   in the table under "In Lean". The words come from the proposition's review record
   ([review/SCHEMA.md](../review/SCHEMA.md), its `short`); what they mean is in
   [FORMALIZATION.md](FORMALIZATION.md).
4. **The figure at a glance,** with its caption.
5. **Euclid's proof:** his figure with Heath's letters, a figure note under it where the
   figure shows one case of several, draws every case, or our drawing departs from Heath's
   (section 7), and Heath's proof in full.
6. **In Lean:** a short table of the formal facts (proof, statement, extra hypotheses,
   argument, representation, overlap with an axiom, and what was reviewed, at which
   commit); a clause map where the statement leaves a clause out, which says the omission
   in full once; "How the Lean follows the text", the review record's notes, each led by a
   plain word for its kind (a step done by a lemma, sentences carried together, a further
   case, a step already given, a step argued another way, a passage left in Euclid's
   words); then the listing, with the main theorem open, its helpers folded before it and
   the declarations after it folded and named by their role.
7. **What it rests on:** the certificate for every declaration the page shows (the
   theorem, its porism, its companions), with Heath's references beside the Lean's
   citations, the postulates, definitions taken as axioms, Common Notions and tacit
   rules, and the generated line naming the shared steps that bring in propositions.
8. **The mishnah,** our commentary (section 3). The page sets any modern figure under
   its paragraph "The modern way" (section 7); S24 checks that the source has the paragraph.
9. **Further reading,** when something apt exists (section 6).
10. **The foot of the page:** links to the scan leaves of Heath's text and figure, the
    thanks to the authors of System E and LeanEuclid, and the navigation again.

**Why two figures.** The figure at a glance, in Oliver Byrne's colours, shows the main
relation before a word is read: equal things share a colour, and a reader sees what the
proposition is about. Euclid's figure is the one to follow the proof by, sentence by
sentence. Each does what the other cannot, and neither is decoration. Both carry Heath's
letters, the names the text and the Lean use, so a reader passes from the colours to the
proof by the same A and B (section 7). Colour may carry an equality, but never alone: the
caption names the colours, so that a reader who cannot tell them apart still has the point.
Where the modern way is easier to follow with a picture, it has a third, its own figure,
drawn as Euclid's is and with his letters, so that a reader moves between the coordinates
and the proof by the same names (section 7).

**Each thing in one place.** Scope and exceptions go at the top, in the status line and
the table. Citations, postulates and rules go in the certificate and the line under it.
The book's shared machinery goes in its introduction, the finer gaps in its gap catalogue,
and a departure of our drawing in the figure note. The mishnah tells the story behind any
of these only when it is this proposition's story. A normal page stays uncluttered; an
exceptional page carries enough to prevent a false impression.

**Each book's index page** opens with the book's introduction, `mishnah/intro/<book>.md`,
in the same voice. It tells the book's shared machinery once (section 3) and links the
book's brief. Every book with pages has one **[checked]**.

## 3. The mishnah

**What it is for.** The mishnah, `mishnah/<book>/NN.md`, explains why Euclid's proof and
ours look as they do; a Lean note explains how a particular step works. The proof and the
table are on the page, so the mishnah says why they look as they do, not what they say. It
does up to four things, in about this order:

- **The mathematical move.** What Euclid does here, and why this step matters: a way into
  the figure. Open on Euclid.
- **The historical or interpretive point.** What Heath, Proclus or another reader adds, when
  it adds something. A quotation is welcome and never compulsory. Cite the source, keep a
  chain of reports clear ("Heath reports Proclus"), and keep evidence apart from
  interpretation.
- **The formalization's important decision.** A real gap, case, construction choice,
  representation or change of route, usually in one paragraph, told on the page where it
  first matters, and told as what it is: "Euclid's figure quietly settles the order of its points, and Lean wants each
  of those facts said" (I.5). For the hardest formal blocks (I.7, I.35, I.47, III.8 and
  their kin) say what obstacle the block resolves, and why Euclid did not need to say it.
  The finer gaps go in the book's gap catalogue, `docs/reports/gaps-book-<book>.md`.
- **The modern way,** where one helps: a correct modern comparison, with the conditions it
  needs, in coordinates, vectors, complex numbers or matrices, exactly right, and as long
  as accuracy needs. It is optional: a page leaves it out when it would only restate the
  proposition in symbols. When a page has one, it is a paragraph of its own that opens
  **The modern way.**, usually the last, and that paragraph alone may set mathematics in
  `$…$` (section 4, "Mathematics"). Say so when it is not Euclid's route or changes the
  construction (I.43, I.48; I.2's L lies on DA produced, so it is not A + (C − B)). Write
  it for a curious reader: words where they serve ("the argument of", "turn B through θ"),
  a formula where it is clearer (`$e^{i\theta}$`), and only the range of a variable the
  reader needs. A modern method may recur on neighbouring pages when it is the clearest
  correct comparison: link the earlier page and give this page's own point.

These are functions, not four compulsory paragraphs: combine, expand or leave them out as
the proposition asks.

**Its shape.** There is no count of words or paragraphs: a mishnah is as long as its
proposition needs, and a proposition that offers little gets a short one. Nothing is
padded to reach a length, and no qualification is cut to keep one. A paragraph may open
with a short bold lead where a hook helps the reader, proposition-specific and ending in a
full stop (a question mark if it asks): a question (**Must the circles meet?**), a claim
(**A compass that closes.**), or Euclid's or Heath's words (**"Less than two right
angles."**). A lead that could head a paragraph on another page is a label. No paragraph
needs a lead, and the pages should not fall into one rhythm, of leads or of lengths.

**Lean names.** A few exact Lean names, in backticks, where they help the reader find the
work (`circles_meet`, `Prop1.figure`): usually four at most **[reported]**, and every one a
name Lean knows **[checked]**.

**Bookkeeping.** The page's table shows what the proof rests on: its postulates,
definitions, Common Notions and tacit rules, counting those of the propositions it cites;
and the generated line under it, "Some of these come in through lemmas shared by many
proofs", names what each shared step brings in. So the mishnah does not restate the table, say what the certificate "cites" or
"records", explain what a cited proposition or shared step brings in, or trace the paths
of Postulate 5, Postulates 1 to 4, Definition I.15, the Common Notions or the tacit rules.
It speaks of them only when the reason is this proposition's story, and then says "the
Lean cites": a departure from Euclid's route (I.2 uses no Postulate 2; I.5 takes the produced
sides as given, but still rests on it through proved rules, in its own Lean the order rule
`Tacit.between_of_between_right`, beneath `OnRay.between_of_len_lt`, and Metric 8,
`Tacit.area_swap`, and through I.4, which it cites;
the Lean cites I.10 in I.42 and I.17 in II.12, where Heath gives no reference: one clause
naming the step), a gap the text leaves (I.1's circles, I.35's G), or a landmark
(Postulate 5, called on in the text at I.29, I.44 and II.10; I.31's proof, which does not
use it).

**Told once.** Each book's shared machinery is told once, in its introduction. Book I's
tells System E, Book Zero, Postulate 1 naming a straight line, `produce_longer`,
superposition in I.4 and I.8 alone, Postulate 5 beneath every proof from I.29 on but
I.31's, and `Prop30.meet`, credited to Proclus (Heath, vol. 1, pp. 207 and 316). Book II's
tells the steps of `Elements/BookII/Rectangles.lean`, with `Parallel.between`,
`quadArea_add_of_parallelograms` and the unlettered point of `exists_off_line`, and how
Book II's areas correspond to the pieces drawn: which expression is which piece, and why
the pieces make up the whole. Book III's tells how proofs take a circle's centre: from
geometric data such as equal circles, by III.1's construction in III.4, III.8 and III.17,
and from `exists_centre` in III.2 and where Heath gives no reference. It tells the constructions whose references the text
leaves unstated (I.10, I.11, I.12, I.23), its definitions and the circumference measured by
twice its angle, the steps of `Squares.lean`
and `Circumferences.lean`, the porisms of III.1 and III.16, and where its statements part
from Euclid's. A shared step may be told on its home page (II.1's rectangle contained,
II.4's "For the same reason"); elsewhere it gets a clause at most ("as in II.4"). A
limitation that affects this page's claim stays visible on this page, in a clause, even
when its full explanation lives elsewhere.

**Retired refrains.** Each was once said on a dozen pages. In the mishnah of a
proposition, the phrases in quotation marks below are failed by the script on any page
not named **[checked]**; what the list says besides is judged by a reader:

- "I.4 and I.34" for a drawn rectangle; Proclus on parallels, and "a straight line meeting
  one of two parallels meets the other"; `exists_off_line`; `Rectangle.of_right`;
  `Square.described`: told in the book's introduction, with a clause on the home page. The
  words "with no letter", "proves it once", and "under I.31" in a sentence naming Proclus:
  nowhere.
- "Uses Postulate 1", "brings it in": I.1 and I.3 only.
- "Comes in through" (as in "Postulate 5 comes in through …"): I.29 only, and the
  introductions, which the rule does not read.
- "Certificate cites", "certificate records", "Of the postulates", "besides Euclid's",
  "just Euclid's three": nowhere.
- The leads "What Lean made us say.", "What else Lean made us say.", "What it rests on.",
  "Where the parallels meet.", "Naming the pieces.", "Where X falls.": nowhere. Name the
  discovery, ask the question, or quote, as I.35 does: **"He allows this to appear from
  the figure simply."**
- "Lean wants it said" and its kin, "Lean asks why", "Lean makes us say so": I.1, I.5 and
  I.22 only, for I.22's payoff, "Lean is exactly that dull"; elsewhere state the gap and
  say that we prove it.
- "And the Lean cites it." closing a sentence: nowhere; the table shows it.
- "We give his argument once": nowhere in the mishnah; the introduction and the Lean notes
  may say it.
- A paragraph closing on "our statement asks for …": only where the hypothesis is the
  story (I.33's "in the same directions", I.37's coinciding vertices).
- The same figure-reading point page after page (which side a point is on, why the angles
  are alternate, Postulate 4 and `∟`, `Prop5.base`, `produce_longer`): told once where it
  first does work (I.27, I.11, the introduction), a clause elsewhere. This one is judged by
  a reader, not the script.

## 4. Words

**Euclid's words for Euclid's things:** straight line, produced, joined, greater and less,
the angle ABC, the square on AB, the rectangle contained by AB, BC, circumference (an arc),
touches (a tangent), segment, the angle in the segment, the angle at the centre. Never
"chord" or "segment" for a straight line (save Heath's segments of a straight line cut at
a point, in Book II and III.35), "arc" outside the modern way, or "the tangent" where
Heath does not write it. "Diameter" is Euclid's word for a diagonal: gloss it at its
first use in each book (in Book III it is the circle's). Gloss "applied" (I.44) and
"gnomon" (II.5). Modern words stay in the modern way, and a Lean word gets a plain gloss
the first time it appears.

**Tightening the language.** These are the habits that the language passes
([#111](https://github.com/dodecaplex-co/stoicheia/pull/111) and
[#115](https://github.com/dodecaplex-co/stoicheia/pull/115)) and read-through 02 removed from
the commentary, the reading lines, the records and the Lean notes, each with one example;
section 1 sets the voice and the rule for vague hedges.

- Labels for leads: I.21's lead "Three facts in one word." goes, and the paragraph opens on
  its claim, "Our statement reads 'within the triangle' as three facts".
- Announcing sentences, caught in the passes' own reviews: "The proof is short" gave way
  to "Euclid joins BC" (I.33).
- One opening for every reading line: each opened "For …", and II.1's "For algebra drawn
  as rectangles" gives way to what Nelsen's book shows. Section 6 gives the reading lines
  their shape.
- Inflated praise: Fowler's chapter on II.10 loses its "beautifully argued".
- Padded phrases: "Book VI has a name for this cut" becomes "Book VI names the cut" (II.11).
- Recaps in threes: I.41's commentary drops its retelling of Heath's summary of Proclus'
  three results, "greater than, equal to or less than double the triangle", and keeps
  Proclus' construction.
- Sweeping closings: "Book II leans on it again and again" becomes "II.2 to II.8, II.11 and
  II.14 use it again" (II.1).
- Stock closings: II.2 ended on a modern way that only restated it, "the whole times each
  part, added together, is the whole times itself"; it now ends on Heath's count of the
  words in Euclid's proof.
- Retelling the Lean notes: I.17's commentary drops "we prove his case for any triangle and
  call on it three times", which its Lean note tells.
- Refrains: I.21's record said "a rule we assume, not a proof" at four steps; now each of
  its two rules is "a rule we assume" once, and pointed back to after.
- Change-logs on the page: a docstring on I.13's page, "This was an assumption until 19
  October 2026 and is now proved from I.13 and Common Notion 3", now says "We prove it from
  I.13 and Common Notion 3".
- Blaming Lean for our choices: I.7's "Lean has no reader to leave cases to" becomes "A
  proof that leaves no case to its reader must find D in four places".
- Certainty beyond the evidence: I.18's "We prove both", of two steps, one of them a rule
  we assume, now says "we prove it" of the first and "which we assume" of the rule.

Two things stay: a list that supplies necessary cases, and a qualification that belongs to
the claim, which section 1 requires.

**Tacit rules,** never "tacit assumptions" or "tacit laws", outside Heath's words
**[checked]**.

**Heath's references.** The bracketed references in Heath's text, [I. 3], [Post. 1],
[C.N. 1], are his editorial references. Heath remarks, of an Arabic version that adds such
references with care: "Such specific quotations of earlier propositions are rare in
Euclid" (vol. 1, p. 83). So our prose calls them Heath's references, never Euclid's
citations: no "Euclid cites" and no "Euclid's own bracketed references" **[checked]**.
Where a step has none, say so of Heath: "Heath gives no reference here: it is I.10"
**[reported]**. An absent reference does not show that Euclid gave no reason, and a
reference is Heath's reading, not a machine-checked reconstruction. "The Lean cites" is for
the dependencies the certificate computes. The three stay apart: Heath's references, the
Lean's dependencies, and our account of the argument (the review records and the gap
catalogues). In our prose, "brackets" alone means Heiberg's, round a passage he judged
added later, or Heath's own round III.12.

**"This proof uses Postulate 5."** Say what a proof uses: "this proof uses Postulate 5",
"the proofs of I.1–I.28 do not use it". Never "never need it" **[checked]**, and not
"needs Postulate 5" of a proposition or a proof **[reported]**. Whether some other proof
could do without the postulate is a different question, and a claim of that kind names its
evidence ([FORMALIZATION.md](FORMALIZATION.md), section 9).

**Our representation, not Lean's limits.** What is our choice is said as ours: "our
representation of a segment includes its circle", "our foundations allow superposition
only in I.4 and I.8". Not "Lean cannot" **[reported]**.

**A figure given with its triangles.** I.45 and II.14 are full through their outline
companions ([#116](https://github.com/dodecaplex-co/stoicheia/issues/116)), which take a figure
given by its outline alone; their older companions take a figure "given with a checked
division into triangles", and every text a reader meets that describes those (a record, a
commentary, a file's notes, an introduction, a gap catalogue) uses the same words: given
with, not "supplied", and not the tag's "dissection". Its triangles "do not overlap, no
point inside two of them", in full at their first mention in each of these texts, and "lie
apart" after. "Equal to the figure" there means equal to those triangles together, which is
the figure's area, the same for every division. Where a main theorem takes its two
triangles unchecked, the sentence that describes it says so. In these sentences the figure
is divided, not cut; "outline" never stands unexplained for its boundary; and what Euclid
takes for granted there is not called "tacit", a word kept for the tacit rules.

**Numbers and names.** Our prose writes I.5, II.4, and I.1–I.24 with an en dash; Postulate
3 and Common Notion 1 in a sentence, Post. 3 and C.N. 1 in parentheses and tables. A
definition always keeps its book, since Books II and III have their own: "Definition I.15"
in a sentence, "Def. I.15" in parentheses and tables **[checked]**. The generated tables
write "Def. I.15" in every book, Book I's included, and "Def. III.11". [I. 5] appears
only in Euclid's text, and "I. 5" only inside Heath's words. A tacit rule is named by its
docstring label, "System E, Intersection 5" (a diagram rule, §3.4 of System E) or "System
E, Intersections 8" (a construction rule, §3.3), or by its Lean name. Titles and foreign
words are in italics: *pons asinorum*, *reductio ad absurdum*.

For an exact count from [scripts/generated_counts.py](../scripts/generated_counts.py),
write &lt;!-- count:vocabulary -->91&lt;!-- /count -->; `render.py` fills only the
number. Append `:word` to the name for words, or `:Word` for a sentence's first word.
The module lists the names and prints their current values when run. Literal examples
escape `<`, even in code spans. Markers are refused in the decisions log, its page and
the files of `docs/decisions/` alike, and in `docs/reports/`, except the living
`gaps-book-*.md` and `overlaps.md` catalogues.
They are also refused in `book/`, `CERTIFICATE.md` and `GRAPH.md`: copied prose keeps
the computed value but loses the count comments. A marker may stand elsewhere in
README.md or PROGRAM.md, but may not overlap README.md's `scope` regions or PROGRAM.md's
`status` region, including their delimiters, since `render.py` replaces those regions.
Only tracked Markdown and review records are scanned, with Git's work tree checked against
the supplied root; symlinks in any component below it and paths resolving outside it are
refused.

**Heath's letters, one style.** Heath's letters name points, straight lines and figures,
and a reader meets them in the text, in both figures, in the Lean and in the modern way.
They look the same in each: upright, never italic. Heath's page sets them in italic, but a
Lean listing cannot, and the page shows Heath's sentences there too, as `--` lines; so the
letters take the Lean's upright style everywhere. In prose they are plain capitals
(section 5, "The letters rule"); in the figures, upright Georgia (section 7); in a formula,
`$\mathrm{A}$`, or `$\mathrm{(C - A)/(B - A)}$` for a whole expression of them. The
variables of a formula (a, r, z, θ) are not Heath's letters, and take mathematics' usual
italic.

**Mathematics.** Angles are in radians throughout, as modern mathematics measures them: a
right angle is π/2, two right angles π, a whole turn 2π, and an angle of a triangle lies
between 0 and π. No degrees, and no "two right angles" inside a formula ("cos θ falls as θ
grows from 0 to π"); Euclid's right angles stay in Euclid's words, outside the modern way.
A formula may be written in plain characters, (a + b)² = a² + b² + 2ab, or, in the modern
way alone, in TeX between single dollars, `$e^{i\theta}$`, which GitHub renders as
mathematics. TeX stands nowhere else in the mishnah: not in another paragraph, and not
outside the dollars **[checked]**. The modern way's paragraph ends where Markdown ends it:
at a blank line, or at a line that opens a heading, a list item (a numbered list only
from 1), a quotation, a code fence, an HTML block, a rule or a table **[checked]**. A line
that only looks like one, `|z| is one` or `2. So`, goes on with the paragraph. A span is
mathematics only where GitHub reads it so, and the check refuses the shapes known to break
one **[checked]**. GitHub's renderer, tried with sample spans on 18 October, needs the
dollars in pairs within the paragraph, and never `$$`; each span on one line, with no space
just inside either dollar; the opening dollar at a line's start or after a space or "(",
and the closing one before a space, a line's end or one of the punctuation marks that S10
lists (section 8); braces that balance; no backslash before a punctuation mark, which
GitHub's Markdown removes (write `\lbrace`, `\rbrace`, `\thinspace` and `\Vert` for `\{`,
`\}`, `\,` and `\|`); and `\lt` and `\gt` for < and >, which GitHub escapes twice inside a
span. Those lost backslashes show that GitHub's Markdown reads inside a span, and by
CommonMark's rules for emphasis, checked with a CommonMark parser and not tried on GitHub,
a `*`, or a `_` after anything but a letter or a digit, pairs with another across two
spans. So a span holds no `*` (write `\ast`), no `~`, which GitHub can read as
strikethrough (write a space or `\sim`), and no backtick, which opens code; and a `_`
stands straight after a letter or a digit: `x_{1}^{2}`, not `x^{2}_{1}`, and
`\mathrm{A_1}`, not `\mathrm{A}_1`. A shape not yet found may still break, so the reviewer
sees each span rendered on GitHub (section 8, the reviewer's checklist, item 5).
`scripts/render.py` copies the mishnah onto its page unchanged but for its count comments
and the insertion of its modern figure beneath "The modern way", so the page shows the
same mathematics.

**The modern way's notation.** In a `$…$` span, a vector is a bold lower-case letter,
`$\mathbf{u}$`, never `$\vec{u}$`. The modern figure beneath sets the same name in italic,
as section 7 asks; the bold is the paragraph's mark of a vector. A vector between Heath's
points is written `$\mathrm{C - B}$` or with an arrow over the point letters,
`$\overrightarrow{\mathrm{AC}}$`, as in Books II and III. A length or an absolute value
takes plain bars, `$|\mathbf{u}|$` or `$|y|$`, never `\lvert` and `\rvert`.
Write the dot product `$\mathbf{u} \cdot \mathbf{v}$` and the plane's cross product
`$\mathbf{u} \times \mathbf{v}$`; the components `$u_{1}$`, `$u_{2}$` stay italic.
For Heath's upright letters, see "Heath's letters, one style" above; for radians and
the rules every span must obey, see "Mathematics".

**System E and LeanEuclid** are thanked by name in every page's footer, so the mishnah
does not thank them again; a particular debt is still said where it falls (Intersection 4
is LeanEuclid's corrected form).

## 5. Heath's text and quotations

**`heath/` is Heath's, untouched.** Each file opens with its source comment (volume, pages,
scan leaves, the leaf of the figure), then the enunciation in italics, then one sentence
or clause per paragraph, as the `--` comments take them. A change is made only against the
page image, and carries a comment naming the leaf checked. Heath's square brackets are kept
exactly: his references [I. 2], [Post. 3], [C.N. 1], [Def. 15], [Post. 4 and C.N. 1];
II.10's [I. Post. 5] with its book; Book III's [I. Def. 10] (another book's definition,
with its book), [III. Def. 3] and [III. 1, Por.] (a porism, cited with its proposition);
Heiberg's brackets round a passage he judged added later (I.4, I.15's Porism), with a
comment; and Heath's own round a whole proposition (III.12), with its reason. In the Lean,
a `/- … -/` remark may give a step that Heath leaves without a reference its
justification in his form, as a `--` line would: "subtracted from each [C.N. 1, C.N. 3]".

**The scans.** Heath's volume 1 (Books I–II) is the Internet Archive's
`thirteenbookseu02heibgoog`, where page N is leaf N + 20; volume 2 (Books III–IX) is
`thirteenbookseu00heibgoog`, where page N is leaf N + 12. Page N's image is
`https://archive.org/download/<id>/page/n<leaf>.jpg`, and the OCR text, flattened, is what
a quotation is first checked against. The page image decides.

**Quoting Heath.**

- Heath's exact 1908 words, in straight double quotes **[checked]**, with the page: "(vol.
  1, p. 242)", "(vol. 2, pp. 63–64)" when the passage crosses a page, and "(Heath, vol. 1,
  p. 252)" when the sentence does not name him. Those Heath reports (Proclus, Todhunter, De
  Morgan) take his page, and the sentence makes the chain plain. Every reference to Heath
  keeps its volume, however close the one before it: "(vol. 1, p. 243)" after "(vol. 1,
  p. 242)", never "(p. 243)", since Heath's volumes share page numbers and each reference
  must be checkable on its own. Never invent a quotation or a page.
- Single quotes inside, "…" for a cut, and brackets inside are Heath's own.
- Heath's prose has em dashes, and a page has none (section 1): end the quotation at his
  dash, or cut it there with "…".
- **Italics.** Keep Heath's italics for his emphasis and his titles: those he printed, all
  of them, and only those ("the two circles *will* meet"), as `*…*`. Add none. Heath sets
  every enunciation in italic type, which is his setting, not his emphasis, so words quoted
  from an enunciation stay roman (I.14, I.17, I.33, II.1); a theorem he states in italic in
  a note keeps its italic (Heron's converse, under II.12).
- **The letters rule.** Heath's letters are plain everywhere, inside his quotations too
  **[checked]**. His page sets them in italic; ours writes them as the rest of the page
  does: "the middle point of CE" (vol. 2, p. 8), not "of *CE*". Where his italic runs on
  through letters and words together, the words keep it and the letters do not: "AE, EB,
  EC *will also pass through the remaining points of the segment*" (III.25). The figures
  set the letters upright too: one style for them everywhere (section 4).
- Each of Heath's notes is quoted on the page of the proposition it belongs to, and
  elsewhere only referred to in a clause: "as Todhunter remarks under I.14". A passage from
  his introduction, or from his notes on the definitions and postulates, is quoted once,
  where it matters most, and referred to elsewhere.

## 6. Further reading

`reading/<book>/NN.md`, shown after the mishnah, is one to three friendly lines, each a
list item **[checked]** naming a work from [the reading list](reading.md) and what it
gives this proposition. A line goes in only where a verified work truly helps with this
proposition; nothing is added to fill a slot, and with nothing apt there is no file and no
section. A work is new to the project only once it is on the list, checked against the
work itself, its publisher or a library catalogue, and in [references.bib](references.bib).
Every link a line gives is one the list gives **[checked]**.

Each item stands on one line of the file **[checked]**, however long; the examples below
are wrapped only for this page. A line says, in its own words, what a reader of this
proposition will find in the work, and it gives the work's facts: the author in full; the
title with the list's link, in italics for a book and in quotation marks for a paper or a
web page, as the list has it; the year of the edition linked, with "free online" beside it
where the list says **Free**; and the chapter, where a checked table of contents gives
one. The order and the sentence are the writer's: a line may open on the work, on its
author or on what it shows, and the lines of a book should not fall into one mould. Two
shapes, of many:

> - For the dot product of the modern way, Grant Sanderson's [*Essence of linear
>   algebra*](https://www.3blue1brown.com/topics/linear-algebra) (2016, free online),
>   ch. 9, "Dot products and duality", one short animated lesson that explains it in
>   pictures.
> - Grant Sanderson's [*Essence of linear
>   algebra*](https://www.3blue1brown.com/topics/linear-algebra) (2016, free online) shows
>   the dot product in pictures, in ch. 9, "Dot products and duality": one short animated
>   lesson.

A work is described in full the first time it appears in each book. A later line keeps a
few words on what the work is, when it has them, or else links the page where it is
described, `(also on [I.18](../I/18.md))`, and says what this page finds there.
A reader may land on any page, so a line never points back in words alone. A line that
would fit any page of the book is left out.

## 7. Figures

Each proposition has two required figures, `NN-idea.svg` and `NN.svg`, on the parchment
card (`#fbf7ee`, a rect with `rx="10"` over the whole canvas), in Georgia. It may also
have `NN-modern.svg` beneath its paragraph **The modern way.** Section 2 says why the
first two are required.

**`NN-idea.svg`, the figure at a glance.** A canvas of 400 × 300 **[checked]**. Byrne's red
`#d0312d`, yellow `#f2b705`, blue `#1f5aa6` and black `#222222`, and white only for grid
lines and for numbers on a fill, as in I.47 **[checked]**. Equal things share a colour, and
Heath's letters name every point it shows; any letter is Heath's, and may name a line or a
figure as well (below). The title is `<book>.N at a glance`, the proposition's book by its
numeral and its number with no leading zero ("II.4 at a glance", "III.17 at a glance"),
with a name after a colon if it has one ("I.5 at a glance: the bridge of asses", "III.31 at
a glance: the angle in a semicircle"). The `<desc>` is the caption on the page: one or two
short sentences in the house voice, the colours named in brackets, about 40 words
**[reported]** and 50 at most **[checked]**.

**`NN.svg`, Euclid's figure.** 400 wide, and 440 at most where two or three of Heath's
figures stand side by side (III.25, III.33, III.35, III.36) **[checked]**. Upright letters
(section 4) at 17 **[checked]**; ink `#3b2f2f` for lines, dots and letters; circles
`#8c7b62`; what the proposition is about in `#a0522d`, drawn heavier; triangle fills
`#e9dcc0` at 0.55; no other colour **[checked]**. Dots of radius 2.6, lines 1.6, circles
1.3, what the proposition is about 2.4 to 2.6, angle marks in `#8c7b62` at 1.3
**[reported]**, and no stroke thinner than 1.2 or heavier than 3.2 **[checked]**. The title
is `Euclid <book>.N: …`, a name after the colon ("Euclid II.1: a rectangle cut into three
rectangles", "Euclid III.1: finding the centre of a given circle"), with no caption
**[checked]**.

**Heath's letters, all and only [checked].** Each point stands where the proof puts it
(I.6: D on AB). The Lean uses the same letters, save in a helper written once over any
letters (`Prop44.place`). A point Heath leaves without a letter gets a name in the Lean
and none in the figure; a letter Heath gives a point the Lean does not need (III.3's C and
D) is still drawn; the letters inside shared steps do not count; and "PORISM" is not a
letter.

**One letter, one point [checked].** A letter names one thing, a point unless Heath gives
it to a straight line or a figure (below), and the figure leaves no doubt which. It draws
each letter once, or once in each of Heath's figures where two or three stand side by
side; and each letter stands 2 clear of every stroke and every dot, and of the canvas's
edge, so that no straight line or circle runs through it and nothing touches the frame.
The same holds at a glance (S26, section 8). In the Lean, a letter that names one of
Heath's points names no straight line or circle, which a reviewer checks (section 8, the
reviewer's checklist, item 16).

**The same letters at a glance [checked].** Byrne's book uses coloured diagrams and
symbols "instead of letters for the greater ease of learners", as its title says, and its
pages are a delight without them. We add Heath's letters all the same, because a proof is
read by its points: the colours carry the equalities, and the letters tie them to the
text, so that the yellow angle at B is the angle ABC of I.5's proof. The figure at a
glance carries Heath's letters, the same names as Euclid's figure and the Lean, at every
point it shows, so that a reader can follow it however it turns or reflects Euclid's
figure. Each letter is one that `NN.svg` draws, upright, at 14, small and beside its point,
in the figure's black `#222222`, clear of every colour where there is room, and 2 clear
of every stroke and dot (above).
A point inside a coloured piece, with no parchment near it, takes its letter on the fill
(I.43's K, II.4's G): in black on yellow, and in the parchment's `#fbf7ee` on red, blue or
black (II.12's D), where black would hardly show. A point is shown when it is drawn as a
dot, ends a straight line or is a corner of a coloured figure, and its letter stands
within 30 of it; a straight line shorter than 25 is a mark, such as an equals sign, and
shows no point. A point Heath leaves without a letter stays without one here too, and what
draws it says why, on the element or on a `<g>` round several:
`data-unlettered="the squares of the reading in areas, which Heath's figure does not draw"`
(II.9). A letter Heath gives a straight line or a figure (I.3's C, II.14's A) may stand
beside it or within it. How the script reads this, and the switches that held the figures
while they were being lettered and while their letters were being set upright, are in
section 8.

**Checked as geometry, not only as a picture.** A label count or a colour check does not
validate a figure. Before a changed figure is signed off, render it
(`rsvg-convert -w 800 figures/<book>/NN.svg -o /tmp/fig.png`) and look at:

- incidence, betweenness, sides and intersections: each point lies where the proof puts
  it, and each crossing is where it should be;
- the cases: a figure drawn for one case says so, in the caption or the figure note, and
  does not suggest that the other cases were proved by the drawing; where a theorem covers
  several cases, the review record's `[figure]` names the one shown; a figure that draws
  every case, side by side or on one figure, says so too, with `every_case` in the
  record's `[figure]` and its `case` naming the cases drawn; and a figure that draws more
  than one case but not every one says so with `some_cases`, its `case` naming the cases
  drawn and its `note` the cases the theorem covers that it does not draw;
- a reductio: a figure that draws the impossible supposition is said to be one. It may
  draw it as Heath's printed figure does, departing from the construction so that the
  supposition can be seen, provided the figure note says so (I.14's E, drawn off CB produced
  although the construction puts it there; I.26's BG and BH, drawn shorter than the DE and
  EF they are cut off equal to); the owner's ruling of 21 October;
- the scope: the figure does not show more than the theorem proves;
- legibility at the size the page shows it: nothing clipped, letters clear.

**`NN-modern.svg`, the figure of the modern way.** Where the paragraph that opens **The
modern way.** is easier to follow with a picture (its coordinates, its vectors, Book II's
lengths a and b), it has a figure of its own. The page sets the figure under that paragraph;
S24 checks that the source has the paragraph.
It is drawn as Euclid's figure is: the same canvas, palette and strokes **[checked]**, and
Euclid's figure's letters, upright at 17 **[checked]**, at the points his figure gives
them, placed on the axes or in the plane as the paragraph places them. What the
paragraph measures takes the paragraph's own names (a, b, θ, u), italic at 17, and the
figure uses no name the paragraph does not **[checked]**. A name is a lower-case letter
of the paragraph's `$…$`, or one standing alone in its words, as in Book II's "AC = a",
that a reader sees (not in a comment, code, an HTML tag or a link's target or reference
identifier) and that English does not use as a
word: not the s of "A's", nor the letters of e.g. and i.e., nor a page reference such as
p. 383, nor the article "a" unless a sign of an expression, a digit or a bracket stands
beside it. A capital stands alone, as one of Heath's letters: a length or a vector is named
by its lower-case letter. The title is `<book>.N: the modern way` ("I.47: the modern way",
"II.3: the modern way"), with no caption, for its paragraph serves as one **[checked]**. A
page with no modern way has no such figure **[checked]**, and a modern way that would only
restate the proposition in symbols needs none. The figure shows what the paragraph says
and no more, drawn under the conditions the paragraph states (A = (0, 0), b > 0), and is
checked as geometry, as Euclid's is.

**Departures go in the figure note.** Where our drawing places a point otherwise than
Heath's figure, because the Lean does, draw the proof and say so in one line under the
figure (I.39, I.40, III.16); not in the mishnah. The line is the review record's
`[figure] note` ([review/SCHEMA.md](../review/SCHEMA.md)), which the page shows. Whoever
draws the figure proposes the line in the handback, and the records' owner writes it.

## 8. Checks

### What `scripts/check_style.py` checks

Run it from the repository's root. It reads the files below; "outside quotations" means
with every `"…"` span, every link target `](…)`, every code span and every fenced code
block removed first. What is removed is read as spaces, so the words of a phrase may
stand apart across a code span, a quotation or a link target: S3 finds "I think" in
`as I "so" think`. The words of a phrase in S2 to S7, S9, S11 and D7 to D10 are found
however a line or a comment wraps them: they may stand apart by spaces or tabs (and
commas, between S9's letters), or by one line break with the next line's indent and its
comment leader (`--`, or a quotation's `>`). A blank line ends such a phrase, save S2's
"first mate" and the "Definition N" of S7 and D10, whose words may stand apart by any
white space. A word that a rule seeks elsewhere in the clause or the sentence (what
follows S5's "never need", S11's "Proclus", D9's "need") is found as its row says. The
patterns are tested on such phrases, case by case, with S20's reading of a letter on an
angle's wedge and S26's measure of a letter beside a stroke, and the scopes' reading of a
review record, a rendered docstring, a `name : type` and letters in backticks, in
`tests/test_check_style.py`, which CI runs just before the script
([WORKFLOW](WORKFLOW.md), section 8).

- **Prose:** `mishnah/<book>/NN.md`, `mishnah/intro/<book>.md`, `reading/<book>/NN.md`.
- **Mishnah:** `mishnah/<book>/NN.md` alone.
- **Review notes:** the texts of `review/<book>/NN.toml` that its page shows: the
  statement's `note`, `short` and `hypotheses`; the `note` of `[route]`,
  `[representation]` and `[overlap]`; the `case` and `note` of `[figure]`; the `checked`
  and `explains` of `[coverage]`; and each passage's `note`; with each tag's `meaning` and
  `badge` in `review/terms.toml`. Heath's words in a record (`omitted`, `text_only`, a
  passage's `at`) are `scripts/check_fidelity.py`'s, and a `helper` is a Lean name.
- **Catalogues:** `docs/reports/gaps-book-*.md` and `docs/reports/overlaps.md`, which
  describe the edition as it stands.
- **Other reports:** every other `docs/reports/*.md`, save an outside review
  (`outside-review-*.md`), which keeps its reviewer's words as written; the crew's own
  logs, `docs/reports/crew/`, are not read. S12 reads them with every book's namespace
  open, as texts with no book of their own. For these reports alone, it distinguishes
  declaration references from repository file names, known by their shape (an extension,
  a numeric line location) or by prose that calls them files; from Lean's syntax and
  namespace-only names; and from what the prose identifies as a namespace, an external
  tactic, an Internet Archive scan identifier or a revision identifier. A name the prose
  calls a declaration goes to Lean, whatever else it could be. It also recognizes documented certificate fields and review schema fields and values
  where the prose discusses their files or records. Lean supplies the syntax, tactic and
  attribute vocabulary; these are categories, not a list of unknown names to excuse.
  A trailing dot names a family, not a complete declaration. A typed hypothesis still
  goes to Lean, and an unknown declaration reference still fails unless its file is
  pending for S12. None of these report classifications excuses a mishnah name.
- **README:** `README.md`, without its section "How it was made".
- **Lean notes:** in `Elements/**/*.lean`, the text of `/- … -/` blocks and docstrings,
  except the docstring of each `theorem PropN` (Heath's enunciation). The `--` lines are
  Heath's proof, and out of scope.
- **Rendered docstrings:** of the Lean notes, the docstrings `scripts/render.py` copies
  onto every page that rests on their rule: each tacit rule's, and any other axiom's of
  `Elements/Foundations/` that is not a postulate or a definition.
- **Generated:** `CERTIFICATE.md`, `GRAPH.md`, `book/<book>/index.md`,
  `book/<book>/front.md` and `book/names.md`. A failure here is mended in
  `scripts/render.py` or in the source it reads.
- **Idea figures:** `figures/<book>/NN-idea.svg`. **Euclid's figures:**
  `figures/<book>/NN.svg`. **Modern figures:** `figures/<book>/NN-modern.svg`.

**Failures.** S1 to S26 fail the script, naming the file, the line and the rule.

S23 reads every tracked text file's raw contents, including comments and fenced code
blocks in Markdown; text means bytes with no NUL that decode as UTF-8. It uses
`git ls-files` at the root, or, in a copy without Git, walks the tree excluding `.git`,
`.lake` at every depth (including `model/.lake`), `__pycache__`, `.pytest_cache`,
`.mypy_cache`, `.ruff_cache`, `.tox`, `.venv`, `venv`, `node_modules`, `build`, `dist`
and `_build`. Traversal errors stop the check with the affected path. Symlinks are
skipped, since Git stores the target path rather than the target's contents. This walk
serves S23 alone; S12 still requires Git's tracked-file index.

| Rule | What fails | Where |
|---|---|---|
| S1 | An em dash (—) | Prose, Review notes, Catalogues, Other reports, README, Lean notes, figure titles and captions |
| S2 | Crew talk: the words crew, captain, first mate, bosun, sailor, voyage, fleet, enforcer, polisher (whole words, any case), outside quotations | Prose, Review notes, Catalogues, README, Lean notes, figure titles and captions |
| S3 | The first person singular outside quotations: "I am", "I was", "I have", "I think", "I found", "I would", "my", "me" | Prose, Review notes, Catalogues, README, Lean notes |
| S4 | "note that", "strictly speaking", "it is worth noting" (any case), outside quotations | Prose, Review notes, Catalogues, Lean notes |
| S5 | "Euclid cites", "Euclid's own bracketed", or "never need" or "never needs" with "it", a postulate or parallels later in the same clause ("never need it", "never needs the fifth postulate"), outside quotations. This is the one home of the rule; `check_fidelity.py` no longer repeats it | Prose, Review notes, Catalogues, README, Lean notes, Generated |
| S6 | "tacit assumption(s)", "tacit law(s)" (any case), outside quotations | Prose, Review notes, Rendered docstrings, Generated |
| S7 | A definition without its book: "Definition N" or "Def. N", N a numeral, outside quotations and square brackets | Prose, Review notes, Catalogues, Other reports, Rendered docstrings, Generated |
| S8 | A curly quotation mark: “ ” ‘ ’ | Prose, Review notes, Catalogues, Other reports |
| S9 | An italic letter or run of letters, matched by `(^\|[^*])\*[A-Z]+[′₀-₉]*(([ \t,]+\|[ \t,]*\n[ \t]*((--\|>)[ \t]*)?[ \t,]*)[A-Z]+[′₀-₉]*)*\*($\|[^*])`: the letters may stand apart by spaces, tabs and commas, or by one line break, as above | Prose, Review notes, Catalogues, Lean notes |
| S10 | TeX in the mishnah: a backslash, `^{` or `$`, save within a `$…$` span of a paragraph that opens `**The modern way.**`, a paragraph that ends where Markdown ends it, at a blank line or at a line opening a heading, a list item (a numbered list only from 1), a quotation, a code fence, an HTML block, a rule or a table; and there, a span of a shape known to break on GitHub (section 4, "Mathematics"): a `$` unpaired in the paragraph, `$$`, a span across a line break or with white space just inside a dollar, an opening `$` not at a line's start or after white space or `(`, a closing `$` not before white space, a line's end or one of `. , ; : ! ? ) ] ' " - – /`, braces that do not balance, a backslash before an ASCII punctuation mark, `<`, `>` or `&`, a `*`, `~` or backtick, or a `_` first in the span or after anything but a letter or digit within it. Before reading anything else, the script checks its reading of this boundary against sample mishnahs on both sides of it | Mishnah |
| S11 | A retired refrain of section 3, on a page not allowed it: "certificate cites", "certificate records", "Of the postulates", "besides Euclid's", "just Euclid's three" (nowhere); "comes in through" (I.29 only); "Lean wants it said", "Lean asks why", "Lean makes us say so" (I.1, I.5, I.22 only); "uses Postulate 1", "brings it in" (I.1, I.3 only); "with no letter", "proves it once", "We give his argument once", "and the Lean cites it.", and "under I.31" in a sentence naming Proclus (nowhere); a paragraph opening `**What Lean made us say.**`, `**What else Lean made us say.**`, `**What it rests on.**`, `**Where the parallels meet.**`, `**Naming the pieces.**`, or `**Where X falls.**` with X a run of capitals (nowhere) | Mishnah |
| S12 | A backticked Lean name, other than a file name, that `#check` does not know, with `Elements`, `Elements.Book<book>` and `Elements.Tacit` open; every book's namespace for a text with no book (the overlap catalogue, Other reports, `review/terms.toml`), so that a name two books share is written with its book; and `Elements` and `Elements.Tacit` alone for the Rendered docstrings. The name before the colon of a backticked `name : type` is read as well (section 1, "Hypotheses in words"). A word that is Lean's but no declaration, as a tactic or a field of `facts.json`, is listed in the script with its reason, and fails once no text uses it. Run when the tree is built; the overlap catalogue's audit lemmas once `lake build Audit` has run, and listed as not checked till then. The mishnah is asked as it always was, every name with `import Elements` alone: neither excuse holds there | Prose, Review notes, Catalogues, Other reports, Rendered docstrings, `book/<book>/front.md` |
| S13 | A caption (`<desc>`) missing, or over 50 words | Idea figures |
| S14 | A viewBox other than `0 0 400 300`; a colour other than `#fbf7ee`, `#d0312d`, `#f2b705`, `#1f5aa6`, `#222222` and white; a missing `<title>`, or one other than `<book>.N at a glance` ("II.4 at a glance", "III.17 at a glance"), with a name after a colon if it has one | Idea figures |
| S15 | A viewBox width outside 400–440; a letter not at font-size 17, or, with the switch for upright letters on (below), not upright; a colour other than `#fbf7ee`, `#3b2f2f`, `#8c7b62`, `#a0522d`, `#e9dcc0`; a stroke-width under 1.2 or over 3.2; a `<desc>`; a missing `<title>`, or one other than `Euclid <book>.N: …` ("Euclid II.1: …", "Euclid III.1: …") | Euclid's figures |
| S16 | Letters drawn that are not Heath's, or Heath's letters not drawn: the letters of the figure's `<text>` elements against the capital letters of `heath/<book>/NN.md`, with comments, Heath's references, "Q. E. D.", "Q. E. F.", "I say" and "PORISM." taken out (the command is below). An exception is listed in the script with its reason | Euclid's figures |
| S17 | A reading file of no lines or more than three, a line that is not a list item ("- "), or a web link that `docs/reading.md` does not give | `reading/<book>/NN.md` |
| S18 | A book with pages and no `mishnah/intro/<book>.md` | `mishnah/intro/` |
| S19 | A book introduction that does not link the book's brief in `docs/briefs/` (section 2 requires it) | `mishnah/intro/` |
| S20 | A `<text>` holding a Latin letter that is not one letter (a capital, with a prime or a subscript) or not one that `NN.svg` draws; a letter not upright (with the switch for upright letters on, below), not at font-size 14, or not in the ink of what its middle stands on: `#222222` on the parchment or yellow, `#fbf7ee` on a red, blue or black fill: a polygon, polyline, rect, circle, ellipse or path (an angle's wedge), transforms applied, its arcs and curves followed | Idea figures |
| S21 | A point the figure shows with no letter within 30 of it: a dot (a filled `<circle>` of radius 6 at most), an end of a `<line>` 25 long or more in a Byrne colour or black, or a corner of a `<polygon>` filled or stroked in one. Transforms are applied; a letter stands at its glyph's middle, reckoned from its x, y, anchor and size; points within 8 of one another are one point. A point drawn by an element marked `data-unlettered`, or inside a `<g>` so marked, is excused, and each mark is printed on every run; a mark whose reason is under two words, or that excuses no point, fails. With the switch on (below), S21 holds every figure | Idea figures |
| S22 | Letters in backticks: a code span that holds only letters, a capital or a run of capitals (each with its prime or subscript) or several such runs apart by commas or spaces, as `P`, `PQ`, `ABCD` or `AB, CD` (section 1, "Lean notes") | Prose, Review notes, Catalogues, Other reports, Lean notes, Generated |
| S23 | A merge-conflict marker, with its kind: a line beginning with exactly seven `<`, `\|` or `>` followed by a space or the line's end; or exactly seven `=` with optional trailing spaces or tabs. A trailing CR is allowed. A middle is refused between opening and closing markers, outside `.md` files, or unless every line of the preceding block is ordinary paragraph text. Blank lines, markers, ATX or completed setext headings, thematic breaks, fences, HTML blocks and GFM tables bound or disqualify the block; indented code cannot start a paragraph, but indented continuations are allowed. Any possible reference definition prefix (up to three spaces, a bracketed label allowing escaped brackets, then a colon), block quote or list item disqualifies the whole block; within a paragraph, a list item counts only where it can interrupt one, as a bullet or an ordered item numbered 1, with some text, so `2. item` or a bare `*` goes on with the paragraph. S23 errs toward refusal: other lengths of equals are never examined as middles, so a refused heading can use eight. Fences inside comments or HTML blocks open no block | Every tracked text file except symlinks, or the files of the walk described above |
| S24 | A viewBox width outside 400–440 or non-positive height; a colour other than Euclid's figure's five, or a shape or a `<text>` with no fill, which SVG paints black; a stroke-width under 1.2 or over 3.2; a `<desc>`; anything but exactly one `<title>` directly under the root, with the text `<book>.N: the modern way` ("II.3: the modern way"); no `NN.svg` beside it, or no paragraph opening `**The modern way.**` in `mishnah/<book>/NN.md` for it to stand under, read as Markdown reads it (not in a comment or a code block). The modern figure is UTF-8 with no NUL, DTD, entity declaration, stylesheet processing instruction or `@import`, and may use only the elements, attributes and spellings that the modern figures on main use; a character reference in a serialised attribute is refused before XML can normalise it. An arc with a radius of 0, or whose ends are one point, is refused, for SVG draws it as a straight line or not at all. | Modern figures |
| S25 | A `<text>` not at font-size 17, or a `<tspan>`; an explicit `font-style` other than `italic` (an upright letter omits it); a capital letter (with a prime or a subscript) that `NN.svg` does not draw, or not upright; a capital in a longer text; any other text holding a character besides lower-case Latin and Greek letters, digits and the signs of an expression, or with letters not italic, or with a letter that is not a name of the page's modern way: in its `$…$` spans, each lower-case letter once the commands are taken out (`\vec`, `\frac`, `\mathrm{…}` and what it sets) and the Greek ones read as their letters (`\theta` as θ, and a variant such as ϑ as the letter it is a form of); outside them, each Greek letter, and each lower-case letter standing alone, with no letter of any script (Greek too: the r of 2πr is a name only in TeX), mark or format character beside it, save one straight after an apostrophe (`'` or `’`, the s of "A's"), the letters of e.g. and i.e. (a full stop escaped or not, spaces after the first or not) and the p of Heath's page before its number (p. 383), with a Roman number's letters (p. ix, pp. v–vii), and the article a with no sign of an expression (=, +, -, −, ×, ·, /, <, >, ≤, ≥), digit (raised or lowered, as ²) or bracket beside it, spaces between; and none of it from an HTML tag or comment, a code span or a link's target or resolved reference identifier, which a reader does not see, the paragraph being read as Markdown reads it, so that a line holding only a code span goes on with it. A character reference, an invisible character (a format character of Unicode's, such as a zero-width space or a soft hyphen, or another of its default-ignorable characters, such as a Hangul filler or a variation selector), emphasis inside a word (through an apostrophe or a full stop too, escaped or not, with the emphasis on one side of it or both: `*e*.g.`, `*e*.*g*.`), inline HTML, a reference-style link, a reference definition in the selected block or one used by a link in the paragraph is refused; an unrelated definition elsewhere is not. | Modern figures |
| S26 | One letter, one point: a letter drawn twice in a figure, or twice in one of Heath's figures where two or three stand side by side (III.25, III.33, III.35, III.36, each split at the x of the straight cuts the script gives, a letter belonging to the figure its middle stands in), or across such a cut; or a letter that a stroke, a dot or the canvas's edge comes within 2 of. S26 reads only the elements, attributes and spellings that the figures on main use, and refuses any other. It refuses an arc whose ends are one point, for which SVG's implementation notes for arcs (F.6.2) draw nothing, whatever its radii, and one with a radius of 0 and two ends, which they draw as a straight line; every other arc draws, whatever its large-arc and sweep flags, its radii enlarged when they cannot reach its ends (F.6.6). Every element is in the SVG namespace; only the root `<svg>` and a `<g>` may contain elements, so titles and descriptions are text-only and drawn elements are leaves. A text payload is one Heath letter or an ASCII integer annotation; text children, an invisible point label with fill none, zero fill or stroke opacity, processing instructions (an `<?xml-stylesheet?>` among them) and every other payload fail. Before parsing, every figure reader refuses `<!DOCTYPE` or `<!ENTITY` anywhere in the bytes, including UTF-16 and UTF-32 spellings and such text inside comments. The refusal is independent of ElementTree's C accelerator; the doctype callback remains a second guard. A letter is measured as Georgia draws its capital, upright or italic as the figure sets it, by the convex hull of the points of its outline, at its x, y and size, anchored by the whole label's advance (a prime or a subscript after it included, though not itself measured), transforms applied; a stroke (a `<line>`, `<polyline>`, `<polygon>`, `<rect>` with its corners rounded as rx and ry round them, `<circle>`, `<ellipse>`, or each subpath of a `<path>`, closed only where a Z closes it, a dashed one read whole, a single-point subpath closed by Z retained for round caps, a shape that SVG does not draw left out) less half its width and that subpath's conservative chord allowance. Literal `stroke-dasharray="none"` is solid; a numeric dash array must contain a positive component, so an all-zero array is refused rather than named as dashed. Mitre joins include their filled corners, transformed after applying the inherited stroke-linejoin (by default miter, with a mitre limit of 4), with round joins and mitres over the limit covered by the existing half-width measure; a dot (a filled `<circle>` of radius 6 at most) less its radius; a width and a radius each taken at the most its transform stretches it. The hull holds the ink and spans its hollows, so a stroke that ends in an L's corner or a K's notch is found while the ink is clear: move the letter | Idea figures, Euclid's figures |

**Reports.** Each is listed, with its count, and fails nothing.

| Rule | What is listed | Where |
|---|---|---|
| D4 | More than four distinct Lean names | Mishnah |
| D5 | A caption over 40 words, or of more than two sentences | Idea figures |
| D6 | Each "first", "only", "better", "best", "unlike", for a reader to judge as a comparison or a claim to priority | Prose, README |
| D7 | "Lean cannot", "Lean can't", "Lean can not" | Prose, Review notes, Catalogues, Lean notes |
| D8 | "gives no citation" (say "Heath gives no reference") | Prose, Review notes, Catalogues |
| D9 | A sentence that joins "need", "needs" or "needed" to Postulate 5 or the parallel postulate (say "uses"; a claim that a result holds without the postulate names its evidence) | Prose, Review notes, Catalogues, README, Lean notes |
| D10 | S6 and S7 outside their failing scope | S6: Catalogues, README, Lean notes; S7: README, Lean notes; the Rendered docstrings aside |
| D11 | Euclid's figure strokes other than lines 1.6, circles 1.3, the subject 2.4 to 2.6, angle marks 1.3, or dots of radius other than 2.6 | Euclid's figures |
| D14 | The figures at a glance with no letter yet, book by book, with the points each has to letter, while the switch is off (below) | Idea figures |
| D15 | The figures whose letters are all italic, book by book, while the switch for upright letters is off (below) | Idea figures, Euclid's figures |
| D16 | A finding of the reach of 19 October, of a rule its file is still listed for (below), with the rule it would fail; and each rule of a listed file with no finding of it left, to be taken out of the file's entry, or the entry out of the list once each of its rules is | The files listed |

**The switch for S21.** The figures at a glance were lettered one by one, and while they
were, `IDEA_LETTERS_REQUIRED` in `scripts/check_style.py` was `False`: S20 held every
figure, S21 held each figure that carried at least one letter, so a figure once begun was
lettered whole, and D14 listed the rest. Every figure now carries its letters, and the
switch is `True`: S21 fails any figure with a point unlettered, and D14 is empty. The
switch is never turned back to quiet a figure: the figure is lettered.

**The switch for upright letters.** The figures were drawn with italic letters, and were
set upright (section 4) in a change of their own. While they were,
`UPRIGHT_LETTERS_REQUIRED` in `scripts/check_style.py` was `False`: S15 and S20 took a
figure whose letters were all italic as well as one whose letters were all upright, and
failed a figure that mixed the two, so that a figure once begun was set upright whole, and
D15 listed the figures still italic. Every figure is now upright, and the switch is
`True`: S15 and S20 fail an italic letter, and D15 is empty. The switch is never turned
back to quiet a figure: the figure is set upright.

**The reach of 19 October.** On that day the rules came to every text a reader meets
([#66](https://github.com/dodecaplex-co/stoicheia/issues/66)): the Review notes, the overlap
catalogue, the Other reports, the Rendered docstrings, the front pages and the table of
names, with S7 in the gap catalogues and the Generated files, S12 beyond the mishnah (and
the name of a `name : type`), and S22. A file that had findings of that reach on the day was
listed in `REACH_PENDING` in `scripts/check_style.py`, with the rules it had findings of
and whoever mends them; while it is listed, its findings of those rules are reported (D16)
and fail nothing. Every other finding of the reach fails at once, in a listed file as in
any other, and every file is held to what it was held to before, so nothing is loosened.
A rule of a listed file with no finding of it left is reported as done, and comes out of
its entry in a change to the check, and the entry comes out once each of its rules has;
S12, which alone asks Lean, is not reported under `--no-lean`, or when Lean could not be
run. A done rule cannot fail, since the change that mends a file may not change the check
that judges it ([WORKFLOW](WORKFLOW.md), section 10). Once no entry is left, the list
goes. No file, and no rule of a file, is ever added to quiet a new finding: the text is
mended.

### The reviewer's checklist

The script cannot judge these; a reviewer reads for them. F is the file, NN its
proposition, and a later book's numeral replaces `I` in the paths.

**Every reader-facing file**

1. The voice of section 1: facts stated directly, conditions beside their claims,
   attributions exact, nothing competitive (read each hit of D6), production kept out.
2. Each paragraph earns its place, and could not be pasted onto ten neighbouring pages.

**The mishnah**

3. It does the things of section 3 that this proposition needs, at the length they need,
   and nothing the table, the generated line or the introduction already says. More than
   four Lean names (D4) has a reason.
4. A lead, where a paragraph has one, is a hook, not a label, and neither the leads nor the
   lengths of the pages fall into one rhythm.
5. The modern way, where there is one, is exactly right, with its conditions, in radians,
   and says when it is not Euclid's route. Each `$…$` shows as mathematics, formula for
   formula, on the page as GitHub renders it, and Heath's letters in it are upright.
6. Every Lean name names what the sentence means. S12 shows each is known to Lean; it
   cannot see a bare `Prop4` on a page of Book II, which Lean reads as II.4 when the
   sentence means I.4. An earlier book's names are written `BookI.PropN`, `BookII.PropN`.
7. Each quotation has Heath's words and page. Flatten the OCR once,
   `perl -0pe 's/-[ \t]*\n\s*//g; s/\s+/ /g' "$HEATH_OCR" > /tmp/heath.txt`, then
   `grep -oi 'a distinctive phrase.\{0,80\}' /tmp/heath.txt`: it agrees but for OCR
   misreadings ("toudi" for "touch"), or the page image does. The running head above it
   gives the page. `$HEATH_OCR` is the OCR text of the volume; the task gives its path.
8. Each quoted page lies between the first page of `heath/I/NN.md` and that of the next
   file (`grep -m1 -o 'pp\?\. [0-9]*' heath/I/NN.md`), or is Heath's introduction or front
   matter; otherwise the quotation becomes a clause.
9. `grep -ohE '"[^"]{40,}"' mishnah/*/*.md | sort | uniq -d` prints nothing but Euclid's
   own words.
10. Every italic Heath printed for emphasis or a title is kept, and no other. The scan's
    ABBYY file (`https://archive.org/download/<id>/<id>_abbyy.gz`) flags each italic
    character with `italic="true"` on its `<formatting>`; on the quoted page (the `<page>`
    of its leaf, counting from 0) every word inside the quotation so flagged is in italics
    in F, save the names of points, straight lines and figures, which Heath also sets in
    italic and we write plain (S9), and the words of an enunciation, which he sets wholly
    in italic type and we quote in roman (section 5). Where a flag is doubtful, the page
    image decides.
11. What it says of the Lean's citations and postulates matches `facts.json`:
    `python3 -c "import json,sys; p={x['ref']:x for x in json.load(open('facts.json'))['propositions']}[sys.argv[1]]; print(*p['direct_axioms']); print('cites', *p['cites'])" I.N`.
12. Every letter named is Heath's, every name spelled as Heath spells it, and each person
    has a full name at the first mention on the page.
13. Each mention of Avigad or LeanEuclid is a particular debt, not thanks, and each rule
    name is a docstring label: `grep -rn 'Intersection 5' Elements/Foundations/Tacit`.

**The Lean notes**

14. They read as section 1 asks: full sentences, letters plain, a shared step pointed to
    rather than explained again, how rather than why. The rules for the Lean itself are in
    [FORMALIZATION.md](FORMALIZATION.md), and its reviewers' checklist is in
    [WORKFLOW.md](WORKFLOW.md).

**Figures**

15. The figure is checked as geometry (section 7), rendered and looked at.
16. The Lean uses the figure's letters: S16 checks the figure against Heath, and
    `grep -oE '\{[^}]*: Point\}|obtain ⟨[^⟩]*⟩' Elements/BookI/PropNN.lean` shows the
    Lean's own. One letter, one point: a letter that names one of Heath's points names no
    straight line or circle in the Lean (`{L : Line}`, or `obtain ⟨L, …⟩ := Postulate1 …`,
    beside Heath's point L);
    `grep -nE '[{(]([A-Z] )*[A-Z] : (Line|Circle)\b|⟨[A-Z],' Elements/BookI/PropNN.lean`
    shows the candidates, a binder of several names (`{L M : Line}`) and a line taken
    from inside another fact (`obtain ⟨-, -, ⟨L, …⟩, -⟩`) among them.
17. On the figure at a glance, rendered beside Euclid's, each letter is the one Euclid's
    figure gives that point, beside it and clear of every colour, or on the fill as section
    7 says; S21 sees only that a letter is near, and S26 that it is clear of the strokes.
    Each `data-unlettered` reason is true of Heath's figure.
18. A departure from Heath's figure has its line in the figure note. A figure of one case
    among several names it; a figure marked as every case draws them all and names them.

**Heath's text**

19. `git diff main -- heath/` is empty, or each change carries a comment naming the leaf
    checked.

**Further reading**

20. Each line helps with this proposition, gives the facts of section 6 in its own words,
    and describes a work in full only at its first appearance in the book; the lines of a
    book do not fall into one mould.
