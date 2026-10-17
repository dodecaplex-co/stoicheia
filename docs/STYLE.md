# House style

How Stoicheia reads and looks at its best, drawn from the mishnah of I.1–I.5, I.29 and
I.47, the bosun's reviews, the [read-through](reports/read-through-01.md) of Books I to
III, [CONTRIBUTING](../CONTRIBUTING.md) and the
[first inspection](reports/crew/inspection-01.md). Everyone who writes for the
project works from it; every new or changed file is checked against the list at
the end.

## 1. Voice

- **One warm, plain voice**: a friend who knows Euclid well, talking over his figure
  with a curious reader. Short, plain sentences, sure of themselves; nothing hedged,
  and nothing written for a checker. "So the tacit rule is doing real work: it says
  the plane has the square roots that ruler and compass need" (I.1). "Generations of
  schoolchildren knew it as the *pons asinorum*, the bridge of asses" (I.5).
- **"We" is the project**: its statements, figures, choices and discoveries ("our
  I.1 lets the side be named"; "we prove Euclid's case … and get the other"), and it
  may take the reader along ("Postulate 3 lets us draw a circle"). Two to four a
  page. "Lean" is the machine and what it insists on ("Lean wants it said"). No "I"
  or "my" outside quotations.
- **No crew talk where readers look** (the mishnah, captions, Lean comments, the
  gap catalogue, the README, the pages): "Book Zero proves it once", not "the first
  mate added it". Ranks belong in `docs/reports/crew/` and `docs/briefs/`, and in the
  README's "How it was made", which says plainly how the work is done.
- **People by name**, spelled as Heath spells them (Proclus', an-Nairīzī, van
  Pesch); modern authors in full ("Robin Hartshorne's *Geometry: Euclid and
  Beyond*"), and a person's full name at the first mention on each page ("Robert
  Simson", then "Simson"): Augustus De Morgan, Henry Savile, Robert Simson, John
  Playfair, J. L. Heiberg, Paul Tannery, Isaac Todhunter, David Hilbert, Christopher
  Clavius, Dionysius Lardner, H. G. Zeuthen. Heath is Heath. Say who saw a gap first,
  where we know; call a find new only when it is.
- **No comparisons.** Nothing here is first, only, better or unlike anyone else's
  work; we say what others' work does well, and link to it. ("Only one triangle"
  is geometry, and fine.)
- **Euclid's words for Euclid's things**: straight line, produced, joined, greater
  and less, the angle ABC, the square on AB, the rectangle contained by AB, BC,
  circumference (an arc), touches (a tangent), segment. "Diameter" is Euclid's word
  for a diagonal: gloss it at its first use in each book (in Book III it is the
  circle's). Gloss "applied" (I.44) and "gnomon" (II.5). Modern words stay in "The
  modern way"; a Lean word gets a plain gloss the first time.
- **House words.** "Tacit rules", never "tacit assumptions" or "tacit laws" outside
  Heath's words. "Cites" for a citation ("Euclid gives no citation for it: it is
  I.10"); "brackets" only for Heiberg's, and Heath's own round III.12.
- Short sentences, and no em dashes: a comma, colon or full stop does it. No "note
  that", "strictly speaking" or "it is worth noting".

## 2. The mishnah

**Shape.** 250–450 words, in three to five paragraphs of about 120 words at most,
"The modern way" last. Each opens with a short bold lead ending in a full stop (a
question mark if it asks), and the lead is a hook: a question (**Must the circles
meet?**), a claim (**A compass that closes.**), or Euclid's or Heath's words
(**"Less than two right angles."**). A lead that could head a paragraph on another
page is a label, not a lead.

**What it tells.** Each paragraph tells one thing worth telling. Open on Euclid:
what he does here and why it matters. Then what Heath, Proclus or the history adds,
in one or two quotations. What Lean made us say out loud takes one paragraph at
most, told as a discovery ("Euclid's figure quietly settles the order of its
points, and Lean wants each of those facts said", I.5), on the page where it first
happens, with four Lean names at most, exact and in backticks (`circles_meet`,
`Prop1.figure`). The proof and the table are on the page: say why they look as they
do, not what they say. Finer gaps go in the [gap catalogue](reports/gaps-book-I.md).

**The modern way.** Always the last paragraph: coordinates, vectors, complex
numbers or matrices, one or two sentences, exactly right. If the modern route is not
Euclid's, say so (I.43, I.48; I.2's L lies on DA produced, so it is not
A + (C − B)). Never repeat a neighbour's.

**Bookkeeping.** The page's table shows what the proof rests on, its postulates,
definitions, Common Notions and tacit rules alike counting those of the propositions
it cites, and the generated line under it, "Brought in by shared steps", names what
each shared step brings in. So the mishnah does not restate the table, say what the
certificate "cites" or "records", explain what a cited proposition or shared step
brings in, or trace the paths of Postulate 5, Postulates 1 to 4, Definition I.15, the
Common Notions or the tacit rules. It speaks of them only when the reason is this
proposition's story, and then says "the Lean cites": a departure from Euclid's route
(I.2 and I.5 need no Postulate 2; the Lean cites I.10 in I.42 and I.17 in II.12,
where Euclid gives no citation: one clause naming his step), a gap he leaves (I.1's
circles, I.35's G), or a landmark (Postulate 5 at I.29, I.44 and II.10; I.31 without
it).

**Told once.** Each book's shared machinery is told once, in the book's
introduction, `mishnah/intro/<book>.md`, which `render.py` sets on the book's index
page in the same voice. Book I's tells System E, Book Zero, Postulate 1 naming a
straight line, `produce_longer`, superposition in I.4 and I.8 alone, Postulate 5
beneath every proposition from I.29 on but I.31, and `Prop30.meet`, credited to
Proclus (Heath, vol. 1, pp. 207 and 316). Book II's tells the steps of
`Elements/BookII/Rectangles.lean`, with `Parallel.between`,
`quadArea_add_of_parallelograms` and the unlettered point of `exists_off_line`; Book
III's tells a circle's centre by hypothesis and III.1, its definitions and the
circumference measured by twice its angle, `Squares.lean` and `Circumferences.lean`,
and the porisms of III.1 and III.16. A shared step may be told on its home page
(II.1's rectangle contained, II.4's "For the same reason"); elsewhere it gets a
clause at most ("as in II.4").

**Retired refrains**, each once said on a dozen pages:

- "I.4 and I.34" for a drawn rectangle; Proclus "under I.31", and "a straight line
  meeting one of two parallels meets the other"; `exists_off_line` and the point
  "with no letter"; `Rectangle.of_right`; `Square.described`; "Lean proves it once":
  the book's introduction, and a clause on the home page.
- "Uses Postulate 1", "(… brings it in as well)": I.1 and I.3 only.
- "Postulate 5 comes in through …": I.29 and the introductions only.
- "The certificate cites/records …", "Of the postulates …", "besides Euclid's …",
  "just Euclid's three brackets": nowhere.
- The leads "What (else) Lean made us say.", "What it rests on.", "Where the
  parallels meet.", "Naming the pieces.", "Where X falls.": name the discovery, ask
  the question, or quote, as I.35 does: **"He allows this to appear from the figure
  simply."**
- "Lean wants it said" and its kin ("Lean asks why", "Lean makes us say so"): I.1,
  I.5 and I.22's payoff, "Lean is exactly that dull"; elsewhere state the gap and
  say that we prove it.
- "…, and the Lean cites it" closing a sentence: the table shows it. Where Euclid
  gives no citation, one clause names his step ("it is I.10, though he gives no
  citation").
- "We give his argument once and use it twice" in the mishnah: the introduction and
  the Lean notes, save I.17, where "taken together in any manner" is Euclid's own.
- A paragraph closing on "our statement asks for …": only where the hypothesis is the
  story (I.33's "in the same directions", I.37's coinciding vertices).
- The same figure-reading point page after page (which side a point is on, why the
  angles are alternate, Postulate 4 and `∟`, `Prop5.base`, `produce_longer`): told
  once where it first does work (I.27, I.11, the introduction), a clause elsewhere.

**Quotations.**

- Heath's exact 1908 words, in straight double quotes, with the page: "(vol. 1,
  p. 242)", or "pp. 253–254" when the passage crosses a page; "(Heath, vol. 1,
  p. 252)" when the sentence doesn't name him. Those Heath reports (Proclus,
  Todhunter, De Morgan) take his page. Never invent a quotation or a page.
- Single quotes inside, "…" for a cut, and brackets inside are Heath's own. No
  added italics, and keep Heath's italics: those he printed, all of them, and only
  those ("the two circles *will* meet"), as `*…*`.
- Each of Heath's notes is quoted on the page of the proposition it belongs to, and
  elsewhere only referred to in a clause: "as Todhunter remarks under I.14". A
  passage from his introduction, or his notes on the definitions and postulates, is
  quoted once, where it matters most.

**System E.** Every page's footer (from `render.py`) thanks the authors of
System E and of LeanEuclid by name, so the mishnah doesn't. Name a rule by its
docstring label, "System E, Intersection 5" (a diagram rule, §3.4) or "System E,
Intersections 8" (a construction rule, §3.3), or by its Lean name. A particular
debt is still said where it falls: Intersection 4 is LeanEuclid's corrected form.

**Further reading.** `reading/<book>/NN.md`, shown after the mishnah, is one to three
friendly lines, each a list item naming a work from [the reading list](reading.md) and
what it gives this proposition. Every line runs the same way: "For" and what the reader
will find; the author in full; the title with the list's link, in italics for a book and
in quotation marks for a paper or a web page, as the list has it; the year of the edition
linked, with "free online" beside it where the list says **Free**; the chapter, where a
checked table of contents gives one; and a few words on the work. For instance:

> - For the dot product of the modern way, Grant Sanderson's [*Essence of linear
>   algebra*](https://www.3blue1brown.com/topics/linear-algebra) (2016, free online),
>   ch. 9, "Dot products and duality", one short animated lesson that explains it in
>   pictures.

Verified works only: a new one goes on the list first, checked, and into
`references.bib`. Every new page adds its own, Book III's among them; with nothing apt,
there is no file and no section.

## 3. Lean

- **Euclid's words in `--` comments, ours in `/- … -/`.** The docstring of
  `theorem PropN` is Heath's enunciation; in the proof each of Euclid's sentences
  is a `--` line, word for word (indentation may change), with its Lean directly
  under it.
- **Our notes read as the mishnah does.** Each `/- … -/` remark and helper docstring
  is a full sentence or two, with Heath's letters plain (AB, not `AB`: the page shows
  the Lean in a code block, where backticks print), and backticks only for Lean names
  and expressions (`Prop30.meet`, `∠ A B C`). A shared step is explained once, where
  it is first used or in the book's introduction; elsewhere a pointer does it: "I.5
  (`Prop5.base`)", "(`produce_longer`, as in I.11)". A note does not repeat the
  mishnah: the mishnah says why in plain words, the note says how.
- **Heath's letters.** Points, lines and circles take his names (`BCD` for the
  circle BCD; a line he calls C becomes `C₁ C₂`), and hypotheses read off them
  (`hAB : A ≠ B`, `hA_BCD`).
- **Order.** Helpers named `PropN.something` come before the main theorem, each
  with a docstring saying what Euclid takes for granted; porisms and other
  corollaries after it (`Prop15.porism`). Import `Elements.Figure.Basics`, every
  proposition cited, and `Elements.BookI.HelpersParallels` when a step from it is
  cited.
- **Book Zero first.** Search `Elements/Figure/` before writing a helper, and cite
  its lemma rather than keep a copy; Book Zero imports no proposition. A shared
  step that cites a proposition goes in `Elements/BookI/Helpers.lean`, named after
  it (`Prop5.base`), or, if it cites I.28, I.30 or I.31, in
  `Elements/BookI/HelpersParallels.lean` (`Prop30.meet`), or, if it is a
  consequence of PropN that later proofs share, as a corollary after PropN
  (`Prop34.bisect`). In Book II, a shared step that cites Book I goes in
  `Elements/BookII/Rectangles.lean`, and a proof cites Book I as `BookI.PropN`. In Book
  III, a shared step that cites Books I or II goes in `Elements/BookIII/Squares.lean`,
  one that cites III.20–III.22 in `Elements/BookIII/Circumferences.lean`, and a proof cites
  the earlier books as `BookI.PropN`, `BookII.PropN`.
- **Euclid's route**: the propositions he cites, in his order, nothing later. When
  Lean cites one he gives no citation for, the page's generated line shows the shared
  step that brings it in, or the mishnah names his step in a clause (§2,
  Bookkeeping).
- **No `axiom` outside `Elements/Foundations/`, no `native_decide`.**
  Superposition only in I.4 and I.8; nothing before I.29 rests on Postulate 5 or
  `Elements.Tacit.Euclidean`. A new tacit rule comes from System E, with its
  citation, through the captain.
- **Never change a statement** without the first mate or the captain (from outside,
  open an issue): other proofs are written against it.

## 4. Figures

Two per proposition, on the parchment card (`#fbf7ee`, a rect with `rx="10"` over
the whole canvas), in Georgia.

- **`NN-idea.svg`, at a glance.** 400 × 300. Byrne's red `#d0312d`, yellow
  `#f2b705`, blue `#1f5aa6` and black `#222222` (white only for grid lines and
  numbers on a fill, as in I.47); equal things share a colour; no letters. Title
  "I.N at a glance", with a name if it has one (": the bridge of asses"). The
  `<desc>` is the caption on the page: one or two short sentences in the house
  voice, about 40 words at most, colours named in brackets.
- **`NN.svg`, Euclid's figure.** 400 wide (440 at most). Italic letters at 17; ink
  `#3b2f2f` for lines, dots and letters; circles `#8c7b62`; what the proposition is
  about in `#a0522d`, drawn heavier; triangle fills `#e9dcc0` at 0.55. Dots r 2.6,
  lines 1.6, circles 1.3, what the proposition is about 2.4 to 2.6, and angle marks in
  `#8c7b62` at 1.3. Title "Euclid I.N: …", no caption.
- **Heath's letters, all and only**, each point where the proof puts it (I.6: D on
  AB), clear of every stroke, nothing touching the frame. Where the Lean places a
  point otherwise than Heath's figure, draw the proof and say so in one line under
  the figure, from `FIGURE_NOTES` in `render.py` (I.39, I.40), not in the
  mishnah.

## 5. Text and citations

- **`heath/` is Heath's, untouched.** The source comment first (pages, scan
  leaves), the enunciation in italics, then one sentence or clause per paragraph,
  as the `--` comments take them. Changes only against the page image.
- **Square brackets** there are his, kept exactly: the justifications `[I. 2]`,
  `[Post. 3]`, `[C.N. 1]`, `[Def. 15]`, `[Post. 4 and C.N. 1]`, II.10's
  `[I. Post. 5]` with its book, Book III's `[I. Def. 10]` (another book's definition,
  with its book), `[III. Def. 3]` and `[III. 1, Por.]` (a porism, cited with its
  proposition), and Heiberg's brackets round a passage he judged added later (I.4,
  I.15's Porism), with a comment; and Heath's own round a whole proposition (III.12),
  with its reason. In our prose a bracket appears only when we quote one: "Euclid cites
  [I. 20]". In the Lean, a `/- … -/` remark may give a step Euclid leaves unbracketed
  its justification in his form, as a `--` line would: "subtracted from each [C.N. 1,
  C.N. 3]".
- **Our prose writes** I.5, II.4, I.1–I.24 (en dash); Postulate 3, Common Notion 1 in
  a sentence; Post. 3, C.N. 1 in parentheses and tables. A definition always keeps its
  book, since Books II and III have their own: "Definition I.15" in a sentence,
  "Def. I.15" in parentheses and tables (Book I's own tables write 15, as Heath's
  brackets there do). [I. 5] only in Euclid's text, and "I. 5" only inside Heath's
  words.
- Titles and foreign words in italics: *pons asinorum*, *reductio ad absurdum*.

## 6. The enforcer's checklist

Run from the repo root after `lake build`; F is the file, NN its proposition.
`$HEATH_OCR` is the OCR text of the Internet Archive scan of Heath's volume 1,
`thirteenbookseu02heibgoog` (the captain gives the path); page N's image is
`https://archive.org/download/thirteenbookseu02heibgoog/page/n<N+20>.jpg`. For Books
III to IX it is volume 2, `thirteenbookseu00heibgoog`, where page N's image is
`https://archive.org/download/thirteenbookseu00heibgoog/page/n<N+12>.jpg`, and quotations
give "vol. 2". Each check is yes or no; a no goes back with the line that failed. For a
proposition of a later book, read its numeral for `I` in the paths (`heath/II/NN.md`,
`figures/II/NN.svg`).

**Every reader-facing file**

1. No "I", no crew talk:
   `sed 's/"[^"]*"//g' F | grep -nE "\bI (am|was|have|think|found|would)\b|\b(my|me)\b|crew|captain|first mate|bosun|sailor|voyage"` prints nothing.
2. Each hit of `grep -nwiE 'first|only|better|best|unlike' F`, read, is not a
   comparison or a claim to priority.
3. `grep -c '—' F` is 0.

**Mishnah**

4. `wc -w F` is 250–450.
5. `awk 'BEGIN{RS=""}{print NR": "NF}' F` shows 3–5 paragraphs, none much over 120.
6. This prints nothing:
   `awk 'BEGIN{RS=""} !/^\*\*[^*]+[.?]"?\*\* /{print "no lead: " NR} {l=$0} END{if (l !~ /^\*\*The modern way\.\*\* /) print "not last: the modern way"}' F`
6b. Each lead is a hook, not a label (§2, Shape), and none is a retired one; the
    page says "we" two to four times (`grep -oiwE 'we|our|us' F | wc -l`); and this
    prints nothing that is not this page's own story (§2, Bookkeeping and Retired
    refrains):
    `grep -niE 'certificate|comes in through|brings it in|besides Euclid|of the postulates|under I\. ?31|with no letter|proves it once' F`
7. The modern way is one or two sentences, exactly right, and not a neighbour's.
8. There are four Lean names at most, and Lean knows every one (no "Unknown"):
   ```sh
   { echo 'import Elements'; echo 'open Elements Elements.BookI Elements.Tacit'
     grep -oE '`[A-Za-z_][A-Za-z0-9_.₀-₉]*`' F | tr -d '`' | grep -v '\.lean$' | sort -u | sed 's/^/#check @/'; } > /tmp/Names.lean
   lake env lean /tmp/Names.lean
   ```
   For a proposition of Book II or III, open `Elements.BookII` or `Elements.BookIII` in
   place of `Elements.BookI`; the earlier books' names are then written `BookI.PropN`,
   `BookII.PropN`, as the orders ask. Opened as above, a bare `Prop4` would be I.4 and
   pass unnoticed.
9. Each quotation has Heath's wording and page. Flatten the OCR once,
   `perl -0pe 's/-[ \t]*\n\s*//g; s/\s+/ /g' "$HEATH_OCR" > /tmp/heath.txt`, then
   `grep -oi 'a distinctive phrase.\{0,80\}' /tmp/heath.txt`: it agrees but for OCR
   misreadings ("toudi" for "touch"), or the page image does. The running head
   above it gives the page.
10. Each quoted page lies between the first page of `heath/I/NN.md` and that of
    the next file (`grep -m1 -o 'pp\?\. [0-9]*' heath/I/NN.md`), or is Heath's
    introduction or front matter; otherwise the quotation becomes a clause.
11. `grep -ohE '"[^"]{40,}"' mishnah/*/*.md | sort | uniq -d` prints nothing but
    Euclid's own words.
12. Each hit of `grep -nE '[“”‘’]|(^|[^*])\*"|"\*($|[^*])' F` is an italic Heath
    printed.

12b. Every italic Heath printed is kept. The scan's ABBYY file
    (`https://archive.org/download/<id>/<id>_abbyy.gz`, `<id>` as for the page images)
    flags each italic letter with `italic="true"` on its `<formatting>`; on the quoted
    page (the `<page>` of its leaf, counting from 0), every word inside the quotation
    so flagged is in italics in F, and no other. Where a flag is doubtful, the page
    image decides.
13. Each hit of `grep -nE 'Avigad|LeanEuclid' F` is a particular debt, not thanks.
    Each rule name is a docstring label: `grep -rn 'Intersection 5' Elements/Foundations/Tacit`.
14. What it says of the Lean's citations and postulates matches `facts.json`:
    `python3 -c "import json,sys; p={x['ref']:x for x in json.load(open('facts.json'))['propositions']}[sys.argv[1]]; print(*p['direct_axioms']); print('cites', *p['cites'])" I.N`.
15. Every letter named is in `heath/I/NN.md`; every name is spelled as Heath
    spells it, and each person has a full name at the first mention on the page
    (§1).

**Lean**

16. `lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py`
    passes (leave the regenerated `facts.json` uncommitted).
17. `git diff main -- F` leaves every `theorem PropN` statement alone, or the first
    mate or captain agreed.
18. `grep -nE '^(theorem|lemma) ' F`: helpers before `PropN`, corollaries after;
    none restates a Book Zero lemma (search `Elements/Figure/` for its conclusion).
19. The `cites` from check 14 match the brackets in `heath/I/NN.md`, or the
    difference is accounted for. An extra citation that a shared step brings in is
    shown by the page's generated "Brought in by shared steps" line, and the mishnah
    says nothing of it. The mishnah explains a citation only where the Lean departs
    from Euclid's route or the reason is part of the story: one clause naming his
    step ("Euclid gives no citation for it: it is I.10").

**Figures**

20. The letters are Heath's, no more and no fewer (this prints nothing), and
    `grep -oE '\{[^}]*: Point\}|obtain ⟨[^⟩]*⟩' Elements/BookI/PropNN.lean` shows
    the Lean using the same (a helper written once over any letters, such as
    `Prop44.place`, may use its own):
    ```sh
    diff <(grep -o '<text[^>]*>[A-Z]</text>' figures/I/NN.svg | sed 's/<[^>]*>//g' | sort -u) \
         <(sed -e 's/<!--.*-->//' -e 's/\[[^]]*\]//g' -e 's/Q\. E\. [DF]\.//g' -e 's/I say//g' -e 's/PORISM\.//' -e '/^#/d' heath/I/NN.md \
             | grep -oE '\b[A-Z]+\b' | fold -w1 | sort -u)
    ```
21. `grep -oE '#[0-9a-fA-F]{3,6}' F | sort -u` lists only section 4's colours, and
    the `viewBox` is the right size.
22. `grep -o '<desc>.*</desc>' F`: one or two short sentences, in the house voice,
    and `sed -n 's:.*<desc>\(.*\)</desc>.*:\1:p' F | wc -w` is about 40 at most.
23. `rsvg-convert -w 800 F -o /tmp/fig.png`, and look: letters clear, nothing
    clipped, points where the proof puts them, sizes like the others'.

**Heath's text**

24. `git diff main -- heath/` is empty, or each change carries a comment naming the
    page image checked.

**Further reading**

25. `grep -c . F` is 1 to 3 and `grep -vc '^- ' F` is 0, and every link is one the
    reading list gives (this prints nothing):
    ```sh
    grep -oE '\]\(https?://[^)]+\)' F | sed 's/^](//; s/)$//' |
      while read -r u; do grep -qF "]($u)" docs/reading.md || echo "not on the list: $u"; done
    ```
