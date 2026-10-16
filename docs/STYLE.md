# House style

How Stoicheia reads and looks at its best, drawn from the mishnah of I.1–I.3, the
bosun's reviews, [CONTRIBUTING](../CONTRIBUTING.md) and the
[first inspection](reports/crew/inspection-01.md). Everyone who writes for the
project works from it; every new or changed file is checked against the list at
the end.

## 1. Voice

- **One warm, plain voice.** "We" for the project ("our I.1 lets the side be
  named"), "Lean" for what the machine insists on. No "I" or "my" outside
  quotations.
- **No crew talk where readers look** (the mishnah, captions, Lean comments, the
  gap catalogue, the README, the pages): "Book Zero proves it once", not "the first
  mate added it". Ranks belong in `docs/reports/crew/` and `docs/briefs/`, and in the
  README's "How it was made", which says plainly how the work is done.
- **People by name**, spelled as Heath spells them (Proclus', an-Nairīzī, van
  Pesch); modern authors in full ("Robin Hartshorne's *Geometry: Euclid and
  Beyond*"). Say who saw a gap first, where we know; call a find new only when it
  is.
- **No comparisons.** Nothing here is first, only, better or unlike anyone else's
  work; we say what others' work does well, and link to it. ("Only one triangle"
  is geometry, and fine.)
- **Euclid's words for Euclid's things**: "straight line", "produced", "on one
  straight line", "the angle ABC". A Lean word gets a plain gloss the first time.
- Short sentences, and no em dashes: a comma, colon or full stop does it.

## 2. The mishnah

**Shape.** 200–500 words, aiming at 300–400, in 3–5 paragraphs of no more than
about 150 words. Each opens with a short bold lead ending in a full stop (a
question mark if it asks): **The circles that must meet.** A lead may quote
Euclid or Heath: **"Not lying on the same side."**

**The modern way.** Always the last paragraph: coordinates, vectors, complex
numbers or matrices, a sentence or three (under 100 words), exactly right.
If the modern point is not Euclid's, say so: I.2's L lies on DA produced, so it is
not A + (C − B).

**What belongs.** What Euclid takes for granted; what Lean made us say out loud,
with exact Lean names in backticks (`circles_meet`, `Prop1.figure`); one or two of
Heath's best notes. Finer gaps go in the [gap catalogue](reports/gaps-book-I.md).

**The certificate** counts everything a proof rests on, cited propositions
included. Say the proof *uses* Postulate 1 at a step, check `facts.json` before
saying more, and name any cited proposition that brings it in too.

**Quotations.**

- Heath's exact 1908 words, in straight double quotes, with the page: "(vol. 1,
  p. 242)", or "pp. 253–254" when the passage crosses a page; "(Heath, vol. 1,
  p. 252)" when the sentence doesn't name him. Those Heath reports (Proclus,
  Todhunter, De Morgan) take his page.
- Single quotes inside, "…" for a cut, and brackets inside are Heath's own. No
  added italics: only those Heath printed.
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
friendly lines, each a list item naming a work from [the reading list](reading.md): the
author in full, the title in italics with the list's link, then a sentence on what the
work gives this proposition, with the chapter where the list names one, and **Free**
where the list says so. Verified works only: a new one goes on the list first, checked,
and into `references.bib`. Every new page adds its own, Book III's among them; with
nothing apt, there is no file and no section.

## 3. Lean

- **Euclid's words in `--` comments, ours in `/- … -/`.** The docstring of
  `theorem PropN` is Heath's enunciation; in the proof each of Euclid's sentences
  is a `--` line, word for word (indentation may change), with its Lean directly
  under it.
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
  Lean cites one he gives no bracket for, the mishnah says why.
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
  voice, colours named in brackets.
- **`NN.svg`, Euclid's figure.** 400 wide (440 at most). Italic letters at 17; ink
  `#3b2f2f` for lines, dots and letters; circles `#8c7b62`; what the proposition is
  about in `#a0522d`, drawn heavier; triangle fills `#e9dcc0` at 0.55. Dots r 2.6,
  lines 1.6, circles 1.3. Title "Euclid I.N: …", no caption.
- **Heath's letters, all and only**, each point where the proof puts it (I.6: D on
  AB), clear of every stroke, nothing touching the frame. Where the Lean places a
  point otherwise than Heath's figure, draw the proof and let the mishnah say so
  (I.23).

## 5. Text and citations

- **`heath/` is Heath's, untouched.** The source comment first (pages, scan
  leaves), the enunciation in italics, then one sentence or clause per paragraph,
  as the `--` comments take them. Changes only against the page image.
- **Square brackets** there are his, kept exactly: the justifications `[I. 2]`,
  `[Post. 3]`, `[C.N. 1]`, `[Def. 15]`, `[Post. 4 and C.N. 1]`, II.10's
  `[I. Post. 5]` with its book, and Heiberg's brackets round a passage he judged
  added later (I.4, I.15's Porism), with a comment. In our prose a bracket appears only when we quote one: "the bracket
  [I. 20]".
- **Our prose writes** I.5, II.4, I.1–I.24 (en dash); Postulate 3, Common Notion 1,
  Definition 15 in a sentence; Post. 3, C.N. 1, Def. 15 in parentheses and tables.
  Quotations keep Heath's "I. 5".
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

4. `wc -w F` is 200–500.
5. `awk 'BEGIN{RS=""}{print NR": "NF}' F` shows 3–5 paragraphs, none much over 150.
6. This prints nothing:
   `awk 'BEGIN{RS=""} !/^\*\*[^*]+[.?]"?\*\* /{print "no lead: " NR} {l=$0} END{if (l !~ /^\*\*The modern way\.\*\* /) print "not last: the modern way"}' F`
7. The modern way is one to three sentences, under 100 words, and exactly right.
8. Lean knows every backticked name (no "Unknown"):
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
13. Each hit of `grep -nE 'Avigad|LeanEuclid' F` is a particular debt, not thanks.
    Each rule name is a docstring label: `grep -rn 'Intersection 5' Elements/Foundations/Tacit`.
14. What it says of the certificate matches `facts.json`:
    `python3 -c "import json,sys; p={x['ref']:x for x in json.load(open('facts.json'))['propositions']}[sys.argv[1]]; print(*p['direct_axioms']); print('cites', *p['cites'])" I.N`.
15. Every letter named is in `heath/I/NN.md`, and every name is spelled as Heath
    spells it.

**Lean**

16. `lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py`
    passes (leave the regenerated `facts.json` uncommitted).
17. `git diff main -- F` leaves every `theorem PropN` statement alone, or the first
    mate or captain agreed.
18. `grep -nE '^(theorem|lemma) ' F`: helpers before `PropN`, corollaries after;
    none restates a Book Zero lemma (search `Elements/Figure/` for its conclusion).
19. The `cites` from check 14 match the brackets in `heath/I/NN.md`, or the
    mishnah explains each extra one. When a shared step brings it in, a sentence
    naming the step is explanation enough (`Prop30.meet` brings in I.30).

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
22. `grep -o '<desc>.*</desc>' F`: one or two short sentences, in the house voice.
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
