# Brief 0010: the notation of the Lean statements

*Status, 21 October 2026: approved, and from that day frozen. [The decisions entry of that
day](../decisions/2026-10-21-briefs-0010-and-0012.md) records the owner's ruling and the
coordinator's reading of it, by which each question of section 8 takes this brief's
recommendation. The option the owner chose names the brief "with its centre aliases", an
amendment of 19 October not yet in this file (a sentence added on 25 October, as the
entry's note of that day says). Question 3, on which the brief makes no choice, was left
open that day, to be settled before the consolidation release.*

*Drafted 18 October 2026 and brought up to main on 19 October. **A draft, for the owner's
approval: nothing changes until it is approved.** The owner decided on 18 October
([issue #69]) that the notation of the Lean statements is settled once, in a short brief,
and applied once, between the consolidation release of Books I to III ([#38]) and Book IV,
so that the records of Books I to III are re-stamped once. This brief sets out each point
raised, its options, a recommendation and what it costs, and ends with the questions the
owner and the coordinator decide (section 8). Nothing in `Elements/`, `Staging/`, the
scripts or the review records changes with it: the pass of section 6 begins only after the
approval. Once approved it is frozen, as [WORKFLOW.md](../WORKFLOW.md), section 2, says of a
brief, and a later change is a revision of it.*

*A first review, on 18 October, by a reader who did not write the draft, added the clash of
our angle with Mathlib's scoped `∠` (section 3.2), the cost of scoping released bars
(section 3.1) and tests 10 to 13, and corrected the counts. On 19 October the counts were
taken again on main, and the tests that need no Mathlib were run again there (the
appendix). Then a challenger who did not write it, Astra (through Codex, read-only),
returned the draft for correction, with five material findings and three editorial; every
one is answered below, and the second appendix lists them. The largest changes the
recommendation for the angle (section 3.2). Warm thanks to Astra. An independent review
of the revised draft, that day, found that the new angle reaches one more protected file,
`scripts/negative_tests.py`, which quotes I.16's statement; section 6 adds it, ahead of the
content pass, and a further review that day made the citation of brief 0012 checkable,
completed section 6's lists and corrected two counts (sections 2 and 3.5). A last review
that day set the cost of statements written with `Arc.ofHeath` apart from the notation's
(sections 2, 3.3, 5 and 6, and question 3), and limited what a build without warnings
shows (section 6).*

The points are Argon's. Its second review of the `book-III` release, which read the checks,
the records and the pages line by line, gave section 3.3 to the notation of the Lean
statements, with every case located, and the responses to that review ([#71]) send the
whole section here. Warm thanks to Argon, for reading the statements as a Lean user first
meets them. The symbols themselves come from the System E of Jeremy Avigad, Edward Dean and
John Mumma, and LeanEuclid and Mathlib show two other good ways to write the same things;
each is cited below where its choice bears on ours.

Base: main at `89c5da4` (19 October, after trains #100 to #111: stage 2 and stage 4b's
III.7, III.8 and III.17 in the edition, the formal model complete, the table of names and
the naming policy of [#76] landed). The draft was first written on main at `4d02d50`.
Every claim below about how Lean behaves was tested in Lean 4.35, in scratch files outside
the repository; the appendix lists the tests and the revision each ran on, and none is
committed.

## 1. What weighs

The owner's direction, 18 October: "this is about being the definitive Stoicheia project;
think what makes it easiest for others to use, not others to have to fix". Two kinds of
user read the Lean statements:

- **Readers** meet them on every page, in the "In Lean" block under Heath's enunciation and
  among his sentences. A reader should be able to read a statement without a key, or with a
  short one beside it.
- **Lean users** depend on the library: the README's "Use it" gives the one `require`
  line, [the table of names](../../book/names.md) gives every proposition, porism and
  companion, and FORMALIZATION, section 2, "Names, and how they change", promises that a
  released name never changes without a deprecated alias for one release ([#76], landed
  in train D2, #106). Most of them work with Mathlib open in the same file.

Five rules follow, and every recommendation below applies them.

1. **A symbol stays where it says what Euclid says and means nothing else to a Lean user.**
   Otherwise the plain word, which every reader can read and every Lean user can type,
   search for and hover over.
2. **Change how a word is written before changing the word.** A notation is seen only by
   Lean's parser and printer: the statement Lean records, its certificate, the lock and the
   records' fingerprints do not see it (section 2). A word belongs to the foundations, and
   renaming one is a foundation decision.
3. **Once released, arguments or fields of one type are never reordered in place.** Lean
   cannot tell `circumference α B K C` from `circumference α K B C`: a user's code would
   still compile, and mean something else. Such a change is made before the first release,
   or under a new name with the old one deprecated.
4. **The names of bound variables are part of the interface.** A caller may name an
   argument, as I.23 calls I.22 with `(A₁ := C) (A₂ := D) … (C₂ := E)`; the library names
   an argument so 199 times, in 42 files, 141 of them a point or a circle by Heath's
   letters, in 23. Renaming a bound variable changes the statement's fingerprint, since
   bound names are printed; for its callers, Lean 4.35's `@[deprecated_arg old new]` keeps
   the old name working for a release, with a warning (appendix, test 15), as a deprecated
   alias does for a name.
5. **Explain where the reader meets the Lean.** FORMALIZATION's vocabulary is the one home
   of what each word means; a key under each page's Lean block, generated from the words
   that page's statements use, puts it where it is read.

## 2. What a change costs

`Certificate/Facts.lean` prints each statement for `facts.json` "with every name written
out and no notation" (the options `pp.notation false` and `pp.fullNames true`). A review
record's fingerprint is a hash of those strings
([review/SCHEMA.md](../../review/SCHEMA.md)), and the lock prints its entries the same way.
I.3, as `facts.json` has it (one line in the file):

```
∀ {A B C₁ C₂ : Elements.Point}, Ne C₁ C₂ → LT.lt (Elements.len C₁ C₂) (Elements.len A B) →
  Exists fun (E : Elements.Point) => And (Elements.Between A E B) (Eq (Elements.len A E) (Elements.len C₁ C₂))
```

The bars of `‖C₁ C₂‖` are not there; the word `len` and the bound names `C₁`, `C₂` are. So
four kinds of change cost differently:

| Change | Records | Lock | Lean users |
|---|---|---|---|
| How a word is written (a notation) | the `lean` stamp of each proposition file whose text changes; no fingerprint | nothing | the old notation kept for one release, with a warning (section 7) |
| A word renamed (`len`, `Triangle`) | the `lean` stamp, and the fingerprint of every statement that names the word | the word's entry and every entry that names it (eleven axioms and five definitions name `len`), with the two lock hashes, `tests/model/lock.sha256` and `model/lock.sha256`, MODEL.md and the formal model's signature ([#73]) | a deprecated alias for one release ([#76]) |
| A bound variable renamed (`ABCD`, `C₁`) | the `lean` stamp, and the fingerprint of each statement that binds it | nothing | calls that name it warn for one release, under `@[deprecated_arg]` (test 15), then break |
| Arguments or fields of one type reordered | as for a renamed word | a reordered definition's entry, or, for a structure, the entries of the fields that move (for `Arc`, `Arc.C` and `Arc.K`, not `Arc`'s own); and every entry that applies a reordered function by position | nothing warns: old code compiles with a new meaning |

Issue #69 plans for every record of Books I to III to be re-stamped once. On the
recommendations below the notation pass costs less than that: no fingerprint changes and
nothing in the lock, and the `lean` stamps of 98 of the 99 proposition files are re-read
once (section 6). Open question 9, if the owner keeps the angle's symbol, would lower the
98 files to 77. Open question 3 is not a change of notation, and is costed apart (section
3.3). Heath's field order for the arc, taken before the consolidation release, would change
the fingerprints of the four statements that build an arc by position and two lock entries.
A constructor in Heath's order costs nothing while no statement uses it; each statement
rewritten with it is a statement change, with its own approval, that changes the
statement's fingerprint and `lean` stamp and brings the constructor's definition into the
lock, with the two lock hashes renewed after review.

## 3. The five points

### 3.1 `‖A B‖` reads as a norm

**What Argon found.** "Writing `‖A B‖` for segment length looks to a mathematician like the
norm of a product $AB$".

**What the Lean has.** `len : Point → Point → Length`, an opaque word, written `‖A B‖` by a
global notation in `Elements/Foundations/Magnitudes.lean`. System E writes the length `ab`,
for its function segment(a, b), beside `∠abc` and `△abc` (Avigad, Dean and Mumma, section
3.1, "The language of E"); Lean reads `A B` as an application, so ours took bars. There are
1,932 lengths written so in the Lean, 1,233 of them in 72 of the 99 proposition files and
the rest in the foundations, Book Zero, the helpers, `Staging/` and the audit. The
commentary has none: it says "the straight line AB".

**What a Lean user meets.** Mathlib writes the norm `‖e‖` by a global notation of its own
(`Mathlib/Analysis/Normed/Group/Defs.lean`). With both in scope, every `‖…‖` that both can
parse has two readings, and Lean elaborates both. A correct `‖A B‖` still works, but slips
are reported in the other reading's terms, both ways round. With a stand-in for Mathlib's
notation (appendix, tests 1 and 2), and again with Mathlib v4.35.0 itself (test 10), our
`‖A B C‖` gave "Function expected at A", the norm's error; and a Mathlib user's own slip,
the norm of a two-argument function, gave "overloaded, errors", with a mismatch against our
`len` and `Point`. So importing the
library changes the error messages of a Mathlib user's own norms: just what the owner asks
us not to leave others to fix.

**Options.**

- *Keep, and explain.* The vocabulary and the page key say that the bars are a length. The
  clash stays, and so does the first impression.
- *Keep, scoped to `Elements`, and explain.* Every file of the library that writes the bars
  is inside `namespace Elements…` or opens it, and keeps them; a user who imports the
  library without `open Elements` never meets them (appendix, test 3). One line of the
  foundations changes, and no proposition file. But `open Elements` is the natural first
  line of a user's file, and with it the clash comes back; and a reader still sees a norm.
  Scoping released bars also breaks, with a parse error, every file outside the library
  that writes them without opening the namespace, and no release of warnings leads up to
  it cleanly: a deprecated global form beside the scoped one makes every use ambiguous
  after `open Elements` (test 13), and a deprecated global form alone warns every user,
  those who already open the namespace included.
- *Another bracket.* `|A B|`, the school form, meets Mathlib's absolute value `|a|` instead
  of its norm, and, declared as plainly as ours, it breaks Lean's own
  `fun | 0 => … | _ => …` (test 4). `⟦…⟧` is Lean's quotient, `⟪…⟫` Mathlib's inner
  product, and `∥` Mathlib's parallel. LeanEuclid, which brought System E to Lean, writes a
  length `|(a─b)|`: a segment object `(a─b)` inside bars that take priority over the
  absolute value. That suits its segments well; we have no segment object, and the bars
  would still meet Mathlib's.
- *The word, `len A B`.* No notation at all. It is two characters longer than `‖A B‖`, and
  reads without a key: I.20 becomes `len B C < len B A + len A C`. Neither Lean nor
  Mathlib declares a `len` outside a namespace (test 10), so it means nothing else to a
  Lean user. A Lean user types what the page shows in any file that opens `Elements`, or
  `Elements.len A B` in one that does not, with no notation to bring into scope, and finds
  `len` by search or hover. Lean records the same term, so this is a change of notation:
  no fingerprint, and nothing in the lock.

**Recommended: the word, `len A B`.** It is the one option that serves the reader and the
Lean user with Mathlib open at once, and it costs only `lean` stamps. Book II's magnitudes
already read so (`rect A B C D`, `sq A B`, `quadArea A B C D`). The bars stay for one
release, with a warning (section 7). If the owner weighs the look of the pages more, the
fallback is the second option, scoped bars with a key on every page.

### 3.2 `△ A B C` is an area, while `Triangle A B C` says the points are not in line

**What Argon found.** "`△ A B C` denotes the *numerical area* (`Area`) of the triangle,
whereas `Triangle A B C` is the `Prop` that $A, B, C$ are non-collinear."

**What the Lean has.** `area : Point → Point → Point → Area`, opaque, written `△ A B C`; and
`Triangle A B C`, Definition I.19's trilateral figure, defined as `¬ Collinear A B C`. There
are 271 areas written `△` in the Lean, 190 of them in 20 proposition files and the rest in
the foundations, Book Zero, the helpers and `Staging/`; `Triangle` is in 41 of the
certificate's 121 statements (porisms and companions among them).

**Why it misleads.** In the systems ours follows, △ is the area: System E writes `△abc` for
its function area(a, b, c), and LeanEuclid's `△ a:b:c`, a triangle object, stands for its
area through a coercion. To most modern readers, though, △ABC is the triangle itself, so
`△ A B C = △ D E F` invites "the triangles are congruent", which says more than the Lean
does. The Lean says what I.4's "the triangle will be equal to the triangle" means: equal in
area.

**Options.**

- *Keep, and explain.* The key says that △ is the area, with System E's and LeanEuclid's
  precedent behind it.
- *Rename the predicate* (`NonCollinear`, `Trilateral`). A renamed word, in 41 fingerprints
  and the lock, for a word that reads exactly as Euclid's setting-out does: I.20's "let ABC
  be a triangle" is `Triangle A B C`.
- *The word, `area A B C`*, System E's own name for the function. Lean records the same
  term, and `area A B C` beside `Triangle A B C` says plainly which is the magnitude and
  which the claim.

**Recommended: `area A B C`; `Triangle` stays.** Of the 20 files it touches, 15 change for
`len` already, so it adds five (I.37, I.39, I.41, I.42, I.43). The △ stays for one release,
with a warning.

**The angle, `∠ A B C`.** It is System E's symbol, and Mathlib's for the same unoriented
angle (`EuclideanGeometry.angle`), so a reader and a Lean user both read it rightly. The two
notations do collide, though, and more sharply than the bars: there a correct term still
works in either reading, and here a correct Mathlib angle does not (appendix, test 11, with
Mathlib v4.35.0 itself). Mathlib's `∠` is scoped, a bare symbol applied like a function;
ours is global and takes its three points, so it is the longer parse, and Lean keeps only
the longer. In a file that imports the library and opens `EuclideanGeometry`, a Mathlib user's
`∠ p q r` is read as ours and fails ("Application type mismatch", in `Elements.ang p`), and
`∠ p q` no longer parses; the user writes `EuclideanGeometry.angle p q r` instead, since a
file cannot switch off a global notation it imports. Giving ours Mathlib's shape
(`notation "∠" => ang`) does not mend it: both readings then elaborate on our points, and
Lean calls `∠ A B C` ambiguous (test 12). The word `ang A B C` ends the clash, at the cost
of 21 more proposition files (98 of the 99 in all; `∠` is written 1,974 times in the Lean),
and of pages that read `ang A B C` where they now read `∠ A B C`.

The first draft recommended keeping `∠` and explaining it. The challenge of this draft
argued the other way, and we agree: the clash reaches every Mathlib user who imports the
library and writes Mathlib's angle, whether or not they open `Elements`, and an
explanation tells them how to repair their code without removing the reason to. That is
just what the owner asks us not to leave to others. **Recommended: the word `ang A B C`,
with `∠` kept for one release in the form of section 7, and then removed.** If the owner
weighs the look of the pages more, the fallback is `∠` kept global, recorded as an accepted
limitation for Mathlib users, with the key and the table of names saying how to write
Mathlib's angle beside it (open question 9). `∟` stays: LeanEuclid writes the right angle
the same way, and Mathlib has no `∟`.

### 3.3 `circumference` and `standing` take their arguments in different orders

**What Argon found.** Two words "with different argument conventions for the same arc",
"confusing for any reader of Book III's Lean statements (especially in `Prop27` and
`Prop30`, where `standing ADB A B D = standing ADB D A B` is used for arc bisection)".

**What the Lean has.** Both are `Circle → Point → Point → Point → Angle`, defined in
`Elements/Foundations/DefinitionsIII.lean`. In `circumference α B K C` the middle letter K
is on the arc's side of BC: Heath's "the circumference BKC" (III.26). In
`standing α B A C` the middle letter A is the vertex of the angle BAC, on the other side,
which in Definition III.9's words "is said to stand upon that circumference". Each puts its
distinguished letter where Heath does. The trouble is that Lean cannot tell the two
conventions apart, and accepts a vertex where a point of the arc is meant. Four statements
use `circumference` (III.24, III.26, III.28, III.29) and two use `standing` (III.27,
III.30).

**What stage 3 adds.** [Brief 0006](0006-statements.md) (frozen) makes arcs objects,
`structure Arc` with the fields `circle`, `B`, `C`, `K`, and
`Arc.measure a = circumference a.circle a.B a.K a.C`, and it keeps "the four-argument
`circumference` and `standing` … as Heath's measure words". So after stage 3 one arc is
written in a third order: the staged III.24 writes Heath's segment AEB as `⟨AEB, A, B, E⟩`
(`Arc.Congruent ⟨AEB, A, B, E⟩ ⟨CFD, C, D, F⟩`), and its circumference as
`circumference AEB A E B`. Stage 3 is proved in `Staging/` ([#89]), and its move into
`Elements/` is under way ([#25]); [#67] plans to restate III.30 with arcs, which would
leave `standing` in III.27 alone. Book IV will write arcs too: its regular figures are
inscribed by the equal circumferences their sides cut off (brief 0012, Book IV's draft
brief for [#97], not yet on main).

*25 October 2026: stage 3 has since moved into `Elements/`, with train C6a ([#240], 21
October). The III.24 called staged above is now `Prop24` in
[`Elements/BookIII/Prop24.lean`](../../Elements/BookIII/Prop24.lean), which writes the
segments as above; `circumference AEB A E B` is written by its companion
`Prop24.equalCircles`, in the same file. `Staging/` holds no part of stage 3. [#67] gave
III.30 a companion in arcs, `Prop30.halves`, and III.30's statement keeps `standing`. The
move landed before the arc's field order was decided, so question 3's later limit, the
consolidation release, is the one that stands. The paragraph above is left as drafted.*

*26 October 2026: question 3 is answered. On 25 October the owner accepted the
coordinator's recommendation to keep the arc's fields in the order they have in
`Elements`, `circle`, `B`, `C`, `K`, as
[the decisions entry of that day](../decisions/2026-10-25-arc-field-order.md) records; no
field, statement or lock entry changes. The options and the recommendation below are left
as drafted.*

**Options.**

- *Keep both words, and explain* the middle letter, in their docstrings, the vocabulary and
  the key.
- *Rename `standing`* (`standsOn`, `arcUnder`). The middle letter keeps its meaning, so a
  new name buys little; it costs two fingerprints, a lock entry and a deprecation; and
  Heath's word is "stand upon".
- *Reorder `standing`'s arguments*, vertex first. It would no longer read as Heath's angle
  BAC, and nothing would warn its users (rule 3).
- *A notation for arcs* (`⌒`). Another symbol to learn, for a reader who has Heath's words
  beside it.
- *One order for an arc, Heath's.* Give `Arc` its fields in the order Heath letters an arc,
  `circle`, `B`, `K`, `C`, so that the segment AEB is `⟨AEB, A, E, B⟩` and its circumference
  `circumference AEB A E B`. The fields read by name (`a.B`, `a.K`, `a.C`) as before, and
  so does construction by name (`{ circle := AEB, B := A, C := B, K := E }`); positional
  construction and matching change (`⟨…⟩`, `Arc.mk`, patterns).
- *A constructor in Heath's order, beside the fields.* Keep the fields in their order, and
  add `Arc.ofHeath α B K C`, which builds the arc BKC. Added and unused, it moves nothing:
  no field, no statement and no lock entry changes, so it can be added before the release
  or after it. Writing a statement with it in place of `⟨…⟩` is another change, a
  statement correction with its own approval. Lean then records `Arc.ofHeath AEB A E B`
  where it recorded `Arc.mk AEB A B E` (III.24), so the statement's fingerprint changes
  and its file's `lean` stamp goes stale; and the certificate's vocabulary walk, which
  starts from the constants of the statements, reaches the new word, so its definition
  joins the lock, and the lock and the two lock hashes are renewed after review.

**Recommended: keep both words and explain them; and decide the arc's field order before
the consolidation release** (open question 3). Before `Arc` is first released, reordering
its fields costs the fingerprints of the statements that write an arc as `⟨…⟩` (III.24,
III.26, III.28 and III.25's `Prop25.complete`, as staged) and the lock's entries for the
two fields that trade places, `Arc.C` and `Arc.K` (the challenge of this draft found, with
the certificate's printer, that the entry for `Arc` itself would not change), and needs no
deprecation. After the release the fields could not be reordered: `⟨α, B, C, K⟩` would
silently mean another arc (rule 3). A third way works before the release or after it: keep
the fields, and add a function that takes Heath's order, `Arc.ofHeath α B K C` for the arc
BKC. Adding it costs nothing; writing the four statements with it in place of `⟨…⟩` costs
what reordering does in the records, their fingerprints and `lean` stamps, and in the lock
one new entry, `Arc.ofHeath`'s, in place of the two fields' changed entries. The staged
III.28 shows what is at stake:
Heath's circumference ACB of the circle ABC is `⟨ABC, A, B, C⟩` there, and would be
`⟨ABC, A, C, B⟩` in Heath's order, or `Arc.ofHeath ABC A C B`. Either way changes what
Lean records, so it is a statement change with its own approval, and no part of the
notation pass of section 6. The decision
belongs with brief 0006, whose definition it would revise, and with the migration of stage
3 now under way ([#25]); this brief raises it, and does not take it. It is the one question
here with a deadline that is not the owner's to set: the move puts `Arc` into `Elements/`,
and the consolidation release would release it. Taken before the move lands, either way
costs the staged files alone, which the certificate does not yet read: the move then brings
the statements into `facts.json` in the chosen form, and a constructor's entry into the lock
with stage 3's other words.

### 3.4 Circles named ABCD beside the points A, B, C, D

**What Argon found.** "Circle variables named by 3 or 4 point letters (`ABC`, `ABCD`,
`ABDC`, `AEB : Circle`) alongside points `A, B, C, D : Point`", and a straight line `AB` in
I.29's proof.

**What the Lean has.** FORMALIZATION, section 2: "Points, straight lines and circles take
Heath's letters (`BCD` for the circle BCD)". Fourteen circle names are bound in 42
statements: every proposition of Book III, the porisms of III.1 and III.16, and the
companions of III.7, III.8 and III.17. Hypotheses are named from them (`hA_BCD`). The axioms and Book Zero's general facts use
Greek letters (`α`, `β`), as System E does ("α, β, γ, . . . to range over circles", section
3.1).

**Options.**

- *Keep, and explain the split:* a proposition's circle takes Heath's name, a general fact's
  a Greek letter. `OnCircle A ABCD` reads as Heath's "A on the circle ABCD", and Lean sees
  one name, `ABCD`, declared `{ABCD : Circle}` in the statement.
- *Greek letters throughout.* Lean's idiom and System E's, but the tie to Heath's text
  (AGENTS.md, rule 5) moves into a remark, each statement's fingerprint changes, since bound
  names are printed, and calls that name the circle warn for a release and then break
  (rule 4).
- *A marked name.* Lean's unquoted identifiers cannot hold `⊙`, the usual mark for a
  circle (test 9); quoted, `«⊙ABCD»`, it can, but every use must type the guillemets, and a
  letter prefix (`cABCD`) reads worse than the plain name.

**Recommended: keep Heath's letters, and explain the split**, in the vocabulary and in the
key of each page with a circle ("`ABCD` is the circle ABCD, named by Heath's letters"). The
same holds for a straight line named in a proof (`AB : Line`), which no statement binds.
Cost: none.

### 3.5 Euclid's straight line C, written as the points C₁ C₂

**What Argon found.** "Subscripted point pairs `A₁ A₂`, `B₁ B₂`, `C₁ C₂` or `C₁ C C₂` where
Euclid names a single magnitude `A`, `B`, `C` or angle `C`", in I.3 and I.22, and, for a
given rectilineal angle, three points such as `D₁ D D₂` in I.42, I.44, I.45, III.33 and
III.34.

**What the Lean has.** FORMALIZATION, section 2: "a straight line he names with one letter
becomes two points (`A₁ A₂`)". Nine main theorems name an object of Euclid's single letter
by its points, and eight companions of I.45, II.1 and II.14 do the same: a straight line by
its ends (I.3, I.22, II.1); a rectilineal angle by its vertex and a point on each arm (the
angle D of I.42, I.44 and III.34, `∠ D₁ D D₂`; the angle E of I.45; the angle C of III.33);
and a triangle or a figure by its corners (I.44's triangle C, `C₁ C₂ C₃`; II.14's figure
A, `A₁ A₂ A₃ A₄`). Euclid's straight line C is a finite straight line, with two ends,
and his one letter labels it.

**Options.**

- *Keep, and explain:* C₁ and C₂ are the ends of Euclid's straight line C.
- *A length in place of the straight line* (`c : Length`). That changes the meaning, not the
  notation: I.3 places at A a straight line equal to C, by I.2, which needs C's ends, and no
  rule of the foundations says that every length is the length of some straight line.
- *A segment object* (`C : Segment`, its ends `C.1` and `C.2`). It reads as Euclid's "the
  straight line C", but it is a new word in the foundations and the lock, it renames bound
  variables in five statements, I.3, I.22 and II.1 and II.1's companions `Prop1.general`
  and `Prop1.two` (rule 4: I.23's call of I.22 names all six, and would warn, then break),
  and it asks
  every caller to wrap two points as `⟨P, Q⟩`.

**Recommended: keep, and explain**, in the vocabulary and the key ("C₁ and C₂ are the ends
of Euclid's straight line C"; "D₁ and D₂ are points on the arms of Euclid's angle D"). For a
Lean user, two points are the plainest thing to pass. Cost: none.

## 4. Argon's further points in section 3.3

The responses to Argon's review ([#71]) send three more points here.

- **I.34's vertex order**, `Parallelogram A C D B`. This is Heath's own name, "Let ACDB be a
  parallelogrammic area, and BC its diameter", with the corners in order round the figure,
  as `Parallelogram` takes them. Keep it, and the key says so.
- **A foot of a perpendicular given by a `∀`**, in III.14 and III.15 and a helper of III.9.
  Stage 4 brings `Foot E A B F` (brief 0006, "The foot of the perpendicular"), which the new
  statements of III.14 and III.15 use. Rewriting an older statement with it changes what
  Lean records, so it is a statement correction with its own approval, and not part of this
  pass.
- **Book I's names declared in later books' files**: `BookI.Prop47.sq` in Book II's
  `Rectangles.lean`, and `BookI.Prop46.sq` in Book III's `Squares.lean`. The square `sq` is
  defined with Book II, so I.47 said with squares cannot stand in Book I's file, and the
  name says whose fact it is. Keep the names: their modules are `Elements.BookII.Rectangles`
  and `Elements.BookIII.Squares`, respectively, and I.47's page explains its form in squares.
  A rename would cost a deprecation and show a reader nothing new.

## 5. The vocabulary, as recommended

| Euclid | Now | Recommended | Why |
|---|---|---|---|
| the straight line AB, as a length | `‖A B‖` | `len A B` | the bars read as a norm, and clash with Mathlib's |
| the angle ABC | `∠ A B C` | `ang A B C` | the symbol is System E's and Mathlib's, but ours, global, hides Mathlib's in every file that imports the library (open question 9) |
| the triangle ABC, as an area | `△ A B C` | `area A B C` | △ reads as the triangle itself; `area` is System E's name |
| a right angle | `∟` | `∟` | unchanged |
| "let ABC be a triangle" | `Triangle A B C` | `Triangle A B C` | Euclid's setting-out, word for word |
| the rectangle AB, CD; the square on AB | `rect A B C D`, `sq A B` | unchanged | words already |
| the circumference BKC | `circumference α B K C` | unchanged, explained | Heath's letters: K on the arc |
| the circumference on which the angle BAC stands | `standing α B A C` | unchanged, explained | Heath's letters: A the vertex |
| the arc BKC, and its segment (stage 3) | `⟨α, B, C, K⟩` | `⟨α, B, K, C⟩`, if decided before the release, or `Arc.ofHeath α B K C`: a statement change either way, not notation (open question 3) | one order for one arc |
| the circle ABCD | `ABCD` | unchanged, explained | Heath's name, and part of the interface |
| the straight line C; the angle D | `C₁ C₂`; `D₁ D D₂` | unchanged, explained | its ends; its vertex and a point on each arm |

A notation added from now on is `scoped` to `Elements`, so that a user meets it only after
`open Elements` or `open scoped Elements` (which brings in the notation and no names), or
inside the namespace, as the library's own files are; at a notation's birth that costs
nothing. Scoping one already released would break every user who never opened the
namespace, with no clean release of warnings before it (section 3.1), so a released symbol
either stays global or becomes a word: `∟` stays, and `∠`, `‖ ‖` and `△` become words. This brief is about the Lean alone: the notation of "the modern way"
passages is [#48]'s, in STYLE.

## 6. The cost, once, and the order of work

**What the pass changes.**

- *Proposition files:* 98 of the 99 change their text: 72 for `len`, five more (I.37, I.39,
  I.41, I.42 and I.43) for `area`, and 21 more for `ang`; II.2 writes none of the three.
  If open question 9 keeps `∠`, 77. Their
  records' `lean` stamps go stale, and each is re-read and re-stamped once (WORKFLOW,
  section 6). No fingerprint changes, nothing in the lock, and nothing in either lock
  hash (`tests/model/lock.sha256`, `model/lock.sha256`).
- *The rest of the Lean:* Book Zero, the helpers, whatever remains in `Staging/`, and
  `Audit/Overlaps.lean`. The foundations (`Elements/Foundations/`), whose definitions and
  docstrings write the bars too, are the coordinator's, and change in step 5 below.
- *The prose:* FORMALIZATION's vocabulary (section 2) and its table of representations; the
  book briefs ([Book I](book-I.md), [Book II](book-II.md), [Book III](0004-book-III.md)),
  which agree with the code; the README's two examples, in "Use it" and above it; STYLE's
  example of a Lean expression, `∠ A B C` ([STYLE.md](../STYLE.md), section 1, "Lean
  notes"); and the one review record whose text writes `‖` (III.15; the records of I.45 and II.14, which
  wrote the bars when this draft began, were rewritten with stage 2). The other briefs that
  write the old forms keep the notation they were written in: 0002, the decisions page,
  where its entry quotes Argon's examples (`‖A B‖`, `△ A B C`); 0003 as history, as
  FORMALIZATION, section 1, keeps the early briefs; and 0006 to 0009 as written, the frozen
  among them unchanged (0009 writes no bars, only `∠` and `△`). The reports under
  `docs/reports/` are kept as their day's record too: the crew's reports and the acceptance
  calibration, which between them write all three, and the prototype of mixed angles, which
  writes `∠`. A line in FORMALIZATION says so. The ∠ABC of III.22's "modern way" is
  mathematics, not Lean, and is [#48]'s (section 5).
- *Protected paths*, each named in a decisions entry and given a security review:
  `scripts/render.py` (its definitions maps write `∠ A B C` for Book I's Definitions 8 and
  9, and the bars, `∠ A E B` and `∠ A E B = ∠ C F D` for Book III's; `DEFINITION_LEAN`
  writes `‖E F‖ = ‖E G‖` and `‖E H‖ < ‖E K‖` for Definitions III.4 and III.5; and the page
  key is new), `scripts/scaffold_book.py` (the statement tables of Books I to
  III; Book IV's table, written in its ground step, takes the chosen notation from the
  start), `scripts/test_safe_push.py` (one planted law writes `‖A A‖`),
  `scripts/negative_tests.py` (it quotes I.16's statement, `∠ C B A < ∠ A C D ∧ …`, and
  stops unless it finds those words once) and `tests/model/MODEL.md` (its table names both
  forms). The formal model's hand-written docstrings follow: those of
  `model/Model/Signature.lean` ("written `‖A B‖` in the library", and the same for `∠` and
  `△`, [#73]), and of `model/Model/Laws/order.lean` and `model/Model/Laws/circles.lean`,
  which write the library's `‖A B‖ + ‖B C‖` and `‖A C‖ < ‖A B‖`. The model's other bars
  are Mathlib's norm, and stay.

**How a reviewer knows it is notation only.** A notation change leaves every recorded term
alone, so `facts.json` regenerated before and after the pass must agree entry by entry in
what it says of each entry: its statement, its citations, its axioms and inherited rules,
and the lock's vocabulary. The line numbers it records may move, where a longer word
reflows a line, and only they. Any other difference means the pass changed more than
notation. A slip in the substitution (`f len A B` for `f ‖A B‖`) is a type error, which
`lake build` finds. With both, re-reading 98 files against their records is reading a
mechanical substitution, and the reviewer still reads each file before stamping it. The
comparison is for the notation substitutions alone: a change taken under open question 3
changes recorded terms by design, so it lands before the pass, with its own approval,
review and `facts.json`, and the pass's "before" is taken after it.

Neither check sees a docstring or a `/- … -/` note, which Lean never elaborates, nor the
prose. So the pass begins from an inventory, taken by searching the Lean and the prose for
`‖`, `△` and `∠`, which lists each occurrence to be replaced and each kept on purpose, with
its reason: the deprecated forms of section 7 and their docstrings; the briefs and reports
kept as written, and the decisions page's quotation of Argon; the modern way's mathematics;
the formal model's Mathlib norms; and this brief. The reviewer checks the pass against the
inventory, and searches again after step 5 for anything it does not list.

**The order.**

1. If the owner and the coordinator take open question 3, the arc's field order or its
   statements written with `Arc.ofHeath`, as a revision of brief 0006, before the
   consolidation release: a statement change with its own approval and records, apart from
   the notation pass. And, in a pull request of its own before step 2,
   `scripts/negative_tests.py` taught to find I.16's statement however its angle is
   written: it quotes the statement's words, so step 2's `ang` would stop CI's `negative`
   job, and `safe_push` would keep the two changes apart (WORKFLOW, section 10).
2. After the consolidation release, the content pass outside the foundations: the
   substitution, the docstrings and the prose, while the old notation still stands, so that
   the build never warns.
3. The records re-read and re-stamped, once, with `facts.json` compared.
4. The other protected paths, in a branch of their own if `safe_push`'s keep_apart asks for
   one.
5. The coordinator's change to the foundations: their definitions and docstrings written
   with the words, and the bars, the △ and the ∠ made the deprecated forms of section 7.
   From then on `lake build`, `lake build Audit` and `lake build Staging` show no
   deprecation warning, which shows that no term Lean elaborates in those targets still
   uses the old forms. It shows nothing of the docstrings and notes, which the inventory
   above covers, and the foundations themselves still write the old forms, in section 7's
   deprecated declarations. The pages are regenerated in the same change, since their Lean
   blocks quote the source.
6. A release later, the deprecated forms removed, and the release notes say so.

Book IV's statements are scaffolded after step 4, in the new notation. Brief 0012, Book
IV's draft brief for [#97], not yet on main, already writes its lengths `len A B`, which Lean reads the same today; it
still writes the angle `∠ A B C`, which follows the answer to open question 9 when its
statements are scaffolded.

## 7. The old forms, for one release

FORMALIZATION, section 2, "Names, and how they change" ([#76]), promises that a released
name is never renamed or removed without a deprecated alias for one release, and gives the
alias's form, `@[deprecated NewName (since := "YYYY-MM-DD")]` on the old name. A notation is
not a name, and a name's alias does not reach it, so this brief proposes the same promise
for a notation, in this form:

```lean
/-- `‖A B‖`, the old way of writing `len A B`, kept for one release. -/
@[deprecated "write `len A B` for the length of the straight line AB"
  (since := "YYYY-MM-DD")]
abbrev BarsLength := Length

notation:max "‖" A:max B:max "‖" => (len A B : BarsLength)
```

and the same for `△ A B C`, as `(area A B C : TriangleArea)` with a deprecated
`abbrev TriangleArea := Area`, and for `∠ A B C`, as `(ang A B C : SymbolAngle)`. The old
notation expands to the word itself, ascribed a type whose name is deprecated. Lean warns
at every use, with the message; the term it records is `len A B`, unchanged, so every law
and theorem about `len` still rewrites it; and, once the bars are only this deprecated
form, goals print as `len A B` (test 7). The names `BarsLength`, `TriangleArea` and
`SymbolAngle` are placeholders. Two other ways were tried and set aside:

- `@[deprecated]` on the `notation` command itself: Lean 4.35 accepts it, and warns nowhere
  (test 5).
- The old notation expanding to a deprecated alias of the word (`abbrev lenOld := len`):
  Lean warns, but the user's terms then hold `lenOld`, and `rw [Tacit.len_symm]` no longer
  finds `len` in them (test 6), so a user's proofs would break in the very release meant to
  warn them.

A notation that logs its own warning would need `macro` or `elab`, which FORMALIZATION,
section 7, forbids under `Elements/`. For that one release the bars still meet Mathlib's
norm, and `∠` Mathlib's angle, for anyone who keeps writing them.

## 8. Open questions

Each is the owner's, or the coordinator's where marked; the recommendation is the brief's.

1. **Lengths.** `len A B` (recommended), or scoped bars with a key (the fallback)?
2. **Areas.** `area A B C` (recommended), or `△` kept and explained?
3. **The arc's field order.** Heath's (`circle`, `B`, `K`, `C`), decided before stage 3's
   move lands, and at the latest before the consolidation release, since afterwards the
   fields cannot move without silently changing users' arcs; or the fields kept, with a
   function in Heath's order (`Arc.ofHeath`) beside them? Added unused, the function
   changes nothing; each statement written with it changes its printed term, fingerprint
   and `lean` stamp, and brings the function's definition into the lock, with the two lock
   hashes renewed after review. Either way it is a statement change, approved apart from
   the notation pass (section 3.3). *For the coordinator and the owner*, as a revision of
   brief 0006; it touches the migration of stage 3 ([#25]), III.25's restatement (stage 4)
   and Book IV's bridges ([#97]).

   *26 October 2026: answered on 25 October. The fields keep the order they have in
   `Elements`, `circle`, `B`, `C`, `K`;
   [the decisions entry of that day](../decisions/2026-10-25-arc-field-order.md) records
   the owner's words and the choice, which adds no function in Heath's order.*
4. **The page key.** A line under each "In Lean" block, generated by `render.py` from the
   words the page's statements use, its wording taken from FORMALIZATION's vocabulary:
   wanted?
5. **Deprecating a notation.** One release, in the form of section 7, written into
   FORMALIZATION, section 2, "Names, and how they change", beside the names?
6. **New notation scoped** to `Elements` from now on?
7. **Timing.** As decided: after the consolidation release, and before Book IV's statements
   are scaffolded. One trade-off for the owner to see: stage 5 re-reads every record for the
   consolidation review ([#29]), and a pass made before it would share that reading; made
   after the release, as decided, the records are read once more, for their `lean` stamps
   alone. The brief keeps the owner's timing.
8. **Argon's further points.** Kept and explained, as section 4 says?
9. **The angle.** The word `ang A B C` (recommended, after the challenge), with `∠` kept for
   one release in the form of section 7 and then removed; or `∠` kept global, in 21 fewer
   proposition files, recorded as an accepted limitation for Mathlib users, who must then
   write `EuclideanGeometry.angle` in any file that imports the library?

## Appendix: what was tested

Lean 4.35.0, in scratch files outside the repository, run with `lake env lean` against the
library, or on their own. Tests 1 to 9 were first run against main at `4d02d50`, and tests
10 to 13 were added in review there; tests 10 to 12 load Mathlib v4.35.0 beside the
library. On 19 October tests 1, 3 to 9 and 13 were run again against main at `89c5da4`,
each with the result below, and test 7 once more with a stand-in word that has no notation
of its own, for how goals print once the bars are only the deprecated form. Tests 14 and 15
were added that day, the second when the challenge of this draft pointed to Lean's
`deprecated_arg`. Tests 2 and 10 to 12, which need Mathlib, were not run again: nothing
they rest on has changed, neither Lean's version nor our notations. Nothing here is
committed.

| Test | What it showed |
|---|---|
| 1. A stand-in for Mathlib's norm, `notation "‖" e "‖" => norm e`, beside the library | `‖A B‖` and a norm `‖n‖` both elaborate; our `‖A B C‖ = ‖A B‖` reports "Function expected at A", then a mismatch with the norm's type |
| 2. The same, with a Mathlib user's slip, `‖f n‖` for a two-argument `f` | "overloaded, errors": the norm's missing instance, and a mismatch naming our `len` and `Point` |
| 3. A `scoped notation` in a namespace `T` | active in a file inside `namespace T.BookI`; inactive after `import` alone and after `open T (len Point)`; active after `open T` |
| 4. A plain notation `"\|" A:max B:max "\|"` | Lean's own `fun \| 0 => 1 \| _ => 2` no longer parses |
| 5. `@[deprecated]` on a `notation` command | accepted; no warning at any use |
| 6. An old notation expanding to a deprecated alias of `len` | a warning at each use; `rw [Tacit.len_symm]` finds no `len` |
| 7. An old notation expanding to `len A B` or `area A B C`, ascribed a deprecated `abbrev` (section 7's form) | a warning at each use, with the message; `rw` with `Tacit.len_symm` and `Tacit.area_rotate` works; for a word with no other notation, `#check` prints the word (`len2 A B`, for a stand-in), while beside today's bars it prints the bars |
| 8. A theorem binding a circle `ABCD`, called as `T (ABCD := c)` and as `T (α := c)` | the first elaborates; the second fails, "Invalid argument name `α`" |
| 9. The identifiers `⊙ABCD`, `○ABCD` and `ωABCD` | the first two are refused; the Greek letter is accepted |
| 10. Mathlib's norm beside the library, then the whole of `import Mathlib` | tests 1 and 2 give the same messages; with nothing opened, `len`, `area`, `ang` and `Triangle` are unknown identifiers, and `open Elements` gives ours |
| 11. Mathlib's scoped `∠`, with `open EuclideanGeometry`, beside the library | Mathlib's `∠ p q r`, on points of `EuclideanSpace ℝ (Fin 2)`, is read as ours: "Application type mismatch", in `Elements.ang p`; `∠ p q` gives "unexpected token ')'"; ours on `Point` still works |
| 12. A stand-in angle in Mathlib's shape, `notation "∠" => angX`, beside Mathlib's with `open EuclideanGeometry` | Mathlib's `∠ p q r` works; the stand-in's `∠ A B C` is an "Ambiguous term" |
| 13. One symbol twice: a global notation ascribed a deprecated `abbrev` type (section 7's form), and a `scoped` one | outside the namespace, a warning; after `open`, an "Ambiguous term" |
| 14. The words as they read today, `len B C < len B A + len A C` from I.20, with `open Elements` | elaborates; Lean records the term the bars give |
| 15. A theorem whose circle `ABCD` is renamed `α`, marked `@[deprecated_arg ABCD α]` | `T (α := c)` elaborates; `T (ABCD := c)` elaborates, with "parameter `ABCD` of `T` has been deprecated, use `α` instead" |

The counts in this brief were taken again from main at `89c5da4`: the uses of each symbol
under `Elements/`, `Staging/` and `Audit/`, and in the 99 proposition files; the statements
that reach each word, from `facts.json` (121 entries, porisms and companions among them);
the lock's entries (87 axioms, 91 words); and the named arguments (`(X := …)`) under
`Elements/`.

## Appendix: the challenge of 19 October

Astra read the draft at `72610fb` against the code, recounted the appendix's figures (all
confirmed but one), ran its own Lean tests through standard input, and returned it for
correction. Each finding, and what was done:

| Finding | Severity | Done |
|---|---|---|
| A renamed binder can keep its old name for callers, with a warning, by Lean 4.35's `@[deprecated_arg]`; "no alias possible" was false | material | rule 4, the table of section 2, sections 3.4 and 3.5 corrected; test 15 added |
| Reordering the arc's fields changes two lock entries, `Arc.C` and `Arc.K`, not the one for `Arc`; positional `Arc.mk` and patterns change too, not only `⟨…⟩` | material | sections 2 and 3.3 corrected |
| The arc's order should be decided before stage 3's move lands, and a constructor in Heath's order is a third way, which leaves the fields where they are | material | section 3.3's options and question 3; a later review set apart the cost of statements written with it (sections 2, 3.3, 5 and 6) |
| Keeping `∠` global leaves the clash with Mathlib's angle for every Mathlib user who imports the library | material | the recommendation is now `ang A B C`, with `∠` deprecated for one release (sections 3.2, 5, 6, 7 and question 9) |
| The pass's checks should cover `Audit/` and `Staging/`, the pages should be regenerated, and the comparison of `facts.json` should allow moved line numbers | material | section 6, "How a reviewer knows" and step 5 |
| `scaffold_book.py` holds Books I to III's tables only; Book IV's is yet to be written | editorial | section 6 |
| `open scoped Elements` brings a scoped notation without the names | editorial | section 5 |
| A quoted identifier, `«⊙ABCD»`, can hold the circle's mark | editorial | section 3.4 |
| The named arguments are 199, in 42 files; 141, in 23, name a point or a circle | (count) | rule 4 |

[issue #69]: https://github.com/jackChallis/stoicheia/issues/69
[#25]: https://github.com/jackChallis/stoicheia/issues/25
[#29]: https://github.com/jackChallis/stoicheia/issues/29
[#38]: https://github.com/jackChallis/stoicheia/issues/38
[#48]: https://github.com/jackChallis/stoicheia/issues/48
[#67]: https://github.com/jackChallis/stoicheia/issues/67
[#71]: https://github.com/jackChallis/stoicheia/issues/71
[#73]: https://github.com/jackChallis/stoicheia/issues/73
[#76]: https://github.com/jackChallis/stoicheia/issues/76
[#89]: https://github.com/jackChallis/stoicheia/pull/89
[#97]: https://github.com/jackChallis/stoicheia/issues/97
[#240]: https://github.com/jackChallis/stoicheia/pull/240
