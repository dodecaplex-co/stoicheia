# Book II: rectangles, squares and gnomons

*The design for Book II (15 October 2026): how Lean says "the rectangle contained by
AB, BC", "the square on AB" and "the gnomon", where the facts about them live, and how
Book II's propositions are stated. Where it differs from the code, the code is right.*

## What Book II needs

Book I compares figures that are drawn: "the parallelogram BL is double of the triangle
ABD", "the square BDEC is equal to the squares GB, HC". In Lean those are `quadArea`
and `△` of named points. Book II speaks of rectangles and squares that need not be drawn
at all:

> I say that the rectangle contained by AB, BC together with the rectangle contained by
> BA, AC is equal to the square on AB. (II.2)

and in its proofs moves between the drawn figure and the named magnitude:

> Now AE is the square on AB; AF is the rectangle contained by BA, AC, for it is
> contained by DA, AC, and AD is equal to AB. (II.2)

Definition 1 of Book II is the license for that move: "Any rectangular parallelogram is
said to be contained by the two straight lines containing the right angle." Euclid never
asks whether two rectangles contained by equal straight lines are equal; Lean has to.

## The words

All three are definitions, in `Elements/Foundations/DefinitionsII.lean`. None is an
assumption.

| Euclid | Lean | What it is |
|---|---|---|
| "a rectangular parallelogram" `ABCD` (Def. II.1) | `Rectangle A B C D` | `Parallelogram A B C D` with all four angles right, in the order `Square` (Def. I.22) gives them |
| "the rectangle contained by AB, CD" | `rect A B C D` | the area of any rectangle whose sides about a right angle are equal to `AB` and `CD` |
| "the square on AB" | `sq A B` | `rect A B A B` |
| "the gnomon NOP" (Def. II.2) | the sum of its three parallelograms | one parallelogram about the diameter with the two complements |

**How `rect` is defined.** `Contain a b x` says that some rectangle `PQRS` has `PQ` equal
to `a`, `PS` equal to `b`, and area `x` (or that `a` or `b` is nothing, and so is `x`).
`rect A B C D` is `Classical.epsilon (Contain ‖A B‖ ‖C D‖)`: Lean picks one such area.
Three consequences follow at once, with no proposition:

- `rect A B C D` depends only on the lengths of `AB` and `CD` (`rect_congr`), so "since
  AC is equal to CE, the square on AC is also equal to the square on CE" (II.9) is
  `sq_congr`;
- `rect A B C D = rect C D A B` (`rect_comm`), because a rectangle read the other way
  round, `PSRQ`, has its two sides in the other order;
- a rectangle with a side that is nothing is nothing (`rect_self_left`), as a "triangle"
  with a repeated corner is (System E, Metric 6).

**Why the choice makes no difference.** `Rectangle.contained` proves that every rectangle
`PQRS` is the rectangle contained by `PQ`, `PS`: the diameter `QS` cuts off a triangle
right-angled at `P` that is half of it [I. 34], and two such triangles with equal sides
are equal [I. 4]. So whichever rectangle `rect` chose, the one drawn is equal to it. This
is Definition II.1 made into a theorem, and every Book II proof that names a drawn
rectangle uses it, so I.4 and I.34 appear in their certificates. That is honest: those
are the propositions that make the naming sound.

**Squares.** "The square on AB" is the rectangle contained by `AB`, `AB`. A square that
I.46 describes is a parallelogram [I. 28] and so a rectangle, and `Square.described` says
it is the square on its side. Book I's statements about drawn squares (I.46, I.47, I.48)
stay as they are; `BookI.Prop47.sq` restates I.47 for `sq`, as Book II cites it a dozen
times: "the square on EA is equal to the squares on AC, CE, for the angle ACE is right".

**The gnomon.** Definition II.2 names three parallelograms taken together, and Euclid
only ever adds the gnomon to things or compares it with them. So Lean has no word for
it: "the gnomon NOP" is the sum of its three `quadArea`s, written where it is used. The
fact Euclid needs, that the gnomon and the remaining parallelogram make up the whole
(II.5–II.8), is `Parallelogram.about_diameter`.

## Where the facts live

The rule is Book I's: a fact that needs no proposition goes in Book Zero; one that cites
a proposition goes beside the propositions.

**Book Zero, `Elements/Figure/Rectangles.lean`** (cites no proposition, declares no
axiom, never uses Postulate 5): `exists_off_line` (every Book II figure starts on one
straight line, and the first square or perpendicular needs a side to stand on; it rests
on Postulates 1 and 3, Definition 15 and System E's rules, as I.1 does);
`rect_congr`, `sq_congr`, `sq_symm`, `rect_comm`, `rect_self_left`, `rect_self_right`,
`sq_self`; `Rectangle.rotate`, `Rectangle.reverse`, `Square.reverse`,
`Square.rectangle`, `Square.len_eq`. Book II also uses `Parallel.between` (parallels
keep order) in `Elements/Figure/Parallelograms.lean`: the closing of Book I removed it
as unused, and Book II restores it for `Parallelogram.figure`.

**Book II's ground, `Elements/BookII/Rectangles.lean`**, which may cite Book I. Each
lemma's docstring ends with what it cites; the certificate's walk confirms them.

| Lemma | What Euclid takes for granted | Adds |
|---|---|---|
| `Rectangle.of_right` | a parallelogram with one right angle has all four right | I.29 |
| `Rectangle.congr` | rectangles contained by equal straight lines are equal | I.4, I.34 |
| `Rectangle.contained`, `Rectangle.eq_rect` | a rectangle drawn is the rectangle contained by its sides: "BH is the rectangle A, BC, for it is contained by GB, BC, and BG is equal to A" | I.4, I.34 |
| `Square.eq_sq` | a square (and parallelogram) is the square on its side | I.4, I.34 |
| `Square.described` | the square I.46 describes on `AB` is a parallelogram, and the square on `AB` | I.4, I.28, I.34 |
| `Square.about_diameter` | in square areas the parallelograms about the diameter are squares (the Greek text's porism to II.4, which Heath calls interpolated) | I.5, I.6, I.29, I.34 |
| `Parallelogram.complements` | the complements of I.43 are parallelograms | I.30 |
| `Parallelogram.about_diameter` | the two parallelograms about the diameter and the two complements are the whole | I.30 |
| `Parallelogram.figure` | "let the figure be drawn": the diameter, and the parallels through a point of a side and through the point where it cuts the diameter, with every point where Euclid's figure puts it | I.30, I.31 |
| `BookI.Prop47.sq` | I.47 said of `sq` | I.4, I.28, I.34, I.46, I.47 |

## How the statements say Euclid's phrases

| Euclid | Lean |
|---|---|
| "the rectangle contained by AB, BC" | `rect A B B C` |
| "the square on AB" | `sq A B` |
| "twice the rectangle", "four times the rectangle" | `r + r`, `r + r + r + r` |
| "are double of the squares on AC, CD" | `x + x`, with `x = sq A C + sq C D` |
| "greater than ... by", "less than ... by" | an equation: the less with the excess is the greater |
| "the straight line A" (II.1) | two points, `A₁ A₂` (STYLE §3) |
| "the square described on AB, BC as on one straight line" (II.8) | `sq A D` for every `D` with `B` between `A` and `D` and `BD` equal to `CB` |
| "the rectilineal figure A" (II.14) | the figure I.45 takes, cut by a diameter into two triangles: `△ A₁ A₂ A₄ + △ A₄ A₂ A₃` |
| "let BD be drawn perpendicular to CA produced" (II.12), "AD ... perpendicular to BC" (II.13) | I.12's form: `D` on the straight line, and every angle there right; where `D` falls is then proved |

Hypotheses come from the setting-out and conclusions from "I say that", as in Book I,
with four choices worth naming:

- **II.1** cuts `BC` at the two points of its setting-out, "at the points D, E", as
  I.45 takes the two triangles of its figure. One point of section is not an instance
  of it (see "Later").
- **II.5 and II.9** take `D` anywhere between `A` and `B` except at `C`, as the
  enunciation does ("cut into equal and unequal segments"): the setting-out's "into
  unequal segments at D" names no side. Euclid's figure has `D` between `C` and `B`,
  and the other side is the same with `A` and `B` exchanged. The general form is for
  later citers: III.35 meets the point of section on either side of the middle point.
  II.14 does not need it. After "Let BE be greater", `E` lies between `G` and `F`,
  II.5's own figure, and Heath suggests that is why Euclid wrote the words (vol. 1,
  p. 410). `D ≠ C` is Euclid's "unequal". At `C` both statements hold in a line
  (`rect_congr`, `sq_self`), so a citer whose point of section may be the middle point
  takes that case first.
- **II.12 and II.13** take the perpendicular as I.12 gives it, so that a later book can
  feed I.12's foot straight in. "CA produced" (II.12) and "cut off within" (II.13) are
  then proved from the obtuse angle, and from the two acute angles at `B` and `C`
  (I.13, I.17), and every hypothesis is used. Heath notes that II.13's enunciation
  speaks of acute-angled triangles; the angle at `A` plays no part, so only `B` and `C`
  are asked to be acute.
- **II.14** squares exactly the figures I.45 can turn into a parallelogram, since its
  proof hands the figure to I.45. Euclid's own proof of I.45 takes a four-sided figure,
  two triangles, though Heath observes that any rectilineal area "can of course be
  resolved into triangles" (vol. 1, p. 347). A figure of more than two triangles needs
  I.45 extended first.

## Book I's rules, in Book II

- **Postulate 5.** Every proposition of Book II comes after I.29, so any may rest on it;
  II.10 cites it by name. `check_fidelity.py` keeps the I.29 boundary for Book I and
  allows Book II from II.1; the certificate says so in Book II's section.
- **Superposition** stays with I.4 and I.8.
- **Citing Book I.** A Book II proof cites `BookI.Prop46` under "[I. 46]". The scaffold
  imports Book Zero, `Elements.BookII.Rectangles`, and every proposition Euclid cites,
  from either book.
- **The scripts.** `heath.BOOKS` lists the books and their sizes; `render.py` writes
  `book/II/`, a Book II section in `CERTIFICATE.md` and in `GRAPH.md` (with the Book I
  propositions it cites drawn in white), and links `[I.47](../I/47.md)` from Book II's
  pages. Book I's pages come out byte for byte as before.
- **Brackets and numbers across books.** II.10's "[I. Post. 5]" stays as Heath prints
  it, and the scripts read it as Post. 5: the postulates and common notions are Book I's
  alone. Definitions are numbered book by book, so a Book II page and Book II's rows of
  the certificate write Book I's Definition 15 as I.15, beside Book II's own
  Definitions 1 and 2.
- **Checks across books.** `check_fidelity.py` fails if `facts.json` does not cover
  exactly the books in `heath.BOOKS` (`Certificate/Facts.lean` keeps its own list), or
  if any proposition cites one that does not come before it: nothing after II.N, and
  nothing of Book II in Book I.

## Later

- **II.1 for one point of section.** II.1 is stated as its setting-out has it: `BC`
  cut at two points `D`, `E`, both strictly within it. The enunciation's "any number of
  segments whatever" is wider, and Heath calls the extension easy (vol. 1, p. 376). The
  simplest case, the rectangle A, BC equal to the rectangles A, BD and A, DC, is not an
  instance, and getting it from the three-piece form needs a cancellation that is not
  Euclid's. If a later book cites II.1 with one point of section, that form is proved
  then, as a corollary after II.1 from the same figure (one parallel `DK`).
- `rect` has no existence or positivity lemma yet (that a rectangle contained by any two
  straight lines can be drawn, and is something). Book II never needs one, since it
  always draws its rectangles; Book VI will.
- A gap catalogue for Book II, as `docs/reports/gaps-book-I.md` is for Book I. Book II's
  index page links it once it exists.
- I.45 for any number of triangles, if a later book squares a figure of more sides;
  II.14's proof would then cite it in place of I.45, and its statement could take any
  number of triangles.
