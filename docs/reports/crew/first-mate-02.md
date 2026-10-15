# First mate: Book Zero, and the statements of I.9–I.24 (15 October 2026)

Getting ready for the second voyage, which will send sailors to I.9–I.16 and then
I.17–I.24. Two jobs: gather the small facts that the first voyage's sailors each
proved for themselves into Book Zero, so that the next sailors can cite them; and
read the statements of I.9–I.24 once more against Heath, and against every later
proposition that will lean on them.

## Book Zero

`Elements/Figure/Basics.lean` now just gathers seven short files, each with a
note on what Euclid takes for granted there. What it used to hold has moved,
unchanged, into the first four. Every proposition still imports
`Elements.Figure.Basics`, so every proposition sees all of Book Zero.

| File | What Euclid takes for granted there |
|---|---|
| `Lengths.lean` | something added makes a thing greater; the part is less than the whole |
| `Lines.lean` | order on a straight line; a finite straight line can be produced |
| `Circles.lean` | points on, inside and outside a circle |
| `Triangles.lean` | a triangle's corners, named in any order; the straight lines through them |
| `Rays.lean` | the half of a straight line that starts at a point; one point at each distance |
| `Sides.lean` | "on the same side of AB", "on the other side of AB" |
| `Angles.lean` | an angle depends only on its rays; adding angles; a straight line within an angle crosses its base; one ray for one angle |

### What moved

| Lemma in Book Zero | File | Was |
|---|---|---|
| `OnRay.eq_of_len_eq` | Rays | `Prop4.coincide`, `Prop8.coincide` |
| `onRay_of_angle_eq` | Angles | `Prop4.on_ray` (now says "same side of DE" as `SameSideOf`) |
| `between_inner` | Lines | `Prop5.between_inner` |
| `OnRay.between_of_len_lt` | Rays | `Prop5.beyond`, for any two points of a ray |
| `Triangle.of_line` | Triangles | `Prop5.triangle` |
| `angle_eq_of_onRay`, `angle_onRay_left`, `angle_onRay_right` | Angles | `Prop5.angle_along`, `Prop6.angle` |
| `angle_add_of_between` | Angles | `Prop5.angle_add` (takes the triangle, not three named lines) |
| `Triangle.bca`, `.cab`, `.acb`, `.bac`, `.cba` | Triangles | `Prop8.triangle`, `Prop6.rotate`, `Prop6.swap` |
| `SameSideOf.swap`, `SameSideOf.symm` | Sides | `Prop7.sameSideOf_swap`, `Prop7.sameSideOf_symm` |
| `SameSideOf.of_line` | Sides | `Prop8.sameSide` |
| `produce` | Lines | `Prop7.produce` |

I.4–I.8 now cite these, and their own copies are gone; I.4 has no helper lemmas
left. Their statements and every `--` line are unchanged, and the hoisting alone
left every certificate exactly as it was.

### New beside them

A few small companions, so that the lemmas above are easy to reach:
`len_lt_of_between`, `collinear_of_between`, `Triangle.off_line` (the corner `C` of
the triangle `ABC` is off any straight line through `A` and `B`, a step the first
voyage wrote out by hand again and again), `OnRay.self`, `OnRay.of_between`,
`OnRay.of_beyond`, `OnRay.symm`, `OnRay.onLine`, `OnRay.not_between`,
`SameSideOf.sameSide`, `SameSideOf.trans`, `SameSideOf.triangle`,
`OppositeSidesOf.of_line`, `.oppositeSides`, `.swap`, `.symm` and `.triangle`, and
`exists_oppositeSidesOf` ("let a point be taken at random on the other side of
the straight line AB", I.12).

And one that the statement review turned up: `crossbar`. If `D` lies within the
angle `BAC`, the ray from `A` through `D` meets `BC` between `B` and `C`. Euclid
uses it without a word in I.10 (the bisector `CD` meets `AB` at `D`) and in I.21
(`BD` "drawn through" to `AC`). It follows from System E's triple incidence and
Pasch rules.

### What stayed home

Lemmas that belong to one figure stay in their proposition's file:
`Prop1.figure`, `Prop5.chance_point`, `Prop6.figure`, `Prop6.less`, and
`Prop7.triangle`, `Prop7.cross`, `Prop7.cases`, `Prop7.figure`, `Prop7.within`.

### Names to update elsewhere

The gap catalogue now uses the new names. The mishnah, which is outside this
job, still names some of the old ones:

- `mishnah/I/04.md`: `Prop4.coincide` → `OnRay.eq_of_len_eq`; `Prop4.on_ray` → `onRay_of_angle_eq`.
- `mishnah/I/05.md`: `Prop5.beyond` → `OnRay.between_of_len_lt`; `Prop5.angle_along` → `angle_onRay_left`; `Prop5.angle_add` → `angle_add_of_between`; `Prop5.between_inner` → `between_inner`.
- `mishnah/I/06.md`: `Prop6.angle` → `angle_onRay_left`.
- `mishnah/I/08.md`: `Prop8.coincide` → `OnRay.eq_of_len_eq`; `Prop8.sameSide` → `SameSideOf.of_line`.

## The statements of I.9–I.24

For each proposition: does the Lean say what Euclid's enunciation and his "I say
that" say, in Heath's letters? Is it true, with nothing false in a degenerate
case? And can every later proposition that cites it (Heath's bracketed
references) actually apply it? For the three that changed, and for the uses that
looked delicate, I also wrote the later steps out in Lean against the new
statements, in a scratch file that is not committed: I.23 in full from I.22, I.20
and I.8; I.10 in full from I.1, I.9 and I.4 (with `crossbar`); and the first
steps of I.9, I.11, I.14 and I.24.

| Prop | Verdict |
|---|---|
| I.9 | **Changed.** Now also says that `AF` falls within the angle `BAC` (`F` on `C`'s side of `AB` and on `B`'s side of `AC`). The old statement, two equations between angles, did not say where `F` is; nothing in it ruled out `F` being `A` itself, so I.10 could not use it to make the bisector meet `AB`. "Bisected by the straight line AF" means both things. |
| I.10 | OK. Fits I.12, I.16 and I.42. |
| I.11 | OK. Fits I.13; and it puts the perpendicular on the side of a given point `Q`, which I.46 and I.48 need. |
| I.12 | OK. Not cited again in Book I; Book II will use it. |
| I.13 | OK. Fits I.14, I.15, I.17, I.28, I.29, I.32 (with `angle_symm` to turn an angle round). |
| I.14 | OK. Fits I.45 and I.47; `OppositeSidesOf.swap` and `.symm` turn their hypotheses round, and `onRay_of_angle_eq` is the heart of its own proof. |
| I.15 | OK. Fits I.16 (twice), I.28, I.29, I.44. |
| I.16 | OK. Fits I.17, I.18, I.21, I.26, I.27. |
| I.17 | OK. |
| I.18 | OK. Fits I.19. |
| I.19 | OK. Fits I.20 and I.24. |
| I.20 | OK. Fits I.21, and supplies the condition I.22 asks for when I.23 uses it. |
| I.21 | OK. |
| I.22 | **Changed.** The triangle `KFG` now has its corner `F` at a given point, its side `FG` along a given ray from `F` through `E`, and `K` on the side of a given point `P`. Before, `F` lay wherever `DF` equal to A put it along a ray from a given `D`, so I.23 would first have had to set out a `D` behind `A`, a step Euclid never takes. Now I.23 goes through line by line as Euclid writes it. In I.22's own proof, Euclid's `DE` is set out through `F`, with `D` behind `F`. |
| I.23 | OK. Stated more strongly than Euclid, and rightly: the angle is built on the ray `AB` and on the side of a given point, which is what I.24 (the side of `F`), I.31 (the side away from `C`) and I.42 (the side of `A`) need. |
| I.24 | OK. Fits I.25. |

### Upstream: I.1

**Changed.** I.1 now takes a point `P` and puts the triangle on `P`'s side of `AB`
when `P` is off it:
`∃ C, Equilateral A B C ∧ (¬ Collinear A B P → SameSideOf C P A B)`.
When no side matters, give a point of `AB` (I.2 gives `A`).

Why: in I.9 the equilateral triangle on `DE` must fall on the side away from `A`.
On `A`'s side its corner can land on `A` itself (when `ADE` is equilateral) or
behind `A`, outside the angle (when the angle `BAC` is wider than an angle of an
equilateral triangle), and then `AF` does not bisect the angle at all. I.11 needs
the triangle on `Q`'s side too. The two circles of I.1 cut one another on both
sides of `AB`, so the stronger statement is Euclid's own construction (System E,
Intersections 8). The proof of I.2 changed by one line and a remark; no `--` line changed.

What it costs: a certificate counts everything a theorem rests on, so I.1 now
lists Postulate 1 (which Euclid cites there), Intersections 8 and the uniqueness
of the line through two points, and its Lean foundations gain `propext` and
`Quot.sound` (from the case split). I.2, I.3 and I.5–I.8, which rest on I.1, now
list Intersections 8 as well. If you'd rather keep I.1 as it was, the other way is
for I.9 to build its triangle straight from the two circles (Euclid gives no
bracket there) and for I.11 to produce `FC` through `C` when `F` falls on the
wrong side (Diagram-angle 3 keeps the angles right). The stronger I.1 seemed
cleaner.

`scripts/scaffold_book.py` has the new statements of I.1, I.9 and I.22, and all 48
of its statements match the Lean files.

## For the sailors

- **I.10 and I.21:** `crossbar` is in Book Zero.
- **I.5 wants its equal sides produced.** When only the base angles are needed,
  `produce` gives the points (as I.7 does).
- **"Let CE be made equal to CD [I. 3]" on a produced straight line** (I.11, I.16,
  I.20, I.22, I.24). I.3 cuts off from a longer straight line, and Postulate 2
  gives no length, so a long enough line has to be found first: a circle about the
  point (Post. 3) and `line_circle_beyond` is one way. A shared helper can't live in
  Book Zero, since it would cite I.2 or I.3.
- **I.23:** feed I.22 the lengths as `A₁A₂ := CE`, `B₁B₂ := CD`, `C₁C₂ := DE`; its
  three conditions come from I.20 on the triangle `DCE`, so `Prop23.lean` now
  imports I.20. Its module note says so.
- **Looking further ahead:** I.44 says of the parallelogram from I.42 "let it be
  placed so that BE is in a straight line with AB", but I.42 as stated builds its
  parallelogram on the given triangle's own base. Worth a look before the I.42–I.45
  voyage.

## Housekeeping

- `lake build`, `lake env lean Certificate/Facts.lean` and
  `python3 scripts/check_fidelity.py` all pass. The generated files (`facts.json`,
  `book/`, `CERTIFICATE.md`, `GRAPH.md`) are left for the captain to regenerate.
- The README's excerpt of I.1 is now slightly abridged: the proof chooses a side
  between the two lines it quotes.
