# Reviewed examples

Four pages to learn from, each chosen for a reason and tied to the commit at which it was
read. They show the standards of [STYLE.md](STYLE.md) and
[FORMALIZATION.md](FORMALIZATION.md) at work. They guide judgment; they are not templates.
Copying their leads, their rhythm or their sentences onto another page would make the drift
the voice passes were run to remove. Take from them how a decision was made, and make your
own for your proposition.

Each was read again at commit `6b3c462`, after the voice and records passes of brief 0005.
I.1, I.7 and II.4 have revised commentary and records at the `full` stage; III.31 now uses
III.2's helpers for its circle facts, with its record read again. When one of them changes,
it is read again and its commit here brought up to date, or it is replaced.

## A short construction: I.1

[Page](../book/I/01.md) · [Lean](../Elements/BookI/Prop01.lean) ·
[mishnah](../mishnah/I/01.md) · [figure](../figures/I/01.svg)

**Why this one.** The first proposition, a short construction whose circles, helper and
side choice can be read together.

- **The statement says a little more than Euclid's, and says so.** The triangle may be put
  on the side of a given point P when P is off AB, because I.9 and I.11 need a particular
  side. The file's header gives the reason, and the decision is recorded
  ([0002-decisions.md](briefs/0002-decisions.md), 15 October).
- **A helper supplies one named step.** `Prop1.figure` proves that C is off AB, so that ABC
  is a triangle: a fact Euclid reads off the figure. Its docstring says so; it does not hide
  the construction, which stays in the main proof under Heath's sentences.
- **The gap is a named rule, credited.** The circles' meeting is System E's Intersection 5
  (`circles_meet`), and the remark above it says why the circles cross and why the side can
  be chosen. The remark also says plainly that the straight lines CA, CB are drawn for the
  eye: our proof uses only the point C.
- **The mishnah does all four things in four paragraphs:** the move (must the circles
  meet?), the history (Zeno's worries, reported by Heath, with the chain of report clear),
  the formal decision (C off AB, and the side), and a modern way that earns its place: the
  √3 of the complex point is why the rational plane fails I.1, with Robin Hartshorne's book
  credited warmly.

**Do not copy.** "Lean wants it said" is allowed on I.1, I.5 and I.22 alone (STYLE,
section 3). The first three leads are questions; the last is **The modern way.** The
questions suit the first page; a run of pages that all open on questions is a rhythm, not
a voice.

## A hard diagram argument: I.7

[Page](../book/I/07.md) · [Lean](../Elements/BookI/Prop07.lean) ·
[mishnah](../mishnah/I/07.md) · [figure](../figures/I/07.svg)

**Why this one.** Euclid draws one figure and leaves the rest to the reader; Lean has no
reader to leave them to. I.7 shows how to make every case explicit without losing Euclid's
argument.

- **Each helper settles one thing the figure shows.** `Prop7.triangle` (ACD is a triangle),
  `Prop7.cross` (when BC separates D from A, AD meets BC within CB or beyond C),
  `Prop7.cases` (where D can fall), `Prop7.figure` (in Euclid's figure, CB falls within the
  angle ACD and DA within the angle CDB), and `Prop7.within` (the case Euclid leaves out,
  answered as Proclus answers it, by the second part of I.5). Each docstring says which step
  it supplies.
- **The cases are labelled where they are taken.** A remark in the main proof names all
  four figures, exchanges C and D for the one that is Euclid's figure lettered the other
  way, sends the Proclus case to its helper, and then follows Euclid's reductio sentence by
  sentence.
- **A missing step is told in Heath's words.** Where Heath says "It would be natural to
  insert here the step …", the remark quotes him and says what the figure supplies.
- **The mishnah** keeps the formal story to its fourth paragraph (**Four places for D.**):
  it names `Prop7.cases`, explains why there is no fifth place, and says why Euclid could
  leave the other figures to his reader. The first three paragraphs have no bold leads;
  they give Heath's reading of the enunciation, Charles Dodgson's hinged rods and Proclus's
  answer to the missing case. The fifth, the modern way, shows the two mirror-image
  answers, one on each side, which is the proposition's point.

III.8 is a second example of the kind: its helpers are De Morgan's two assumptions, named as
his, and where Euclid's "which was proved impossible" does not cover a third straight line
the Lean compares the angles at the centre instead, and the mishnah says so.

## An area proof: II.4

[Page](../book/II/04.md) · [Lean](../Elements/BookII/Prop04.lean) ·
[mishnah](../mishnah/II/04.md) · [figure](../figures/II/04.svg)

**Why this one.** Book II speaks of rectangles and squares that need not be drawn, and
proves its equalities with figures that are. II.4 shows the representation (`rect`, `sq`)
meeting the drawn figure, and a shared step told on its home page.

- **The statement is Euclid's, in areas:** the square on AB equals the squares on AC, CB
  with twice the rectangle AC, CB. Twice the rectangle is the area added to itself; the
  numerical and vector comparisons belong to the modern way.
- **The figure is drawn as Euclid draws it,** by shared steps with recognisable names: the
  square by I.46 and `Square.described`, its side chosen by `exists_off_line`, and the
  parallels and the point G by `Parallelogram.figure`. Each drawn piece is then named as a
  rectangle or square of Euclid's words by the bridge lemmas of Book II's ground.
- **Euclid's proof is followed in full,** down to every right angle of CGKB, and the mishnah
  names the subtraction of a right angle as Common Notion 3. It also identifies I.43 behind
  the equality of the complements, where Heath gives no reference.
- **"For the same reason"** is Euclid's own, and the general fact behind it, the porism
  Heath calls interpolated, is proved once as `Square.about_diameter` and used again in
  II.5–II.8. II.4's second mishnah paragraph tells it alongside the proof for CGKB; the
  later mishnahs leave that history here. Its first paragraph links Book II's introduction
  for the account of how the areas correspond to the pieces drawn.

## A page completed by companions: III.31

[Page](../book/III/31.md) · [Lean](../Elements/BookIII/Prop31.lean) ·
[mishnah](../mishnah/III/31.md) · [figure](../figures/III/31.svg)

Read again against the Lean, record and page at commit `560da15a2`, on 25 October 2026.

**Why this one.** The main theorem and its companions cover the whole enunciation. III.31
shows how to account for clauses proved after the main theorem, state the limits of a
representation, and extend Euclid's worked case where a later citer needs it.

- **The completion.** The angles "of the greater segment" and "of the less segment" are
  contained by a straight line and a circumference. The main theorem proves the
  rectilineal claims; `Prop31.greater` and `Prop31.less`, after it, prove the mixed-angle
  comparisons for every straight line in the circle not through the centre, at either
  end. The companions use the right angle BAC, and the less-segment proof obtains the
  adjacent right angle CAF. The note beside Heath's closing sentences points to the
  companions and says that the final `exact` returns only the main theorem's claims.
- **The widening.** Euclid proves the angle in the greater segment less than a right angle
  at B, but IV.5 needs it at any point. The statement says it of every point of the segment,
  the Lean reaches the other points through III.22, and the mishnah's fourth paragraph says
  why.
- **The representation still has limits.** The tag `mixed-angles-local` names a comparison
  of regions near the vertex: near A the right angle BAC lies within the greater segment
  with room to spare, and the less segment lies within the right angle CAF. The companions
  also prove that the named points give well-formed mixed angles. No addition, ratio or
  motion of mixed angles is claimed. The page's Representation row and the mishnah explain
  this meaning beside the claim of full coverage.
- **The record, and what the page makes of it.** The review record,
  [review/III/31.toml](../review/III/31.toml), declares the statement's scope `full`,
  lists both companions and keeps the route `euclid`, its note giving the further step
  through III.22. Of its nine passages, four are `helper` passages, naming
  `Prop2.triangle`, `Definition15` twice and `angle_add_of_between`; one, a `case`,
  finds by III.2 the point of the less segment that the further case needs; and four are
  `carried` by the companions, two by `Prop31.greater` and two by `Prop31.less`, since a
  step proved as a companion is declared as carried. The page says the whole enunciation
  is proved, names both companions in its table, explains where they carry the closing
  sentences, and gives each its certificate.

III.24 uses its companions another way: its main theorem carries the whole enunciation, and
one companion keeps an alternative proof. The main theorem keeps Euclid's application of
one segment to the other (`placement`) and argues the coincidence of the circumferences
point by point, in place of his reductio, so its route is `modified`. The proof by the
radii is kept as the companion `Prop24.equalCircles`, which proves less: the circles equal,
and the circumferences equal in our measure. The [page](../book/III/24.md) lists it after the
main theorem, its docstring naming it the alternative, and its Argument row and the
[record](../review/III/24.toml)'s route note say so.

**Do not copy.** Full coverage does not make the representation's limits disappear, and a
proof after the main theorem still needs a clear connection to the sentences it carries.
The record and the page must describe the declarations that actually do the work.
