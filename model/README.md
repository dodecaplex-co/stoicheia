# The formal model

Stoicheia's proofs rest on 48 laws: Euclid's postulates, Definition 15 and the tacit rules,
each an `axiom` about seventeen `opaque` words, with their exact statements in
[Certificate/axioms.lock](../Certificate/axioms.lock). Lean checks that every proof follows
from the laws. It cannot check that the laws can all be true at once.
[tests/model/MODEL.md](../tests/model/MODEL.md) argues that they can, law by law, by
reading the words in the ordinary plane, and tests each law there numerically. This
package gives a formal proof: a Lake package of its own, with Mathlib, in which the
words are the fields of a structure, the ordinary plane fills them, and Lean checks that
the plane satisfies each law.

**Where it stands.** The package builds, with the signature, the plane, and all 48 laws,
written by a generator from the library's elaborated declarations into one structure,
`Laws`, and checked against those declarations. The plane satisfies all 48 locked laws.
`Model/Assembly.lean` gathers these proofs into `euclidean_laws`, with no remaining
hypotheses, and proves `model_exists`. This establishes a model relative to Lean's logic
and Mathlib's construction of the real numbers.

## Building it

```sh
export PATH=$HOME/.elan/bin:$PATH
cd model
lake exe cache get      # Mathlib's prebuilt files: about 450 MB to download, 6.6 GB unpacked
lake build              # this package: about 15 seconds once Mathlib's files are in place
lake lean Check/Write.lean   # writes the generated files again, after the lock or a proof changes
```

`lake exe cache get` resolves the pinned Mathlib on the first run and downloads its build
in about a minute on a fast connection; without it, building Mathlib from source takes
hours. The whole of `model/.lake` comes to about 7.2 GB, and git ignores it. The main
package is untouched: it depends on nothing here and never sees Mathlib, and `lake build`
at the repository's root builds the library exactly as before.

| File | What it holds | Imports |
|---|---|---|
| [lakefile.toml](lakefile.toml) | the package: Mathlib pinned to `v4.35.0`, the release for the toolchain both packages use; the library itself, read only by `Check`; and the files besides Lean imports that `Check` reads | |
| [Model/Signature.lean](Model/Signature.lean) | the seventeen words as the fields of `Signature`, and the words behind the magnitudes | nothing |
| [Model/Laws.lean](Model/Laws.lean) | **generated:** every law, and the defined words they reach, translated from the library; the structures `Neutral` and `Laws` | `Signature` |
| [Model/Hand.lean](Model/Hand.lean) | the laws first proved in the plane, translated **by hand**, and the proposed `exists_centre` | `Laws` |
| [Model/Laws/angles.lean](Model/Laws/angles.lean) | the ten angle laws, with `Collinear` and `IsRightAngle`, translated **by hand** | `Signature` |
| [Model/Laws/areas-p5.lean](Model/Laws/areas-p5.lean) | the eight area laws and Postulate 5, translated **by hand** | `Signature` |
| [Model/Laws/circles.lean](Model/Laws/circles.lean) | the 19 circle rules, translated **by hand** | `Model.Hand` |
| [Model/Laws/incidence.lean](Model/Laws/incidence.lean) | the incidence and line laws, and `Hand.LinesMeet`, **by hand** | `Signature`, `Hand` |
| [Model/Laws/intersections.lean](Model/Laws/intersections.lean) | the five line intersection rules and the four circle rules, and separate hand copies of `LinesMeet` and `LineMeetsCircle` | `Hand` |
| [Model/Laws/lengths.lean](Model/Laws/lengths.lean) | the three metric length laws, translated **by hand** | `Signature` |
| [Model/Laws/order.lean](Model/Laws/order.lean) | the fifteen order laws, Between 1 to 7 and the diagram-segment rules, **hand-translated** | `Signature` |
| [Model/Laws/sides.lean](Model/Laws/sides.lean) | the five same-side rules, four Pasch rules and three triple-incidence rules, translated **by hand** | `Signature` |
| [Model/Laws/superposition.lean](Model/Laws/superposition.lean) | the rule of superposition, and the words `Collinear` and `Triangle` it reaches, **by hand** | `Signature` |
| [Model/Euclidean.lean](Model/Euclidean.lean) | the ordinary plane as a `Signature` | Mathlib |
| [Model/Euclidean/AngleAdd.lean](Model/Euclidean/AngleAdd.lean) | angle addition, both ways (diagram-angle rule 2), proved in the plane | Mathlib |
| [Model/Euclidean/AngleBasics.lean](Model/Euclidean/AngleBasics.lean) | the bridge from the plane's angle to Mathlib's, and the line through two points | Mathlib |
| [Model/Euclidean/Angles.lean](Model/Euclidean/Angles.lean) | Definition 15, Postulate 4, the two metric angle laws and diagram-angle rules 1, 3 and 4 proved in the plane | Mathlib |
| [Model/Euclidean/Areas.lean](Model/Euclidean/Areas.lean) | the eight area laws, including collinear and repeated corners, proved by determinants | Mathlib |
| [Model/Euclidean/Avoidance.lean](Model/Euclidean/Avoidance.lean) | Postulate 2 and all finite avoidance rules for lines, regions and circumferences proved in the plane | Mathlib |
| [Model/Euclidean/Centre.lean](Model/Euclidean/Centre.lean) | the proposed `exists_centre` proved in the plane | Mathlib |
| [Model/Euclidean/CircleBasics.lean](Model/Euclidean/CircleBasics.lean) | Postulate 3, Definition 15 and the generalities of a centre and of the inside of a circle, proved in the plane | Mathlib |
| [Model/Euclidean/CircleRules.lean](Model/Euclidean/CircleRules.lean) | System E's Circle 1 to 4 proved in the plane, and `CirclesMeet α α` | Mathlib |
| [Model/Euclidean/CircleSides.lean](Model/Euclidean/CircleSides.lean) | Intersections 8 and 9 proved in the plane | Mathlib |
| [Model/Euclidean/Circles.lean](Model/Euclidean/Circles.lean) | Intersection 4 and Intersection 5 proved in the plane | Mathlib |
| [Model/Euclidean/Incidence.lean](Model/Euclidean/Incidence.lean) | Postulate 1, `line_unique`, the other generalities and Intersection 1 proved in the plane | Mathlib |
| [Model/Euclidean/Lengths.lean](Model/Euclidean/Lengths.lean) | the three metric length laws proved by nonnegative distance | Mathlib |
| [Model/Euclidean/LineCircle.lean](Model/Euclidean/LineCircle.lean) | Intersection 3, Intersections 4 and 5 of the constructions, and Circle 1, proved in the plane | Mathlib |
| [Model/Euclidean/LineSides.lean](Model/Euclidean/LineSides.lean) | Intersections 1 and 2, and Circles 2, 3 and 4, proved in the plane | Mathlib |
| [Model/Euclidean/Magnitudes.lean](Model/Euclidean/Magnitudes.lean) | the eight magnitude laws proved in the plane | Mathlib |
| [Model/Euclidean/Order.lean](Model/Euclidean/Order.lean) | Between 1, 4, 5 and 7 proved in the plane | Mathlib |
| [Model/Euclidean/OrderLines.lean](Model/Euclidean/OrderLines.lean) | Between 2, 3 and 6, which bring in a straight line, proved in the plane | Mathlib |
| [Model/Euclidean/Pasch.lean](Model/Euclidean/Pasch.lean) | Pasch 1 to 4 proved in the plane | Mathlib |
| [Model/Euclidean/Postulate5.lean](Model/Euclidean/Postulate5.lean) | Postulate 5, with the meeting on the stated side, proved in the plane | Mathlib |
| [Model/Euclidean/Segments.lean](Model/Euclidean/Segments.lean) | the diagram-segment rules 1 to 4 proved in the plane | Mathlib |
| [Model/Euclidean/Sides.lean](Model/Euclidean/Sides.lean) | `SameSide` read as `SSameSide`, and Same side 1 to 5 proved in the plane | Mathlib |
| [Model/Euclidean/Superposition.lean](Model/Euclidean/Superposition.lean) | superposition proved in the plane: an isometry, with a reflection when the side needs one | Mathlib |
| [Model/Euclidean/TripleIncidence.lean](Model/Euclidean/TripleIncidence.lean) | Triple incidence 1 to 3 proved by signed determinants and affine sides | Mathlib |
| [Model/Assembly.lean](Model/Assembly.lean) | **generated:** `euclidean_laws`, all 48 proofs gathered into `Laws`, and the unconditional `model_exists` | Mathlib |
| [Model/Audit.lean](Model/Audit.lean) | checked at every build: the library is not imported, and what each proof in the plane, and the assembly, rests on | every module of `Model` |
| [Check/Angles.lean](Check/Angles.lean) | the hand-translated angle laws and their two words compared with the library and the generated laws | `Elements.Foundations`, `Elements.BookI.Prop13`, `Check.Hand`, the generator, `Model.Laws.angles` |
| [Check/AreasP5.lean](Check/AreasP5.lean) | the hand-translated area laws and Postulate 5 compared with the library and the generated laws | `Elements.Foundations`, `Check.Hand`, `Model.Laws.«areas-p5»` |
| [Check/Circles.lean](Check/Circles.lean) | the hand-translated circle rules compared with the library and the generated laws | `Elements.Foundations`, `Elements.BookI.Prop07`, `Elements.Figure.Circles`, `Check.Hand`, the generator, `Model.Laws.circles` |
| [Check/Generated.lean](Check/Generated.lean) | checked at every build: the lock, its hash and the axioms, and that the generated files are what the generator writes | `Elements.Foundations`, `Model.Signature`, the generator |
| [Check/Generator.lean](Check/Generator.lean) | the generator: reading the library, translating, writing, and the checks it makes | Lean alone |
| [Check/Hand.lean](Check/Hand.lean) | each hand translation compared with the library's declaration and with the generated law | `Elements.Foundations`, `Model.Hand` |
| [Check/Incidence.lean](Check/Incidence.lean) | the hand-translated incidence and line laws, and `Hand.LinesMeet`, compared with the library and the generated laws | `Elements.Foundations`, `Elements.Figure.Circles`, `Check.Hand`, the generator, `Model.Laws.incidence` |
| [Check/Intersections.lean](Check/Intersections.lean) | the hand-translated intersection rules and their two words compared with the library and the generated laws | `Elements.BookI.Prop07`, `Elements.Figure.Circles`, `Check.Hand`, the generator, `Model.Laws.intersections` |
| [Check/Laws.lean](Check/Laws.lean) | **generated:** each generated law and word compared with the library's by the kernel | `Elements.Foundations`, `Model.Laws` |
| [Check/Lengths.lean](Check/Lengths.lean) | the hand-translated metric length laws compared with the library and the generated laws | `Elements.Foundations`, `Check.Hand`, `Model.Laws.lengths` |
| [Check/Order.lean](Check/Order.lean) | the hand-translated order laws compared with the library and the generated laws | `Elements.Foundations`, `Check.Hand`, `Model.Laws.order` |
| [Check/Original.lean](Check/Original.lean) | `original`, the library's own words as a signature | `Elements.Foundations`, `Model.Signature` |
| [Check/RoundTrip.lean](Check/RoundTrip.lean) | checked at every build: each generated law and word translated back and compared with the library's by syntax; planted faults it must refuse | `Elements.Foundations`, `Model.Laws`, `Model.Hand`, seven files of `Model/Laws/` (all but angles and superposition), the generator |
| [Check/Sides.lean](Check/Sides.lean) | the hand-translated same-side, Pasch and triple-incidence rules compared with the library and the generated laws | `Elements.Figure.Circles`, `Check.Hand`, the generator, `Model.Laws.sides` |
| [Check/Superposition.lean](Check/Superposition.lean) | the hand translation of superposition and its two words compared with the library and the generated law | `Elements.Foundations`, `Check.Hand`, `Model.Laws.superposition` |
| [Check/Write.lean](Check/Write.lean) | run by hand, never built: writes the generated files | as `Check/Generated.lean` |
| [lock.sha256](lock.sha256) | the hash of the lock the model was last checked against | |

Nothing under `Model/` imports the library, and nothing under `Check/` imports Mathlib. The
three generated files are committed, so that anyone can read them, and `lake build` fails
while any of them differs from what the generator writes.

## The signature

[Model/Signature.lean](Model/Signature.lean) states the seventeen words as the fields of
one structure. Each field has the type of the opaque constant it stands for, with the
earlier fields standing in for the earlier words, and with the library's defined words
`Magnitude k`, `Length`, `Angle` and `Area` written out as what they unfold to,
`(MagnitudeImpl k).type` at the matching kind, since a structure's fields cannot use a word
defined from those fields:

```lean
structure Signature where
  Point : Type
  Line : Type
  Circle : Type
  OnLine : Point → Line → Prop
  SameSide : Point → Point → Line → Prop
  Between : Point → Point → Point → Prop
  OnCircle : Point → Circle → Prop
  InsideCircle : Point → Circle → Prop
  Centre : Point → Circle → Prop
  MagnitudeImpl : Kind → NonemptyType
  zero : {k : Kind} → (MagnitudeImpl k).type
  add : {k : Kind} → (MagnitudeImpl k).type → (MagnitudeImpl k).type → (MagnitudeImpl k).type
  lt : {k : Kind} → (MagnitudeImpl k).type → (MagnitudeImpl k).type → Prop
  len : Point → Point → (MagnitudeImpl .length).type
  ang : Point → Point → Point → (MagnitudeImpl .angle).type
  area : Point → Point → Point → (MagnitudeImpl .area).type
  rightAngle : (MagnitudeImpl .angle).type
```

The magnitudes are part of the signature, with their zero, addition and order, since eight
laws are about them and many more compare them. The fields copy the library's words so
closely that the translation of a law is a substitution, and putting the library's own
words back in gives the original declaration, which is how the translation is checked
(below). So the types agree up to unfolding, which Lean checks when `Check.original` fills
the fields with the library's words. One consequence: `S.len A B` has the type
`(S.MagnitudeImpl .length).type`, not `S.Length`, so for Lean to find `+`, `0`, `<` and `≤`
for it, `S.Magnitude` is reducible, as the library's `Magnitude` is not; its definition is the
library's all the same. Besides that unfolding, the one difference is the kinds of magnitude:
the library's `Elements.Kind` is declared beside the opaque words and their notation, so the
model declares `Model.Kind`, with the same three constructors, and the translation maps them
by name.

## The plane

[Model/Euclidean.lean](Model/Euclidean.lean) reads the words in Mathlib's Euclidean plane,
`EuclideanSpace ℝ (Fin 2)`, as MODEL.md does on paper and as Astra's third answer
recommends:

| Word | Reading |
|---|---|
| `Point` | a point of `EuclideanSpace ℝ (Fin 2)` |
| `Line` | a one-dimensional affine subspace, equal to another when it has the same points |
| `OnLine` | membership |
| `SameSide` | Mathlib's strict same-side relation, `SSameSide` |
| `Between` | Mathlib's strict betweenness, `Sbtw` |
| `Circle` | a Mathlib `Sphere` with positive radius |
| `OnCircle`, `InsideCircle` | at the radius's distance from the centre, and nearer |
| `Centre` | the sphere's centre |
| each kind of magnitude | `ℝ≥0`, with its own `0`, `+` and `<` |
| `len` | `nndist` |
| `ang` | Mathlib's unoriented angle, in [0, π], but 0 when a point is repeated |
| `area` | half the absolute value of a determinant |
| `rightAngle` | π/2 |

Three choices matter. The angle carrier is all of `ℝ≥0`, since sums of angles must have
somewhere to live, though each angle lies in [0, π]. An angle with a repeated point is 0,
as in MODEL.md's reading. When an arm is a zero vector, that is when `A = B` or `C = B`,
Mathlib's angle is π/2, and with π/2 all four angle conditions of `Square A A A A` would
hold; so the reading takes Mathlib's angle only when both arms are nonzero. And a line is a
subspace, not an equation, since two equations can name one line and `line_unique` would
fail.

Reading our words by Mathlib's own definitions, rather than by new ones, lets the proofs
here stand on Mathlib's lemmas. Its betweenness, sides and spheres are the work of Joseph
Myers; its unoriented angle, of Joseph Myers and Manuel Candales; its perpendicular
bisector, of Yury Kudryashov and Joseph Myers; and its Euclidean plane, `EuclideanSpace`,
of Joseph Myers, Sébastien Gouëzel and Heather Macbeth, as their files record. Angle
addition in both directions stands on the exact case of equality in the triangle inequality
for angles, the work of Ilmārs Cīrulis, Alex Meiburg and Jovan Gerbscheid. Our thanks to
them all.

A model of the laws is one obligation, and a faithful reading of every word the
propositions use is another. The plane here is checked against the laws; whether
`Square`, `rect` or `circumference` mean in it what Euclid means is a question for the
review records, not for this package.

## How the laws are generated

`Model/Laws.lean` is written by a Lean program, [Check/Generator.lean](Check/Generator.lean),
from the library's elaborated declarations, not from their printed text. To write it again,
with the two other generated files, run `lake lean Check/Write.lean` in `model/` (`lake lean`
builds the file's imports first). `lake build` runs the generator again in memory
([Check/Generated.lean](Check/Generated.lean)) and fails while a committed file differs from
what it writes.

1. **Read the declarations, not the text.** The generator imports every module of
   `Elements.Foundations`, and checks that there is one for each file under
   `Elements/Foundations/`, so that no axiom is missed. It takes every axiom declared there,
   which must be exactly the 48 names in the lock's `[axioms]`, as the expression Lean
   elaborated: binders, binder kinds (implicit or explicit), the order of the binders, every
   guard, every instance argument. It checks too that the lock prints each one's statement
   as Lean prints it now, and each word they reach as the lock's `[vocabulary]` has it, so
   the laws it translates are exactly those the lock records.
2. **Translate by structure.** It walks each expression and replaces each of the seventeen
   opaque constants by the matching field of a signature `S`, and `Elements.Kind` and its
   constructors by `Model.Kind`'s. A project definition the law reaches, such as
   `Triangle`, `Collinear`, `CirclesMeet`, `IsRightAngle` or the magnitude instances,
   among them the present definition of `≤`, is translated the same way, once, into a
   definition over `S` in dependency order. The axioms reach 37 words of the lock's
   vocabulary: the seventeen opaque words, `Kind` and its three constructors, and 16
   definitions. Eight of those, the carriers of the magnitudes and their instances, are
   written by hand in `Model/Signature.lean`, since the signature's own fields need them to
   be used at all, and the generator checks them rather than writing them; the other eight
   it writes. Lean's own constants, those of `Init` (`Eq`, `Ne`, `And`, `Or`, `Not`,
   `Exists`, `List`, `Membership.mem`, `LT.lt`, `HAdd.hAdd`, `OfNat.ofNat` and the like),
   stay as they are. **Any other constant is an error**, so nothing untranslated can reach
   the model. (One detail: Lean declares the library's `MagnitudeImpl` at every universe,
   since it generalizes the level of `NonemptyType`, and `Magnitude` uses it at universe 0;
   the field is that one, and the translation insists on it.)
3. **Write a file a reader can read.** The output is plain Lean with no Mathlib: the eight
   translated words, then each law as a definition named as in the lock, `Law.Postulate1 S`
   for `Postulate1` and `Law.Tacit.circles_meet S` for `Tacit.circles_meet`, laid out as a
   reader writes a law, its hypotheses filling the line:

   ```lean
   def circles_meet : Prop :=
     ∀ {A B : S.Point} {α β : S.Circle}, S.OnCircle A α → S.InsideCircle B α → S.InsideCircle A β →
       S.OnCircle B β → S.CirclesMeet α β
   ```

   and last the structures with a field for each law, named as the law's last part:

   ```lean
   structure Neutral (S : Signature) : Prop where
     Definition15 : Law.Definition15 S
     ...
     circles_meet : Law.Tacit.circles_meet S
     ...

   structure Laws (S : Signature) : Prop extends Neutral S where
     Postulate5 : Law.Postulate5 S
   ```

   Postulate 5 stands apart from the other 78, so that a hyperbolic plane can later satisfy
   `Neutral` and fail it; so would any rule the library declared in
   `Elements.Tacit.Euclidean`, for the plane alone, of which there is none. The file's header
   records the sha256 of the lock it was written from, with a table of the 37 words and what
   each becomes, so the vocabulary is pinned with the lock's hash.
4. **Assemble the model.** Each law is proved in the plane as a theorem of its own, named as
   its field, `Euclidean.circles_meet`, in a module of `Model/Euclidean/` that imports the
   laws and Mathlib. The generator finds those theorems in the files under
   `Model/Euclidean/` (a theorem named as a field of `Laws` is taken to prove that law, and
   Lean checks that it does) and writes [Model/Assembly.lean](Model/Assembly.lean), which
   imports them all and gathers them into

   ```lean
   theorem euclidean_laws : Laws Euclidean.plane where
     Definition15 := Euclidean.Definition15
     ...
     circles_meet := Euclidean.circles_meet
     ...
   ```

   with no remaining hypothesis. The generator then writes
   `theorem model_exists : ∃ S : Signature, Laws S := ⟨Euclidean.plane, euclidean_laws⟩`. The
   assembly stands apart from `Model/Laws.lean`, which the proofs import, so that no import
   goes round in a circle and the laws stay free of Mathlib. The proofs are stated with the
   hand-translated laws of `Model/Hand.lean` and `Model/Laws/`, and the files of `Check/`
   compare the locked laws with their generated fields and the retired rules directly
   with their library declarations.

The library's 99 proofs do not change. Rewriting the library over a signature, with
wrappers that keep its present names, is a later and separate decision, and it would need
care not to blur the certificate: if every theorem took one `Laws` hypothesis bundling all
48 laws, Lean's dependency walk would report all 48 beneath every proof.

## How the translation is checked

A hash shows that a file has not changed. It does not show that a translation means what
the original means. These checks do that, at every build.

- **The round trip, by the kernel.** [Check/Original.lean](Check/Original.lean) builds
  `original`, the signature whose fields are the library's own words
  (`Point := Elements.Point`, and so on), and the generated
  [Check/Laws.lean](Check/Laws.lean) asks, for each law the generator wrote,

  ```lean
  example : Law.Tacit.circles_meet original = type_of% @Elements.Tacit.circles_meet := rfl
  ```

  and the same for each word it wrote; [Check/Hand.lean](Check/Hand.lean) asks it of the
  laws translated by hand and the words written by hand in `Model/Signature.lean`, and asks
  whether each hand translation is the law the generator wrote. `type_of%` takes the
  declaration's statement and does not use the axiom. The kernel accepts the `rfl` only if
  the two are the same proposition, up to unfolding definitions; a dropped guard, two
  swapped arguments or a change in the order of the binders fails it, and the build with
  it. This covers all 48 laws and all 15 defined words they reach. The family checks in
  `Check/` retain the original library checks. They also compare each hand-translated law
  with its generated field over any signature, except for the 39 retired axioms. Eight were
  retired first: `adjacent_eq_of_right`, `not_same_side_of_circles_meet`,
  `centre_unique`, `inside_of_between`, `exists_point_outside_circle`,
  `line_meets_circle_of_opposite_sides`, `triple_incidence3` and `inside_of_angle_add`;
  31 more on 19 October 2026 (listed in [MODEL.md](../tests/model/MODEL.md)). These are
  now theorems with the same names and types. Their hand translations are compared
  directly with the library declaration's type by `comparePlanted`, including binder kinds,
  which works for an axiom or a theorem and remains when a generated assumption field
  disappears; the exceptions are Intersections 2 and 3, which reach `LineMeetsCircle`, a
  word no locked law reaches since their retirement and so one the generator no longer
  writes: they use the hand copy of the word in `Model/Laws/intersections.lean`, which is
  checked against the library's word, and are compared with their declarations by the
  kernel through `original`, up to unfolding. Their concrete plane proofs and pinned axiom
  audits remain as evidence for these derived facts.
- **The round trip, by syntax.** [Check/RoundTrip.lean](Check/RoundTrip.lean) takes each
  law and word as Lean elaborated them from `Model/Laws.lean`, translates each back, every
  field of `S` and every word over it replaced by the library's word, and compares it with
  the library's declaration expression for expression. A binder's kind and type always
  count, and so does its name wherever the bound variable is used; an unused hypothesis's
  name does not, since Lean prints it as an arrow and it is no part of what a law says. The
  one difference allowed is that the four carrier words of the magnitudes (`Magnitude`,
  `Length`, `Angle`, `Area`) are unfolded on both sides first, since the fields write the
  carriers out ([the signature](#the-signature)). Anything left over that does not translate
  back is an error. This is stricter than the kernel's check: it notices a translation that
  is right only after unfolding a word, and a binder made explicit where the original's is
  implicit, which the kernel does not see, since neither changes the proposition. The same
  file checks the words written by hand in `Model/Signature.lean`, exactly, the type of each
  field of the signature against the library's opaque word, each hand translation imported
  here under its law name in `Model.Hand` against the law the generator wrote for it, binder
  kinds included, and that `original` gives each field the library's word. That covers the
  hand translations of `Model/Hand.lean` and of seven files of `Model/Laws/`. The hand
  translations kept under suffixed names ([below](#proved-laws)), and the angle and
  superposition translations, which use words of their own written by hand, are compared
  with the generated laws by the kernel in their files of `Check/`, apart from the eleven
  direct declaration comparisons just described.
- **Completeness.** [Check/Generated.lean](Check/Generated.lean) checks that the axioms
  declared in `Elements.Foundations` are exactly the lock's `[axioms]`, so that none is
  missing and none is extra, and `Check/RoundTrip.lean` that `Neutral` and `Laws` have
  exactly one field for each, of type `Law.… S`, and nothing else.
- **The checks catch what they are meant to.** The end of `Check/RoundTrip.lean` plants a
  fault of each kind in a copy of a law (a binder made explicit, two points exchanged, a
  dropped guard, a word written out) and two statements the translation must refuse (a word
  the laws do not reach, and a constant that is neither the library's nor Lean's own), and
  `#guard_msgs` fails the build unless each is refused with the message it pins. The first
  and the fourth pass the kernel's `rfl`, which the file shows too.

The eight magnitude laws quantify over the kind (`∀ {k : Elements.Kind}`), and with two
copies of `Kind` their round trip is an equivalence, not `rfl`. Each direction is the other
statement itself, put at the matching kind, with no other step, so the check is the same
up to relabelling the kinds; a wrong translation of `add_lt_add_right`, with `c` added on
the left, fails it. One small decision would make even these round trips `rfl`: if
`Elements.Kind` moved into a file of its own, a Lean `module`, as every file of `Model/`
is, with no opaque word, no axiom and no notation, the model could import that one file and
share the library's `Kind`. It must be a module because a module cannot import a file that
is not one, and no file of the library is one today.

## How the lock ties it

[lock.sha256](lock.sha256) holds the sha256 of `Certificate/axioms.lock`, as
[tests/model/lock.sha256](../tests/model/lock.sha256) does for the numerical harness. The
formal-model CI job ([below](#the-ci-job)) compares it with the lock:

```sh
grep -v '^#' model/lock.sha256 | shasum -a 256 -c -
```

Then any change to `Certificate/axioms.lock` fails the job, not only a change to an axiom:
the lock also holds every word that the statement of a proposition, a porism or a companion
reaches. A change to the axioms (one added, removed or restated), or to a word an axiom
reaches, sends someone back to the model: to the translation, its checks in `Check/`, and
the proofs in the plane of the laws that changed. A change that touches none of these, such
as a word only a proposition's statement uses, moved into the foundations from `Staging/`,
needs only the hash renewed. A change to the lock renews `model/lock.sha256` in the same
change, as it renews `tests/model/lock.sha256`, and writes the generated files again
(`lake lean Check/Write.lean`): `Model/Laws.lean` records the hash of the lock it was
written from, with the vocabulary its laws reach, so it differs from what the generator
writes until it is written again. `lake build` checks the hash as well, without CI: the
generator computes the lock's sha256 itself, and `Check/Generated.lean` fails unless
`model/lock.sha256` holds it. The round-trip checks tie each translated law to the
declaration itself, more tightly than the hash can; the hash pins the rest of the lock, and
the vocabulary with it. A law proposed for the foundations is proved here before it lands:
`exists_centre`, proposed in issue #59, is already proved in the plane
([Model/Euclidean/Centre.lean](Model/Euclidean/Centre.lean)). In the change that declares
it, the generator writes its law, the assembly gathers `Euclidean.exists_centre`, which is
named as its field, `Check/RoundTrip.lean` compares the hand translation with the generated
law, and its kernel round trip joins `Check/Hand.lean`.

## What the proofs rest on

A model is evidence only if its proofs do not use the laws they are meant to satisfy.
Three things make sure of that.

- **No import of the library.** Nothing under `Model/` imports `Elements`, so no law of
  the library is even in scope there. [Model/Audit.lean](Model/Audit.lean), which
  imports every module of `Model`, checks it at every build: it asks Lean for
  `Elements.Point`, and `#guard_msgs` fails the build unless the answer is "unknown
  identifier". An import through another file is caught as well as a direct one.
- **The axioms, checked at every build.** The same file prints, for each theorem that
  proves a law in the plane, the axioms Lean finds beneath it, and `#guard_msgs` fails the
  build unless they are exactly `propext`, `Classical.choice` and `Quot.sound`: Lean's
  own, which Mathlib's real numbers use. No project axiom and no `sorryAx` can pass.
  `euclidean_laws`, which `Model/Assembly.lean` gathers from every theorem that proves a
  law in the plane, is audited the same way, so a new proof is audited through it as soon
  as the generator gathers it; so is `model_exists`.
- **The library's rules on commands.** `Model/` uses none of the commands the library
  forbids ([FORMALIZATION](../docs/FORMALIZATION.md#7-the-foundations-and-the-policies-the-checks-enforce),
  section 7: `native_decide`, `implemented_by`, `unsafe` and the rest), and the audit
  catches a `sorry` beneath any listed proof. The generator is a Lean program and needs
  metaprogramming, so it lives in `Check/`, apart from the proofs, and nothing under
  `Model/` imports it; it runs as `Certificate/Facts.lean` does, with `run_cmd`, and uses
  none of the commands that get round the kernel (`native_decide`, `implemented_by`,
  `extern`, `unsafe`, `set_option debug.…`). That `Model/` and `Check/` keep to this rests
  on review today: `check_fidelity.py` scans `Elements/` alone, and a `set_option debug.…`
  would not show in `#print axioms`.

The claim this package supports is: Lean checks that the
ordinary Euclidean plane satisfies every law in this revision's foundations, relative to
Lean's logic and Mathlib's construction of the real numbers. It does not show that a
formal statement captures what Euclid meant: that is the work of the review records.

## The order of the work: hardest laws first

Astra's third answer listed the laws whose proofs would settle the representation, and they
were taken first. Each retained axiom proved here is gathered into `euclidean_laws`
by the generator, and `lake build` fails until it has been (`lake lean Check/Write.lean`).
The table also includes the 39 former axioms now proved in the library, whose
[derivations and homes](../docs/FORMALIZATION.md#rules-now-proved) are listed separately.
Their plane proofs remain as derived facts with individual audits; the generator
no longer gathers them as assumptions.

| Group | Laws | State |
|---|---|---|
| Circle intersections | `circles_meet`, `circles_meet_of_on_inside_outside`, `circles_meet_same_side`, `circles_meet_opposite_side` | proved here |
| Magnitudes | the eight laws of `Tacit/Magnitudes.lean`: easy in the plane, but they test the translation of the instances and of `Kind` | proved here |
| Order | the ten laws of Between 1 to 7 and the five diagram-segment laws (`len_add_of_between`, `circle_eq`, `on_circle_of_len_eq`, `inside_of_len_lt`, `len_lt_of_inside`): not among the hard groups, but the proof of every one of the 99 propositions rests on some of them | proved here |
| Line and circle crossings | `line_circle_between`, `line_circle_beyond`, `line_meets_circle_of_inside`, `line_meets_circle_of_opposite_sides`, `lines_meet_of_opposite_sides` | proved here |
| Angle addition, both ways | `angle_add_of_inside`, `inside_of_angle_add` | proved here |
| Postulate 5 | the meeting on the stated side, not only a meeting | proved here |
| Superposition | `superposition`, as locked: an isometry, with a reflection where the side needs one | proved here; a restricted replacement rule would need its own proof |
| Areas | all eight area laws, including `area_congruent`, `area_add_of_between` and `between_of_area_add`, with collinear and repeated corners | proved here |
| Finite avoidance | the `avoid` lists of Postulate 2 and the Points rules: a line, an open region and a circumference are infinite | proved here: infinite real intervals on a line, and injective families indexed by ℕ for regions and circumferences |

`CirclesMeet α α` is true, since a circle has two distinct points (`circlesMeet_self`); the
side laws are proved for that case too, where both centres are one point and the line
through them is any line through it. Circle 4 (`not_same_side_of_circles_meet`) asks that
the circles differ, and needs to: for a circle and itself, two common points can lie on
one side of a line through the centre.

The line-circle constructions rest on one calculation
([Model/Euclidean/LineCircle.lean](Model/Euclidean/LineCircle.lean)): along a line through
a point inside a circle, the squared distance from the centre, less the squared radius, is
a quadratic in the line's parameter, negative at that point, so it has one root on each
side of it, and the points inside are exactly those between the roots. That gives the two
crossings of Intersection 3, the crossing beyond the inside point and the one before an
outside point, and, for Circle 1, that a chord's ends are the two roots. A line through the
centre is no special case. Intersection 1 uses the crossing between points on opposite
sides of a line. Intersection 2 and Circles 2 and 3 use the strict convexity of the disc (`Sbtw.dist_lt_max_dist`, Joseph Myers's): a point strictly
between two points on or inside a circle is strictly inside it. Circle 4 asks for two
different circles, so their centres differ, and the line of centres is the perpendicular
bisector of the common points, as in Intersections 8 and 9.

## Proved laws

The generated [assembly](Model/Assembly.lean) supplies **48 of the 48 locked laws** from
proofs in the plane. This list counts each law once, even where two families supply a proof.
Names other than `Definition15` and the postulates are in `Elements.Tacit` in the lock.
The proposed `exists_centre` is proved too, but is not a locked law and is not counted here.
The 39 retired rules listed above also retain their concrete plane proofs and audits,
as derived facts outside the generated assumption fields and this table.

| Proof file in `Model/Euclidean/` | Count | Locked laws proved |
|---|---:|---|
| [AngleAdd.lean](Model/Euclidean/AngleAdd.lean) | 1 | `angle_add_of_inside` |
| [Angles.lean](Model/Euclidean/Angles.lean) | 6 | `Postulate4`, `angle_eq_of_same_rays`, `angle_eq_zero_of_same_ray`, `angle_le_two_right`, `angle_symm`, `same_ray_of_angle_eq_zero` |
| [Areas.lean](Model/Euclidean/Areas.lean) | 6 | `area_add_of_between`, `area_congruent`, `area_degenerate`, `area_eq_zero_of_on_line`, `area_rotate`, `on_line_of_area_eq_zero` |
| [Avoidance.lean](Model/Euclidean/Avoidance.lean) | 4 | `Postulate2`, `exists_point`, `exists_point_inside_circle`, `exists_point_on_line` |
| [CircleBasics.lean](Model/Euclidean/CircleBasics.lean) | 2 | `Definition15`, `Postulate3` |
| [CircleRules.lean](Model/Euclidean/CircleRules.lean) | 2 | `between_of_inside_chord`, `outside_of_between` |
| [CircleSides.lean](Model/Euclidean/CircleSides.lean) | 1 | `circles_meet_same_side` |
| [Circles.lean](Model/Euclidean/Circles.lean) | 1 | `circles_meet` |
| [Incidence.lean](Model/Euclidean/Incidence.lean) | 3 | `Postulate1`, `line_unique`, `lines_meet_of_opposite_sides` |
| [Lengths.lean](Model/Euclidean/Lengths.lean) | 2 | `len_self`, `len_symm` |
| [LineCircle.lean](Model/Euclidean/LineCircle.lean) | 2 | `line_circle_between`, `line_circle_beyond` |
| [Magnitudes.lean](Model/Euclidean/Magnitudes.lean) | 8 | `add_assoc`, `add_comm`, `add_lt_add_right`, `add_zero`, `lt_irrefl`, `lt_trans`, `lt_trichotomy`, `not_lt_zero` |
| [Order.lean](Model/Euclidean/Order.lean) | 2 | `between_symm`, `not_between_of_between` |
| [OrderLines.lean](Model/Euclidean/OrderLines.lean) | 1 | `between_cases` |
| [Pasch.lean](Model/Euclidean/Pasch.lean) | 1 | `pasch2` |
| [Postulate5.lean](Model/Euclidean/Postulate5.lean) | 1 | `Postulate5` |
| [Segments.lean](Model/Euclidean/Segments.lean) | 2 | `circle_eq`, `len_add_of_between` |
| [Sides.lean](Model/Euclidean/Sides.lean) | 2 | `not_on_line_of_same_side`, `same_side_trans` |
| [Superposition.lean](Model/Euclidean/Superposition.lean) | 1 | `superposition` |

**No locked laws remain.** `euclidean_laws` has no hypotheses, and the package provides
the unconditional theorem `model_exists : ∃ S : Signature, Laws S`.

The overlapping circle and intersection proofs are retained with `_circles` and
`_intersections` suffixes, and the second proof of Definition 15 with `_angles`.
Their hand translations retain the same statements under corresponding names. Each has
its own original-declaration check, a generated-law or direct syntactic comparison as
described above, and its own pinned axiom audit.
The hand copies of `LinesMeet` and `LineMeetsCircle` also remain under distinct names,
with equality checks against the generated words over every signature.

## The CI job

The formal-model CI job is the job `formal-model` in
[.github/workflows/ci.yml](../.github/workflows/ci.yml), not `model`, which is the
numerical harness. On `ubuntu-latest`, after checking out the repository and installing
elan, it runs:

```sh
grep -v '^#' model/lock.sha256 | shasum -a 256 -c -
cd model
lake exe cache get
lake build
```

`lake build` builds both libraries, `Model` (with the assembly and the audit) and `Check`
(with the generator's checks and the round trips), and fails if any check in them fails;
there is nothing else to run, since the generator runs inside the build. On the machine that
built this package, from a fresh clone, `lake exe cache get` took about 65 seconds (cloning
the pinned Mathlib and its dependencies, downloading 9,031 files, 452 MB, and unpacking them
to 6.6 GB). With the generator, `lake build` took 11 to 13 seconds of wall time in two runs,
for this package and the library files `Check` reads. Of the modules the generator added,
`Check/Generator.lean` took about 2 seconds to compile, `Check/Generated.lean` about 1 to run
the generator and compare its output, `Check/RoundTrip.lean` about 1, `Check/Laws.lean` under
half a second and `Model/Assembly.lean` 1 to 2, much of it alongside the proofs in the plane;
a build with nothing changed took a second or so. A runner should expect a few minutes in
all.

Between runs the job caches two directories, keyed on `model/lake-manifest.json`:
`model/.lake/packages`, which holds the pinned clones and the unpacked build, and
`~/.cache/mathlib`, where `lake exe cache get` keeps what it downloads and looks before
downloading again. After a restore, `lake exe cache get` downloads nothing and unpacks
nothing. The job stops after 30 minutes, since without Mathlib's prebuilt files
`lake build` would compile Mathlib from source for hours.

It is not yet a required check: the ruleset on main requires `check`, `model` and
`negative`, and making this one required is the owner's call
([decisions](../docs/briefs/0002-decisions.md#18-october-2026), 18 October). Even so,
`git safe-push --merge`, which lands every pull request, refuses one while any of its
checks fails or is still running, this one among them
([WORKFLOW](../docs/WORKFLOW.md#landing-work-pull-requests), section 10).

## Thanks

To Astra, whose third answer set out this package's shape, the plane's readings and their
pitfalls, the translation checks and the order of the hard laws. To Jeremy Avigad, Edward
Dean and John Mumma, whose System E gives most of the laws, and to LeanEuclid (Logan
Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si), whose
corrected Intersection 4 is the form proved here. And to Mathlib's authors and
maintainers, on whose plane every proof here stands: among them, for the circle rules,
Yaël Dillies and Yury Kudryashov, whose strict convexity gives Circle 1 to 3, and Johannes
Hölzl, Mario Carneiro and Kyle Miller, whose finite sets give the avoidance rules.
