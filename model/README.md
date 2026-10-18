# The formal model

Stoicheia's proofs rest on 87 laws: Euclid's postulates, Definition 15 and the tacit rules,
each an `axiom` about seventeen `opaque` words, with their exact statements in
[Certificate/axioms.lock](../Certificate/axioms.lock). Lean checks that every proof follows
from the laws. It cannot check that the laws can all be true at once.
[tests/model/MODEL.md](../tests/model/MODEL.md) argues that they can, law by law, by
reading the words in the ordinary plane, and tests each law there numerically. This
package is the start of the proof: a Lake package of its own, with Mathlib, in which the
words are the fields of a structure, the ordinary plane fills them, and Lean checks that
the plane satisfies each law.

**Where it stands.** The package builds, with the signature, the plane, and the first hard
laws: the circle-intersection rules, translated by hand for now and proved in the plane.
The rest of the laws, and the generator that will translate them from the library's own
declarations, are to come. Until every locked law is proved here, the evidence that the
laws have a model remains MODEL.md's hand arguments and numerical tests, and this package
is a milestone in progress.

## Building it

```sh
export PATH=$HOME/.elan/bin:$PATH
cd model
lake exe cache get      # Mathlib's prebuilt files: about 450 MB to download, 6.6 GB unpacked
lake build              # this package: about 10 seconds once Mathlib's files are in place
```

`lake exe cache get` resolves the pinned Mathlib on the first run and downloads its build
in about a minute on a fast connection; without it, building Mathlib from source takes
hours. The whole of `model/.lake` comes to about 7.2 GB, and git ignores it. The main
package is untouched: it depends on nothing here and never sees Mathlib, and `lake build`
at the repository's root builds the library exactly as before.

| File | What it holds | Imports |
|---|---|---|
| [lakefile.toml](lakefile.toml) | the package: Mathlib pinned to `v4.35.0`, the release for the toolchain both packages use; the library itself, read only by `Check` | |
| [Model/Signature.lean](Model/Signature.lean) | the seventeen words as the fields of `Signature` | nothing |
| [Model/Hand.lean](Model/Hand.lean) | the laws translated so far, and the defined words they reach, **by hand** | `Signature` |
| [Model/Euclidean.lean](Model/Euclidean.lean) | the ordinary plane as a `Signature` | Mathlib |
| [Model/Euclidean/Circles.lean](Model/Euclidean/Circles.lean) | Intersections 4 and 5 proved in the plane | Mathlib |
| [Model/Euclidean/CircleSides.lean](Model/Euclidean/CircleSides.lean) | Intersections 8 and 9 proved in the plane | Mathlib |
| [Model/Euclidean/Centre.lean](Model/Euclidean/Centre.lean) | the proposed `exists_centre` proved in the plane | Mathlib |
| [Model/Audit.lean](Model/Audit.lean) | checked at every build: the library is not imported, and what each proof in the plane rests on | every module of `Model` |
| [Check/Hand.lean](Check/Hand.lean) | each hand translation compared with the library's declaration | `Elements.Foundations`, `Model.Hand` |
| [lock.sha256](lock.sha256) | the hash of the lock the model was last checked against | |

Nothing under `Model/` imports the library, and nothing under `Check/` imports Mathlib.

## The signature

[Model/Signature.lean](Model/Signature.lean) states the seventeen words as the fields of
one structure, each with exactly the type of the opaque constant it stands for, the earlier
fields standing in for the earlier words:

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
(below). The one difference is the kinds of magnitude: the library's `Elements.Kind` is
declared beside the opaque words and their notation, so the model declares `Model.Kind`,
with the same three constructors, and the translation maps them by name.

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
as in MODEL.md's reading, where Mathlib's angle is π/2; with π/2, all four angle conditions
of `Square A A A A` would hold. And a line is a subspace, not an equation, since two
equations can name one line and `line_unique` would fail.

Reading our words by Mathlib's own definitions, rather than by new ones, lets the proofs
here stand on Mathlib's lemmas. Its betweenness, sides and spheres are the work of Joseph
Myers; its unoriented angle, of Joseph Myers and Manuel Candales; its perpendicular
bisector, of Yury Kudryashov and Joseph Myers; and its Euclidean plane, `EuclideanSpace`,
of Joseph Myers, Sébastien Gouëzel and Heather Macbeth, as their files record. Our thanks
to them all.

A model of the laws is one obligation, and a faithful reading of every word the
propositions use is another. The plane here is checked against the laws; whether
`Square`, `rect` or `circumference` mean in it what Euclid means is a question for the
review records, not for this package.

## How the laws will be generated

Today the laws proved here are translated by hand, in
[Model/Hand.lean](Model/Hand.lean), each with the lock's printed statement above it. The
next step replaces that file with one generated from the library's elaborated
declarations, not from their printed text.

1. **Read the declarations, not the text.** A Lean program in `Check/` imports
   `Elements.Foundations`, and takes every axiom declared there, which must be exactly the
   87 names in the lock's `[axioms]`, as the expression Lean elaborated: binders, binder
   kinds (implicit or explicit), the order of the binders, every guard, every instance
   argument.
2. **Translate by structure.** It walks each expression and replaces each of the seventeen
   opaque constants by the matching field of a signature `S`, and `Elements.Kind` and its
   constructors by `Model.Kind`'s. A project definition the law reaches, such as
   `Triangle`, `Collinear`, `CirclesMeet`, `IsRightAngle` or the magnitude instances,
   among them the present definition of `≤`, is translated the same way, once, into a
   definition over `S` in dependency order: these are the 37 words of the lock's
   vocabulary that the axioms reach. Lean's own constants (`Eq`, `Ne`, `And`, `Or`,
   `Not`, `Exists`, `List`, `Membership.mem`, `LT.lt`, `HAdd.hAdd`, `OfNat.ofNat` and the
   like) stay as they are. **Any other constant of the project is an error**, so nothing
   untranslated can reach the model.
3. **Write a file a reader can read.** The output is `Model/Laws.lean`, plain Lean with no
   Mathlib, holding the translated words and a structure with one field for each law,
   named as in the lock:

   ```lean
   structure Laws (S : Signature) : Prop where
     Postulate1 : ∀ (A B : S.Point), A ≠ B → ∃ L : S.Line, S.OnLine A L ∧ S.OnLine B L
     ...
     circles_meet : ∀ {A B : S.Point} {α β : S.Circle}, S.OnCircle A α →
       S.InsideCircle B α → S.InsideCircle A β → S.OnCircle B β → S.CirclesMeet α β
     ...
   ```

   The file is committed, so that anyone can read the laws as one structure, and CI runs
   the generator again and fails if its output differs from the committed file. Postulate
   5 stands apart from the other 86, as a structure of its own beside them, so that a
   hyperbolic plane can later satisfy the rest and fail it.
4. **Assemble the model.** Each law is proved in the plane as a theorem of its own, as
   here, and the generated file ends with

   ```lean
   theorem euclidean_laws : Laws Euclidean.plane := ⟨Euclidean.Postulate1, ...⟩
   theorem model_exists : ∃ S : Signature, Laws S := ⟨Euclidean.plane, euclidean_laws⟩
   ```

The library's 99 proofs do not change. Rewriting the library over a signature, with
wrappers that keep its present names, is a later and separate decision, and it would need
care not to blur the certificate: if every theorem took one `Laws` hypothesis bundling all
87 laws, Lean's dependency walk would report all 87 beneath every proof.

## How the translation is checked

A hash shows that a file has not changed. It does not show that a translation means what
the original means. Three checks do that.

- **The round trip, by the kernel.** [Check/Hand.lean](Check/Hand.lean) builds `original`,
  the signature whose fields are the library's own words (`Point := Elements.Point`, and
  so on), and asks, for each translated law,

  ```lean
  example : Model.Hand.circles_meet original = type_of% @Elements.Tacit.circles_meet := rfl
  ```

  and the same for each translated word. `type_of%` takes the declaration's statement and
  does not use the axiom. The kernel accepts the `rfl` only if the two are the same
  proposition, up to unfolding definitions; a dropped guard, two swapped arguments or a
  change in the order of the binders fails it, and the build with it. (Both were tried:
  Intersection 4 in System E's printed form, with "on or inside", and Intersection 5 with
  its two points exchanged.) Today this covers the four hand-translated laws and the three
  words they reach; the generator will write one such line for each of the 87 laws and 37
  words.
- **The round trip, by syntax.** The generator also translates each result back and
  compares it with the original expression exactly, which is stricter than the kernel's
  check: it notices a translation that is right only after unfolding.
- **Completeness.** The generator checks that the laws it wrote are exactly the axioms
  declared in `Elements.Foundations`, and exactly the lock's `[axioms]`, so that none is
  missing and none is extra.

One small decision would make every round trip exact. The eight magnitude laws quantify
over the kind (`∀ {k : Elements.Kind}`), and with two copies of `Kind` their round trip is
an equivalence proved case by case rather than `rfl`. If `Elements.Kind` moved into a file
of its own, with no opaque word, no axiom and no notation, the model could import that one
file and share the library's `Kind`.

## How the lock ties it

[lock.sha256](lock.sha256) holds the sha256 of `Certificate/axioms.lock`, as
[tests/model/lock.sha256](../tests/model/lock.sha256) does for the numerical harness. The
model's CI job compares it with the lock:

```sh
grep -v '^#' model/lock.sha256 | shasum -a 256 -c -
```

So any change to an axiom, or to a word an axiom reaches, fails the job until someone has
brought the model up to date: the translation, its checks, and the proofs in the plane of
the laws that changed. The round-trip checks then tie each translated law to the
declaration itself, more tightly than the hash can; the hash covers what the generator does
not yet reach. A law proposed for the foundations is proved here before it lands:
`exists_centre`, proposed in issue #59, is already proved in the plane
([Model/Euclidean/Centre.lean](Model/Euclidean/Centre.lean)), and its round-trip check
joins `Check/Hand.lean` in the change that declares it.

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
  own, which Mathlib's real numbers use. No project axiom and no `sorryAx` can pass. When
  `euclidean_laws` exists, it is audited the same way.
- **The library's rules on commands.** `Model/` uses none of the commands the library
  forbids ([FORMALIZATION](../docs/FORMALIZATION.md#7-the-foundations-and-the-policies-the-checks-enforce),
  section 7: `native_decide`, `implemented_by`, `unsafe` and the rest), and the audit
  catches a `sorry` beneath any listed proof. The generator is a Lean program and needs
  metaprogramming, so it will live in `Check/`, apart from the proofs.

When every law is proved, the claim this package supports will be: Lean checks that the
ordinary Euclidean plane satisfies every law in this revision's foundations, relative to
Lean's logic and Mathlib's construction of the real numbers. It will not show that a
formal statement captures what Euclid meant: that is the work of the review records.

## The order of the work: hardest laws first

Astra's third answer lists the laws whose proofs will settle the representation, and they
come before the easy laws are shared out:

| Group | Laws | State |
|---|---|---|
| Circle intersections | `circles_meet`, `circles_meet_of_on_inside_outside`, `circles_meet_same_side`, `circles_meet_opposite_side` | proved here |
| Line and circle crossings | `line_circle_between`, `line_circle_beyond`, `line_meets_circle_of_inside`, `line_meets_circle_of_opposite_sides` | to do |
| Angle addition, both ways | `angle_add_of_inside`, `inside_of_angle_add` | to do |
| Postulate 5 | the meeting on the stated side, not only a meeting | to do |
| Superposition | an isometry, with a reflection where the side needs one; and the soundness of whichever restricted rule is adopted | to do |
| Areas | `area_congruent`, `area_add_of_between`, `between_of_area_add`, with collinear and repeated corners | to do |
| Finite avoidance | the `avoid` lists of Postulate 2 and the Points rules: a line, an open region and a circumference are infinite | to do |

`CirclesMeet α α` is true, since a circle has two distinct points; the side laws are proved
for that case too, where both centres are one point and the line through them is any line
through it.

## The CI job

The coordinator adds it, in the pull request that lands this package. What it should run,
on `ubuntu-latest`, after checking out the repository and installing elan:

```sh
grep -v '^#' model/lock.sha256 | shasum -a 256 -c -
cd model
lake exe cache get
lake build
```

`lake build` builds both libraries, `Model` (with the audit) and `Check` (with the round
trips), and fails if any check in them fails; there is nothing else to run. On the machine
that built this package, from a fresh clone, `lake exe cache get` took about 65 seconds
(cloning the pinned Mathlib and its dependencies, downloading 9,031 files, 452 MB, and
unpacking them to 6.6 GB), and `lake build` 11 seconds, for this package and the library
files `Check` reads. A runner should expect a few minutes in all. Caching
`model/.lake/packages` between runs, keyed on `model/lake-manifest.json`, would save most
of the download.

## Thanks

To Astra, whose third answer set out this package's shape, the plane's readings and their
pitfalls, the translation checks and the order of the hard laws. To Jeremy Avigad, Edward
Dean and John Mumma, whose System E gives most of the laws, and to LeanEuclid (Logan
Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si), whose
corrected Intersection 4 is the form proved here. And to Mathlib's authors and
maintainers, on whose plane every proof here stands.
