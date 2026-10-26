# The formal model

Stoicheia's proofs rest on <!-- count:axioms -->48<!-- /count --> laws: Euclid's postulates, Definition 15 and the tacit rules,
each an `axiom` about seventeen `opaque` words, with their exact statements in
[Certificate/axioms.lock](../Certificate/axioms.lock). Lean checks that every proof follows
from the laws. Checking the proofs does not show that the laws can all be true at once.
[tests/model/MODEL.md](../tests/model/MODEL.md) argues that they can, law by law, by
reading the words in the ordinary plane, and tests each law there numerically. This
package gives a formal proof: a Lake package of its own, with Mathlib, in which the
words are the fields of a structure, the ordinary plane fills them, and Lean checks that
the plane satisfies each law.

**Where it stands.** The signature, the plane and all <!-- count:axioms -->48<!-- /count --> laws are represented in Lean.
The generator writes the library's elaborated declarations into one structure, `Laws`,
and the translation checks compare them with those declarations. The plane satisfies all
<!-- count:axioms -->48<!-- /count --> laws, including restricted superposition. The build also requires the vocabulary lock
and both model hashes to agree with the same revision.
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
| [lakefile.toml](lakefile.toml) | the package: Mathlib pinned to `v4.35.0`, the release for the toolchain both packages use; the library, read by `Check`, with four pure calculus modules shared by `Model`; and the files besides Lean imports that `Check` reads | |
| [Model/Signature.lean](Model/Signature.lean) | the seventeen words as the fields of `Signature`, and the words behind the magnitudes | nothing |
| [Model/Laws.lean](Model/Laws.lean) | **generated:** every law, and the defined words they reach, translated from the library; the structures `Neutral` and `Laws` | `Signature`, pure calculus syntax and semantics |
| [Model/Hand.lean](Model/Hand.lean) | the laws first proved in the plane, translated **by hand**, and `exists_centre`, proved in the plane before the library declared it | `Laws` |
| [Model/Laws/angles.lean](Model/Laws/angles.lean) | the ten angle laws, with `Collinear` and `IsRightAngle`, translated **by hand** | `Signature` |
| [Model/Laws/areas-p5.lean](Model/Laws/areas-p5.lean) | the eight area laws and Postulate 5, translated **by hand** | `Signature` |
| [Model/Laws/circles.lean](Model/Laws/circles.lean) | the 19 circle rules, translated **by hand** | `Model.Hand` |
| [Model/Laws/incidence.lean](Model/Laws/incidence.lean) | the incidence and line laws, and `Hand.LinesMeet`, **by hand** | `Signature`, `Hand` |
| [Model/Laws/intersections.lean](Model/Laws/intersections.lean) | the five line intersection rules and the four circle rules, and separate hand copies of `LinesMeet` and `LineMeetsCircle` | `Hand` |
| [Model/Laws/lengths.lean](Model/Laws/lengths.lean) | the three metric length laws, translated **by hand** | `Signature` |
| [Model/Laws/order.lean](Model/Laws/order.lean) | the fifteen order laws, Between 1 to 7 and the diagram-segment rules, **hand-translated** | `Signature` |
| [Model/Laws/sides.lean](Model/Laws/sides.lean) | the five same-side rules, four Pasch rules and three triple-incidence rules, translated **by hand** | `Signature` |
| [Model/Laws/superposition.lean](Model/Laws/superposition.lean) | the restricted rule and its interpretation **by hand**, with supporting placement mathematics | `Signature`, pure calculus semantics |
| [Model/Euclidean.lean](Model/Euclidean.lean) | the ordinary plane as a `Signature` | Mathlib |
| [Model/Euclidean/AngleAdd.lean](Model/Euclidean/AngleAdd.lean) | angle addition, both ways (diagram-angle rule 2), proved in the plane | Mathlib |
| [Model/Euclidean/AngleBasics.lean](Model/Euclidean/AngleBasics.lean) | the bridge from the plane's angle to Mathlib's, and the line through two points | Mathlib |
| [Model/Euclidean/Angles.lean](Model/Euclidean/Angles.lean) | Definition 15, Postulate 4, the two metric angle laws and diagram-angle rules 1, 3 and 4 proved in the plane | Mathlib |
| [Model/Euclidean/Areas.lean](Model/Euclidean/Areas.lean) | the eight area laws, including collinear and repeated corners, proved by determinants | Mathlib |
| [Model/Euclidean/Avoidance.lean](Model/Euclidean/Avoidance.lean) | Postulate 2 and all finite avoidance rules for lines, regions and circumferences proved in the plane | Mathlib |
| [Model/Euclidean/Centre.lean](Model/Euclidean/Centre.lean) | `exists_centre`, every circle has a centre, proved in the plane | Mathlib |
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
| [Model/Euclidean/Superposition.lean](Model/Euclidean/Superposition.lean) | restricted superposition from placement by isometry and reflection, its kept side by Same side 3 and Postulate 1, through `Rule.of_placement_of_join` | Mathlib, pure calculus soundness |
| [Model/Euclidean/TripleIncidence.lean](Model/Euclidean/TripleIncidence.lean) | Triple incidence 1 to 3 proved by signed determinants and affine sides | Mathlib |
| [Model/Assembly.lean](Model/Assembly.lean) | **generated:** `euclidean_laws`, all <!-- count:axioms -->48<!-- /count --> proofs gathered into `Laws`, and the unconditional `model_exists` | Mathlib |
| [Model/Audit.lean](Model/Audit.lean) | checked at every build: `Elements.Point` remains unknown, and every proof and the assembly have their pinned logical axioms | every module of `Model` |
| [Check/Angles.lean](Check/Angles.lean) | the hand-translated angle laws and their two words compared with the library and the generated laws | `Elements.Foundations`, `Elements.BookI.Prop13`, `Check.Hand`, the generator, `Model.Laws.angles` |
| [Check/AreasP5.lean](Check/AreasP5.lean) | the hand-translated area laws and Postulate 5 compared with the library and the generated laws | `Elements.Foundations`, `Check.Hand`, `Model.Laws.«areas-p5»` |
| [Check/Circles.lean](Check/Circles.lean) | the hand-translated circle rules compared with the library and the generated laws | `Elements.Foundations`, `Elements.BookI.Prop07`, `Elements.Figure.Circles`, `Elements.BookIII.Prop02`, `Check.Hand`, the generator, `Model.Laws.circles` |
| [Check/Generated.lean](Check/Generated.lean) | checked at every build: the lock, its hash and the axioms, and that the generated files are what the generator writes | `Elements.Foundations`, `Model.Signature`, the generator |
| [Check/Generator.lean](Check/Generator.lean) | the generator: reading the library, auditing shared declarations, source headers and compiled imports, translating, writing, and the checks it makes | Lean alone |
| [Check/Hand.lean](Check/Hand.lean) | each hand translation compared with the library's declaration and with the generated law | `Elements.Foundations`, `Model.Hand` |
| [Check/Incidence.lean](Check/Incidence.lean) | the hand-translated incidence and line laws, and `Hand.LinesMeet`, compared with the library and the generated laws | `Elements.Foundations`, `Elements.Figure.Circles`, `Check.Hand`, the generator, `Model.Laws.incidence` |
| [Check/Intersections.lean](Check/Intersections.lean) | the hand-translated intersection rules and their two words compared with the library and the generated laws | `Elements.BookI.Prop07`, `Elements.Figure.Circles`, `Elements.BookIII.Prop02`, `Check.Hand`, the generator, `Model.Laws.intersections` |
| [Check/Laws.lean](Check/Laws.lean) | **generated:** each generated law and word compared with the library's by the kernel | `Elements.Foundations`, `Model.Laws` |
| [Check/Lengths.lean](Check/Lengths.lean) | the hand-translated metric length laws compared with the library and the generated laws | `Elements.Foundations`, `Check.Hand`, `Model.Laws.lengths` |
| [Check/Order.lean](Check/Order.lean) | the hand-translated order laws compared with the library and the generated laws | `Elements.Foundations`, `Check.Hand`, `Model.Laws.order` |
| [Check/Original.lean](Check/Original.lean) | `original`, the library's own words as a signature | `Elements.Foundations`, `Model.Signature` |
| [Check/RoundTrip.lean](Check/RoundTrip.lean) | checked at every build: each generated law and word translated back and compared with the library's by syntax; planted faults it must refuse | `Elements.Foundations`, `Model.Laws`, `Model.Hand`, seven files of `Model/Laws/` (all but angles and superposition), the generator |
| [Check/Sides.lean](Check/Sides.lean) | the hand-translated same-side, Pasch and triple-incidence rules compared with the library and the generated laws | `Elements.Figure.Circles`, `Check.Hand`, the generator, `Model.Laws.sides` |
| [Check/Superposition.lean](Check/Superposition.lean) | the restricted rule, its interpretation and supporting words compared with the library and the generated definitions | `Elements.Foundations`, `Check.Hand`, `Model.Laws.superposition` |
| [Check/Write.lean](Check/Write.lean) | run by hand, never built: writes the generated files | as `Check/Generated.lean` |
| [lock.sha256](lock.sha256) | the hash of the lock the model was last checked against | |

`Model/` may import exactly these four library modules:
`Elements.Foundations.Superposition.Syntax`, `.Semantics`, `.Soundness` and `.Restriction`.
They share the generic symbolic calculus and its logical proofs. They contain no geometric
words or project axioms. `Elements.primitives` remains outside that boundary: it is
translated into `Model.Signature.primitives`, which interprets the calculus over `S`.
The superposition law applies the shared `Rule` to this generated interpretation.

`Check/` imports no Mathlib. The three generated files are committed so that anyone can
read them, and `lake build` fails while any differs from what the generator writes.

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
   which must be exactly the <!-- count:axioms -->48<!-- /count --> names in the lock's `[axioms]`, as the expression Lean
   elaborated: binders, binder kinds (implicit or explicit), the order of the binders, every
   guard, every instance argument. It checks too that the lock prints each one's statement
   as Lean prints it now, and each word they reach as the lock's `[vocabulary]` has it, so
   the laws it translates are exactly those the lock records.
2. **Translate by structure.** It walks each expression and replaces each of the seventeen
   opaque constants by the matching field of a signature `S`, and `Elements.Kind` and its
   constructors by `Model.Kind`'s. A project definition the law reaches, such as
   `Triangle`, `Collinear`, `CirclesMeet`, `IsRightAngle` or the magnitude instances,
   among them the present definition of `≤`, is translated the same way, once, into a
   definition over `S` in dependency order. Their vocabulary comprises
   the seventeen opaque words, `Kind` and its three constructors, 15 definitions over
   the signature, and the shared calculus declarations. Eight of those definitions,
   the carriers of the magnitudes and their instances, are
   written by hand in `Model/Signature.lean`, since the signature's own fields need them to
   be used at all, and the generator checks them rather than writing them; the other seven
   it writes, including `primitives`. The old root word `Triangle` is no longer reached
   by the laws; the shared calculus has its generic interpretation. Lean's own constants,
   those of `Init` (`Eq`, `Ne`, `And`, `Or`, `Not`,
   `Exists`, `List`, `Membership.mem`, `LT.lt`, `HAdd.hAdd`, `OfNat.ofNat` and the like),
   stay as they are. The four shared modules described below keep their declarations
   unchanged too. **Any other constant is an error.** (One detail: Lean declares the
   library's `MagnitudeImpl` at every universe, since it generalizes the level of
   `NonemptyType`, and `Magnitude` uses it at universe 0; the field is that one, and the
   translation insists on it.)
3. **Write a file a reader can read.** The output is plain Lean with no Mathlib: the seven
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

   Postulate 5 stands apart from the other <!-- count:axioms-but-postulate-5 -->47<!-- /count -->, so that a hyperbolic plane can later satisfy
   `Neutral` and fail it; so would any rule the library declared in
   `Elements.Tacit.Euclidean`, for the plane alone, of which there is none. The file's header
   records the sha256 of the lock it was written from, with a table of the reached words and what
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

The generator shares four modules for the restricted calculus of
[brief 0009](../docs/briefs/0009-superposition.md):
`Elements.Foundations.Superposition.Syntax`,
`Elements.Foundations.Superposition.Semantics`,
`Elements.Foundations.Superposition.Soundness` and
`Elements.Foundations.Superposition.Restriction`. A declaration qualifies by its declaring
canonical module name, never by its namespace. Its translation keeps its name and universe
arguments in both directions, and the generated laws import the shared modules their
vocabulary reaches.
Before translating, the generator audits every declaration in every imported shared module,
including declarations no law reaches. It follows types and values transitively, including
theorem proofs, opaque values, constructors and recursor rules. Every dependency must come
from those four modules or `Init`; the only permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`, and `sorryAx` is refused. All four modules are present.
The generic checks also work when those modules are absent, as they were when the tooling
landed first: an empty shared-import list adds no text to the generated header.

`checkModelImports`, called from `Check/RoundTrip.lean`, also reads the headers of
`Model.lean`, every Lean file under `Model/`, and each of the four pure source files that
exists. A Model file may import only other Model modules, those four pure modules, and
the external module roots listed in `modelImportPackages` in
[Check/Generator.lean](Check/Generator.lean). That single list records Lean's permitted
roots and the library roots supplied by Mathlib and its dependencies, checked against
the pinned packages in `lake-manifest.json`. Every other root is refused, including
`Check`, `Staging`, `Audit` and `Certificate`. Pure files may import only each other and
`Init`. Before applying any root permission, the audit requires a canonical module name:
every component is a non-empty string, with no `/`, `\`, NUL or colon, neither `.` nor
`..`, and no trailing dot or space. Anonymous names and numeric components are refused.
Harmless escaped identifiers, including `areas-p5`, remain valid. The same predicate guards
core, shared and project declaration membership, foundation collection and shared headers.

Before selecting source files, the audit checks the directory listings under `Model/`
and `../Elements/Foundations/`, together with the actual spelling of `Model.lean`.
Every filename and directory component must use only ASCII letters, digits, `_`, `-` and
`.`; empty components, `.` and `..` are refused. This applies to non-source files too.
Unicode names are refused before case comparison: ASCII lowercasing alone misses aliases
such as `ſyntax.lean`, which can resolve to `Syntax.lean`, and the Kelvin sign, which can
resolve to `K`. Among ASCII names, any extension equal to `lean` ignoring case must be
exactly `.lean`; `.LEAN` and mixed spellings are errors. Distinct paths equal after
lowercasing are errors, including directory components. A case variant of a pure module's
prescribed path is refused even when the canonical spelling is absent.

The four pure sources are located independently of those listings: the audit probes
`../Elements/Foundations/Superposition/Syntax.lean`, `Semantics.lean`, `Soundness.lean`
and `Restriction.lean` by their canonical paths and reads whatever files those paths open.
Each receives the stricter pure-module import check. Model sources are read through the
validated ASCII paths, with `Model.lean` required in its canonical spelling. The import
decision also validates supplied source paths before assigning import permissions. Listing
and header regressions use data, so they run without the pure modules or a folding filesystem.

Lean 4.35's `modToFilePath` joins each component as a path: `..` can leave a package and
an absolute component replaces the path before it. Colons and trailing dots or spaces have
additional drive, stream or normalisation meanings on Windows, so they are refused on every
platform. This closes the escaped-component routes, including
`Model.«..».Check.Original` and an absolute path beneath `Init`.

`checkModelImportClosure`, also called from `Check/RoundTrip.lean`, separately follows
the **graph of compiled imports** from `Model`. It resolves each module with `findOLean`
on the current search path and reads the imports in its `.olean` with `readModuleData`.
Lean 4.35's `mkModuleData` copies the whole import header into that first part, including
non-public imports; the graph check follows every edge, regardless of import modifiers.
It checks each name before looking up its file, using the same canonical-name predicate
and Model whitelist as the source audit. Repeated imports are visited once. The source
audit remains necessary for files that nothing imports, and keeps the stricter import
boundary for the pure modules.

The compiled closure reaches `Lake.Util.Version`, through the pinned Mathlib and
ImportGraph imports. `Lake` ships with Lean's toolchain, as `Init`, `Std` and `Lean` do, so
it is among the permitted roots of both import checks; it is not trusted as Lean's own by
`isLeanCore`, which still requires a canonical `Init` name with no package identifier.
The regression cases accept `Lake.Util.Version` in Model source headers and compiled
closures, refuse it in a pure source, and keep it outside the core translation boundary.

A passing check establishes that names in the resolved compiled-import graph stay within the permitted
boundary. **It does not authenticate the files on the search path.** It does not establish
that a compiled file matches a source, authenticate external dependencies or symlink targets,
or recover an earlier environment's import artefacts. Those still depend on the configured
build and search path. Lean 4.35 exposes an imported module's optional package identifier
through `Environment.getModulePackageByIdx?`. All 653 `Init` modules in the installed pinned
toolchain have no identifier, so `isLeanCore` requires both a canonical `Init` name and no
package identifier. This refuses a named package, including `stoicheia`, posing as `Init`.
It does not authenticate an unlabelled replacement. Lean's environment retains no resolved
`.olean` path. `findOLean` searches the current path again; it does not recover the loaded
file's provenance, and Lake can supply explicit import artefacts.

Lake 4.35 defaults the Model library's roots to `Model` and its globs to that root alone.
It builds `Model.lean` and recursively follows imports. The compiled check compares this
closure with the source audit's complete Model list and refuses any source module the
root does not reach: under this configuration it is not otherwise built. If the library's
globs grow, the graph's starting modules and coverage check must grow with them.
The source audit includes the root outside `Model/` and checks unimported files too.
Lean's own header parser reads both legacy headers without `module` and headers with
`module`, comments, blank lines, `public import` and the other import modifiers, stopping
at the first body command; a malformed header is an error. `checkModelImportsWith` makes
the decision from file paths and imports, so planted cases use the same parser and
decision without creating files or loading their imports.

Check continues to import only Lean, the edition and the plain-Lean part of Model, with
no Mathlib imports. Its Lake `needs` now includes `Model:leanArts`, so the whole Model
library is built before any Check module runs, even when a Check module is built directly.
The graph reader examines those compiled files without importing their declarations or
running their initialisers. This prerequisite adds no Lean import edge: Check's compiled
closure still contains only `Check`, `Elements`, `Init`, `Lean`, `Model` and `Std` modules.
The normal build is acyclic because Model imports no Check module. A forbidden Model import
of Check creates a build dependency cycle and is refused by Lake before the audits run.
With an unimported `Model/Uppercase.LEAN` containing `import Check.Original`, the source
audit refuses the non-canonical extension. Importing that fixture from `Model.lean` instead
produces Lake's `build cycle detected` refusal on a case-insensitive filesystem.

The Check library registers `Model.lean` and every case variant of the `.lean` extension
under `Model/` and `../Elements/Foundations/` as text inputs in
[lakefile.toml](lakefile.toml). Both source-directory filters enumerate all sixteen ASCII
spellings, so adding a `.LEAN` file also invalidates the checks. The separate plane-proof
input still selects `.lean`. The existing foundations directory is used because Lake
rejects an input directory that does not exist, and its `Superposition/` subdirectory did
not exist on main when the input was added; this input includes all four pure sources when present, as well as other
foundation sources.

Lake 4.35 filters directory entries before sorting them and combining their content hashes.
Adding or removing a selected file, including a same-content rename from `.txt` to `.lean`
or `.LEAN`, or back, changes that list. This catches the first pure module arriving by such
a rename.
File paths are trace captions, not part of the hash: a rename within the selected set can
still replay a cached result when the ordered contents stay the same. Text hashes normalise
line endings, and a timestamp-only touch can also replay a result. Changes to the selected
contents otherwise rebuild the checks. CI's fresh build runs every check, including the
whole import audit, regardless of local cache traces.
Non-source entries are checked when the audit runs, but are outside the extension-filtered
Lake inputs; changing those entries alone need not rerun a cached check.

The library keeps its geometric words; I.4 and I.8 use the restricted rule.
Rewriting the library over a signature, with
wrappers that keep its present names, is a later and separate decision, and it would need
care not to blur the certificate: if every theorem took one `Laws` hypothesis bundling all
<!-- count:axioms -->48<!-- /count --> laws, Lean's dependency walk would report all <!-- count:axioms -->48<!-- /count --> beneath every proof.

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
  it. This covers all <!-- count:axioms -->48<!-- /count --> laws and all 15 defined words they reach. The family checks in
  `Check/` retain the original library checks. They also compare each hand-translated law
  with its generated field over any signature, except for the 40 retired rules. Eight were
  retired first: `adjacent_eq_of_right`, `not_same_side_of_circles_meet`,
  `centre_unique`, `inside_of_between`, `exists_point_outside_circle`,
  `line_meets_circle_of_opposite_sides`, `triple_incidence3` and `inside_of_angle_add`;
  31 more on 19 October 2026 (listed in [MODEL.md](../tests/model/MODEL.md)); and Circle 3,
  `outside_of_between`, on 24 October 2026, proved after III.2, with Circle 2, Points 9
  and Intersection 2 moved beside it, in `Elements/BookIII/Prop02.lean`, which the circle
  and intersection checks import. These are now theorems with the same names and types. Their hand translations are compared
  directly with the library declaration's type by `comparePlanted`, including binder kinds,
  which works for an axiom or a theorem and remains when a generated assumption field
  disappears. This includes Intersections 2 and 3, which reach `LineMeetsCircle`, a word no
  locked law reaches since their retirement and so one the generator no longer writes.
  Before translating their hand copy in `Model/Laws/intersections.lean`, `comparePlanted`
  checks its type and body against the library's definition, including binder kinds and
  without unfolding. It then compares both rules with their library declarations,
  including binder kinds. Their kernel comparisons through `original`, concrete plane
  proofs and pinned axiom audits remain. A guarded regression in
  `Check/RoundTrip.lean`, beside the other planted faults, confirms that making
  Intersection 3's point A explicit passes `rfl` but fails the structural comparison.
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
  with the generated laws by the kernel in their files of `Check/`, apart from the 49
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
  and the fourth pass the kernel's `rfl`, which the file shows too. `comparePlantedWord`
  also runs on two copies of the translated `Elements.Collinear` definition: the matching
  copy produces no message, and a copy with two points exchanged pins the exact refusal.
  Further cases pass copies of Init declarations to the purity checker without installing
  them in Lean's environment: an Init-only closure passes, while a transitive reference to `Elements.Point`
  in a type or value, a dependency found only in an opaque value or a recursor rule,
  `sorryAx`, and an unapproved axiom are refused. Every helper called
  by `run_cmd` is defined in `Check/Generator.lean`. `plantPureDependency` accepts any
  definition as its root and puts a named dependency in a copy of its type or value.
  The production identity check still refuses `Nat.rec`, which is not shared.
  Parameterised variants extend the production module list with stand-ins to exercise
  successful identity entries in the plan, and forward and reverse translation with zero,
  symbolic and compound universe arguments, before the calculus arrives.
  `List.filterMap` tests two universe arguments; `Model.Kind.rec` tests a shared name
  outside `Elements`, including the residual model-name check. The module-root collector
  accepts an Init module and finds a planted dependency in a declaration no law uses,
  without receiving that declaration as an explicit audit root. These module-root fixtures
  also retain the production list, so the same cases can run after the calculus arrives.
  The header-printer fixtures exercise a non-empty shared-import header using explicit
  stand-in reached words, and build no translation plan. Production keeps the four-module
  boundary throughout.
  Import cases accept the real tree and permitted headers, and refuse geometric imports,
  `Check.Original` in a legacy `Model.lean` header, `Staging`, `Audit`, `Certificate`, an
  unknown root, a module below an approved pure module, and Mathlib in a pure file.
  Escaped traversal and absolute-path headers are refused. A matrix checks empty, dot,
  separator, NUL, drive, stream and trailing-dot or trailing-space components in root,
  intermediate and final positions, through the predicate and import decisions; escaped
  strings also pass through Lean's header parser. Anonymous and numeric names are tested
  directly. Planted declaring-module lookups for `Elements.Point` and `Elements.Collinear`
  exercise the same core and sharing decisions as production, without installing a module.
  Core cases also refuse canonical names with a named package and accept actual Init
  declarations. Canonical names, including harmless escaped identifiers, remain accepted.
  Directory listings supplied as data refuse upper-case and mixed-case extensions, names
  differing only in case, and directory-component aliases, in Model and the foundations.
  Listings and headers also refuse long-s aliases of pure and Model sources, Kelvin-sign
  aliases and other non-ASCII filenames. Canonical ASCII names remain accepted. A listing
  case checks a non-ASCII directory component and another checks a non-source filename.
  Compiled-import cases require the real closure to pass and refuse planted closures containing
  `Check.Original`, `Elements.Foundations.Words` (the module declaring `Elements.Point`),
  and a non-canonical module name. A coverage case refuses an unimported Model source.
  A path regression checks that both relative and absolute Check filenames locate the
  model package.
  The real calculus cases also refuse a changed placement guard, angle and area swapped
  in the interpretation, and a declaration claimed as shared by namespace alone.
  `plantPureDependency` plants `Elements.Point`, `Elements.Tacit.superposition` and
  `sorryAx` separately in copies of `Elements.Superposition.guards`; all three are refused.
  `checkSharedIdentity` checks `Elements.Superposition.Atom.rec` in the production plan,
  preserving zero, symbolic and compound universe arguments in both directions.

The eight magnitude laws quantify over the kind (`∀ {k : Elements.Kind}`), and with two
copies of `Kind` their round trip is an equivalence, not `rfl`. Each direction is the other
statement itself, put at the matching kind, with no other step, so the check is the same
up to relabelling the kinds; a wrong translation of `add_lt_add_right`, with `c` added on
the left, fails it. One small decision would make even these round trips `rfl`: if
`Elements.Kind` moved into a file of its own, a Lean `module`, as every file of `Model/`
is, with no opaque word, no axiom and no notation, the model could share `Kind` too,
subject to a separate approval of that import boundary. It is not among the four pure
modules shared for superposition.

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
`exists_centre`, proposed in issue #59, was proved in the plane
([Model/Euclidean/Centre.lean](Model/Euclidean/Centre.lean)) before the library declared it.
In the change that declared it, the generator wrote its law, the assembly gathered
`Euclidean.exists_centre`, which is named as its field, `Check/RoundTrip.lean` compared the
hand translation with the generated law, and its kernel round trip joined `Check/Hand.lean`.

## What the proofs rest on

A model is evidence only if its proofs do not use the laws they are meant to satisfy.
Three things make sure of that.

- **An exact import boundary.** The source and compiled-import audits above restrict the
  whole Model library, including its root, to the declared boundary: from the library, the
  four pure modules alone. [Model/Audit.lean](Model/Audit.lean) also imports the model's
  proof modules and asks Lean for `Elements.Point`, and `#guard_msgs` fails the build unless
  the answer is "unknown identifier". The compiled graph check covers indirect imports,
  including dependencies of external modules; its source coverage check refuses any Model
  source outside that graph. The generator separately audits every shared declaration's
  transitive dependencies.
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
  `extern`, `unsafe`, `set_option debug.…`). The source scan in `check_fidelity.py` reads
  `Model/` and `Check/` too, with the one generator allowance in `Check/` described in
  [FORMALIZATION, section 7](../docs/FORMALIZATION.md#7-the-foundations-and-the-policies-the-checks-enforce);
  review still reads what a word scan cannot see.

The claim this package supports is: Lean checks that the
ordinary Euclidean plane satisfies every law in this revision's foundations, relative to
Lean's logic and Mathlib's construction of the real numbers. It does not show that a
formal statement captures what Euclid meant: that is the work of the review records.

## The order of the work: hardest laws first

Astra's third answer listed the laws whose proofs would settle the representation, and they
were taken first. Each retained axiom proved here is gathered into `euclidean_laws`
by the generator, and `lake build` fails until it has been (`lake lean Check/Write.lean`).
The table also includes the 40 former axioms now proved in the library, whose
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
| Superposition | `superposition`: the restricted rule, from `superposition_placement`, Same side 3, Postulate 1 and `Rule.of_placement_of_join` | proved here |
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

The generated [assembly](Model/Assembly.lean) supplies **<!-- count:axioms -->48<!-- /count --> of the <!-- count:axioms -->48<!-- /count --> locked laws** from
proofs in the plane. This list counts each law once, even where two families supply a proof.
Names other than `Definition15` and the postulates are in `Elements.Tacit` in the lock.
The 40 retired rules listed above also retain their concrete plane proofs and audits,
as derived facts outside the generated assumption fields and this table.

| Proof file in `Model/Euclidean/` | Count | Locked laws proved |
|---|---:|---|
| [AngleAdd.lean](Model/Euclidean/AngleAdd.lean) | 1 | `angle_add_of_inside` |
| [Angles.lean](Model/Euclidean/Angles.lean) | 6 | `Postulate4`, `angle_eq_of_same_rays`, `angle_eq_zero_of_same_ray`, `angle_le_two_right`, `angle_symm`, `same_ray_of_angle_eq_zero` |
| [Areas.lean](Model/Euclidean/Areas.lean) | 6 | `area_add_of_between`, `area_congruent`, `area_degenerate`, `area_eq_zero_of_on_line`, `area_rotate`, `on_line_of_area_eq_zero` |
| [Avoidance.lean](Model/Euclidean/Avoidance.lean) | 4 | `Postulate2`, `exists_point`, `exists_point_inside_circle`, `exists_point_on_line` |
| [Centre.lean](Model/Euclidean/Centre.lean) | 1 | `exists_centre` |
| [CircleBasics.lean](Model/Euclidean/CircleBasics.lean) | 2 | `Definition15`, `Postulate3` |
| [CircleRules.lean](Model/Euclidean/CircleRules.lean) | 1 | `between_of_inside_chord` |
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
| [Superposition.lean](Model/Euclidean/Superposition.lean) | 1 | `superposition`; `superposition_placement` is supporting mathematics and is not counted as another law |

**No locked laws remain.** `euclidean_laws` has no hypotheses, and the package provides
the unconditional theorem `model_exists : ∃ S : Signature, Laws S`.

The overlapping circle and intersection proofs are retained with `_circles` and
`_intersections` suffixes, and the second proof of Definition 15 with `_angles`.
Their hand translations retain the same statements under corresponding names. Each has
its own original-declaration check, a generated-law or direct syntactic comparison as
described above, and its own pinned axiom audit.
The hand copies of `LinesMeet` and `LineMeetsCircle` also remain under distinct names.
`LinesMeet` has an equality check against the generated word over every signature;
`LineMeetsCircle`, which no locked law reaches now, so the generator no longer writes it,
is checked against the library's definition by `comparePlanted`, as above, and by `rfl`
at the original signature. Superposition adds
one supporting theorem, `superposition_placement`, with its own pinned axiom audit; the
law count remains <!-- count:axioms -->48<!-- /count -->. The restricted rule, `euclidean_laws` and `model_exists` all have
the same three logical axioms pinned by the audit.

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
cd ..
python3 scripts/check_model_kernel.py --self-test
python3 scripts/check_model_kernel.py
```

`lake build` builds both libraries, `Model` (with the assembly and the audit) and `Check`
(with the generator's checks and the round trips), and fails if any check in them fails;
the generator runs inside the build.

Then [scripts/check_model_kernel.py](../scripts/check_model_kernel.py) checks the compiled
proofs a second time, apart from the build (#121), in two replays through Lean's kernel by
Lean's leanchecker, from the pinned toolchain. The first replays every declaration of every
compiled module of `Model` and `Check`, private declarations included, into the environment
of the module's imports. It runs as [scripts/check_kernel.py](../scripts/check_kernel.py)
runs it for `Elements`, but without `--fresh`, so that environment is loaded from the
compiled files, not replayed. The second runs with `--fresh` on `Check`, which never imports
Mathlib, and replays every declaration of `Check`'s whole environment from nothing, into an
empty one: Lean's own library as `Check` loads it (`Init`, `Std` and `Lean`, through
`Check/Generator.lean`'s `import Lean`), the library's modules that `Check` imports, the
plain-Lean part of `Model`, and `Check` itself. So `Model`'s modules over Mathlib are
replayed into an environment loaded with Mathlib's, and `Check`, with all it loads, from
nothing. The first replay still covers `Check`, since it accounts for every compiled module
by name: a module compiled but not imported by `Check.lean` is one the second would never
load.

The declarations of Mathlib, and of the packages it requires, are left to Mathlib's own
checks, a daily job that replays Mathlib and Batteries from nothing with leanchecker and
checks Mathlib with nanoda, on Mathlib's master branch rather than the release pinned here.
Of Lean's own library, everything that `Check` loads is replayed here from nothing, on the
pinned toolchain: all 1,227 of its `Lean` modules, the 435 that lie outside Mathlib's
environment among them. All that `Model` loads lies within it but five of `Lake`'s modules,
which `Model` loads through Mathlib (`Lake.Build.Trace`, `Lake.Config.Glob`,
`Lake.Util.Date`, `Lake.Util.String` and `Lake.Util.Version`); those lie within Mathlib's
environment, which Mathlib's daily job replays, on Mathlib's toolchain rather than the one
pinned here. `Init`, and the library's declarations that `Check` imports, are replayed from
nothing by `check_kernel.py` too, in the `check` job, from that job's own build.

The script lists the modules from the files, the two roots and every module under `Model/`
and `Check/`, and walks the package's build folder (`.lake/build/lib/lean`) for every
compiled module, so a new module is never missed. It compares the list with the modules
leanchecker reports replaying in the first replay: a source with no compiled file, a module
compiled outside the two libraries (from a new root or a new library in `lakefile.toml`), a
build not up to date with its sources, and a compiled module whose source is gone each fail
it. For the freshness check, every compiled source is an explicit `lake build --no-build`
target, including a module its library root does not import: an old compiled file cannot
hide a later edit to that source. Only `Check/Write.lean` is not replayed, by name, since
`lake build` never compiles it.
And what is replayed is the package's own compiled files, not a copy of them: each module
root lies in one folder of Lean's search path, since Lean loads a module from the first
folder that holds its root. So before either replay the script reads the search path that
leanchecker gets through `lake env`, and a root (a folder, or an `.olean` file, at the top
of one of its folders) found in two folders fails the check, naming both: a copy of `Check`
in the build folder of a package that the model requires, earlier on the path, would
otherwise be replayed in place of the package's own. Names are compared without case, as
macOS's file system compares them by default. leanchecker runs the same kernel as
`lake build`, so the replay catches a declaration that reached a compiled file without the
kernel's check, not a fault in the kernel; and it replays any axiom it meets, so which
axioms the proofs rest on stays the audit's check ([above](#what-the-proofs-rest-on)). Its
self-test, which runs first, needs no Mathlib: in a temporary directory outside the
repository it builds small packages of the model's shape that import only Lean, adds a
theorem of `False`, proved by `True.intro`, from a `run_cmd` with the kernel's check
switched off (`debug.skipKernelTC`), once in a `Check` file and once in a `Model` module,
and requires that `lake build` accept each and that the check fail, naming the module and
the declaration. Two more plants lie outside the libraries' names, where leanchecker, given
the two roots, would never look: in a second root of `Model` and in a third library that
`Check` imports. The check must fail on each at its walk of the build folder, naming the
module. Another plant lies in a package of its own that `Check` requires and imports, as
the model's `Check` requires the edition: the walk and the first replay pass it, and the
replay from nothing must fail on it, naming the declaration. A last plant, in a `Check`
file, comes after a copy of `Check`, compiled without it, is put in the build folder of
such a required package, earlier on the search path: both replays would replay the copy and
pass it, so the check must fail before them, naming `Check` and both folders. A control, a
source never compiled and a compiled module without its source are tested the same way. The
control also compiles a module that its root does not import; an edit to the same source
without another build must then fail, naming the module. Every command runs in a process
group of its own. On interruption or termination the script stops that whole group and
waits for its command before its temporary directory is removed, as it does when the replay
from nothing reaches its time limit; the self-test times out a command, interrupts an
untimed one and terminates another, each with a descendant, and requires each descendant to
stop. We thank Kim Morrison and Sebastian Ullrich warmly for leanchecker, which began as
Kim Morrison's [lean4checker](https://github.com/leanprover/lean4checker) and now ships
with Lean.

On the machine that built this package, from a fresh clone, `lake exe cache get` took about
65 seconds (cloning the pinned Mathlib and its dependencies, downloading 9,031 files, 452 MB,
and unpacking them to 6.6 GB). With the generator, `lake build` took 11 to 13 seconds of
wall time in two runs, for this package and the library files `Check` reads. Of the modules
the generator added, `Check/Generator.lean` took about 2 seconds to compile,
`Check/Generated.lean` about 1 to run the generator and compare its output,
`Check/RoundTrip.lean` about 1, `Check/Laws.lean` under half a second and
`Model/Assembly.lean` 1 to 2, much of it alongside the proofs in the plane; a build with
nothing changed took a second or so. The first replay, of every compiled module, took about
a minute (45 and 53 seconds for leanchecker alone, and 58 to 77 for the whole script, before
it had the second replay, in four runs, on a machine busy with other builds). It replays
modules in parallel, each loading its imports' environment afresh, Mathlib's for each
module that imports it: on sixteen threads one run reached a 49 GB footprint, so the script
runs it on two, where it peaked near 2.6 GB. The replay from nothing of `Check`'s
environment is one task, which more threads do not speed: it took 95 seconds on two threads
and 112 on four, with a resident peak of 1.5 GB, on the same machine, busier still. With
both, the whole script took 205 seconds, and its self-test 162, since its control and its
plant in a required package each replay Lean's library from nothing. A runner should
expect several minutes for the step, which the job's limit of 30 minutes leaves room for.
The script stops the replay from nothing after 15 minutes and fails, asking whether `Check`
now imports Mathlib, so that the job ends with a named cause rather than at its limit.

Between runs the job caches two directories, keyed on `model/lake-manifest.json`:
`model/.lake/packages`, which holds the pinned clones and the unpacked build, and
`~/.cache/mathlib`, where `lake exe cache get` keeps what it downloads and looks before
downloading again. After a restore, `lake exe cache get` downloads nothing and unpacks
nothing. The job stops after 30 minutes, since without Mathlib's prebuilt files
`lake build` would compile Mathlib from source for hours.

`formal-model` is a required check. The five checks required by GitHub, and the present
distinction between that ruleset and the merge gate's local presence test, are kept in
[WORKFLOW](../docs/WORKFLOW.md#landing-work-pull-requests), section 10.

## Thanks

To Astra, whose third answer set out this package's shape, the plane's readings and their
pitfalls, the translation checks and the order of the hard laws. To Jeremy Avigad, Edward
Dean and John Mumma, whose System E gives most of the laws, and to LeanEuclid (Logan
Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si), whose
corrected Intersection 4 is the form proved here. And to Mathlib's authors and
maintainers, on whose plane every proof here stands: among them, for the circle rules,
Yaël Dillies and Yury Kudryashov, whose strict convexity gives Circle 1 to 3, and Johannes
Hölzl, Mario Carneiro and Kyle Miller, whose finite sets give the avoidance rules.
