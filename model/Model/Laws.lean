module

public import Model.Signature
public import Elements.Foundations.Superposition.Syntax
public import Elements.Foundations.Superposition.Semantics

/-!
# The laws

**This file is generated: do not edit it.** `Check/Generator.lean` writes it from the axioms
declared in `Elements/Foundations/`, as Lean elaborated them, and `lake build` fails while it
differs from what the generator writes. To write it again, run `lake lean Check/Write.lean` in
`model/`. The [README](../README.md) says how the laws are translated and checked.

It was written from the lock, `Certificate/axioms.lock`, whose sha256 is
`9265a082f7114a20b41ae39690f326a61827250f477e80aad8e8fd99c159e0cb`,
the hash that `model/lock.sha256` holds. The lock has 48 laws, and they reach 152 words of its
vocabulary. Each law here is the library's axiom with the words of a signature `S` put for the
library's words:

| The library's word | Here |
|---|---|
| `Elements.Angle` | `S.Angle`, in `Model/Signature.lean` |
| `Elements.Area` | `S.Area`, in `Model/Signature.lean` |
| `Elements.Between` | `S.Between`, a field of `Signature` |
| `Elements.Centre` | `S.Centre`, a field of `Signature` |
| `Elements.Circle` | `S.Circle`, a field of `Signature` |
| `Elements.CirclesMeet` | `S.CirclesMeet`, below |
| `Elements.Collinear` | `S.Collinear`, below |
| `Elements.InsideCircle` | `S.InsideCircle`, a field of `Signature` |
| `Elements.IsRightAngle` | `S.IsRightAngle`, below |
| `Elements.Kind` | `Kind` |
| `Elements.Kind.angle` | `Kind.angle` |
| `Elements.Kind.area` | `Kind.area` |
| `Elements.Kind.length` | `Kind.length` |
| `Elements.Length` | `S.Length`, in `Model/Signature.lean` |
| `Elements.Line` | `S.Line`, a field of `Signature` |
| `Elements.LinesMeet` | `S.LinesMeet`, below |
| `Elements.Magnitude` | `S.Magnitude`, in `Model/Signature.lean` |
| `Elements.Magnitude.add` | `S.add`, a field of `Signature` |
| `Elements.Magnitude.lt` | `S.lt`, a field of `Signature` |
| `Elements.Magnitude.zero` | `S.zero`, a field of `Signature` |
| `Elements.MagnitudeImpl` | `S.MagnitudeImpl`, a field of `Signature` |
| `Elements.OnCircle` | `S.OnCircle`, a field of `Signature` |
| `Elements.OnLine` | `S.OnLine`, a field of `Signature` |
| `Elements.OppositeSides` | `S.OppositeSides`, below |
| `Elements.OutsideCircle` | `S.OutsideCircle`, below |
| `Elements.Point` | `S.Point`, a field of `Signature` |
| `Elements.SameSide` | `S.SameSide`, a field of `Signature` |
| `Elements.Superposition.Atom` | `Elements.Superposition.Atom`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.Holds` | `Elements.Superposition.Atom.Holds`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.Holds.match_1` | `Elements.Superposition.Atom.Holds.match_1`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.angle` | `Elements.Superposition.Atom.angle`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.area` | `Elements.Superposition.Atom.area`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.between` | `Elements.Superposition.Atom.between`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.casesOn` | `Elements.Superposition.Atom.casesOn`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.eq` | `Elements.Superposition.Atom.eq`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.len` | `Elements.Superposition.Atom.len`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.map` | `Elements.Superposition.Atom.map`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.map.match_1` | `Elements.Superposition.Atom.map.match_1`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.onLine` | `Elements.Superposition.Atom.onLine`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.rec` | `Elements.Superposition.Atom.rec`, shared unchanged from its pure module |
| `Elements.Superposition.Atom.sameSide` | `Elements.Superposition.Atom.sameSide`, shared unchanged from its pure module |
| `Elements.Superposition.Cited` | `Elements.Superposition.Cited`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.Holds` | `Elements.Superposition.Cited.Holds`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.angleSymm` | `Elements.Superposition.Cited.angleSymm`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.areaCongruent` | `Elements.Superposition.Cited.areaCongruent`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.casesOn` | `Elements.Superposition.Cited.casesOn`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.law` | `Elements.Superposition.Cited.law`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.law.match_1` | `Elements.Superposition.Cited.law.match_1`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.lenSymm` | `Elements.Superposition.Cited.lenSymm`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.neOfLen` | `Elements.Superposition.Cited.neOfLen`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.prop7` | `Elements.Superposition.Cited.prop7`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.rayOfAngle` | `Elements.Superposition.Cited.rayOfAngle`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.rayOfAngleSide` | `Elements.Superposition.Cited.rayOfAngleSide`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.rayUnique` | `Elements.Superposition.Cited.rayUnique`, shared unchanged from its pure module |
| `Elements.Superposition.Cited.rec` | `Elements.Superposition.Cited.rec`, shared unchanged from its pure module |
| `Elements.Superposition.Coincidence` | `Elements.Superposition.Coincidence`, shared unchanged from its pure module |
| `Elements.Superposition.Coincidence.step` | `Elements.Superposition.Coincidence.step`, shared unchanged from its pure module |
| `Elements.Superposition.Collinear` | `Elements.Superposition.Collinear`, shared unchanged from its pure module |
| `Elements.Superposition.Derives` | `Elements.Superposition.Derives`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.angle_congr` | `Elements.Superposition.Derives.angle_congr`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.angle_refl` | `Elements.Superposition.Derives.angle_refl`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.angle_symm` | `Elements.Superposition.Derives.angle_symm`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.angle_trans` | `Elements.Superposition.Derives.angle_trans`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.area_congr` | `Elements.Superposition.Derives.area_congr`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.area_refl` | `Elements.Superposition.Derives.area_refl`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.area_symm` | `Elements.Superposition.Derives.area_symm`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.area_trans` | `Elements.Superposition.Derives.area_trans`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.cite` | `Elements.Superposition.Derives.cite`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.eq_refl` | `Elements.Superposition.Derives.eq_refl`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.eq_symm` | `Elements.Superposition.Derives.eq_symm`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.given` | `Elements.Superposition.Derives.given`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.len_congr` | `Elements.Superposition.Derives.len_congr`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.len_refl` | `Elements.Superposition.Derives.len_refl`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.len_symm` | `Elements.Superposition.Derives.len_symm`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.len_trans` | `Elements.Superposition.Derives.len_trans`, shared unchanged from its pure module |
| `Elements.Superposition.Derives.ne_symm` | `Elements.Superposition.Derives.ne_symm`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation` | `Elements.Superposition.Interpretation`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.Angle` | `Elements.Superposition.Interpretation.Angle`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.Area` | `Elements.Superposition.Interpretation.Area`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.Between` | `Elements.Superposition.Interpretation.Between`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.Length` | `Elements.Superposition.Interpretation.Length`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.Line` | `Elements.Superposition.Interpretation.Line`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.OnLine` | `Elements.Superposition.Interpretation.OnLine`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.Point` | `Elements.Superposition.Interpretation.Point`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.SameSide` | `Elements.Superposition.Interpretation.SameSide`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.ang` | `Elements.Superposition.Interpretation.ang`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.area` | `Elements.Superposition.Interpretation.area`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.len` | `Elements.Superposition.Interpretation.len`, shared unchanged from its pure module |
| `Elements.Superposition.Interpretation.mk` | `Elements.Superposition.Interpretation.mk`, shared unchanged from its pure module |
| `Elements.Superposition.Law` | `Elements.Superposition.Law`, shared unchanged from its pure module |
| `Elements.Superposition.Law.Holds` | `Elements.Superposition.Law.Holds`, shared unchanged from its pure module |
| `Elements.Superposition.Law.conclusion` | `Elements.Superposition.Law.conclusion`, shared unchanged from its pure module |
| `Elements.Superposition.Law.mk` | `Elements.Superposition.Law.mk`, shared unchanged from its pure module |
| `Elements.Superposition.Law.premises` | `Elements.Superposition.Law.premises`, shared unchanged from its pure module |
| `Elements.Superposition.Letter` | `Elements.Superposition.Letter`, shared unchanged from its pure module |
| `Elements.Superposition.Letter.A` | `Elements.Superposition.Letter.A`, shared unchanged from its pure module |
| `Elements.Superposition.Letter.B` | `Elements.Superposition.Letter.B`, shared unchanged from its pure module |
| `Elements.Superposition.Letter.C` | `Elements.Superposition.Letter.C`, shared unchanged from its pure module |
| `Elements.Superposition.Letter.D` | `Elements.Superposition.Letter.D`, shared unchanged from its pure module |
| `Elements.Superposition.Letter.E` | `Elements.Superposition.Letter.E`, shared unchanged from its pure module |
| `Elements.Superposition.Letter.F` | `Elements.Superposition.Letter.F`, shared unchanged from its pure module |
| `Elements.Superposition.Letter.P` | `Elements.Superposition.Letter.P`, shared unchanged from its pure module |
| `Elements.Superposition.LineLetter` | `Elements.Superposition.LineLetter`, shared unchanged from its pure module |
| `Elements.Superposition.LineLetter.L` | `Elements.Superposition.LineLetter.L`, shared unchanged from its pure module |
| `Elements.Superposition.LineLetter.M` | `Elements.Superposition.LineLetter.M`, shared unchanged from its pure module |
| `Elements.Superposition.LineLetter.N` | `Elements.Superposition.LineLetter.N`, shared unchanged from its pure module |
| `Elements.Superposition.LineName` | `Elements.Superposition.LineName`, shared unchanged from its pure module |
| `Elements.Superposition.LineName.given` | `Elements.Superposition.LineName.given`, shared unchanged from its pure module |
| `Elements.Superposition.LineName.side` | `Elements.Superposition.LineName.side`, shared unchanged from its pure module |
| `Elements.Superposition.Lit` | `Elements.Superposition.Lit`, shared unchanged from its pure module |
| `Elements.Superposition.Lit.Holds` | `Elements.Superposition.Lit.Holds`, shared unchanged from its pure module |
| `Elements.Superposition.Lit.Holds.match_1` | `Elements.Superposition.Lit.Holds.match_1`, shared unchanged from its pure module |
| `Elements.Superposition.Lit.casesOn` | `Elements.Superposition.Lit.casesOn`, shared unchanged from its pure module |
| `Elements.Superposition.Lit.map` | `Elements.Superposition.Lit.map`, shared unchanged from its pure module |
| `Elements.Superposition.Lit.map.match_1` | `Elements.Superposition.Lit.map.match_1`, shared unchanged from its pure module |
| `Elements.Superposition.Lit.neg` | `Elements.Superposition.Lit.neg`, shared unchanged from its pure module |
| `Elements.Superposition.Lit.pos` | `Elements.Superposition.Lit.pos`, shared unchanged from its pure module |
| `Elements.Superposition.Lit.rec` | `Elements.Superposition.Lit.rec`, shared unchanged from its pure module |
| `Elements.Superposition.Metric` | `Elements.Superposition.Metric`, shared unchanged from its pure module |
| `Elements.Superposition.Metric.Holds` | `Elements.Superposition.Metric.Holds`, shared unchanged from its pure module |
| `Elements.Superposition.Metric.angle` | `Elements.Superposition.Metric.angle`, shared unchanged from its pure module |
| `Elements.Superposition.Metric.area` | `Elements.Superposition.Metric.area`, shared unchanged from its pure module |
| `Elements.Superposition.Metric.casesOn` | `Elements.Superposition.Metric.casesOn`, shared unchanged from its pure module |
| `Elements.Superposition.Metric.len` | `Elements.Superposition.Metric.len`, shared unchanged from its pure module |
| `Elements.Superposition.Metric.map` | `Elements.Superposition.Metric.map`, shared unchanged from its pure module |
| `Elements.Superposition.Metric.rec` | `Elements.Superposition.Metric.rec`, shared unchanged from its pure module |
| `Elements.Superposition.Metric.toAtom` | `Elements.Superposition.Metric.toAtom`, shared unchanged from its pure module |
| `Elements.Superposition.Metric.toAtom.match_1` | `Elements.Superposition.Metric.toAtom.match_1`, shared unchanged from its pure module |
| `Elements.Superposition.Name` | `Elements.Superposition.Name`, shared unchanged from its pure module |
| `Elements.Superposition.Name.given` | `Elements.Superposition.Name.given`, shared unchanged from its pure module |
| `Elements.Superposition.Name.second` | `Elements.Superposition.Name.second`, shared unchanged from its pure module |
| `Elements.Superposition.Name.third` | `Elements.Superposition.Name.third`, shared unchanged from its pure module |
| `Elements.Superposition.Rule` | `Elements.Superposition.Rule`, shared unchanged from its pure module |
| `Elements.Superposition.Rule.mk` | `Elements.Superposition.Rule.mk`, shared unchanged from its pure module |
| `Elements.Superposition.Triangle` | `Elements.Superposition.Triangle`, shared unchanged from its pure module |
| `Elements.Superposition.Val` | `Elements.Superposition.Val`, shared unchanged from its pure module |
| `Elements.Superposition.Val.line` | `Elements.Superposition.Val.line`, shared unchanged from its pure module |
| `Elements.Superposition.Val.mk` | `Elements.Superposition.Val.mk`, shared unchanged from its pure module |
| `Elements.Superposition.Val.pt` | `Elements.Superposition.Val.pt`, shared unchanged from its pure module |
| `Elements.Superposition.branch` | `Elements.Superposition.branch`, shared unchanged from its pure module |
| `Elements.Superposition.guards` | `Elements.Superposition.guards`, shared unchanged from its pure module |
| `Elements.Superposition.kept` | `Elements.Superposition.kept`, shared unchanged from its pure module |
| `Elements.Superposition.rayOfAnglePremises` | `Elements.Superposition.rayOfAnglePremises`, shared unchanged from its pure module |
| `Elements.ang` | `S.ang`, a field of `Signature` |
| `Elements.area` | `S.area`, a field of `Signature` |
| `Elements.instAddMagnitude` | `S.instAddMagnitude`, in `Model/Signature.lean` |
| `Elements.instLEMagnitude` | `S.instLEMagnitude`, in `Model/Signature.lean` |
| `Elements.instLTMagnitude` | `S.instLTMagnitude`, in `Model/Signature.lean` |
| `Elements.instOfNatMagnitudeOfNatNat` | `S.instOfNatMagnitude`, in `Model/Signature.lean` |
| `Elements.len` | `S.len`, a field of `Signature` |
| `Elements.primitives` | `S.primitives`, below |
| `Elements.rightAngle` | `S.rightAngle`, a field of `Signature` |

Each law is a definition named as in the lock: `Law.Postulate1 S` for `Postulate1`. A model of
the laws is a signature `S` with `Laws S`, the structure at the end, which has a field for each
law: those of `Neutral S`, every law but Postulate 5, and Postulate 5 apart from them.
`Check/RoundTrip.lean` translates each word and law here back and compares it with the
library's declaration, binder by binder, and `Check/Laws.lean` asks the kernel whether each,
with the library's own words put back for `S`, is the library's declaration.
-/

@[expose] public section

namespace Model

/-! ## The words the laws reach -/

namespace Signature

variable (S : Signature)

/-- `Elements.CirclesMeet`, translated. -/
def CirclesMeet (α β : S.Circle) : Prop :=
  ∃ A B : S.Point, A ≠ B ∧ S.OnCircle A α ∧ S.OnCircle A β ∧ S.OnCircle B α ∧ S.OnCircle B β

/-- `Elements.Collinear`, translated. -/
def Collinear (A B C : S.Point) : Prop :=
  ∃ L : S.Line, S.OnLine A L ∧ S.OnLine B L ∧ S.OnLine C L

/-- `Elements.IsRightAngle`, translated. -/
def IsRightAngle (A B C : S.Point) : Prop :=
  ∃ D : S.Point, S.Between A B D ∧ ¬S.Collinear A B C ∧ S.ang A B C = S.ang C B D

/-- `Elements.LinesMeet`, translated. -/
def LinesMeet (L M : S.Line) : Prop :=
  L ≠ M ∧ ∃ A : S.Point, S.OnLine A L ∧ S.OnLine A M

/-- `Elements.OppositeSides`, translated. -/
def OppositeSides (A B : S.Point) (L : S.Line) : Prop :=
  ¬S.OnLine A L ∧ ¬S.OnLine B L ∧ ¬S.SameSide A B L

/-- `Elements.OutsideCircle`, translated. -/
def OutsideCircle (A : S.Point) (α : S.Circle) : Prop :=
  ¬S.InsideCircle A α ∧ ¬S.OnCircle A α

/-- `Elements.primitives`, translated. -/
noncomputable def primitives : Elements.Superposition.Interpretation :=
  { Point := S.Point, Line := S.Line, OnLine := S.OnLine, Between := S.Between, SameSide := S.SameSide, Length := S.Length, Angle := S.Angle, Area := S.Area, len := S.len, ang := S.ang, area := S.area }

end Signature

/-! ## The laws -/

namespace Law

variable (S : Signature)

/-- `Elements.Definition15`, translated. -/
def Definition15 : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α → S.OnCircle C α →
    S.len A B = S.len A C

/-- `Elements.Postulate1`, translated. -/
def Postulate1 : Prop :=
  ∀ (A B : S.Point), A ≠ B → ∃ L : S.Line, S.OnLine A L ∧ S.OnLine B L

/-- `Elements.Postulate2`, translated. -/
def Postulate2 : Prop :=
  ∀ {B C : S.Point} {L : S.Line}, S.OnLine B L → S.OnLine C L → B ≠ C → ∀ (avoid : List S.Point),
    ∃ A : S.Point, S.OnLine A L ∧ S.Between B C A ∧ ¬A ∈ avoid

/-- `Elements.Postulate3`, translated. -/
def Postulate3 : Prop :=
  ∀ (A B : S.Point), A ≠ B → ∃ α : S.Circle, S.Centre A α ∧ S.OnCircle B α

/-- `Elements.Postulate4`, translated. -/
def Postulate4 : Prop :=
  ∀ {A B C : S.Point}, S.IsRightAngle A B C → S.ang A B C = S.rightAngle

/-- `Elements.Postulate5`, translated. -/
def Postulate5 : Prop :=
  ∀ {A B C D : S.Point} {L M N : S.Line}, S.OnLine A L → S.OnLine B L → S.OnLine B M →
    S.OnLine C M → S.OnLine C N → S.OnLine D N → B ≠ C → S.SameSide A D M →
    S.ang A B C + S.ang B C D < S.rightAngle + S.rightAngle → ∃ E : S.Point, S.OnLine E L ∧
    S.OnLine E N ∧ S.SameSide E A M

end Law

namespace Law.Tacit

variable (S : Signature)

/-- `Elements.Tacit.add_assoc`, translated. -/
def add_assoc : Prop :=
  ∀ {k : Kind} (a b c : S.Magnitude k), a + b + c = a + (b + c)

/-- `Elements.Tacit.add_comm`, translated. -/
def add_comm : Prop :=
  ∀ {k : Kind} (a b : S.Magnitude k), a + b = b + a

/-- `Elements.Tacit.add_lt_add_right`, translated. -/
def add_lt_add_right : Prop :=
  ∀ {k : Kind} {a b : S.Magnitude k} (c : S.Magnitude k), a < b → a + c < b + c

/-- `Elements.Tacit.add_zero`, translated. -/
def add_zero : Prop :=
  ∀ {k : Kind} (a : S.Magnitude k), a + 0 = a

/-- `Elements.Tacit.angle_add_of_inside`, translated. -/
def angle_add_of_inside : Prop :=
  ∀ {A B C D : S.Point} {L M : S.Line}, S.OnLine A L → S.OnLine A M → S.OnLine B L → S.OnLine C M →
    A ≠ B → A ≠ C → ¬S.OnLine D L → ¬S.OnLine D M → L ≠ M → S.SameSide B D M → S.SameSide C D L →
    S.ang B A C = S.ang B A D + S.ang D A C

/-- `Elements.Tacit.angle_eq_of_same_rays`, translated. -/
def angle_eq_of_same_rays : Prop :=
  ∀ {A B C : S.Point} {L M : S.Line} {B' C' : S.Point}, S.OnLine A L → S.OnLine B L →
    S.OnLine B' L → S.OnLine A M → S.OnLine C M → S.OnLine C' M → B ≠ A → B' ≠ A → C ≠ A → C' ≠ A →
    ¬S.Between B A B' → ¬S.Between C A C' → S.ang B A C = S.ang B' A C'

/-- `Elements.Tacit.angle_eq_zero_of_same_ray`, translated. -/
def angle_eq_zero_of_same_ray : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, A ≠ B → A ≠ C → S.OnLine A L → S.OnLine B L → S.OnLine C L →
    ¬S.Between B A C → S.ang B A C = 0

/-- `Elements.Tacit.angle_le_two_right`, translated. -/
def angle_le_two_right : Prop :=
  ∀ (A B C : S.Point), S.ang A B C ≤ S.rightAngle + S.rightAngle

/-- `Elements.Tacit.angle_symm`, translated. -/
def angle_symm : Prop :=
  ∀ {A B C : S.Point}, A ≠ B → C ≠ B → S.ang A B C = S.ang C B A

/-- `Elements.Tacit.area_add_of_between`, translated. -/
def area_add_of_between : Prop :=
  ∀ {A B C D : S.Point} {L : S.Line}, S.OnLine A L → S.OnLine B L → S.OnLine C L → A ≠ B → A ≠ C →
    B ≠ C → ¬S.OnLine D L → S.Between A C B → S.area A C D + S.area D C B = S.area A D B

/-- `Elements.Tacit.area_congruent`, translated. -/
def area_congruent : Prop :=
  ∀ {A B C D E F : S.Point}, S.len A B = S.len D E → S.len B C = S.len E F → S.len C A = S.len F D →
    S.ang A B C = S.ang D E F → S.ang B C A = S.ang E F D → S.ang C A B = S.ang F D E →
    S.area A B C = S.area D E F

/-- `Elements.Tacit.area_degenerate`, translated. -/
def area_degenerate : Prop :=
  ∀ (A B : S.Point), S.area A A B = 0

/-- `Elements.Tacit.area_eq_zero_of_on_line`, translated. -/
def area_eq_zero_of_on_line : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.OnLine A L → S.OnLine B L → A ≠ B → S.OnLine C L →
    S.area A B C = 0

/-- `Elements.Tacit.area_rotate`, translated. -/
def area_rotate : Prop :=
  ∀ (A B C : S.Point), S.area A B C = S.area C A B

/-- `Elements.Tacit.between_cases`, translated. -/
def between_cases : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, A ≠ B → B ≠ C → A ≠ C → S.OnLine A L → S.OnLine B L →
    S.OnLine C L → S.Between A B C ∨ S.Between B A C ∨ S.Between A C B

/-- `Elements.Tacit.between_of_inside_chord`, translated. -/
def between_of_inside_chord : Prop :=
  ∀ {A B C : S.Point} {L : S.Line} {α : S.Circle}, S.OnLine A L → S.OnLine B L → S.OnLine C L →
    S.InsideCircle A α → S.OnCircle B α → S.OnCircle C α → B ≠ C → S.Between B A C

/-- `Elements.Tacit.between_symm`, translated. -/
def between_symm : Prop :=
  ∀ {A B C : S.Point}, S.Between A B C → S.Between C B A

/-- `Elements.Tacit.circle_eq`, translated. -/
def circle_eq : Prop :=
  ∀ {A B C : S.Point} {α β : S.Circle}, S.Centre A α → S.Centre A β → S.OnCircle B α →
    S.OnCircle C β → S.len A B = S.len A C → α = β

/-- `Elements.Tacit.circles_meet`, translated. -/
def circles_meet : Prop :=
  ∀ {A B : S.Point} {α β : S.Circle}, S.OnCircle A α → S.InsideCircle B α → S.InsideCircle A β →
    S.OnCircle B β → S.CirclesMeet α β

/-- `Elements.Tacit.circles_meet_same_side`, translated. -/
def circles_meet_same_side : Prop :=
  ∀ {α β : S.Circle} {B C D : S.Point} {L : S.Line}, S.CirclesMeet α β → S.Centre C α →
    S.Centre D β → S.OnLine C L → S.OnLine D L → ¬S.OnLine B L → ∃ A : S.Point, S.OnCircle A α ∧
    S.OnCircle A β ∧ S.SameSide A B L

/-- `Elements.Tacit.exists_centre`, translated. -/
def exists_centre : Prop :=
  ∀ (α : S.Circle), ∃ O : S.Point, S.Centre O α

/-- `Elements.Tacit.exists_point`, translated. -/
def exists_point : Prop :=
  ∀ (avoid : List S.Point), ∃ A : S.Point, ¬A ∈ avoid

/-- `Elements.Tacit.exists_point_inside_circle`, translated. -/
def exists_point_inside_circle : Prop :=
  ∀ (α : S.Circle) (avoid : List S.Point), ∃ A : S.Point, S.InsideCircle A α ∧ ¬A ∈ avoid

/-- `Elements.Tacit.exists_point_on_line`, translated. -/
def exists_point_on_line : Prop :=
  ∀ (L : S.Line) (avoid : List S.Point), ∃ A : S.Point, S.OnLine A L ∧ ¬A ∈ avoid

/-- `Elements.Tacit.len_add_of_between`, translated. -/
def len_add_of_between : Prop :=
  ∀ {A B C : S.Point}, S.Between A B C → S.len A B + S.len B C = S.len A C

/-- `Elements.Tacit.len_self`, translated. -/
def len_self : Prop :=
  ∀ (A : S.Point), S.len A A = 0

/-- `Elements.Tacit.len_symm`, translated. -/
def len_symm : Prop :=
  ∀ (A B : S.Point), S.len A B = S.len B A

/-- `Elements.Tacit.line_circle_between`, translated. -/
def line_circle_between : Prop :=
  ∀ {B C : S.Point} {L : S.Line} {α : S.Circle}, S.InsideCircle B α → S.OnLine B L →
    S.OutsideCircle C α → S.OnLine C L → ∃ A : S.Point, S.OnCircle A α ∧ S.OnLine A L ∧
    S.Between B A C

/-- `Elements.Tacit.line_circle_beyond`, translated. -/
def line_circle_beyond : Prop :=
  ∀ {B C : S.Point} {L : S.Line} {α : S.Circle}, S.InsideCircle B α → S.OnLine B L → S.OnLine C L →
    C ≠ B → ∃ A : S.Point, S.OnCircle A α ∧ S.OnLine A L ∧ S.Between A B C

/-- `Elements.Tacit.line_unique`, translated. -/
def line_unique : Prop :=
  ∀ {A B : S.Point} {L M : S.Line}, A ≠ B → S.OnLine A L → S.OnLine B L → S.OnLine A M →
    S.OnLine B M → L = M

/-- `Elements.Tacit.lines_meet_of_opposite_sides`, translated. -/
def lines_meet_of_opposite_sides : Prop :=
  ∀ {A B : S.Point} {L M : S.Line}, S.OppositeSides A B L → S.OnLine A M → S.OnLine B M →
    S.LinesMeet L M

/-- `Elements.Tacit.lt_irrefl`, translated. -/
def lt_irrefl : Prop :=
  ∀ {k : Kind} (a : S.Magnitude k), ¬a < a

/-- `Elements.Tacit.lt_trans`, translated. -/
def lt_trans : Prop :=
  ∀ {k : Kind} {a b c : S.Magnitude k}, a < b → b < c → a < c

/-- `Elements.Tacit.lt_trichotomy`, translated. -/
def lt_trichotomy : Prop :=
  ∀ {k : Kind} (a b : S.Magnitude k), a < b ∨ a = b ∨ b < a

/-- `Elements.Tacit.not_between_of_between`, translated. -/
def not_between_of_between : Prop :=
  ∀ {A B C : S.Point}, S.Between A B C → ¬S.Between B A C

/-- `Elements.Tacit.not_lt_zero`, translated. -/
def not_lt_zero : Prop :=
  ∀ {k : Kind} (a : S.Magnitude k), ¬a < 0

/-- `Elements.Tacit.not_on_line_of_same_side`, translated. -/
def not_on_line_of_same_side : Prop :=
  ∀ {A B : S.Point} {L : S.Line}, S.SameSide A B L → ¬S.OnLine A L

/-- `Elements.Tacit.on_line_of_area_eq_zero`, translated. -/
def on_line_of_area_eq_zero : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.OnLine A L → S.OnLine B L → A ≠ B → S.area A B C = 0 →
    S.OnLine C L

/-- `Elements.Tacit.pasch2`, translated. -/
def pasch2 : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.Between A B C → S.OnLine A L → ¬S.OnLine B L →
    S.SameSide B C L

/-- `Elements.Tacit.same_ray_of_angle_eq_zero`, translated. -/
def same_ray_of_angle_eq_zero : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, A ≠ B → A ≠ C → S.OnLine A L → S.OnLine B L → S.ang B A C = 0 →
    S.OnLine C L ∧ ¬S.Between B A C

/-- `Elements.Tacit.same_side_trans`, translated. -/
def same_side_trans : Prop :=
  ∀ {A B C : S.Point} {L : S.Line}, S.SameSide A B L → S.SameSide A C L → S.SameSide B C L

/-- `Elements.Tacit.superposition`, translated. -/
def superposition : Prop :=
  Elements.Superposition.Rule S.primitives

end Law.Tacit

/-! ## The laws as one structure -/

/-- Every law but those that hold only in the Euclidean plane: Postulate 5, and any rule the
library declares in `Elements.Tacit.Euclidean`. A hyperbolic plane is to satisfy these and
fail Postulate 5. -/
structure Neutral (S : Signature) : Prop where
  Definition15 : Law.Definition15 S
  Postulate1 : Law.Postulate1 S
  Postulate2 : Law.Postulate2 S
  Postulate3 : Law.Postulate3 S
  Postulate4 : Law.Postulate4 S
  add_assoc : Law.Tacit.add_assoc S
  add_comm : Law.Tacit.add_comm S
  add_lt_add_right : Law.Tacit.add_lt_add_right S
  add_zero : Law.Tacit.add_zero S
  angle_add_of_inside : Law.Tacit.angle_add_of_inside S
  angle_eq_of_same_rays : Law.Tacit.angle_eq_of_same_rays S
  angle_eq_zero_of_same_ray : Law.Tacit.angle_eq_zero_of_same_ray S
  angle_le_two_right : Law.Tacit.angle_le_two_right S
  angle_symm : Law.Tacit.angle_symm S
  area_add_of_between : Law.Tacit.area_add_of_between S
  area_congruent : Law.Tacit.area_congruent S
  area_degenerate : Law.Tacit.area_degenerate S
  area_eq_zero_of_on_line : Law.Tacit.area_eq_zero_of_on_line S
  area_rotate : Law.Tacit.area_rotate S
  between_cases : Law.Tacit.between_cases S
  between_of_inside_chord : Law.Tacit.between_of_inside_chord S
  between_symm : Law.Tacit.between_symm S
  circle_eq : Law.Tacit.circle_eq S
  circles_meet : Law.Tacit.circles_meet S
  circles_meet_same_side : Law.Tacit.circles_meet_same_side S
  exists_centre : Law.Tacit.exists_centre S
  exists_point : Law.Tacit.exists_point S
  exists_point_inside_circle : Law.Tacit.exists_point_inside_circle S
  exists_point_on_line : Law.Tacit.exists_point_on_line S
  len_add_of_between : Law.Tacit.len_add_of_between S
  len_self : Law.Tacit.len_self S
  len_symm : Law.Tacit.len_symm S
  line_circle_between : Law.Tacit.line_circle_between S
  line_circle_beyond : Law.Tacit.line_circle_beyond S
  line_unique : Law.Tacit.line_unique S
  lines_meet_of_opposite_sides : Law.Tacit.lines_meet_of_opposite_sides S
  lt_irrefl : Law.Tacit.lt_irrefl S
  lt_trans : Law.Tacit.lt_trans S
  lt_trichotomy : Law.Tacit.lt_trichotomy S
  not_between_of_between : Law.Tacit.not_between_of_between S
  not_lt_zero : Law.Tacit.not_lt_zero S
  not_on_line_of_same_side : Law.Tacit.not_on_line_of_same_side S
  on_line_of_area_eq_zero : Law.Tacit.on_line_of_area_eq_zero S
  pasch2 : Law.Tacit.pasch2 S
  same_ray_of_angle_eq_zero : Law.Tacit.same_ray_of_angle_eq_zero S
  same_side_trans : Law.Tacit.same_side_trans S
  superposition : Law.Tacit.superposition S

/-- Every law of the lock, a field for each: those of `Neutral`, and Postulate 5. A model of
the laws is a signature `S` with `Laws S`. -/
structure Laws (S : Signature) : Prop extends Neutral S where
  Postulate5 : Law.Postulate5 S

end Model
