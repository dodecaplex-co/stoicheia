import Elements

/-!
# Book IV, scratch: the words and the statements (a draft)

The words that brief 0012 proposes for `Elements/Foundations/DefinitionsIV.lean`, the
coordinator's file, and every statement of Book IV as the brief drafts it, each with
`sorry`. Nothing imports this file, and nothing in the edition builds it: from the root of
a checkout that has built `Elements`, `lake env lean docs/reports/crew/scratch-IV/Statements.lean`
checks it. The bridge `Polygon.arcs_measure` speaks of stage 3's arcs, staged when this
draft was written and now in `Elements/Foundations/DefinitionsIII.lean`, which
`import Elements` brings. The prototypes beside it (`Prototype*.lean`) repeat the words,
unchanged, and prove one statement each.

The statements are written as they will stand once brief 0008's rule, that every circle has
a centre, is in the foundations: a given circle carries no hypothesis that it has a centre.
Lengths are written `len A B`, as brief 0010 recommends; the library reads `len A B` and
`‖A B‖` as the same term.

None of the words is an assumption; they are only definitions.
-/

namespace Elements

/-! ## A figure given by its corners -/

/-- **The sides of a figure** given by its corners in order: each corner with the next,
and the last with the first. The sides of `[A, B, C, D]` are AB, BC, CD and DA. -/
def Polygon.sides (ps : List Point) : List (Point × Point) :=
  segments (ps ++ ps.take 1)

/-- **Each corner with its neighbours**: each corner of the figure with the next two, the
last corners wrapping round to the first. The triples of `[A, B, C, D]` are ABC, BCD, CDA
and DAB: the middle corner of each is a corner of the figure, between its two neighbours;
the first two are the ends of a side, and the third is the next corner. -/
def Polygon.cornerTriples (ps : List Point) : List (Point × Point × Point) :=
  triples (ps ++ ps.take 2)

/-- **A rectilineal figure**, given by its corners in order (Definition I.19's figure
"contained by straight lines", as Book IV uses it): at least three corners, no two the
same, and, for each side, every other corner on one and the same side of it. So the figure
is convex, its sides meet only at their ends, and no three corners in a row are on one
straight line. Every figure of Book IV is one; `Polygon [A, B, C]` says that ABC is a
triangle. -/
def Polygon (ps : List Point) : Prop :=
  (∃ A B C : Point, ∃ rest : List Point, ps = A :: B :: C :: rest) ∧ ps.Nodup ∧
    ∀ s ∈ Polygon.sides ps, ∀ P ∈ ps, ∀ Q ∈ ps,
      P ≠ s.1 → P ≠ s.2 → Q ≠ s.1 → Q ≠ s.2 → SameSideOf P Q s.1 s.2

/-- **Magnitudes all equal**: any two of the list are equal. -/
def AllEqual {k : Kind} (xs : List (Magnitude k)) : Prop :=
  ∀ a ∈ xs, ∀ b ∈ xs, a = b

/-- **The figure is equilateral**: its sides are all equal. -/
def Polygon.Equilateral (ps : List Point) : Prop :=
  AllEqual ((Polygon.sides ps).map fun s => len s.1 s.2)

/-- **The figure is equiangular**: its angles are all equal, the angle at each corner being
the one its two sides there contain. -/
def Polygon.Equiangular (ps : List Point) : Prop :=
  AllEqual ((Polygon.cornerTriples ps).map fun t => ∠ t.1 t.2.1 t.2.2)

/-! ## The Definitions of Book IV -/

/-- **Definition IV.3.** "A rectilineal figure is said to be inscribed in a circle when each
angle of the inscribed figure lies on the circumference of the circle": each corner of the
figure is on the circle. -/
def Polygon.InscribedIn (ps : List Point) (α : Circle) : Prop :=
  ∀ P ∈ ps, OnCircle P α

/-- **Definition IV.4.** "A rectilineal figure is said to be circumscribed about a circle,
when each side of the circumscribed figure touches the circumference of the circle": each
side, produced, touches the circle (Definition III.2, `Touches`), and the point of contact
is on the side itself, between its ends. -/
def Polygon.CircumscribedAbout (ps : List Point) (α : Circle) : Prop :=
  ∀ s ∈ Polygon.sides ps, Touches s.1 s.2 α ∧ ∃ T : Point, Between s.1 T s.2 ∧ OnCircle T α

/-- **Definition IV.5.** "A circle is said to be inscribed in a figure when the circumference
of the circle touches each side of the figure in which it is inscribed": Definition IV.4,
read from the circle. -/
def Circle.InscribedIn (α : Circle) (ps : List Point) : Prop :=
  Polygon.CircumscribedAbout ps α

/-- **Definition IV.6.** "A circle is said to be circumscribed about a figure when the
circumference of the circle passes through each angle of the figure about which it is
circumscribed": Definition IV.3, read from the circle. -/
def Circle.CircumscribedAbout (α : Circle) (ps : List Point) : Prop :=
  Polygon.InscribedIn ps α

/-! ## The circumferences a figure inscribed in a circle cuts off -/

/-- **The circumferences cut off by the sides** of a figure inscribed in the circle `α`, one
for each side, in order: the circumference on the far side of the side from the figure,
named as Definition III.9 names it, by the angle that stands on it at the next corner
(`standing α P R Q`, for the side PQ and the next corner R). For a figure inscribed in `α`
they make up the whole circle (the bridge `Polygon.arcs_sum` of brief 0012). -/
noncomputable def Polygon.arcs (ps : List Point) (α : Circle) : List Angle :=
  (Polygon.cornerTriples ps).map fun t => standing α t.1 t.2.2 t.2.1

end Elements

namespace Scratch.BookIV

open Elements Elements.Tacit

/-! ## The sixteen propositions -/

/-- Into a given circle to fit a straight line equal to a given straight line which is not
greater than the diameter of the circle. -/
theorem Prop1 {C D₁ D₂ : Point} {ABC : Circle} (hC : OnCircle C ABC) (hD : D₁ ≠ D₂)
    (hle : ∀ P Q E : Point, Centre E ABC → OnCircle P ABC → OnCircle Q ABC → Between P E Q →
      len D₁ D₂ ≤ len P Q) :
    ∃ A : Point, OnCircle A ABC ∧ len C A = len D₁ D₂ := sorry

/-- In a given circle to inscribe a triangle equiangular with a given triangle. -/
theorem Prop2 {A D E F : Point} {ABC : Circle} (hA : OnCircle A ABC) (hDEF : Triangle D E F) :
    ∃ B C : Point, Triangle A B C ∧ Polygon.InscribedIn [A, B, C] ABC ∧
      ∠ B A C = ∠ E D F ∧ ∠ A B C = ∠ D E F ∧ ∠ A C B = ∠ D F E := sorry

/-- About a given circle to circumscribe a triangle equiangular with a given triangle. -/
theorem Prop3 {D E F : Point} (ABC : Circle) (hDEF : Triangle D E F) :
    ∃ L M N : Point, Triangle L M N ∧ Polygon.CircumscribedAbout [L, M, N] ABC ∧
      ∠ M L N = ∠ E D F ∧ ∠ L M N = ∠ D E F ∧ ∠ L N M = ∠ D F E := sorry

/-- In a given triangle to inscribe a circle. -/
theorem Prop4 {A B C : Point} (hABC : Triangle A B C) :
    ∃ (EFG : Circle) (D E F G : Point), Centre D EFG ∧ Circle.InscribedIn EFG [A, B, C] ∧
      Between A E B ∧ Between B F C ∧ Between C G A ∧
      OnCircle E EFG ∧ OnCircle F EFG ∧ OnCircle G EFG := sorry

/-- About a given triangle to circumscribe a circle. -/
theorem Prop5 {A B C : Point} (hABC : Triangle A B C) :
    ∃ (ABC : Circle) (F : Point), Centre F ABC ∧ Circle.CircumscribedAbout ABC [A, B, C] ∧
      (SameSideOf F A B C → ∠ B A C < ∟) ∧ (Between B F C → ∠ B A C = ∟) ∧
      (OppositeSidesOf F A B C → ∟ < ∠ B A C) := sorry

/-- In a given circle to inscribe a square. -/
theorem Prop6 (ABCD : Circle) :
    ∃ A B C D : Point, Polygon [A, B, C, D] ∧ Polygon.InscribedIn [A, B, C, D] ABCD ∧
      Square A B C D := sorry

/-- About a given circle to circumscribe a square. -/
theorem Prop7 (ABCD : Circle) :
    ∃ F G H K : Point, Polygon [F, G, H, K] ∧ Polygon.CircumscribedAbout [F, G, H, K] ABCD ∧
      Square F G H K := sorry

/-- In a given square to inscribe a circle. -/
theorem Prop8 {A B C D : Point} (hABCD : Polygon [A, B, C, D]) (hsq : Square A B C D) :
    ∃ (α : Circle) (G : Point), Centre G α ∧ Circle.InscribedIn α [A, B, C, D] := sorry

/-- About a given square to circumscribe a circle. -/
theorem Prop9 {A B C D : Point} (hABCD : Polygon [A, B, C, D]) (hsq : Square A B C D) :
    ∃ (ABCD : Circle) (E : Point), Centre E ABCD ∧ Circle.CircumscribedAbout ABCD [A, B, C, D] ∧
      Between A E C ∧ Between B E D := sorry

/-- To construct an isosceles triangle having each of the angles at the base double of the
remaining one. -/
theorem Prop10 {A B : Point} (hAB : A ≠ B) :
    ∃ D : Point, Triangle A B D ∧ len A B = len A D ∧
      ∠ A B D = ∠ B A D + ∠ B A D ∧ ∠ A D B = ∠ B A D + ∠ B A D := sorry

/-- In a given circle to inscribe an equilateral and equiangular pentagon. -/
theorem Prop11 {A : Point} {ABCDE : Circle} (hA : OnCircle A ABCDE) :
    ∃ B C D E : Point, Polygon [A, B, C, D, E] ∧
      Polygon.InscribedIn [A, B, C, D, E] ABCDE ∧
      Polygon.Equilateral [A, B, C, D, E] ∧ Polygon.Equiangular [A, B, C, D, E] ∧
      AllEqual (Polygon.arcs [A, B, C, D, E] ABCDE) := sorry

/-- About a given circle to circumscribe an equilateral and equiangular pentagon. -/
theorem Prop12 (ABCDE : Circle) :
    ∃ G H K L M : Point, Polygon [G, H, K, L, M] ∧
      Polygon.CircumscribedAbout [G, H, K, L, M] ABCDE ∧
      Polygon.Equilateral [G, H, K, L, M] ∧ Polygon.Equiangular [G, H, K, L, M] := sorry

/-- In a given pentagon, which is equilateral and equiangular, to inscribe a circle. -/
theorem Prop13 {A B C D E : Point} (hABCDE : Polygon [A, B, C, D, E])
    (heqs : Polygon.Equilateral [A, B, C, D, E]) (heqa : Polygon.Equiangular [A, B, C, D, E]) :
    ∃ (GHKLM : Circle) (F : Point), Centre F GHKLM ∧
      Circle.InscribedIn GHKLM [A, B, C, D, E] := sorry

/-- About a given pentagon, which is equilateral and equiangular, to circumscribe a
circle. -/
theorem Prop14 {A B C D E : Point} (hABCDE : Polygon [A, B, C, D, E])
    (heqs : Polygon.Equilateral [A, B, C, D, E]) (heqa : Polygon.Equiangular [A, B, C, D, E]) :
    ∃ (ABCDE : Circle) (F : Point), Centre F ABCDE ∧
      Circle.CircumscribedAbout ABCDE [A, B, C, D, E] := sorry

/-- In a given circle to inscribe an equilateral and equiangular hexagon. -/
theorem Prop15 (ABCDEF : Circle) :
    ∃ A B C D E F : Point, Polygon [A, B, C, D, E, F] ∧
      Polygon.InscribedIn [A, B, C, D, E, F] ABCDEF ∧
      Polygon.Equilateral [A, B, C, D, E, F] ∧ Polygon.Equiangular [A, B, C, D, E, F] := sorry

/-- **IV.15, Porism.** "From this it is manifest that the side of the hexagon is equal to
the radius of the circle", and, as for the pentagon, an equilateral and equiangular hexagon
is circumscribed about a given circle, and a circle is inscribed in, and circumscribed
about, a given equilateral and equiangular hexagon. -/
theorem Prop15.porism :
    (∀ (α : Circle) (O A B C D E F : Point), Centre O α →
      Polygon [A, B, C, D, E, F] → Polygon.InscribedIn [A, B, C, D, E, F] α →
      Polygon.Equilateral [A, B, C, D, E, F] → Polygon.Equiangular [A, B, C, D, E, F] →
      len A B = len O A) ∧
    (∀ (α : Circle) (A B C D E F : Point), Polygon [A, B, C, D, E, F] →
      Polygon.InscribedIn [A, B, C, D, E, F] α →
      Polygon.Equilateral [A, B, C, D, E, F] → Polygon.Equiangular [A, B, C, D, E, F] →
      ∃ G H K L M N : Point, Polygon [G, H, K, L, M, N] ∧
        Polygon.CircumscribedAbout [G, H, K, L, M, N] α ∧
        (∀ P ∈ [A, B, C, D, E, F], ∃ s ∈ Polygon.sides [G, H, K, L, M, N], Between s.1 P s.2) ∧
        Polygon.Equilateral [G, H, K, L, M, N] ∧ Polygon.Equiangular [G, H, K, L, M, N]) ∧
    (∀ A B C D E F : Point, Polygon [A, B, C, D, E, F] →
      Polygon.Equilateral [A, B, C, D, E, F] → Polygon.Equiangular [A, B, C, D, E, F] →
      (∃ (α : Circle) (O : Point), Centre O α ∧ Circle.InscribedIn α [A, B, C, D, E, F]) ∧
      (∃ (β : Circle) (O : Point), Centre O β ∧
        Circle.CircumscribedAbout β [A, B, C, D, E, F])) := sorry

/-- **Straight lines fitted in contiguity close up** (IV.16's last step, which Euclid
leaves to the reader: "fit into the circle ABCD straight lines equal to them and in
contiguity"). If n of the circumference PKQ make the whole circle, for some n of three or
more, then n straight lines equal to PQ, fitted into the circle from P, each from the end of
the last (IV.1), close up and inscribe an equilateral and equiangular figure of n corners
whose first side is PQ, its sides cutting off that circumference. A helper of IV.16, before
it in its file: it cites IV.1. -/
theorem Prop16.contiguity {P Q K : Point} {α : Circle} {n : Nat} (hn : 3 ≤ n)
    (hP : OnCircle P α) (hQ : OnCircle Q α) (hK : ¬ Collinear P Q K)
    (hpart : Magnitude.sum (List.replicate n (circumference α P K Q)) = ∟ + ∟ + ∟ + ∟) :
    ∃ rest : List Point, (P :: Q :: rest).length = n ∧ Polygon (P :: Q :: rest) ∧
      Polygon.InscribedIn (P :: Q :: rest) α ∧ Polygon.Equilateral (P :: Q :: rest) ∧
      Polygon.Equiangular (P :: Q :: rest) ∧
      ∀ a ∈ Polygon.arcs (P :: Q :: rest) α, a = circumference α P K Q := sorry

/-- In a given circle to inscribe a fifteen-angled figure which shall be both equilateral
and equiangular. -/
theorem Prop16 (ABCD : Circle) :
    ∃ ps : List Point, ps.length = 15 ∧ Polygon ps ∧ Polygon.InscribedIn ps ABCD ∧
      Polygon.Equilateral ps ∧ Polygon.Equiangular ps := sorry

/-- **IV.16, further.** "And, in like manner as in the case of the pentagon, if through the
points of division on the circle we draw tangents to the circle, there will be circumscribed
about the circle a fifteen-angled figure which is equilateral and equiangular. And further,
by proofs similar to those in the case of the pentagon, we can both inscribe a circle in the
given fifteen-angled figure and circumscribe one about it." A companion, not a porism: Heath
prints no heading, and the claims come before the last "Q. E. F.". -/
theorem Prop16.further :
    (∀ (α : Circle) (ps : List Point), ps.length = 15 → Polygon ps →
      Polygon.InscribedIn ps α → Polygon.Equilateral ps → Polygon.Equiangular ps →
      ∃ qs : List Point, qs.length = 15 ∧ Polygon qs ∧ Polygon.CircumscribedAbout qs α ∧
        (∀ P ∈ ps, ∃ s ∈ Polygon.sides qs, Between s.1 P s.2) ∧
        Polygon.Equilateral qs ∧ Polygon.Equiangular qs) ∧
    (∀ ps : List Point, ps.length = 15 → Polygon ps → Polygon.Equilateral ps →
      Polygon.Equiangular ps →
      (∃ (α : Circle) (O : Point), Centre O α ∧ Circle.InscribedIn α ps) ∧
      (∃ (β : Circle) (O : Point), Centre O β ∧ Circle.CircumscribedAbout β ps)) := sorry

/-! ## Companions: Euclid's "in like manner", for any number of sides -/

/-- **IV.12 for any equilateral and equiangular figure inscribed in a circle**: the
straight lines touching the circle at its corners make an equilateral and equiangular
figure, with as many sides, circumscribed about the circle. -/
theorem Prop12.general {ps : List Point} {α : Circle} (hps : Polygon ps)
    (hin : Polygon.InscribedIn ps α) (heqs : Polygon.Equilateral ps)
    (heqa : Polygon.Equiangular ps) :
    ∃ qs : List Point, qs.length = ps.length ∧ Polygon qs ∧ Polygon.CircumscribedAbout qs α ∧
      (∀ P ∈ ps, ∃ s ∈ Polygon.sides qs, Between s.1 P s.2) ∧
      Polygon.Equilateral qs ∧ Polygon.Equiangular qs := sorry

/-- **IV.13 for any equilateral and equiangular figure**: a circle is inscribed in it. -/
theorem Prop13.general {ps : List Point} (hps : Polygon ps) (heqs : Polygon.Equilateral ps)
    (heqa : Polygon.Equiangular ps) :
    ∃ (α : Circle) (O : Point), Centre O α ∧ Circle.InscribedIn α ps := sorry

/-- **IV.14 for any equilateral and equiangular figure**: a circle is circumscribed about
it. -/
theorem Prop14.general {ps : List Point} (hps : Polygon ps) (heqs : Polygon.Equilateral ps)
    (heqa : Polygon.Equiangular ps) :
    ∃ (α : Circle) (O : Point), Centre O α ∧ Circle.CircumscribedAbout α ps := sorry

/-! ## Bridges in Book Zero: no proposition cited -/

/-- **A figure of three corners is a triangle**, and a triangle is a figure of three
corners. -/
theorem Polygon.triangle_iff {A B C : Point} : Polygon [A, B, C] ↔ Triangle A B C := sorry

/-- **Each circumference of an inscribed figure is stage 3's arc on that side.** For a side
PQ, with R the next corner, and K any point beyond PQ from R, the circumference on which the
angle PRQ stands is the measure of the arc PQ on K's side (`Arc.measure`), and no other
corner is on that arc: the corners lie in order round the circle. -/
theorem Polygon.arcs_measure {ps : List Point} {α : Circle} (hps : Polygon ps)
    (hin : Polygon.InscribedIn ps α) :
    ∀ t ∈ Polygon.cornerTriples ps, ∀ K : Point, OppositeSidesOf K t.2.2 t.1 t.2.1 →
      standing α t.1 t.2.2 t.2.1 = Arc.measure ⟨α, t.1, t.2.1, K⟩ ∧
      ∀ R ∈ ps, R ≠ t.1 → R ≠ t.2.1 → ¬ OnArc R ⟨α, t.1, t.2.1, K⟩ := sorry

/-! ## Bridges to Book III's circumferences

Ground for Book IV, after Book III and before IV.1: each cites Book III alone. -/

/-- **The circumferences cut off by the sides of an inscribed figure make up the whole
circle**: four right angles, the measure of the whole circle (`Circumference.whole`). By
`Circumference.add`, a side at a time. -/
theorem Polygon.arcs_sum {ps : List Point} {α : Circle} (hps : Polygon ps)
    (hin : Polygon.InscribedIn ps α) :
    Magnitude.sum (Polygon.arcs ps α) = ∟ + ∟ + ∟ + ∟ := sorry

/-- **An inscribed figure is equilateral exactly when its sides cut off equal
circumferences.** III.28 and III.29, in one circle; each circumference is less than a
semicircle when the sides are equal. -/
theorem Polygon.equilateral_iff_arcs {ps : List Point} {α : Circle} (hps : Polygon ps)
    (hin : Polygon.InscribedIn ps α) :
    Polygon.Equilateral ps ↔ AllEqual (Polygon.arcs ps α) := sorry

/-- **An inscribed figure whose sides cut off equal circumferences is equiangular.** Each
angle stands on the circumferences of the sides it does not touch, added together
(`Circumference.add`); equal circumferences give equal angles (III.27). -/
theorem Polygon.equiangular_of_arcs {ps : List Point} {α : Circle} (hps : Polygon ps)
    (hin : Polygon.InscribedIn ps α) (harcs : AllEqual (Polygon.arcs ps α)) :
    Polygon.Equiangular ps := sorry

end Scratch.BookIV
