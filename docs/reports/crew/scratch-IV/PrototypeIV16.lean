import Elements

/-!
# Book IV, scratch: a prototype for counting parts of the circle (IV.16)

IV.16 counts: "of the equal segments of which there are fifteen in the circle ABCD, there
will be five in the circumference ABC which is one-third of the circle, and there will be
three in the circumference AB which is one-fifth of the circle; therefore in the remainder
BC there will be two of the equal segments. Let BC be bisected at E; [III. 30] therefore
each of the circumferences BE, EC is a fifteenth of the circle ABCD." (Heath, vol. 2, p.
110.) The prototype proves
that count from the laws of magnitude alone: a part three of which make the whole, less a
part five of which make it, halved, is a part fifteen of which make it. Brief 0012, section
9. Nothing builds this file; `lake env lean` checks it.
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

/-- **A fifteenth of the circle** (IV.16). If three of the circumference `a` make the whole
circle `W`, and five of `b`, and `b` with `c` makes `a`, and `c` is bisected into `e` and
`e`, then fifteen of `e` make `W`: "of the equal segments of which there are fifteen in
the circle ABCD, there will be five in the circumference ABC which is one-third of the
circle, and there will be three in the circumference AB which is one-fifth of the circle;
therefore in the remainder BC there will be two of the equal segments." -/
theorem fifteenth {k : Kind} {W a b c e : Magnitude k} (h3 : a + a + a = W)
    (h5 : b + b + b + b + b = W) (hbc : b + c = a) (he : e + e = c) :
    Magnitude.sum (List.replicate 15 e) = W := by
  /- Three of `a` are three of `b` and six of `e`; five of `b` are three of `b` and two of
     `b`. Both are `W`, so, the three of `b` taken away, six of `e` are two of `b`
     [C.N. 3]. -/
  have h6 : (e + e + e) + (e + e + e) = b + b := by
    apply CommonNotion3 (c := b + b + b) (d := b + b + b) _ rfl
    have hW : (b + (e + e)) + (b + (e + e)) + (b + (e + e)) = b + b + b + b + b := by
      rw [he, hbc, h3, h5]
    calc (e + e + e) + (e + e + e) + (b + b + b)
        = (b + (e + e)) + (b + (e + e)) + (b + (e + e)) := by ac_rfl
      _ = b + b + b + b + b := hW
      _ = (b + b) + (b + b + b) := by ac_rfl
  /- So three of `e` are `b`, and fifteen of `e` are five of `b`, the whole circle. -/
  have h3e : e + e + e = b := Magnitude.eq_of_add_self_eq h6
  rw [← h5, ← h3e]
  simp only [List.replicate, Magnitude.sum, add_zero]
  ac_rfl

end Scratch.BookIV
