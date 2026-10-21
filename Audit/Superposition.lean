import Elements.BookI.Prop04
import Elements.BookI.Prop08
import Elements.Figure.Superposition

/-!
# Superposition: the proofs and their foundations

The first two pins record the complete dependencies of I.4 and I.8, including the
restricted axiom. The pure-calculus pins record soundness, reduction to placement
with its side, fixed-vocabulary derivations and the exportability of conclusions,
and part 4 of the restriction: the rule's part about the figure, which passes to any
part of an interpretation. They also keep the satisfiability and valuation warnings,
the two unrestricted eliminator observations and the passage to numbered symbols
visible. They use only Lean's logical axioms; they establish no global
non-derivability claim.

Each of these theorems is pinned twice: its statement, by `#check`, so that a weaker
statement under the same name fails the build, and then its axioms. The two
definitions part 4 rests on, `Rule.Figure` and `Interpretation.Embedding`, are pinned
whole by `#print`. Every theorem that brief 0009's restriction section names has
its statement pinned here. `Cited.holds_all`, which gives every cited law in one
statement, is pinned the same way, by its statement and then its axioms, at the end of
the file; through I.7 it rests on `Tacit.superposition` itself.

The geometric pins record each cited law and the named-lines proof used for I.4.
Their combined proof uses no construction rule. The last two pins distinguish
I.4's list of such laws from I.8's adapter of I.7, whose proof uses constructions
and inherits the restricted rule through I.4.
-/

/--
info: 'Elements.BookI.Prop4' depends on axioms: [propext,
 Classical.choice,
 Elements.Postulate1,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
 Elements.Tacit.between_cases,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_point,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_unique,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch3,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.superposition,
 Elements.Tacit.triple_incidence2]
-/
#guard_msgs in
#print axioms Elements.BookI.Prop4

/--
info: 'Elements.BookI.Prop8' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_rotate,
 Elements.Tacit.area_swap,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_between_left,
 Elements.Tacit.between_of_between_right,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.inside_of_len_lt,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_lt_of_inside,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.ne_of_between_ends,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_between_of_between_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.on_line_of_between,
 Elements.Tacit.on_line_of_between_ends,
 Elements.Tacit.pasch2,
 Elements.Tacit.pasch3,
 Elements.Tacit.pasch4,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_or,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition,
 Elements.Tacit.triple_incidence1,
 Elements.Tacit.triple_incidence2]
-/
#guard_msgs in
#print axioms Elements.BookI.Prop8

/--
info: @Elements.Superposition.Derives.sound : ∀ {I : Elements.Superposition.Interpretation} {P L : Type}
  {cites : List Elements.Superposition.Cited} {Γ : List (Elements.Superposition.Lit P L)},
  (∀ (c : Elements.Superposition.Cited), c ∈ cites → Elements.Superposition.Cited.Holds I c) →
    ∀ (v : Elements.Superposition.Val I P L),
      (∀ (ℓ : Elements.Superposition.Lit P L), ℓ ∈ Γ → Elements.Superposition.Lit.Holds v ℓ) →
        ∀ {ℓ : Elements.Superposition.Lit P L},
          Elements.Superposition.Derives cites Γ ℓ → Elements.Superposition.Lit.Holds v ℓ
-/
#guard_msgs in
#check @Elements.Superposition.Derives.sound

/--
info: 'Elements.Superposition.Derives.sound' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Elements.Superposition.Derives.sound

/--
info: @Elements.Superposition.Rule.of_placement : ∀ {I : Elements.Superposition.Interpretation},
  (∀ {A B C D G H : I.Point} {L : I.Line},
      Elements.Superposition.Triangle I A B C →
        I.OnLine D L →
          I.OnLine G L →
            D ≠ G →
              ¬I.OnLine H L →
                ∃ B' C' N, Elements.Superposition.Placed I A B C D G H L B' C' ∧ I.OnLine D N ∧ I.OnLine C' N) →
    Elements.Superposition.Rule I
-/
#guard_msgs in
#check @Elements.Superposition.Rule.of_placement

/--
info: 'Elements.Superposition.Rule.of_placement' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.Rule.of_placement

/--
info: @Elements.Superposition.Derives.no_construction : ∀ {I : Elements.Superposition.Interpretation} {P L : Type}
  {cites : List Elements.Superposition.Cited},
  (∀ (c : Elements.Superposition.Cited), c ∈ cites → Elements.Superposition.Cited.Holds I c) →
    ∀ {Γ : List (Elements.Superposition.Lit P L)} {a b c d g h : P} {l : L}
      (w : Elements.Superposition.Val I (Elements.Superposition.Name P) (Elements.Superposition.LineName L)),
      (∀ (ℓ : Elements.Superposition.Lit (Elements.Superposition.Name P) (Elements.Superposition.LineName L)),
          ℓ ∈ Elements.Superposition.branch Γ a b c d g h l → Elements.Superposition.Lit.Holds w ℓ) →
        ∀ {ℓ : Elements.Superposition.Lit (Elements.Superposition.Name P) (Elements.Superposition.LineName L)},
          Elements.Superposition.Derives cites (Elements.Superposition.branch Γ a b c d g h l) ℓ →
            Elements.Superposition.Lit.Holds w ℓ
-/
#guard_msgs in
#check @Elements.Superposition.Derives.no_construction

/--
info: 'Elements.Superposition.Derives.no_construction' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Elements.Superposition.Derives.no_construction

/--
info: @Elements.Superposition.exportable_iff : ∀ {P : Type}
  (m : Elements.Superposition.Metric (Elements.Superposition.Name P)),
  (∃ m₀, Elements.Superposition.Metric.map Elements.Superposition.Name.given m₀ = m) ↔
    ∀ (n : Elements.Superposition.Name P), n ∈ m.names → ∃ p, n = Elements.Superposition.Name.given p
-/
#guard_msgs in
#check @Elements.Superposition.exportable_iff

/--
info: 'Elements.Superposition.exportable_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.exportable_iff

/--
info: @Elements.Superposition.not_exportable_second : ∀ {P : Type}
  {m : Elements.Superposition.Metric (Elements.Superposition.Name P)},
  Elements.Superposition.Name.second ∈ m.names →
    ¬∃ m₀, Elements.Superposition.Metric.map Elements.Superposition.Name.given m₀ = m
-/
#guard_msgs in
#check @Elements.Superposition.not_exportable_second

/--
info: 'Elements.Superposition.not_exportable_second' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.not_exportable_second

/--
info: @Elements.Superposition.not_exportable_third : ∀ {P : Type}
  {m : Elements.Superposition.Metric (Elements.Superposition.Name P)},
  Elements.Superposition.Name.third ∈ m.names →
    ¬∃ m₀, Elements.Superposition.Metric.map Elements.Superposition.Name.given m₀ = m
-/
#guard_msgs in
#check @Elements.Superposition.not_exportable_third

/--
info: 'Elements.Superposition.not_exportable_third' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.not_exportable_third

/--
info: @Elements.Superposition.Metric.holds_place : ∀ {I : Elements.Superposition.Interpretation} {P L : Type}
  (m : Elements.Superposition.Metric P) (v : Elements.Superposition.Val I P L) (B' C' : I.Point) (N : I.Line),
  Elements.Superposition.Metric.Holds (v.place B' C' N)
      (Elements.Superposition.Metric.map Elements.Superposition.Name.given m) ↔
    Elements.Superposition.Metric.Holds v m
-/
#guard_msgs in
#check @Elements.Superposition.Metric.holds_place

/--
info: 'Elements.Superposition.Metric.holds_place' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.Metric.holds_place

/--
info: @Elements.Superposition.Derives.map : ∀ {P L : Type} {cites : List Elements.Superposition.Cited}
  {Γ : List (Elements.Superposition.Lit P L)} {P' L' : Type} (f : P → P') (g : L → L')
  {ℓ : Elements.Superposition.Lit P L},
  Elements.Superposition.Derives cites Γ ℓ →
    Elements.Superposition.Derives cites (List.map (Elements.Superposition.Lit.map f g) Γ)
      (Elements.Superposition.Lit.map f g ℓ)
-/
#guard_msgs in
#check @Elements.Superposition.Derives.map

/--
info: 'Elements.Superposition.Derives.map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.Derives.map

/--
info: @Elements.Superposition.Cited.holds_iff : ∀ {I : Elements.Superposition.Interpretation}
  (c : Elements.Superposition.Cited),
  Elements.Superposition.Cited.Holds I c ↔
    ∀ (v : Elements.Superposition.Val I Elements.Superposition.Letter Elements.Superposition.LineLetter),
      (∀ (ℓ : Elements.Superposition.Lit Elements.Superposition.Letter Elements.Superposition.LineLetter),
          ℓ ∈ c.law.premises → Elements.Superposition.Lit.Holds v ℓ) →
        Elements.Superposition.Lit.Holds v c.law.conclusion
-/
#guard_msgs in
#check @Elements.Superposition.Cited.holds_iff

/--
info: 'Elements.Superposition.Cited.holds_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_iff

/--
info: def Elements.Superposition.Rule.Figure : Elements.Superposition.Interpretation →
  List Elements.Superposition.Cited → Prop :=
fun I cites =>
  ∀ {n m : Nat} {Γ : List (Elements.Superposition.Lit (Fin n) (Fin m))} {a b c d g h : Fin n} {l : Fin m}
    {φ : Elements.Superposition.Metric (Fin n)},
    Elements.Superposition.Derives cites (Elements.Superposition.branch Γ a b c d g h l)
        (Elements.Superposition.Lit.pos
          (Elements.Superposition.Metric.map Elements.Superposition.Name.given φ).toAtom) →
      ∀ (v : Elements.Superposition.Val I (Fin n) (Fin m)),
        Elements.Superposition.Triangle I (v.pt a) (v.pt b) (v.pt c) →
          I.OnLine (v.pt d) (v.line l) →
            I.OnLine (v.pt g) (v.line l) →
              v.pt d ≠ v.pt g →
                ¬I.OnLine (v.pt h) (v.line l) →
                  (∀ (ℓ : Elements.Superposition.Lit (Fin n) (Fin m)), ℓ ∈ Γ → Elements.Superposition.Lit.Holds v ℓ) →
                    Elements.Superposition.Metric.Holds v φ
-/
#guard_msgs in
#print Elements.Superposition.Rule.Figure

/--
info: @Elements.Superposition.Rule.iff_figure : ∀ {I : Elements.Superposition.Interpretation},
  Elements.Superposition.Rule I ↔
    ∀ (cites : List Elements.Superposition.Cited),
      (∀ (c : Elements.Superposition.Cited), c ∈ cites → Elements.Superposition.Cited.Holds I c) →
        Elements.Superposition.Rule.Figure I cites
-/
#guard_msgs in
#check @Elements.Superposition.Rule.iff_figure

/--
info: 'Elements.Superposition.Rule.iff_figure' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.Rule.iff_figure

/--
info: structure Elements.Superposition.Interpretation.Embedding (J I : Elements.Superposition.Interpretation) : Type
number of parameters: 2
fields:
  Elements.Superposition.Interpretation.Embedding.pt : J.Point → I.Point
  Elements.Superposition.Interpretation.Embedding.line : J.Line → I.Line
  Elements.Superposition.Interpretation.Embedding.pt_inj : ∀ {p q : J.Point}, self.pt p = self.pt q → p = q
  Elements.Superposition.Interpretation.Embedding.onLine_iff : ∀ {p : J.Point} {L : J.Line},
      I.OnLine (self.pt p) (self.line L) ↔ J.OnLine p L
  Elements.Superposition.Interpretation.Embedding.between_iff : ∀ {p q r : J.Point},
      I.Between (self.pt p) (self.pt q) (self.pt r) ↔ J.Between p q r
  Elements.Superposition.Interpretation.Embedding.sameSide_iff : ∀ {p q : J.Point} {L : J.Line},
      I.SameSide (self.pt p) (self.pt q) (self.line L) ↔ J.SameSide p q L
  Elements.Superposition.Interpretation.Embedding.len_iff : ∀ {p q r s : J.Point},
      I.len (self.pt p) (self.pt q) = I.len (self.pt r) (self.pt s) ↔ J.len p q = J.len r s
  Elements.Superposition.Interpretation.Embedding.ang_iff : ∀ {p q r s t u : J.Point},
      I.ang (self.pt p) (self.pt q) (self.pt r) = I.ang (self.pt s) (self.pt t) (self.pt u) ↔ J.ang p q r = J.ang s t u
  Elements.Superposition.Interpretation.Embedding.area_iff : ∀ {p q r s t u : J.Point},
      I.area (self.pt p) (self.pt q) (self.pt r) = I.area (self.pt s) (self.pt t) (self.pt u) ↔
        J.area p q r = J.area s t u
  Elements.Superposition.Interpretation.Embedding.line_through : ∀ {p q : J.Point} {N : I.Line},
      p ≠ q → I.OnLine (self.pt p) N → I.OnLine (self.pt q) N → ∃ L, self.line L = N
  Elements.Superposition.Interpretation.Embedding.on_line : ∀ {p : J.Point} {N : I.Line},
      I.OnLine (self.pt p) N → ∃ L, J.OnLine p L
constructor:
  Elements.Superposition.Interpretation.Embedding.mk {J I : Elements.Superposition.Interpretation}
    (pt : J.Point → I.Point) (line : J.Line → I.Line) (pt_inj : ∀ {p q : J.Point}, pt p = pt q → p = q)
    (onLine_iff : ∀ {p : J.Point} {L : J.Line}, I.OnLine (pt p) (line L) ↔ J.OnLine p L)
    (between_iff : ∀ {p q r : J.Point}, I.Between (pt p) (pt q) (pt r) ↔ J.Between p q r)
    (sameSide_iff : ∀ {p q : J.Point} {L : J.Line}, I.SameSide (pt p) (pt q) (line L) ↔ J.SameSide p q L)
    (len_iff : ∀ {p q r s : J.Point}, I.len (pt p) (pt q) = I.len (pt r) (pt s) ↔ J.len p q = J.len r s)
    (ang_iff :
      ∀ {p q r s t u : J.Point}, I.ang (pt p) (pt q) (pt r) = I.ang (pt s) (pt t) (pt u) ↔ J.ang p q r = J.ang s t u)
    (area_iff :
      ∀ {p q r s t u : J.Point},
        I.area (pt p) (pt q) (pt r) = I.area (pt s) (pt t) (pt u) ↔ J.area p q r = J.area s t u)
    (line_through : ∀ {p q : J.Point} {N : I.Line}, p ≠ q → I.OnLine (pt p) N → I.OnLine (pt q) N → ∃ L, line L = N)
    (on_line : ∀ {p : J.Point} {N : I.Line}, I.OnLine (pt p) N → ∃ L, J.OnLine p L) : J.Embedding I
-/
#guard_msgs in
#print Elements.Superposition.Interpretation.Embedding

/--
info: @Elements.Superposition.Rule.Figure.restrict : ∀ {I J : Elements.Superposition.Interpretation} (e : J.Embedding I)
  {cites : List Elements.Superposition.Cited},
  Elements.Superposition.Rule.Figure I cites → Elements.Superposition.Rule.Figure J cites
-/
#guard_msgs in
#check @Elements.Superposition.Rule.Figure.restrict

/--
info: 'Elements.Superposition.Rule.Figure.restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.Rule.Figure.restrict

/--
info: @Elements.Superposition.Metric.holds_const : ∀ {I : Elements.Superposition.Interpretation} {P L : Type}
  (m : Elements.Superposition.Metric P) (X : I.Point) (N : L → I.Line),
  Elements.Superposition.Metric.Holds { pt := fun x => X, line := N } m
-/
#guard_msgs in
#check @Elements.Superposition.Metric.holds_const

/--
info: 'Elements.Superposition.Metric.holds_const' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.Metric.holds_const

/--
info: @Elements.Superposition.valuation_encodes : ∀ {I : Elements.Superposition.Interpretation} (Q : Prop) {X Y : I.Point},
  X ≠ Y →
    (Elements.Superposition.Lit.Holds { pt := fun i => if i = 0 then if Q then X else Y else Y, line := Fin.elim0 }
        (Elements.Superposition.Lit.pos (Elements.Superposition.Atom.eq 0 1)) ↔
      ¬Q)
-/
#guard_msgs in
#check @Elements.Superposition.valuation_encodes

/--
info: 'Elements.Superposition.valuation_encodes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.valuation_encodes

/--
info: @Elements.Superposition.eliminator_iff_exists : ∀ {I : Elements.Superposition.Interpretation}
  (placed : I.Point → I.Point → Prop),
  (∀ (Q : Prop), (∀ (B' C' : I.Point), placed B' C' → Q) → Q) ↔ ∃ B' C', placed B' C'
-/
#guard_msgs in
#check @Elements.Superposition.eliminator_iff_exists

/--
info: 'Elements.Superposition.eliminator_iff_exists' does not depend on any axioms
-/
#guard_msgs in
#print axioms Elements.Superposition.eliminator_iff_exists

/--
info: @Elements.Superposition.eliminator_false_gives_exists : ∀ {I : Elements.Superposition.Interpretation}
  (placed : I.Point → I.Point → Prop), ((∀ (B' C' : I.Point), placed B' C' → False) → False) → ∃ B' C', placed B' C'
-/
#guard_msgs in
#check @Elements.Superposition.eliminator_false_gives_exists

/--
info: 'Elements.Superposition.eliminator_false_gives_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.eliminator_false_gives_exists

/--
info: @Elements.Superposition.Rule.apply : ∀ {I : Elements.Superposition.Interpretation} {P L : Type},
  Elements.Superposition.Rule I →
    ∀ [Elements.Superposition.Symbols P] [Elements.Superposition.Symbols L] {cites : List Elements.Superposition.Cited},
      (∀ (c : Elements.Superposition.Cited), c ∈ cites → Elements.Superposition.Cited.Holds I c) →
        ∀ {Γ : List (Elements.Superposition.Lit P L)} {a b c d g h : P} {l : L} {φ : Elements.Superposition.Metric P},
          Elements.Superposition.Derives cites (Elements.Superposition.branch Γ a b c d g h l)
              (Elements.Superposition.Lit.pos
                (Elements.Superposition.Metric.map Elements.Superposition.Name.given φ).toAtom) →
            ∀ (v : Elements.Superposition.Val I P L),
              Elements.Superposition.Triangle I (v.pt a) (v.pt b) (v.pt c) →
                I.OnLine (v.pt d) (v.line l) →
                  I.OnLine (v.pt g) (v.line l) →
                    v.pt d ≠ v.pt g →
                      ¬I.OnLine (v.pt h) (v.line l) →
                        (∀ (ℓ : Elements.Superposition.Lit P L), ℓ ∈ Γ → Elements.Superposition.Lit.Holds v ℓ) →
                          Elements.Superposition.Metric.Holds v φ
-/
#guard_msgs in
#check @Elements.Superposition.Rule.apply

/--
info: 'Elements.Superposition.Rule.apply' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Elements.Superposition.Rule.apply

/--
info: 'Elements.Superposition.onLine_of_angle_eq_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_symm,
 Elements.Tacit.line_unique,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.triple_incidence2]
-/
#guard_msgs in
#print axioms Elements.Superposition.onLine_of_angle_eq_named

/--
info: 'Elements.Superposition.Cited.holds_lenSymm' depends on axioms: [Classical.choice, Elements.Tacit.len_symm]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_lenSymm

/--
info: 'Elements.Superposition.Cited.holds_angleSymm' depends on axioms: [propext, Classical.choice, Elements.Tacit.angle_symm]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_angleSymm

/--
info: 'Elements.Superposition.Cited.holds_areaCongruent' depends on axioms: [propext,
 Classical.choice,
 Elements.Tacit.area_congruent]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_areaCongruent

/--
info: 'Elements.Superposition.Cited.holds_neOfLen' depends on axioms: [propext,
 Classical.choice,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.len_self]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_neOfLen

/--
info: 'Elements.Superposition.Cited.holds_rayUnique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.between_cases,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_lt_zero]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_rayUnique

/--
info: 'Elements.Superposition.Cited.holds_rayOfAngle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_symm,
 Elements.Tacit.line_unique,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.triple_incidence2]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_rayOfAngle

/--
info: 'Elements.Superposition.Cited.holds_rayOfAngleSide' depends on axioms: [propext,
 Classical.choice,
 Elements.Tacit.pasch3]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_rayOfAngleSide

/--
info: 'Elements.Superposition.Cited.holds_of_drawsNothing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
 Elements.Tacit.between_cases,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_unique,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.pasch3,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.triple_incidence2]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_of_drawsNothing

/--
info: 'Elements.BookI.Prop4.cites_drawNothing' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Elements.BookI.Prop4.cites_drawNothing

/--
info: 'Elements.BookI.Prop8.holds_prop7' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_rotate,
 Elements.Tacit.area_swap,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_between_left,
 Elements.Tacit.between_of_between_right,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.inside_of_len_lt,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_lt_of_inside,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.ne_of_between_ends,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_between_of_between_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.on_line_of_between,
 Elements.Tacit.on_line_of_between_ends,
 Elements.Tacit.pasch2,
 Elements.Tacit.pasch3,
 Elements.Tacit.pasch4,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_or,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition,
 Elements.Tacit.triple_incidence1,
 Elements.Tacit.triple_incidence2]
-/
#guard_msgs in
#print axioms Elements.BookI.Prop8.holds_prop7

/--
info: Elements.Superposition.Cited.holds_all : ∀ (c : Elements.Superposition.Cited),
  Elements.Superposition.Cited.Holds Elements.primitives c
-/
#guard_msgs in
#check @Elements.Superposition.Cited.holds_all

/--
info: 'Elements.Superposition.Cited.holds_all' depends on axioms: [propext,
 Classical.choice,
 Elements.Definition15,
 Elements.Postulate1,
 Elements.Postulate2,
 Elements.Postulate3,
 Quot.sound,
 Elements.Tacit.add_comm,
 Elements.Tacit.add_lt_add_right,
 Elements.Tacit.add_zero,
 Elements.Tacit.angle_add_of_inside,
 Elements.Tacit.angle_eq_of_same_rays,
 Elements.Tacit.angle_symm,
 Elements.Tacit.area_congruent,
 Elements.Tacit.area_rotate,
 Elements.Tacit.area_swap,
 Elements.Tacit.between_cases,
 Elements.Tacit.between_of_between_left,
 Elements.Tacit.between_of_between_right,
 Elements.Tacit.between_symm,
 Elements.Tacit.centre_inside,
 Elements.Tacit.circles_meet,
 Elements.Tacit.circles_meet_same_side,
 Elements.Tacit.eq_of_len_eq_zero,
 Elements.Tacit.exists_point,
 Elements.Tacit.exists_point_between,
 Elements.Tacit.inside_of_len_lt,
 Elements.Tacit.len_add_of_between,
 Elements.Tacit.len_lt_of_inside,
 Elements.Tacit.len_self,
 Elements.Tacit.len_symm,
 Elements.Tacit.line_circle_between,
 Elements.Tacit.line_circle_beyond,
 Elements.Tacit.line_unique,
 Elements.Tacit.lines_meet_of_opposite_sides,
 Elements.Tacit.lt_irrefl,
 Elements.Tacit.lt_trans,
 Elements.Tacit.lt_trichotomy,
 Elements.Tacit.ne_of_between,
 Elements.Tacit.ne_of_between_ends,
 Elements.Tacit.not_between_of_between,
 Elements.Tacit.not_between_of_between_between,
 Elements.Tacit.not_lt_zero,
 Elements.Tacit.not_on_line_of_same_side,
 Elements.Tacit.on_line_of_between,
 Elements.Tacit.on_line_of_between_ends,
 Elements.Tacit.pasch2,
 Elements.Tacit.pasch3,
 Elements.Tacit.pasch4,
 Elements.Tacit.same_ray_of_angle_eq_zero,
 Elements.Tacit.same_side_or,
 Elements.Tacit.same_side_symm,
 Elements.Tacit.same_side_trans,
 Elements.Tacit.superposition,
 Elements.Tacit.triple_incidence1,
 Elements.Tacit.triple_incidence2]
-/
#guard_msgs in
#print axioms Elements.Superposition.Cited.holds_all
