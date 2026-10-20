module

public import Init

/-!
# Superposition, restricted: the formulas

The language of the restricted rule of [brief
0009](../../../docs/briefs/0009-superposition.md), following System E's superposition rule
(Avigad, Dean and Mumma, 2009, §3.7). The rule is a hypothesis, `Rule`, which the theorems
built on it take as an argument.

System E lets a proof act as though a triangle had been laid down on another, but only to
prove facts about the figure already drawn: the corners laid down may never be handed back
as constructed points. To say that in Lean, the facts a hypothetical placement may use and
prove are written as data over **symbols**, and the figure is given separately, as a
**valuation** that says which point or straight line each symbol stands for. This file is
that language.

* A symbol is a member of a type the proof chooses: P for points, L for straight lines.
  The rule (`Rule`) takes its symbols from `Fin n` and `Fin m`, so a symbol is a number and
  nothing else; a proof may name its symbols with an inductive type of its own
  (`Symbols`, in `Soundness.lean`).
* An `Atom` is one of the primitive relations on symbols: equality of points, a point on a
  straight line, betweenness, the same side, and equality of two lengths, two angles or two
  triangles. A `Lit` is an atom or its denial. None of them holds a point, a straight line or
  a proposition: each says one primitive thing of the symbols it names.
* A `Metric` formula is an equality of lengths, of angles or of triangles: the only kind of
  conclusion the rule exports.
* A `Val` is a valuation: a point for each point symbol and a straight line for each line
  symbol. `Holds v` reads a formula in the plane under the valuation `v`.

Two symbols are one symbol only when they are the same symbol. So a derivation, which works
on symbols, can never learn that two of them stand for one point unless a step proves it.
-/

@[expose] public section

namespace Elements.Superposition

/-- A primitive relation on symbols. -/
inductive Atom (P L : Type) where
  /-- `p` and `q` are one point. -/
  | eq (p q : P)
  /-- `p` lies on the straight line `l`. -/
  | onLine (p : P) (l : L)
  /-- `q` lies between `p` and `r`. -/
  | between (p q r : P)
  /-- `p` and `q` lie on the same side of the straight line `l`. -/
  | sameSide (p q : P) (l : L)
  /-- The straight line `pq` is equal to the straight line `rs`. -/
  | len (p q r s : P)
  /-- The angle `pqr` is equal to the angle `stu`. -/
  | angle (p q r s t u : P)
  /-- The triangle `pqr` is equal to the triangle `stu`. -/
  | area (p q r s t u : P)

namespace Atom

variable {P L P' L' P'' L'' : Type}

/-- The atom with its point symbols renamed by `f` and its line symbols by `g`. -/
def map (f : P → P') (g : L → L') : Atom P L → Atom P' L'
  | eq p q => eq (f p) (f q)
  | onLine p l => onLine (f p) (g l)
  | between p q r => between (f p) (f q) (f r)
  | sameSide p q l => sameSide (f p) (f q) (g l)
  | len p q r s => len (f p) (f q) (f r) (f s)
  | angle p q r s t u => angle (f p) (f q) (f r) (f s) (f t) (f u)
  | area p q r s t u => area (f p) (f q) (f r) (f s) (f t) (f u)

/-- Renaming twice is renaming once, by the composite. -/
theorem map_map (f : P → P') (g : L → L') (f' : P' → P'') (g' : L' → L'') (a : Atom P L) :
    (a.map f g).map f' g' = a.map (f' ∘ f) (g' ∘ g) := by
  cases a <;> rfl

end Atom

/-- An atom, or its denial: the facts a placement may use and the steps it may take. -/
inductive Lit (P L : Type) where
  /-- The atom holds. -/
  | pos (a : Atom P L)
  /-- The atom does not hold. -/
  | neg (a : Atom P L)

namespace Lit

variable {P L P' L' P'' L'' : Type}

/-- The literal with its symbols renamed. -/
def map (f : P → P') (g : L → L') : Lit P L → Lit P' L'
  | pos a => pos (a.map f g)
  | neg a => neg (a.map f g)

/-- Renaming twice is renaming once, by the composite. -/
theorem map_map (f : P → P') (g : L → L') (f' : P' → P'') (g' : L' → L'') (ℓ : Lit P L) :
    (ℓ.map f g).map f' g' = ℓ.map (f' ∘ f) (g' ∘ g) := by
  cases ℓ <;> simp only [map, Atom.map_map]

end Lit

/-- An equality of magnitudes: of two lengths, two angles or two triangles. These are the
only conclusions the restricted rule exports. They name points and no straight line. -/
inductive Metric (P : Type) where
  /-- The straight line `pq` is equal to the straight line `rs`. -/
  | len (p q r s : P)
  /-- The angle `pqr` is equal to the angle `stu`. -/
  | angle (p q r s t u : P)
  /-- The triangle `pqr` is equal to the triangle `stu`. -/
  | area (p q r s t u : P)

namespace Metric

variable {P L P' L' P'' L'' : Type}

/-- The metric formula as an atom, in a language with any line symbols. -/
def toAtom : Metric P → Atom P L
  | len p q r s => .len p q r s
  | angle p q r s t u => .angle p q r s t u
  | area p q r s t u => .area p q r s t u

/-- The metric formula with its symbols renamed by `f`. -/
def map (f : P → P') : Metric P → Metric P'
  | len p q r s => len (f p) (f q) (f r) (f s)
  | angle p q r s t u => angle (f p) (f q) (f r) (f s) (f t) (f u)
  | area p q r s t u => area (f p) (f q) (f r) (f s) (f t) (f u)

/-- The symbols the metric formula names, in order. -/
def names : Metric P → List P
  | len p q r s => [p, q, r, s]
  | angle p q r s t u => [p, q, r, s, t, u]
  | area p q r s t u => [p, q, r, s, t, u]

/-- Renaming a metric formula and then reading it as an atom is reading it as an atom and
then renaming. -/
theorem toAtom_map (f : P → P') (g : L → L') (m : Metric P) :
    ((m.map f).toAtom : Atom P' L') = (m.toAtom : Atom P L).map f g := by
  cases m <;> rfl

/-- The symbols of a renamed formula are the renamed symbols. -/
theorem names_map (f : P → P') (m : Metric P) : (m.map f).names = m.names.map f := by
  cases m <;> rfl

end Metric

/-!
## The laws and the derivations

The steps a hypothetical placement may take, as a datatype ([brief
0009](../../../docs/briefs/0009-superposition.md)). `Derives cites Γ ℓ` says that the literal
`ℓ` follows from the literals `Γ`, all over the same symbols, by the rules below. This is a
checked judgment, with its hypotheses, theorem applications and conclusions controlled.

**A law is data.** A law the derivation may cite (`Law`) is a list of premises and one
conclusion, literals written in a fixed alphabet of letters (`Letter`, `LineLetter`). What
it asserts (`Law.Holds`) is that, whatever points and straight lines the letters stand for,
if the premises hold so does the conclusion. A law therefore asserts no existence: it has
no field in which an existential claim could be written.

**What a step may do.** There are two kinds of rule, and neither introduces a symbol.

* **Logic.** Point equality has reflexivity and symmetry rules, but no transitivity rule
  in `Derives`. Equality of lengths, angles and triangles has all three. Common Notion 4
  puts a point for one that coincides with it in a length, angle or triangle equality.
  Each of these three congruence constructors takes a `Coincidence` argument. A derivation
  supplies `Coincidence.step` when it takes that step; the certificate counts this marker.
  A transformer such as `Derives.map` passes the argument it receives, so renaming alone
  does not count as a use of Common Notion 4. These rules hold by logic alone.
* **Citing a law** (`Derives.cite`). A step names a law from the fixed list `Cited`, puts a
  symbol of the derivation for each of its letters, derives its premises, and concludes its
  conclusion. The law is applied to symbols the derivation already has: citing it draws
  nothing. The derivation may cite only the laws in its list `cites`.

**Why the laws are cited, not built in.** The restricted rule (`Rule`) asks every law a
derivation cites to hold, and assumes none of them. Were Metric 9 a rule of its own, the
rule of superposition would contain Metric 9, and the certificate of I.4, walking the
proof, would never see it: the derivation is data, and Lean records no dependency on the
facts a datatype mentions. Were I.7 a rule of its own, the foundations would assume what
Book I proves from I.4. Cited, each law is supplied by a proof, and the theorem that cites
it rests on that proof, where the certificate can see it.

**Why the list is fixed.** A law whose premises can never hold together holds vacuously.
Were any law with any proof allowed, one whose premises describe a placement and whose
conclusion is false would hold exactly when no placement exists, and citing it would turn
that absence into a contradiction, which classical logic turns into points (brief 0009,
"The design").

**What the laws' proofs draw.** Citing a law draws nothing in the placement; the law's own
proof, a universal statement proved outside it, may. Every law but I.7 is proved from the
library with no rule that constructs (`Cited.holds_of_drawsNothing`; brief 0009 lists the
axioms). The law of one ray for one angle names all three of its straight lines, the third
the one through the point it speaks of, so that its proof draws nothing: in I.4 that straight line
is the side AC laid down, which the placement supplies. I.7's proof draws the six straight
lines joining its points, produces two and cites I.5; Euclid's I.8 uses I.7 inside the
placement (brief 0009, question 4, approved as prototyped on 20 October 2026; its
finishing is tracked in #150).

`Derives.sound` shows that every step holds of the very points its symbols stand for, under
any valuation that makes the context true: the derivation needs no point and no straight
line beyond those its symbols stand for.
-/

/-- The letters a law is written in, for its points. -/
inductive Letter where
  | A | B | C | D | E | F | P

/-- The letters a law is written in, for its straight lines. -/
inductive LineLetter where
  | L | M | N

/-- **A law a derivation may cite**: premises and a conclusion, literals in the letters. -/
structure Law where
  /-- What the law needs. -/
  premises : List (Lit Letter LineLetter)
  /-- What the law gives. -/
  conclusion : Lit Letter LineLetter

/-- The laws a step of a derivation may cite. -/
inductive Cited where
  /-- Metric 3: the straight line AB is the straight line BA. -/
  | lenSymm
  /-- Metric 4: the angle ABC is the angle CBA. -/
  | angleSymm
  /-- Metric 9: triangles equal in all their sides and angles are equal in area. -/
  | areaCongruent
  /-- A straight line equal to one with two distinct ends has two distinct ends. -/
  | neOfLen
  /-- On a ray, one point lies at a given distance from its start (Savile's argument). -/
  | rayUnique
  /-- On one side of a straight line, one ray from a point of it makes a given angle with
  it: the point lies on that ray's straight line. -/
  | rayOfAngle
  /-- The same, for the side of the point: it is not behind the corner. -/
  | rayOfAngleSide
  /-- I.7: two points on one side of a straight line, as far from each of its ends as one
  another, are one point. Euclid's I.8 uses it inside the placement. -/
  | prop7
  deriving DecidableEq

open Lit in
/-- The premises of the laws of one ray for one angle. With D and E on L, D and F on M, and
D and P on N: D is not E, P is on F's side of L, and the angle EDP is the angle EDF. -/
def rayOfAnglePremises : List (Lit Letter LineLetter) :=
  [neg (.eq .D .E), pos (.onLine .D .L), pos (.onLine .E .L), pos (.onLine .D .M),
   pos (.onLine .F .M), pos (.onLine .D .N), pos (.onLine .P .N), pos (.sameSide .P .F .L),
   pos (.angle .E .D .P .E .D .F)]

open Lit in
/-- **The laws, as data**, each exactly as a step uses it. -/
def Cited.law : Cited → Law
  | lenSymm => ⟨[], pos (.len .A .B .B .A)⟩
  | angleSymm => ⟨[neg (.eq .A .B), neg (.eq .C .B)], pos (.angle .A .B .C .C .B .A)⟩
  | areaCongruent =>
    ⟨[pos (.len .A .B .D .E), pos (.len .B .C .E .F), pos (.len .C .A .F .D),
      pos (.angle .A .B .C .D .E .F), pos (.angle .B .C .A .E .F .D),
      pos (.angle .C .A .B .F .D .E)],
     pos (.area .A .B .C .D .E .F)⟩
  | neOfLen => ⟨[pos (.len .A .B .C .D), neg (.eq .C .D)], neg (.eq .A .B)⟩
  | rayUnique =>
    ⟨[neg (.eq .A .B), neg (.eq .P .A), pos (.onLine .A .L), pos (.onLine .B .L),
      pos (.onLine .P .L), neg (.between .P .A .B), pos (.len .A .P .A .B)],
     pos (.eq .P .B)⟩
  | rayOfAngle => ⟨rayOfAnglePremises, pos (.onLine .P .M)⟩
  | rayOfAngleSide => ⟨rayOfAnglePremises, neg (.between .P .D .F)⟩
  | prop7 =>
    ⟨[neg (.eq .A .B), pos (.onLine .A .L), pos (.onLine .B .L), pos (.sameSide .C .D .L),
      pos (.len .C .A .D .A), pos (.len .C .B .D .B)],
     pos (.eq .C .D)⟩

/-- The laws whose proofs from the library draw nothing: every law but I.7, whose proof the theorem
citing it supplies. -/
def Cited.drawsNothing : Cited → Bool
  | prop7 => false
  | _ => true

open Lit

/-- Common Notion 4's step in the calculus. A derivation that takes a congruence step
supplies this marker, and the certificate counts it. -/
inductive Coincidence : Prop where
  | step

/-- **A restricted derivation.** `Derives cites Γ ℓ`: the literal `ℓ` follows from the
literals `Γ` by logic and by the laws listed in `cites`, all over the same symbols. No rule
introduces a symbol, so no step constructs anything. -/
inductive Derives {P L : Type} (cites : List Cited) (Γ : List (Lit P L)) : Lit P L → Prop where
  /-- A fact of the context. -/
  | given {ℓ : Lit P L} : ℓ ∈ Γ → Derives cites Γ ℓ
  /-- A point is itself. -/
  | eq_refl {p : P} : Derives cites Γ (pos (.eq p p))
  /-- If p is q, q is p. -/
  | eq_symm {p q : P} : Derives cites Γ (pos (.eq p q)) → Derives cites Γ (pos (.eq q p))
  /-- If p is not q, q is not p. -/
  | ne_symm {p q : P} : Derives cites Γ (neg (.eq p q)) → Derives cites Γ (neg (.eq q p))
  /-- A length is equal to itself. -/
  | len_refl {p q : P} : Derives cites Γ (pos (.len p q p q))
  /-- Equality of lengths is symmetric. -/
  | len_symm {p q r s : P} :
      Derives cites Γ (pos (.len p q r s)) → Derives cites Γ (pos (.len r s p q))
  /-- Equality of lengths is transitive (Common Notion 1). -/
  | len_trans {p q r s t u : P} :
      Derives cites Γ (pos (.len p q r s)) → Derives cites Γ (pos (.len r s t u)) →
      Derives cites Γ (pos (.len p q t u))
  /-- An angle is equal to itself. -/
  | angle_refl {p q r : P} : Derives cites Γ (pos (.angle p q r p q r))
  /-- Equality of angles is symmetric. -/
  | angle_symm {p q r s t u : P} :
      Derives cites Γ (pos (.angle p q r s t u)) → Derives cites Γ (pos (.angle s t u p q r))
  /-- Equality of angles is transitive (Common Notion 1). -/
  | angle_trans {p q r s t u x y z : P} :
      Derives cites Γ (pos (.angle p q r s t u)) →
      Derives cites Γ (pos (.angle s t u x y z)) → Derives cites Γ (pos (.angle p q r x y z))
  /-- A triangle is equal to itself. -/
  | area_refl {p q r : P} : Derives cites Γ (pos (.area p q r p q r))
  /-- Equality of triangles is symmetric. -/
  | area_symm {p q r s t u : P} :
      Derives cites Γ (pos (.area p q r s t u)) → Derives cites Γ (pos (.area s t u p q r))
  /-- Equality of triangles is transitive (Common Notion 1). -/
  | area_trans {p q r s t u x y z : P} :
      Derives cites Γ (pos (.area p q r s t u)) →
      Derives cites Γ (pos (.area s t u x y z)) → Derives cites Γ (pos (.area p q r x y z))
  /-- Straight lines whose ends coincide are equal (Common Notion 4). -/
  | len_congr (cn4 : Coincidence) {p q p' q' : P} :
      Derives cites Γ (pos (.eq p p')) → Derives cites Γ (pos (.eq q q')) →
      Derives cites Γ (pos (.len p q p' q'))
  /-- Angles whose points coincide are equal (Common Notion 4). -/
  | angle_congr (cn4 : Coincidence) {p q r p' q' r' : P} :
      Derives cites Γ (pos (.eq p p')) → Derives cites Γ (pos (.eq q q')) →
      Derives cites Γ (pos (.eq r r')) → Derives cites Γ (pos (.angle p q r p' q' r'))
  /-- Triangles whose corners coincide are equal (Common Notion 4). -/
  | area_congr (cn4 : Coincidence) {p q r p' q' r' : P} :
      Derives cites Γ (pos (.eq p p')) → Derives cites Γ (pos (.eq q q')) →
      Derives cites Γ (pos (.eq r r')) → Derives cites Γ (pos (.area p q r p' q' r'))
  /-- **Citing a law.** Put a symbol of the derivation for each letter of the law (`σ` for
  its points, `τ` for its straight lines), derive its premises, and conclude its
  conclusion. The law must be in the list `cites`. -/
  | cite (c : Cited) (σ : Letter → P) (τ : LineLetter → L)
      (premises : ∀ ℓ ∈ c.law.premises, Derives cites Γ (ℓ.map σ τ)) (cited : c ∈ cites) :
      Derives cites Γ (c.law.conclusion.map σ τ)

namespace Derives

variable {P L : Type} {cites : List Cited} {Γ : List (Lit P L)}

/-- **Every rule is a scheme in its symbols.** A derivation, its symbols renamed by any `f`
and `g` (even renamings that merge symbols), is a derivation from the renamed context. No
rule depends on which symbols it is given, and none introduces one. -/
theorem map {P' L' : Type} (f : P → P') (g : L → L') {ℓ : Lit P L}
    (d : Derives cites Γ ℓ) : Derives cites (Γ.map (Lit.map f g)) (ℓ.map f g) := by
  induction d with
  | given h => exact .given (List.mem_map_of_mem h)
  | eq_refl => exact .eq_refl
  | eq_symm _ ih => exact .eq_symm ih
  | ne_symm _ ih => exact .ne_symm ih
  | len_refl => exact .len_refl
  | len_symm _ ih => exact .len_symm ih
  | len_trans _ _ ih₁ ih₂ => exact .len_trans ih₁ ih₂
  | angle_refl => exact .angle_refl
  | angle_symm _ ih => exact .angle_symm ih
  | angle_trans _ _ ih₁ ih₂ => exact .angle_trans ih₁ ih₂
  | area_refl => exact .area_refl
  | area_symm _ ih => exact .area_symm ih
  | area_trans _ _ ih₁ ih₂ => exact .area_trans ih₁ ih₂
  | len_congr cn4 _ _ ih₁ ih₂ => exact .len_congr cn4 ih₁ ih₂
  | angle_congr cn4 _ _ _ ih₁ ih₂ ih₃ => exact .angle_congr cn4 ih₁ ih₂ ih₃
  | area_congr cn4 _ _ _ ih₁ ih₂ ih₃ => exact .area_congr cn4 ih₁ ih₂ ih₃
  | cite c σ τ _ hc ih =>
    rw [Lit.map_map]
    exact .cite c (f ∘ σ) (g ∘ τ) (fun ℓ hℓ => by rw [← Lit.map_map]; exact ih ℓ hℓ) hc

/-! ## The laws, as steps

Each cited law, as a step with its premises in order, so that a proof reads as Euclid's
sentences do. Each is `cite` with the letters put for the symbols named. -/

/-- The straight line pq is the straight line qp (Metric 3, cited). -/
theorem len_comm [Inhabited L] {p q : P} (hc : Cited.lenSymm ∈ cites := by decide) :
    Derives cites Γ (pos (.len p q q p)) :=
  .cite .lenSymm (fun | .A => p | _ => q) (fun _ => default) (by simp [Cited.law]) hc

/-- The angle pqr is the angle rqp, for p and r other than q (Metric 4, cited). -/
theorem angle_comm [Inhabited L] {p q r : P} (hpq : Derives cites Γ (neg (.eq p q)))
    (hrq : Derives cites Γ (neg (.eq r q))) (hc : Cited.angleSymm ∈ cites := by decide) :
    Derives cites Γ (pos (.angle p q r r q p)) :=
  .cite .angleSymm (fun | .A => p | .B => q | _ => r) (fun _ => default) (by
    intro ℓ hℓ
    simp only [Cited.law, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
    rcases hℓ with rfl | rfl
    · exact hpq
    · exact hrq) hc

/-- Triangles equal in all their sides and angles are equal in area (Metric 9, cited). -/
theorem area_of_congruent [Inhabited L] {p q r p' q' r' : P}
    (h₁ : Derives cites Γ (pos (.len p q p' q'))) (h₂ : Derives cites Γ (pos (.len q r q' r')))
    (h₃ : Derives cites Γ (pos (.len r p r' p')))
    (h₄ : Derives cites Γ (pos (.angle p q r p' q' r')))
    (h₅ : Derives cites Γ (pos (.angle q r p q' r' p')))
    (h₆ : Derives cites Γ (pos (.angle r p q r' p' q')))
    (hc : Cited.areaCongruent ∈ cites := by decide) :
    Derives cites Γ (pos (.area p q r p' q' r')) :=
  .cite .areaCongruent
    (fun | .A => p | .B => q | .C => r | .D => p' | .E => q' | _ => r') (fun _ => default) (by
    intro ℓ hℓ
    simp only [Cited.law, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
    · exact h₅
    · exact h₆) hc

/-- A straight line equal to a straight line with two distinct ends has two distinct ends
(cited). -/
theorem ne_of_len [Inhabited L] {p q r s : P} (hlen : Derives cites Γ (pos (.len p q r s)))
    (hrs : Derives cites Γ (neg (.eq r s))) (hc : Cited.neOfLen ∈ cites := by decide) :
    Derives cites Γ (neg (.eq p q)) :=
  .cite .neOfLen (fun | .A => p | .B => q | .C => r | _ => s) (fun _ => default) (by
    intro ℓ hℓ
    simp only [Cited.law, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
    rcases hℓ with rfl | rfl
    · exact hlen
    · exact hrs) hc

/-- **One point at one distance on a ray** (cited). A point `p` of the straight line `l`
through `a` and `b`, other than `a`, with `a` not between it and `b`, and as far from `a` as
`b` is, is `b`. -/
theorem ray_unique {a b p : P} {l : L} (hab : Derives cites Γ (neg (.eq a b)))
    (hpa : Derives cites Γ (neg (.eq p a))) (ha : Derives cites Γ (pos (.onLine a l)))
    (hb : Derives cites Γ (pos (.onLine b l))) (hp : Derives cites Γ (pos (.onLine p l)))
    (hpab : Derives cites Γ (neg (.between p a b))) (hlen : Derives cites Γ (pos (.len a p a b)))
    (hc : Cited.rayUnique ∈ cites := by decide) :
    Derives cites Γ (pos (.eq p b)) :=
  .cite .rayUnique (fun | .A => a | .B => b | _ => p) (fun _ => l) (by
    intro ℓ hℓ
    simp only [Cited.law, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hab
    · exact hpa
    · exact ha
    · exact hb
    · exact hp
    · exact hpab
    · exact hlen) hc

/-- **One ray for one angle**, its straight line (cited). With `d`, `e` on `l`, with `d`,
`f` on `m`, and with `d`, `p` on `n`: a point `p` on `f`'s side of `l` making the angle `edp`
equal to the angle `edf` lies on `m`. -/
theorem ray_of_angle {d e f p : P} {l m n : L} (hde : Derives cites Γ (neg (.eq d e)))
    (hd : Derives cites Γ (pos (.onLine d l))) (he : Derives cites Γ (pos (.onLine e l)))
    (hdm : Derives cites Γ (pos (.onLine d m))) (hfm : Derives cites Γ (pos (.onLine f m)))
    (hdn : Derives cites Γ (pos (.onLine d n))) (hpn : Derives cites Γ (pos (.onLine p n)))
    (hside : Derives cites Γ (pos (.sameSide p f l)))
    (hang : Derives cites Γ (pos (.angle e d p e d f)))
    (hc : Cited.rayOfAngle ∈ cites := by decide) :
    Derives cites Γ (pos (.onLine p m)) :=
  .cite .rayOfAngle (fun | .D => d | .E => e | .F => f | _ => p)
    (fun | .L => l | .M => m | .N => n) (by
    intro ℓ hℓ
    simp only [Cited.law, rayOfAnglePremises, List.mem_cons, List.mem_nil_iff,
      or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hde
    · exact hd
    · exact he
    · exact hdm
    · exact hfm
    · exact hdn
    · exact hpn
    · exact hside
    · exact hang) hc

/-- **One ray for one angle**, its side (cited). Under the same premises, `d` is not between
`p` and `f`: `p` lies on the ray from `d` through `f`. -/
theorem ray_of_angle_side {d e f p : P} {l m n : L} (hde : Derives cites Γ (neg (.eq d e)))
    (hd : Derives cites Γ (pos (.onLine d l))) (he : Derives cites Γ (pos (.onLine e l)))
    (hdm : Derives cites Γ (pos (.onLine d m))) (hfm : Derives cites Γ (pos (.onLine f m)))
    (hdn : Derives cites Γ (pos (.onLine d n))) (hpn : Derives cites Γ (pos (.onLine p n)))
    (hside : Derives cites Γ (pos (.sameSide p f l)))
    (hang : Derives cites Γ (pos (.angle e d p e d f)))
    (hc : Cited.rayOfAngleSide ∈ cites := by decide) :
    Derives cites Γ (neg (.between p d f)) :=
  .cite .rayOfAngleSide (fun | .D => d | .E => e | .F => f | _ => p)
    (fun | .L => l | .M => m | .N => n) (by
    intro ℓ hℓ
    simp only [Cited.law, rayOfAnglePremises, List.mem_cons, List.mem_nil_iff,
      or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hde
    · exact hd
    · exact he
    · exact hdm
    · exact hfm
    · exact hdn
    · exact hpn
    · exact hside
    · exact hang) hc

/-- **I.7** (cited). Two points `c`, `d` on one side of the straight line `l` through `a` and
`b`, with `ca` equal to `da` and `cb` to `db`, are one point. -/
theorem prop7 {a b c d : P} {l : L} (hab : Derives cites Γ (neg (.eq a b)))
    (ha : Derives cites Γ (pos (.onLine a l))) (hb : Derives cites Γ (pos (.onLine b l)))
    (hside : Derives cites Γ (pos (.sameSide c d l)))
    (hca : Derives cites Γ (pos (.len c a d a))) (hcb : Derives cites Γ (pos (.len c b d b)))
    (hc : Cited.prop7 ∈ cites := by decide) :
    Derives cites Γ (pos (.eq c d)) :=
  .cite .prop7 (fun | .A => a | .B => b | .C => c | _ => d) (fun _ => l) (by
    intro ℓ hℓ
    simp only [Cited.law, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hab
    · exact ha
    · exact hb
    · exact hside
    · exact hca
    · exact hcb) hc

end Derives

/-- The point symbols of a hypothetical placement: the figure's, and the two corners the
placement lays down. When the triangle ABC is laid down with A on D, `second` is where B
comes down and `third` is where C comes down. -/
inductive Name (P : Type) where
  /-- A point symbol of the figure. -/
  | given (p : P)
  /-- Where the second corner of the triangle comes down. -/
  | second
  /-- Where the third corner of the triangle comes down. -/
  | third

/-- The line symbols of a hypothetical placement: the figure's, and the side the placement
lays down from the first corner to the third. -/
inductive LineName (L : Type) where
  /-- A line symbol of the figure. -/
  | given (l : L)
  /-- The side from the first corner to the third, laid down: AC in I.4. -/
  | side

variable {P L P' L' : Type}

instance : Inhabited (LineName L) := ⟨.side⟩

/-- The point symbols of a placement, the figure's renamed by `f`. -/
def Name.map (f : P → P') : Name P → Name P'
  | given p => given (f p)
  | second => second
  | third => third

/-- The line symbols of a placement, the figure's renamed by `g`. -/
def LineName.map (g : L → L') : LineName L → LineName L'
  | given l => given (g l)
  | side => side

/-- **The guards**, as literals: D and G are on L and are two points, and H is off L. (That
ABC is a triangle is a guard too, but not a literal.) -/
def guards (d g h : P) (l : L) : List (Lit P L) :=
  [pos (.onLine d l), pos (.onLine g l), neg (.eq d g), neg (.onLine h l)]

/-- **What the placement keeps.** The triangle ABC laid down with A on D is D B′ C′, where B′
is `Name.second` and C′ is `Name.third`: B′ on L, with D not between B′ and G (on the ray from
D through G); C′ on H's side of L; DB′, B′C′, C′D equal to AB, BC, CA; the angles at D, C′
and B′ equal to those at A, C and B; and the side AC laid down, `LineName.side`, a straight
line through D and C′. -/
def kept (a b c d g h : P) (l : L) : List (Lit (Name P) (LineName L)) :=
  [pos (.onLine .second (.given l)), neg (.between .second (.given d) (.given g)),
   pos (.sameSide .third (.given h) (.given l)),
   pos (.len (.given d) .second (.given a) (.given b)),
   pos (.len .second .third (.given b) (.given c)),
   pos (.len .third (.given d) (.given c) (.given a)),
   pos (.angle .second (.given d) .third (.given b) (.given a) (.given c)),
   pos (.angle (.given d) .third .second (.given a) (.given c) (.given b)),
   pos (.angle .third .second (.given d) (.given c) (.given b) (.given a)),
   pos (.onLine (.given d) .side), pos (.onLine .third .side)]

/-- **The context of a hypothetical placement**: the given facts Γ and the guards, over the
figure's symbols, and what the placement keeps. -/
def branch (Γ : List (Lit P L)) (a b c d g h : P) (l : L) : List (Lit (Name P) (LineName L)) :=
  (Γ ++ guards d g h l).map (Lit.map .given .given) ++ kept a b c d g h l

/-- Renaming a placement's context renames the figure's facts and keeps the placement's. -/
theorem branch_map (f : P → P') (g' : L → L') (Γ : List (Lit P L)) (a b c d g h : P) (l : L) :
    (branch Γ a b c d g h l).map (Lit.map (Name.map f) (LineName.map g')) =
      branch (Γ.map (Lit.map f g')) (f a) (f b) (f c) (f d) (f g) (f h) (g' l) := by
  have hcomm : Lit.map (Name.map f) (LineName.map g') ∘ Lit.map Name.given LineName.given =
      Lit.map Name.given LineName.given ∘ Lit.map f g' := by
    funext ℓ
    simp only [Function.comp, Lit.map_map]
    rfl
  simp only [branch, List.map_append, List.map_map, hcomm]
  rfl

/-! ## The facts of the branch, by name

So that a derivation can say which fact it uses: `Kept.len₁` is "DB′ is AB", and so on. -/

section Facts

variable {cites : List Cited} {Γ : List (Lit P L)} {a b c d g h : P} {l : L}

/-- A given fact, in the placement. -/
theorem Branch.given {ℓ : Lit P L} (hℓ : ℓ ∈ Γ) :
    Derives cites (branch Γ a b c d g h l) (ℓ.map .given .given) :=
  .given (List.mem_append_left _ (List.mem_map_of_mem (List.mem_append_left _ hℓ)))

/-- A guard, in the placement. -/
theorem Branch.guard {ℓ : Lit P L} (hℓ : ℓ ∈ guards d g h l) :
    Derives cites (branch Γ a b c d g h l) (ℓ.map .given .given) :=
  .given (List.mem_append_left _ (List.mem_map_of_mem (List.mem_append_right _ hℓ)))

/-- A fact the placement keeps. -/
theorem Branch.kept {ℓ : Lit (Name P) (LineName L)} (hℓ : ℓ ∈ kept a b c d g h l) :
    Derives cites (branch Γ a b c d g h l) ℓ :=
  .given (List.mem_append_right _ hℓ)

/-- D is on L. -/
theorem Guard.on_D :
    Derives cites (branch Γ a b c d g h l) (pos (.onLine (.given d) (.given l))) :=
  Branch.guard (ℓ := pos (.onLine d l)) (by simp [guards])
/-- G is on L. -/
theorem Guard.on_G :
    Derives cites (branch Γ a b c d g h l) (pos (.onLine (.given g) (.given l))) :=
  Branch.guard (ℓ := pos (.onLine g l)) (by simp [guards])
/-- D is not G. -/
theorem Guard.ne_DG :
    Derives cites (branch Γ a b c d g h l) (neg (.eq (.given d) (.given g))) :=
  Branch.guard (ℓ := neg (.eq d g)) (by simp [guards])
/-- H is off L. -/
theorem Guard.off_H :
    Derives cites (branch Γ a b c d g h l) (neg (.onLine (.given h) (.given l))) :=
  Branch.guard (ℓ := neg (.onLine h l)) (by simp [guards])

/-- B′ is on L. -/
theorem Kept.on_line :
    Derives cites (branch Γ a b c d g h l) (pos (.onLine .second (.given l))) :=
  Branch.kept (by simp [kept])
/-- D is not between B′ and G: B′ is on the ray from D through G. -/
theorem Kept.not_between :
    Derives cites (branch Γ a b c d g h l) (neg (.between .second (.given d) (.given g))) :=
  Branch.kept (by simp [kept])
/-- C′ is on H's side of L. -/
theorem Kept.same_side :
    Derives cites (branch Γ a b c d g h l) (pos (.sameSide .third (.given h) (.given l))) :=
  Branch.kept (by simp [kept])
/-- DB′ is AB. -/
theorem Kept.len₁ :
    Derives cites (branch Γ a b c d g h l) (pos (.len (.given d) .second (.given a) (.given b))) :=
  Branch.kept (by simp [kept])
/-- B′C′ is BC. -/
theorem Kept.len₂ :
    Derives cites (branch Γ a b c d g h l) (pos (.len .second .third (.given b) (.given c))) :=
  Branch.kept (by simp [kept])
/-- C′D is CA. -/
theorem Kept.len₃ :
    Derives cites (branch Γ a b c d g h l) (pos (.len .third (.given d) (.given c) (.given a))) :=
  Branch.kept (by simp [kept])
/-- The angle B′DC′ is the angle BAC. -/
theorem Kept.angle₁ : Derives cites (branch Γ a b c d g h l)
    (pos (.angle .second (.given d) .third (.given b) (.given a) (.given c))) :=
  Branch.kept (by simp [kept])
/-- The angle DC′B′ is the angle ACB. -/
theorem Kept.angle₂ : Derives cites (branch Γ a b c d g h l)
    (pos (.angle (.given d) .third .second (.given a) (.given c) (.given b))) :=
  Branch.kept (by simp [kept])
/-- The angle C′B′D is the angle CBA. -/
theorem Kept.angle₃ : Derives cites (branch Γ a b c d g h l)
    (pos (.angle .third .second (.given d) (.given c) (.given b) (.given a))) :=
  Branch.kept (by simp [kept])
/-- The side AC laid down passes through D. -/
theorem Kept.side_first :
    Derives cites (branch Γ a b c d g h l) (pos (.onLine (.given d) .side)) :=
  Branch.kept (by simp [kept])
/-- The side AC laid down passes through C′. -/
theorem Kept.side_third :
    Derives cites (branch Γ a b c d g h l) (pos (.onLine .third .side)) :=
  Branch.kept (by simp [kept])

end Facts

/-! ## 1. No symbol of the placement is exported -/

/-- **A formula of the placement can be exported exactly when it names only the figure's
symbols.** The rule's conclusion is a `Metric` over the figure's symbols; a formula over the
placement's symbols is the image of one exactly when every symbol in it is the figure's. -/
theorem exportable_iff (m : Metric (Name P)) :
    (∃ m₀ : Metric P, m₀.map Name.given = m) ↔ ∀ n ∈ m.names, ∃ p : P, n = .given p := by
  constructor
  · rintro ⟨m₀, rfl⟩ n hn
    rw [Metric.names_map, List.mem_map] at hn
    obtain ⟨p, -, rfl⟩ := hn
    exact ⟨p, rfl⟩
  · intro h
    cases m with
    | len p q r s =>
      obtain ⟨p, rfl⟩ := h p (by simp [Metric.names])
      obtain ⟨q, rfl⟩ := h q (by simp [Metric.names])
      obtain ⟨r, rfl⟩ := h r (by simp [Metric.names])
      obtain ⟨s, rfl⟩ := h s (by simp [Metric.names])
      exact ⟨.len p q r s, rfl⟩
    | angle p q r s t u =>
      obtain ⟨p, rfl⟩ := h p (by simp [Metric.names])
      obtain ⟨q, rfl⟩ := h q (by simp [Metric.names])
      obtain ⟨r, rfl⟩ := h r (by simp [Metric.names])
      obtain ⟨s, rfl⟩ := h s (by simp [Metric.names])
      obtain ⟨t, rfl⟩ := h t (by simp [Metric.names])
      obtain ⟨u, rfl⟩ := h u (by simp [Metric.names])
      exact ⟨.angle p q r s t u, rfl⟩
    | area p q r s t u =>
      obtain ⟨p, rfl⟩ := h p (by simp [Metric.names])
      obtain ⟨q, rfl⟩ := h q (by simp [Metric.names])
      obtain ⟨r, rfl⟩ := h r (by simp [Metric.names])
      obtain ⟨s, rfl⟩ := h s (by simp [Metric.names])
      obtain ⟨t, rfl⟩ := h t (by simp [Metric.names])
      obtain ⟨u, rfl⟩ := h u (by simp [Metric.names])
      exact ⟨.area p q r s t u, rfl⟩

/-- **B′ is never exported.** A formula of the placement that names B′ (`Name.second`) is the
image of no conclusion the rule can give. -/
theorem not_exportable_second {m : Metric (Name P)} (h : Name.second ∈ m.names) :
    ¬ ∃ m₀ : Metric P, m₀.map Name.given = m := fun hm => by
  obtain ⟨p, hp⟩ := (exportable_iff m).1 hm _ h
  exact nomatch hp

/-- **C′ is never exported.** A formula of the placement that names C′ (`Name.third`) is the
image of no conclusion the rule can give. -/
theorem not_exportable_third {m : Metric (Name P)} (h : Name.third ∈ m.names) :
    ¬ ∃ m₀ : Metric P, m₀.map Name.given = m := fun hm => by
  obtain ⟨p, hp⟩ := (exportable_iff m).1 hm _ h
  exact nomatch hp

end Elements.Superposition
