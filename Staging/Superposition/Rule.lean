import Staging.Superposition.Derivations

/-!
# Superposition, restricted: the rule

The restricted rule of superposition, as a hypothesis `Rule` that theorems take as an
argument ([brief 0009](../../docs/briefs/0009-superposition.md)). Nothing here is an axiom.

System E writes the rule as a sequent inference (Avigad, Dean and Mumma, 2009, §3.7). We read
it so: if the facts Γ, with the facts Π of a triangle laid down, prove Δ′, then Γ proves Δ′,
where Δ′ speaks only of the objects Γ already has. Ours is that inference over a finite
symbolic context:

* **The figure's symbols.** The given facts Γ are literals over the symbols `Fin n` for
  points and `Fin m` for straight lines; a valuation `v` says which point and which straight
  line each symbol stands for, and the rule asks that Γ hold under it.
* **The placement's symbols** (`Name`, `LineName`). Laid down with A on D, the triangle ABC
  becomes D B′ C′, its side AC a straight line through D and C′. The placement adds exactly
  three symbols to the figure's: `Name.second` (B′), `Name.third` (C′) and `LineName.side`
  (the side AC laid down). They are fresh by their type: no symbol of the figure is one of
  them, and no valuation of the figure gives them a point or a straight line.
* **The guards.** The triangle ABC is a triangle; D and G are two points of the straight line
  L, so the ray from D through G has a direction; H is off L, so it has a side. These are the
  hypotheses of the present rule, `Tacit.superposition`. Those that are literals are
  available in the placement (`guards`).
* **What the placement keeps** (`kept`). B′ is on the ray from D through G, C′ is on H's side
  of L, and each side and each angle is kept: the present rule's conclusion, word for word.
  And the side AC, laid down, is a straight line through D and C′: Euclid's "the straight
  line AC" of I.4, as it falls.
* **What it exports.** One equality of lengths, angles or triangles over the figure's
  symbols, a `Metric (Fin n)`, which can name no symbol of the placement.
* **What it assumes.** Nothing about lengths, angles, areas or rays: a derivation cites the
  laws it uses (`Cited`), and the rule asks each of them to hold.

The derivation comes before the valuation in the rule's statement: one derivation, over
symbols, gives the conclusion for every figure that satisfies the guards and the given facts.

`Symbols` lets a proof name its symbols with an inductive type of its own (`Rule.apply`);
`Rule.of_placement` shows that wherever triangles can be laid down, as the present rule
says, with the side AC drawn, the restricted rule holds, by logic alone.
-/

namespace Elements.Superposition

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

/-- The valuation of a placement: the figure's symbols as `v` says, B′ at `B'`, C′ at `C'`
and the side laid down along `N`. -/
def Val.place (v : Val P L) (B' C' : Point) (N : Line) : Val (Name P) (LineName L) where
  pt
    | .given p => v.pt p
    | .second => B'
    | .third => C'
  line
    | .given l => v.line l
    | .side => N

open Lit Tacit

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

/-- **The restricted rule of superposition**, as a hypothesis. For a triangle abc, a ray from
d through g along the straight line l, and a point h off l, all symbols of the figure: an
equality of lengths, angles or triangles over the figure's symbols that a restricted
derivation proves from the given facts Γ, the guards and what the placement keeps, holds in
every figure that satisfies the guards and Γ. A derivation may cite the laws listed in
`cites`, once they hold.

The placement's symbols are symbols of the derivation and nowhere else: the conclusion is a
`Metric (Fin n)`, which names only the figure's symbols, and the valuation `v` gives a point
and a straight line to the figure's symbols only. -/
structure Rule : Prop where
  /-- Use the rule: lay abc down on the ray from d through g, on h's side, and keep what a
  restricted derivation proves of the figure. -/
  infer : ∀ {cites : List Cited}, (∀ c ∈ cites, c.Holds) →
    ∀ {n m : Nat} {Γ : List (Lit (Fin n) (Fin m))} {a b c d g h : Fin n} {l : Fin m}
      {φ : Metric (Fin n)},
      Derives cites (branch Γ a b c d g h l) (pos (φ.map Name.given).toAtom) →
      ∀ v : Val (Fin n) (Fin m), Triangle (v.pt a) (v.pt b) (v.pt c) →
        OnLine (v.pt d) (v.line l) → OnLine (v.pt g) (v.line l) → v.pt d ≠ v.pt g →
        ¬ OnLine (v.pt h) (v.line l) → (∀ ℓ ∈ Γ, ℓ.Holds v) → φ.Holds v

/-! ## Naming the symbols

The rule numbers its symbols. A proof may name them instead, with an inductive type of its
own, once it numbers them: `Symbols`. -/

/-- **A finite vocabulary**: its symbols numbered `0`, …, `card - 1`, each number read back
as its symbol. -/
class Symbols (P : Type) where
  /-- How many symbols there are. -/
  card : Nat
  /-- The number of a symbol. -/
  index : P → Fin card
  /-- The symbol a number stands for. -/
  symbol : Fin card → P
  /-- A symbol's number is read back as the symbol. -/
  symbol_index : ∀ p, symbol (index p) = p

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

/-- **The rule, with named symbols.** The rule for a figure whose symbols are named by finite
vocabularies `P` and `L` of the proof's own: number the symbols, and use the rule on the
numbers. -/
theorem Rule.apply (S : Rule) [Symbols P] [Symbols L] {cites : List Cited}
    (hcites : ∀ c ∈ cites, c.Holds) {Γ : List (Lit P L)} {a b c d g h : P} {l : L}
    {φ : Metric P}
    (dφ : Derives cites (branch Γ a b c d g h l) (pos (φ.map Name.given).toAtom))
    (v : Val P L) (hT : Triangle (v.pt a) (v.pt b) (v.pt c)) (hd : OnLine (v.pt d) (v.line l))
    (hg : OnLine (v.pt g) (v.line l)) (hdg : v.pt d ≠ v.pt g) (hh : ¬ OnLine (v.pt h) (v.line l))
    (hΓ : ∀ ℓ ∈ Γ, ℓ.Holds v) : φ.Holds v := by
  let i : P → Fin (Symbols.card P) := Symbols.index
  let j : L → Fin (Symbols.card L) := Symbols.index
  /- The figure, on the numbers: each number stands for what its symbol stands for. -/
  let w : Val (Fin (Symbols.card P)) (Fin (Symbols.card L)) :=
    v.comap Symbols.symbol Symbols.symbol
  have hw : w.comap i j = v := by
    cases v with
    | mk pt line =>
      simp only [w, i, j, Val.comap, Val.mk.injEq]
      exact ⟨funext fun p => congrArg pt (Symbols.symbol_index p),
        funext fun l => congrArg line (Symbols.symbol_index l)⟩
  have hpt : ∀ p, w.pt (i p) = v.pt p := fun p => congrArg (fun u => u.pt p) hw
  have hline : ∀ l, w.line (j l) = v.line l := fun l => congrArg (fun u => u.line l) hw
  /- The derivation, on the numbers. -/
  have d' := dφ.map (Name.map i) (LineName.map j)
  rw [branch_map] at d'
  have hφ : (pos (φ.map Name.given).toAtom : Lit (Name P) (LineName L)).map (Name.map i)
      (LineName.map j) = pos ((φ.map i).map Name.given).toAtom := by
    cases φ <;> rfl
  rw [hφ] at d'
  have key := S.infer hcites d' w (by rw [hpt, hpt, hpt]; exact hT) (by rw [hpt, hline]; exact hd)
    (by rw [hpt, hline]; exact hg) (by rw [hpt, hpt]; exact hdg) (by rw [hpt, hline]; exact hh)
    (by
      intro ℓ hℓ
      obtain ⟨ℓ₀, hℓ₀, rfl⟩ := List.mem_map.1 hℓ
      rw [Lit.holds_map, hw]
      exact hΓ ℓ₀ hℓ₀)
  rw [Metric.holds_map i j, hw] at key
  exact key

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

/-! ## No stronger than laying a triangle down -/

/-- The triangle ABC, laid down with A on D, is D B′ C′, with B′ on the ray from D through G
and C′ on H's side of L, its sides and angles kept: the conclusion of the present rule,
`Tacit.superposition`, word for word. -/
def Placed (A B C D G H : Point) (L : Line) (B' C' : Point) : Prop :=
  OnLine B' L ∧ ¬ Between B' D G ∧ SameSide C' H L ∧
    ‖D B'‖ = ‖A B‖ ∧ ‖B' C'‖ = ‖B C‖ ∧ ‖C' D‖ = ‖C A‖ ∧
    ∠ B' D C' = ∠ B A C ∧ ∠ D C' B' = ∠ A C B ∧ ∠ C' B' D = ∠ C B A

/-- **Wherever a triangle can be laid down, the restricted rule holds.** If every triangle can
be laid down on every ray, on either side, as the present rule says, with a straight line
through D and C′ for its side AC, then `Rule` holds, by logic alone: `Derives.sound` uses only
the laws a derivation cites, which the rule assumes rather than asserts. So the restricted
rule is no stronger than the present one with Postulate 1 (the `example` below), and a model
of the plane satisfies it once triangles can be laid down there. -/
theorem Rule.of_placement
    (hplace : ∀ {A B C D G H : Point} {L : Line}, Triangle A B C → OnLine D L → OnLine G L →
      D ≠ G → ¬ OnLine H L →
      ∃ B' C' : Point, ∃ N : Line, Placed A B C D G H L B' C' ∧ OnLine D N ∧ OnLine C' N) :
    Rule := by
  refine ⟨fun {cites} hcites {n m Γ a b c d g h l φ} dφ v hT hd hg hdg hh hΓ => ?_⟩
  obtain ⟨B', C', N, ⟨hB'L, hB'DG, hC'H, hDB', hB'C', hC'D, hB'DC', hDC'B', hC'B'D⟩, hDN,
    hC'N⟩ := hplace hT hd hg hdg hh
  /- Read the placement's symbols as the points and the straight line just found. -/
  let w := v.place B' C' N
  have hw : w.comap Name.given LineName.given = v := rfl
  have hbranch : ∀ ℓ ∈ branch Γ a b c d g h l, ℓ.Holds w := by
    intro ℓ hℓ
    simp only [branch, List.mem_append, List.mem_map] at hℓ
    rcases hℓ with ⟨ℓ₀, hℓ₀, rfl⟩ | hk
    · rw [Lit.holds_map, hw]
      rcases hℓ₀ with hΓ₀ | hg₀
      · exact hΓ ℓ₀ hΓ₀
      · simp only [guards, List.mem_cons, List.mem_nil_iff, or_false] at hg₀
        rcases hg₀ with rfl | rfl | rfl | rfl
        · exact hd
        · exact hg
        · exact hdg
        · exact hh
    · simp only [kept, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hB'L
      · exact hB'DG
      · exact hC'H
      · exact hDB'
      · exact hB'C'
      · exact hC'D
      · exact hB'DC'
      · exact hDC'B'
      · exact hC'B'D
      · exact hDN
      · exact hC'N
  have hd' := Derives.sound hcites w hbranch dφ
  show (φ.toAtom : Atom (Fin n) (Fin m)).Holds v
  rw [← hw, ← Atom.holds_map, ← Metric.toAtom_map]
  exact hd'

/-- The present rule, with Postulate 1 for the side laid down, satisfies the restricted one:
`Rule` holds in today's foundations. This checks that `Placed` is the present rule's
conclusion; nothing may cite it. -/
example : Rule :=
  Rule.of_placement fun hABC hD hG hDG hH => by
    obtain ⟨B', C', hB'L, hB'DG, hC'H, hDB', hB'C', hC'D, hB'DC', hDC'B', hC'B'D⟩ :=
      superposition hABC hD hG hDG hH
    have hC'D_ne : C' ≠ _ := Elements.ne_of_len_eq hC'D hABC.ne₁₃.symm
    obtain ⟨N, hDN, hC'N⟩ := Postulate1 _ _ hC'D_ne.symm
    exact ⟨B', C', N, ⟨hB'L, hB'DG, hC'H, hDB', hB'C', hC'D, hB'DC', hDC'B', hC'B'D⟩, hDN, hC'N⟩

end Elements.Superposition
