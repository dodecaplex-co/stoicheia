module

public import Elements.Foundations.Superposition.Semantics

/-!
# Superposition, restricted: soundness

A derivation holds under any interpretation in which its cited laws hold. Renaming symbols
changes only how a valuation is read. If triangles can be laid down with their sides and
angles kept and their side AC drawn, the restricted rule follows by logic alone.
-/

@[expose] public section

namespace Elements.Superposition

variable {I : Interpretation} {P L P' L' : Type}

namespace Atom

/-- A renamed atom says under `v` what the atom says under `v` read through the renaming. -/
theorem holds_map (f : P → P') (g : L → L') (v : Val I P' L') (a : Atom P L) :
    (a.map f g).Holds v ↔ a.Holds (v.comap f g) := by
  cases a <;> exact Iff.rfl

end Atom

namespace Lit

/-- A renamed literal says under `v` what the literal says under `v` read through the
renaming. -/
theorem holds_map (f : P → P') (g : L → L') (v : Val I P' L') (ℓ : Lit P L) :
    (ℓ.map f g).Holds v ↔ ℓ.Holds (v.comap f g) := by
  cases ℓ with
  | pos a => exact Atom.holds_map f g v a
  | neg a => exact not_congr (Atom.holds_map f g v a)

end Lit

namespace Metric

/-- A renamed metric formula says under `v` what the formula says under `v` read through
the renaming. -/
theorem holds_map (f : P → P') (g : L → L') (v : Val I P' L') (m : Metric P) :
    (m.map f).Holds v ↔ m.Holds (v.comap f g) := by
  cases m <;> exact Iff.rfl

end Metric

/-- **A cited law asserts no existence.** It says that, whatever points and straight lines
its letters stand for, its premises give its conclusion: a universal statement about
primitive relations, with nothing to construct. -/
theorem Cited.holds_iff (c : Cited) :
    c.Holds I ↔ ∀ v : Val I Letter LineLetter, (∀ ℓ ∈ c.law.premises, ℓ.Holds v) →
      c.law.conclusion.Holds v :=
  Iff.rfl

open Lit

namespace Derives

variable {cites : List Cited} {Γ : List (Lit P L)}

/-- **Soundness, symbol by symbol.** If the laws cited hold, then whatever a derivation
proves holds under every valuation that makes the context true. No step needs a point or a
straight line beyond those the symbols stand for. The proof uses the cited laws and logic,
and nothing else. -/
theorem sound (hcites : ∀ c ∈ cites, c.Holds I) (v : Val I P L) (hΓ : ∀ ℓ ∈ Γ, ℓ.Holds v)
    {ℓ : Lit P L} (d : Derives cites Γ ℓ) : ℓ.Holds v := by
  induction d with
  | given h => exact hΓ _ h
  | eq_refl => exact rfl
  | eq_symm _ ih => exact Eq.symm ih
  | ne_symm _ ih => exact fun h => ih h.symm
  | len_refl => exact rfl
  | len_symm _ ih => exact Eq.symm ih
  | len_trans _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
  | angle_refl => exact rfl
  | angle_symm _ ih => exact Eq.symm ih
  | angle_trans _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
  | area_refl => exact rfl
  | area_symm _ ih => exact Eq.symm ih
  | area_trans _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
  | len_congr _cn4 _ _ ih₁ ih₂ =>
    change I.len _ _ = I.len _ _
    exact ih₁ ▸ ih₂ ▸ rfl
  | angle_congr _cn4 _ _ _ ih₁ ih₂ ih₃ =>
    change I.ang _ _ _ = I.ang _ _ _
    exact ih₁ ▸ ih₂ ▸ ih₃ ▸ rfl
  | area_congr _cn4 _ _ _ ih₁ ih₂ ih₃ =>
    change I.area _ _ _ = I.area _ _ _
    exact ih₁ ▸ ih₂ ▸ ih₃ ▸ rfl
  | cite c σ τ _ hc ih =>
    rw [Lit.holds_map]
    exact hcites c hc (v.comap σ τ) fun ℓ hℓ => (Lit.holds_map σ τ v ℓ).1 (ih ℓ hℓ)

end Derives

/-- The valuation of a placement: the figure's symbols as `v` says, B′ at B', C′ at C'
and the side laid down along N. -/
def Val.place (v : Val I P L) (B' C' : I.Point) (N : I.Line) : Val I (Name P) (LineName L) where
  pt
    | .given p => v.pt p
    | .second => B'
    | .third => C'
  line
    | .given l => v.line l
    | .side => N

/-- **Wherever a triangle can be laid down, the restricted rule holds.** If every triangle can
be laid down on every ray, on either side, with a straight line through D and C′ for its side
AC, then `Rule` holds, by logic alone: `Derives.sound` uses only
the laws a derivation cites, which the rule assumes rather than asserts. So the restricted
rule holds in a model of the plane once triangles can be laid down there with that side. -/
theorem Rule.of_placement
    (hplace : ∀ {A B C D G H : I.Point} {L : I.Line}, Triangle I A B C → I.OnLine D L → I.OnLine G L →
      D ≠ G → ¬ I.OnLine H L →
      ∃ B' C' : I.Point, ∃ N : I.Line, Placed I A B C D G H L B' C' ∧ I.OnLine D N ∧ I.OnLine C' N) :
    Rule I := by
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

/-- **What the side laid down costs.** If every triangle can be laid down on every ray, on
either side, with its sides and angles kept but no side drawn, then `Rule` holds once a point
on one side of a straight line is off it and a straight line passes through any two distinct
points. C′ is on H's side of L, so it is off L, while D is on L: so D is not C′, and a
straight line through them is the side AC laid down. `Rule.of_placement` does the rest. This
is the kept side's cost made a theorem: beyond the placement, the side AC laid down costs no
more than Same side 3's form and Postulate 1's. -/
theorem Rule.of_placement_of_join
    (hplace : ∀ {A B C D G H : I.Point} {L : I.Line}, Triangle I A B C → I.OnLine D L → I.OnLine G L →
      D ≠ G → ¬ I.OnLine H L → ∃ B' C' : I.Point, Placed I A B C D G H L B' C')
    (hoff : ∀ {P Q : I.Point} {L : I.Line}, I.SameSide P Q L → ¬ I.OnLine P L)
    (hjoin : ∀ {P Q : I.Point}, P ≠ Q → ∃ N : I.Line, I.OnLine P N ∧ I.OnLine Q N) :
    Rule I := by
  apply Rule.of_placement
  intro A B C D G H L hT hd hg hdg hh
  obtain ⟨B', C', hp⟩ := hplace hT hd hg hdg hh
  /- C′ is on H's side of L, so off L; D is on L. -/
  obtain ⟨N, hDN, hC'N⟩ := hjoin fun heq : D = C' => hoff hp.2.2.1 (heq ▸ hd)
  exact ⟨B', C', N, hp, hDN, hC'N⟩

/-! ## Naming the symbols

The rule numbers its symbols. A proof may name them instead, with an inductive type of its
own, once they are numbered: `Symbols`. `Symbols.ofList` numbers them from a list of their
names, so that a proof writes the names alone. -/

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

/-- **A vocabulary from a list of its symbols.** The figure's points, or its straight lines,
listed by name, each at least once: a symbol is numbered by its first place in the list, and
a number is read back as the symbol in that place. -/
abbrev Symbols.ofList [DecidableEq P] (l : List P) (hl : ∀ p, p ∈ l) : Symbols P where
  card := l.length
  index p := ⟨l.idxOf p, List.idxOf_lt_length_of_mem (hl p)⟩
  symbol i := l[i]
  symbol_index p := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hl p))

/-- **The rule, with named symbols.** The rule for a figure whose symbols are named by finite
vocabularies P and L of the proof's own: number the symbols, and use the rule on the
numbers. -/
theorem Rule.apply (S : Rule I) [Symbols P] [Symbols L] {cites : List Cited}
    (hcites : ∀ c ∈ cites, c.Holds I) {Γ : List (Lit P L)} {a b c d g h : P} {l : L}
    {φ : Metric P}
    (dφ : Derives cites (branch Γ a b c d g h l) (pos (φ.map Name.given).toAtom))
    (v : Val I P L) (hT : Triangle I (v.pt a) (v.pt b) (v.pt c)) (hd : I.OnLine (v.pt d) (v.line l))
    (hg : I.OnLine (v.pt g) (v.line l)) (hdg : v.pt d ≠ v.pt g) (hh : ¬ I.OnLine (v.pt h) (v.line l))
    (hΓ : ∀ ℓ ∈ Γ, ℓ.Holds v) : φ.Holds v := by
  let i : P → Fin (Symbols.card P) := Symbols.index
  let j : L → Fin (Symbols.card L) := Symbols.index
  /- The figure, on the numbers: each number stands for what its symbol stands for. -/
  let w : Val I (Fin (Symbols.card P)) (Fin (Symbols.card L)) :=
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

end Elements.Superposition
