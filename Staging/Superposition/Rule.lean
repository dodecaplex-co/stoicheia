import Staging.Superposition.Derivations

/-!
# Superposition, restricted: the rule

The restricted rule of superposition, as a hypothesis `Rule` that theorems take as an
argument ([brief 0009](../../docs/briefs/0009-superposition.md)). Nothing here is an axiom.

System E writes the rule as a sequent inference (Avigad, Dean and Mumma, 2009, §3.7): if
the facts Γ, with the facts Π of a triangle laid down, prove Δ′, then Γ proves Δ′, where
Δ′ speaks only of the objects Γ already has. Ours is that inference with Π the facts our
present rule (`Tacit.superposition`) gives, a proof of Δ′ that is a `Derives`, and Δ′ a
list of equalities of magnitudes among the given points:

* **The guards.** The triangle ABC is a triangle (its corners are not on one straight
  line); D and G are two points of the straight line L, so the ray from D through G has a
  direction; H is off L, so it has a side. These are the hypotheses of the present rule,
  and the guards of `guards` are the literals the placement may use from them.
* **What the placement keeps** (`kept`). Laid down with A on D, the triangle becomes D B′ C′:
  B′ is on the ray from D through G, C′ is on H's side of L, and each side and each angle
  is kept. The placement also keeps that its corners are three points and that C′ is off
  L; these follow from the rest (`Rule.of_placement` shows how), and are listed because
  the arguments use them.
* **What it exports.** Equalities of lengths, angles and triangles among the given points:
  a `Metric Point`, whose names can only be given points.
* **What it assumes.** Nothing about lengths, angles, areas or rays: a derivation cites the
  laws it uses (`Cited`), and the rule asks each of them to hold. So the theorem that uses
  the rule rests, where the certificate can see it, on the proof of every law it cites.

`Rule.of_placement` shows that wherever triangles can be laid down, as the present rule
says, the restricted rule holds: so it is no stronger than the present rule, and a model
of the plane satisfies it once it satisfies the present rule.
-/

namespace Elements.Superposition

open Lit Tacit

/-- **The guards**, as literals the placement may use: the corners of the triangle ABC are
three points, D and G are on L and are two points, and H is off L. -/
def guards (A B C D G H : Point) (L : Line) : List (Lit Name) :=
  [neg (.eq A B), neg (.eq B C), neg (.eq A C),
   pos (.onLine D L), pos (.onLine G L), neg (.eq D G), neg (.onLine H L)]

/-- **What the placement keeps.** The triangle ABC laid down with A on D is D B′ C′, where
B′ is `Name.second` and C′ is `Name.third`: B′ on L, with D not between B′ and G (on the
ray from D through G); C′ on H's side of L; DB′, B′C′, C′D equal to AB, BC, CA; the angles
at D, C′ and B′ equal to those at A, C and B; B′, C′ and D three points; and C′ off L. -/
def kept (A B C D G H : Point) (L : Line) : List (Lit Name) :=
  [pos (.onLine .second L), neg (.between .second D G), pos (.sameSide .third H L),
   pos (.len D .second A B), pos (.len .second .third B C), pos (.len .third D C A),
   pos (.angle .second D .third B A C), pos (.angle D .third .second A C B),
   pos (.angle .third .second D C B A),
   neg (.eq .second D), neg (.eq .third D), neg (.eq .second .third),
   neg (.onLine .third L)]

/-- **The context of a hypothetical placement**: the given facts Γ, the guards, and what
the placement keeps. -/
def branch (Γ : List (Lit Point)) (A B C D G H : Point) (L : Line) : List (Lit Name) :=
  Γ.map (Lit.map Name.given) ++ guards A B C D G H L ++ kept A B C D G H L

/-- **The restricted rule of superposition**, as a hypothesis. For a triangle ABC, a ray
from D through G along the straight line L, and a point H off L: whatever equalities of
lengths, angles and triangles among the given points a restricted derivation proves from
the given facts Γ, the guards and what the placement keeps, hold. A derivation may cite
the propositions listed in `cites`, once their statements hold.

The laid-down corners are names in the derivation and nowhere else: the conclusion is a
list of `Metric Point`, which can name only given points. -/
structure Rule : Prop where
  /-- Use the rule: lay ABC down on the ray from D through G, on H's side, and keep what a
  restricted derivation proves of the given points. -/
  infer : ∀ {cites : List Cited}, (∀ c ∈ cites, c.Law) →
    ∀ {A B C D G H : Point} {L : Line}, Triangle A B C → OnLine D L → OnLine G L → D ≠ G →
    ¬ OnLine H L →
    ∀ {Γ : List (Lit Point)}, (∀ ℓ ∈ Γ, ℓ.Holds id) →
    ∀ {φ : List (Metric Point)},
      (∀ m ∈ φ, Derives cites (branch Γ A B C D G H L) (pos (m.map Name.given).toAtom)) →
      ∀ m ∈ φ, m.Holds id

/-! ## The facts of the branch, by name

So that a derivation can say which fact it uses: `Kept.len₁` is "DB′ is AB", and so on. -/

section Facts

variable {cites : List Cited} {Γ : List (Lit Point)} {A B C D G H : Point} {L : Line}

/-- A given fact, in the placement. -/
theorem Branch.given {ℓ : Lit Point} (h : ℓ ∈ Γ) :
    Derives cites (branch Γ A B C D G H L) (ℓ.map Name.given) :=
  .given (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem h)))

/-- A guard, in the placement. -/
theorem Branch.guard {ℓ : Lit Name} (h : ℓ ∈ guards A B C D G H L) :
    Derives cites (branch Γ A B C D G H L) ℓ :=
  .given (List.mem_append_left _ (List.mem_append_right _ h))

/-- A fact the placement keeps. -/
theorem Branch.kept {ℓ : Lit Name} (h : ℓ ∈ kept A B C D G H L) :
    Derives cites (branch Γ A B C D G H L) ℓ :=
  .given (List.mem_append_right _ h)

/-- A is not B. -/
theorem Guard.ne_AB : Derives cites (branch Γ A B C D G H L) (neg (.eq A B)) :=
  Branch.guard (by simp [guards])
/-- B is not C. -/
theorem Guard.ne_BC : Derives cites (branch Γ A B C D G H L) (neg (.eq B C)) :=
  Branch.guard (by simp [guards])
/-- A is not C. -/
theorem Guard.ne_AC : Derives cites (branch Γ A B C D G H L) (neg (.eq A C)) :=
  Branch.guard (by simp [guards])
/-- D is on L. -/
theorem Guard.on_D : Derives cites (branch Γ A B C D G H L) (pos (.onLine D L)) :=
  Branch.guard (by simp [guards])
/-- G is on L. -/
theorem Guard.on_G : Derives cites (branch Γ A B C D G H L) (pos (.onLine G L)) :=
  Branch.guard (by simp [guards])
/-- D is not G. -/
theorem Guard.ne_DG : Derives cites (branch Γ A B C D G H L) (neg (.eq D G)) :=
  Branch.guard (by simp [guards])
/-- H is off L. -/
theorem Guard.off_H : Derives cites (branch Γ A B C D G H L) (neg (.onLine H L)) :=
  Branch.guard (by simp [guards])

/-- B′ is on L. -/
theorem Kept.on_line : Derives cites (branch Γ A B C D G H L) (pos (.onLine .second L)) :=
  Branch.kept (by simp [kept])
/-- D is not between B′ and G: B′ is on the ray from D through G. -/
theorem Kept.not_between :
    Derives cites (branch Γ A B C D G H L) (neg (.between .second D G)) :=
  Branch.kept (by simp [kept])
/-- C′ is on H's side of L. -/
theorem Kept.same_side :
    Derives cites (branch Γ A B C D G H L) (pos (.sameSide .third H L)) :=
  Branch.kept (by simp [kept])
/-- DB′ is AB. -/
theorem Kept.len₁ : Derives cites (branch Γ A B C D G H L) (pos (.len D .second A B)) :=
  Branch.kept (by simp [kept])
/-- B′C′ is BC. -/
theorem Kept.len₂ :
    Derives cites (branch Γ A B C D G H L) (pos (.len .second .third B C)) :=
  Branch.kept (by simp [kept])
/-- C′D is CA. -/
theorem Kept.len₃ : Derives cites (branch Γ A B C D G H L) (pos (.len .third D C A)) :=
  Branch.kept (by simp [kept])
/-- The angle B′DC′ is the angle BAC. -/
theorem Kept.angle₁ :
    Derives cites (branch Γ A B C D G H L) (pos (.angle .second D .third B A C)) :=
  Branch.kept (by simp [kept])
/-- The angle DC′B′ is the angle ACB. -/
theorem Kept.angle₂ :
    Derives cites (branch Γ A B C D G H L) (pos (.angle D .third .second A C B)) :=
  Branch.kept (by simp [kept])
/-- The angle C′B′D is the angle CBA. -/
theorem Kept.angle₃ :
    Derives cites (branch Γ A B C D G H L) (pos (.angle .third .second D C B A)) :=
  Branch.kept (by simp [kept])
/-- B′ is not D. -/
theorem Kept.ne₁ : Derives cites (branch Γ A B C D G H L) (neg (.eq .second D)) :=
  Branch.kept (by simp [kept])
/-- C′ is not D. -/
theorem Kept.ne₂ : Derives cites (branch Γ A B C D G H L) (neg (.eq .third D)) :=
  Branch.kept (by simp [kept])
/-- B′ is not C′. -/
theorem Kept.ne₃ : Derives cites (branch Γ A B C D G H L) (neg (.eq .second .third)) :=
  Branch.kept (by simp [kept])
/-- C′ is off L. -/
theorem Kept.off_line : Derives cites (branch Γ A B C D G H L) (neg (.onLine .third L)) :=
  Branch.kept (by simp [kept])

end Facts

/-! ## No stronger than laying a triangle down -/

/-- The triangle ABC, laid down with A on D, is D B′ C′, with B′ on the ray from D through
G and C′ on H's side of L, its sides and angles kept: the conclusion of the present rule,
`Tacit.superposition`, word for word. -/
def Placed (A B C D G H : Point) (L : Line) (B' C' : Point) : Prop :=
  OnLine B' L ∧ ¬ Between B' D G ∧ SameSide C' H L ∧
    ‖D B'‖ = ‖A B‖ ∧ ‖B' C'‖ = ‖B C‖ ∧ ‖C' D‖ = ‖C A‖ ∧
    ∠ B' D C' = ∠ B A C ∧ ∠ D C' B' = ∠ A C B ∧ ∠ C' B' D = ∠ C B A

/-- **Wherever a triangle can be laid down, the restricted rule holds.** If every triangle
can be laid down on every ray, on either side, as the present rule says, then `Rule`
holds. So the restricted rule is no stronger than the present one, and a model of the
plane satisfies it once triangles can be laid down there: `Derives.sound` uses only the
laws a derivation cites, which the rule assumes rather than asserts. The kept facts that
the present rule does not state (that B′, C′ and D are three points, and C′ is off L) are
proved here from those it does. -/
theorem Rule.of_placement
    (h : ∀ {A B C D G H : Point} {L : Line}, Triangle A B C → OnLine D L → OnLine G L →
      D ≠ G → ¬ OnLine H L → ∃ B' C' : Point, Placed A B C D G H L B' C') : Rule := by
  refine ⟨fun {cites} hcites {A B C D G H L} hABC hD hG hDG hH {Γ} hΓ {φ} hφ m hm => ?_⟩
  obtain ⟨B', C', hB'L, hB'DG, hC'H, hDB', hB'C', hC'D, hB'DC', hDC'B', hC'B'D⟩ :=
    h hABC hD hG hDG hH
  have hAB : A ≠ B := hABC.ne₁₂
  have hBC : B ≠ C := hABC.ne₂₃
  have hAC : A ≠ C := hABC.ne₁₃
  have hB'D : B' ≠ D := ne_of_len_eq ((len_symm B' D).trans hDB') hAB
  have hC'D' : C' ≠ D := ne_of_len_eq hC'D hAC.symm
  have hB'C'' : B' ≠ C' := ne_of_len_eq hB'C' hBC
  have hC'L : ¬ OnLine C' L := not_on_line_of_same_side hC'H
  /- Name each name: the given points for themselves, `second` B′ and `third` C′. -/
  let σ := Name.at B' C'
  have hσ : σ ∘ Name.given = id := rfl
  have hbranch : ∀ ℓ ∈ branch Γ A B C D G H L, ℓ.Holds σ := by
    intro ℓ hℓ
    simp only [branch, List.mem_append, List.mem_map] at hℓ
    rcases hℓ with (⟨ℓ₀, hℓ₀, rfl⟩ | hg) | hk
    · rw [Lit.holds_map, hσ]
      exact hΓ ℓ₀ hℓ₀
    · simp only [guards, List.mem_cons, List.mem_nil_iff, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hAB
      · exact hBC
      · exact hAC
      · exact hD
      · exact hG
      · exact hDG
      · exact hH
    · simp only [kept, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hB'L
      · exact hB'DG
      · exact hC'H
      · exact hDB'
      · exact hB'C'
      · exact hC'D
      · exact hB'DC'
      · exact hDC'B'
      · exact hC'B'D
      · exact hB'D
      · exact hC'D'
      · exact hB'C''
      · exact hC'L
  have hd := Derives.sound hcites σ hbranch (hφ m hm)
  show m.toAtom.Holds id
  rw [← hσ, ← Atom.holds_map, ← Metric.toAtom_map]
  exact hd

/-- The present rule satisfies the restricted one: `Rule` holds in today's foundations.
This is a check that `Placed` is the present rule's conclusion; nothing may cite it. -/
example : Rule :=
  Rule.of_placement fun hABC hD hG hDG hH => superposition hABC hD hG hDG hH

end Elements.Superposition
