import Staging.Superposition.Formulas

/-!
# Superposition, restricted: the derivations

The steps a hypothetical placement may take, as a datatype ([brief
0009](../../docs/briefs/0009-superposition.md)). `Derives cites Γ ℓ` says that the literal
`ℓ` follows from the literals `Γ` by the rules below, each a fixed scheme on named
objects. Astra's third answer asks for exactly this: a checked judgment, not an arbitrary
Lean function, with its hypotheses, its theorem applications and its conclusions
controlled.

**What a step may do.** Every rule has literals as premises and one literal as its
conclusion, and none introduces a name: there is no rule that constructs a point, draws a
straight line or a circle, splits cases, argues by contradiction or concludes anything from
a contradiction. There are two kinds of rule.

* **Logic.** Equality of points, of lengths, of angles and of triangles is reflexive,
  symmetric and transitive, and Common Notion 4 puts one point for another that coincides
  with it. These hold of anything, by logic alone.
* **Cited laws.** Every other step cites a law by name, from the list `Cited`, and may be
  taken only when the derivation lists that law: Metric 3, Metric 4, Metric 9, that a
  straight line equal to one with two distinct ends has two distinct ends, that on a ray
  one point lies at a given distance from its start, that on one side of a straight line
  one ray from a point of it makes a given angle with it, and I.7. Each law is stated
  exactly as the step uses it, with its straight lines named.

**Why the laws are cited, not built in.** The restricted rule (`Rule`) asks every law a
derivation cites to hold, and assumes none of them. Were Metric 9 a rule of its own, the
rule of superposition would contain Metric 9, and the certificate of I.4, walking the
proof, would never see it: the derivation is data, and Lean records no dependency on the
facts a datatype mentions. Were I.7 a rule of its own, the foundations would assume what
Book I proves from I.4. Cited, each law is supplied by a proof (`Cited.law_lenSymm` and
the rest, from Book Zero; I.7 from Book I), and the theorem that cites it rests on that
proof, where the certificate can see it. The list is fixed: arbitrary rules, each with a
proof of soundness, would let a rule hold vacuously and smuggle back the points (brief
0009, "The design").

`Derives.sound` shows that every step holds of the very points its names stand for, under
any assignment of points to names: the derivation needs no point beyond those it names. It
uses the cited laws and nothing else.
-/

namespace Elements.Superposition

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
  /-- On one side of a straight line, one ray from a point of it makes a given angle
  with it. -/
  | rayOfAngle
  /-- I.7: two points on one side of a straight line, as far from each of its ends as one
  another, are one point. Euclid cites it inside the placement of I.8. -/
  | prop7
  deriving DecidableEq

/-- The statement of each law, exactly as the step citing it uses it. -/
def Cited.Law : Cited → Prop
  | lenSymm => ∀ A B : Point, ‖A B‖ = ‖B A‖
  | angleSymm => ∀ {A B C : Point}, A ≠ B → C ≠ B → ∠ A B C = ∠ C B A
  | areaCongruent => ∀ {A B C D E F : Point}, ‖A B‖ = ‖D E‖ → ‖B C‖ = ‖E F‖ →
      ‖C A‖ = ‖F D‖ → ∠ A B C = ∠ D E F → ∠ B C A = ∠ E F D → ∠ C A B = ∠ F D E →
      △ A B C = △ D E F
  | neOfLen => ∀ {A B C D : Point}, ‖A B‖ = ‖C D‖ → C ≠ D → A ≠ B
  | rayUnique => ∀ {A B P : Point} {L : Line}, A ≠ B → P ≠ A → OnLine A L → OnLine B L →
      OnLine P L → ¬ Between P A B → ‖A P‖ = ‖A B‖ → P = B
  | rayOfAngle => ∀ {D E F P : Point} {L M : Line}, D ≠ E → OnLine D L → OnLine E L →
      OnLine D M → OnLine F M → SameSide P F L → ∠ E D P = ∠ E D F →
      OnLine P M ∧ ¬ Between P D F
  | prop7 => ∀ {A B C D : Point} {L : Line}, A ≠ B → OnLine A L → OnLine B L →
      SameSide C D L → ‖C A‖ = ‖D A‖ → ‖C B‖ = ‖D B‖ → C = D

/-! ## The laws, from the foundations

Each law but I.7 is proved here from Book Zero and the foundations, without superposition.
I.7 is a proposition of Book I; the theorem citing it supplies it. -/

open Tacit

/-- Metric 3, as `Tacit.len_symm` states it. -/
theorem Cited.law_lenSymm : Cited.lenSymm.Law := len_symm

/-- Metric 4, as `Tacit.angle_symm` states it. -/
theorem Cited.law_angleSymm : Cited.angleSymm.Law := fun hAB hCB => angle_symm hAB hCB

/-- Metric 9, as `Tacit.area_congruent` states it. -/
theorem Cited.law_areaCongruent : Cited.areaCongruent.Law :=
  fun h₁ h₂ h₃ h₄ h₅ h₆ => area_congruent h₁ h₂ h₃ h₄ h₅ h₆

/-- Book Zero's `ne_of_len_eq`. -/
theorem Cited.law_neOfLen : Cited.neOfLen.Law := fun h hCD => ne_of_len_eq h hCD

/-- Book Zero's `OnRay.eq_of_len_eq`, with the straight line named. -/
theorem Cited.law_rayUnique : Cited.rayUnique.Law :=
  fun hAB hPA hA hB hP hPAB hlen => OnRay.eq_of_len_eq ⟨hAB, hPA, ⟨_, hA, hB, hP⟩, hPAB⟩ hlen

/-- Book Zero's `onRay_of_angle_eq`, with both straight lines named: the point lies on the
named straight line `M`, since two points fix one straight line. -/
theorem Cited.law_rayOfAngle : Cited.rayOfAngle.Law := by
  intro D E F P L M hDE hD hE hDM hFM hside hang
  obtain ⟨hDF, -, ⟨N, hDN, hFN, hPN⟩, hPDF⟩ :=
    onRay_of_angle_eq (SameSideOf.of_line hDE hD hE hside) hang
  exact ⟨line_unique hDF hDN hFN hDM hFM ▸ hPN, hPDF⟩

/-- I.7, as the library states it, gives the law: "on the same side of AB" is the same side
of the straight line L through A and B, however it is named. -/
theorem Cited.law_prop7
    (h7 : ∀ {A B C D : Point}, SameSideOf C D A B → ‖C A‖ = ‖D A‖ → ‖C B‖ = ‖D B‖ → C = D) :
    Cited.prop7.Law :=
  fun hAB hA hB hside hCA hCB => h7 (SameSideOf.of_line hAB hA hB hside) hCA hCB

open Lit

/-- **A restricted derivation.** `Derives cites Γ ℓ`: the literal `ℓ` follows from the
literals `Γ` by the fixed rules below, citing only the laws in `cites`. No rule introduces
a name, so no step constructs anything. -/
inductive Derives {V : Type} (cites : List Cited) (Γ : List (Lit V)) : Lit V → Prop where
  /-- A fact of the context. -/
  | given {ℓ : Lit V} : ℓ ∈ Γ → Derives cites Γ ℓ
  /-- A point is itself. -/
  | eq_refl {P : V} : Derives cites Γ (pos (.eq P P))
  /-- If P is Q, Q is P. -/
  | eq_symm {P Q : V} : Derives cites Γ (pos (.eq P Q)) → Derives cites Γ (pos (.eq Q P))
  /-- If P is not Q, Q is not P. -/
  | ne_symm {P Q : V} : Derives cites Γ (neg (.eq P Q)) → Derives cites Γ (neg (.eq Q P))
  /-- A length is equal to itself. -/
  | len_refl {P Q : V} : Derives cites Γ (pos (.len P Q P Q))
  /-- Equality of lengths is symmetric. -/
  | len_symm {P Q R S : V} :
      Derives cites Γ (pos (.len P Q R S)) → Derives cites Γ (pos (.len R S P Q))
  /-- Equality of lengths is transitive (Common Notion 1). -/
  | len_trans {P Q R S T U : V} :
      Derives cites Γ (pos (.len P Q R S)) → Derives cites Γ (pos (.len R S T U)) →
      Derives cites Γ (pos (.len P Q T U))
  /-- An angle is equal to itself. -/
  | angle_refl {P Q R : V} : Derives cites Γ (pos (.angle P Q R P Q R))
  /-- Equality of angles is symmetric. -/
  | angle_symm {P Q R S T U : V} :
      Derives cites Γ (pos (.angle P Q R S T U)) → Derives cites Γ (pos (.angle S T U P Q R))
  /-- Equality of angles is transitive (Common Notion 1). -/
  | angle_trans {P Q R S T U X Y Z : V} :
      Derives cites Γ (pos (.angle P Q R S T U)) →
      Derives cites Γ (pos (.angle S T U X Y Z)) → Derives cites Γ (pos (.angle P Q R X Y Z))
  /-- A triangle is equal to itself. -/
  | area_refl {P Q R : V} : Derives cites Γ (pos (.area P Q R P Q R))
  /-- Equality of triangles is symmetric. -/
  | area_symm {P Q R S T U : V} :
      Derives cites Γ (pos (.area P Q R S T U)) → Derives cites Γ (pos (.area S T U P Q R))
  /-- Equality of triangles is transitive (Common Notion 1). -/
  | area_trans {P Q R S T U X Y Z : V} :
      Derives cites Γ (pos (.area P Q R S T U)) →
      Derives cites Γ (pos (.area S T U X Y Z)) → Derives cites Γ (pos (.area P Q R X Y Z))
  /-- Straight lines whose ends coincide are equal (Common Notion 4). -/
  | len_congr {P Q P' Q' : V} :
      Derives cites Γ (pos (.eq P P')) → Derives cites Γ (pos (.eq Q Q')) →
      Derives cites Γ (pos (.len P Q P' Q'))
  /-- Angles whose points coincide are equal (Common Notion 4). -/
  | angle_congr {P Q R P' Q' R' : V} :
      Derives cites Γ (pos (.eq P P')) → Derives cites Γ (pos (.eq Q Q')) →
      Derives cites Γ (pos (.eq R R')) → Derives cites Γ (pos (.angle P Q R P' Q' R'))
  /-- Triangles whose corners coincide are equal (Common Notion 4). -/
  | area_congr {P Q R P' Q' R' : V} :
      Derives cites Γ (pos (.eq P P')) → Derives cites Γ (pos (.eq Q Q')) →
      Derives cites Γ (pos (.eq R R')) → Derives cites Γ (pos (.area P Q R P' Q' R'))
  /-- The straight line PQ is the straight line QP (Metric 3, cited). -/
  | len_comm {P Q : V} (cite : Cited.lenSymm ∈ cites := by decide) :
      Derives cites Γ (pos (.len P Q Q P))
  /-- The angle PQR is the angle RQP, for P and R other than Q (Metric 4, cited). -/
  | angle_comm {P Q R : V} (hPQ : Derives cites Γ (neg (.eq P Q)))
      (hRQ : Derives cites Γ (neg (.eq R Q))) (cite : Cited.angleSymm ∈ cites := by decide) :
      Derives cites Γ (pos (.angle P Q R R Q P))
  /-- Triangles equal in all their sides and angles are equal in area (Metric 9, cited). -/
  | area_of_congruent {P Q R P' Q' R' : V} (h₁ : Derives cites Γ (pos (.len P Q P' Q')))
      (h₂ : Derives cites Γ (pos (.len Q R Q' R'))) (h₃ : Derives cites Γ (pos (.len R P R' P')))
      (h₄ : Derives cites Γ (pos (.angle P Q R P' Q' R')))
      (h₅ : Derives cites Γ (pos (.angle Q R P Q' R' P')))
      (h₆ : Derives cites Γ (pos (.angle R P Q R' P' Q')))
      (cite : Cited.areaCongruent ∈ cites := by decide) :
      Derives cites Γ (pos (.area P Q R P' Q' R'))
  /-- A straight line equal to a straight line with two distinct ends has two distinct
  ends (cited). -/
  | ne_of_len {P Q R S : V} (hlen : Derives cites Γ (pos (.len P Q R S)))
      (hRS : Derives cites Γ (neg (.eq R S))) (cite : Cited.neOfLen ∈ cites := by decide) :
      Derives cites Γ (neg (.eq P Q))
  /-- **One point at one distance on a ray** (cited). A point `P` of the straight line `L`
  through `A` and `B`, other than `A`, with `A` not between it and `B`, and as far from `A`
  as `B` is, is `B`. -/
  | ray_unique {A B P : V} {L : Line} (hAB : Derives cites Γ (neg (.eq A B)))
      (hPA : Derives cites Γ (neg (.eq P A))) (hA : Derives cites Γ (pos (.onLine A L)))
      (hB : Derives cites Γ (pos (.onLine B L))) (hP : Derives cites Γ (pos (.onLine P L)))
      (hPAB : Derives cites Γ (neg (.between P A B))) (hlen : Derives cites Γ (pos (.len A P A B)))
      (cite : Cited.rayUnique ∈ cites := by decide) :
      Derives cites Γ (pos (.eq P B))
  /-- **One ray for one angle**, its straight line (cited). With `D`, `E` on `L` and `D`,
  `F` on `M`, a point `P` on `F`'s side of `L` making the angle `EDP` equal to the angle
  `EDF` lies on `M`. -/
  | ray_of_angle {D E F P : V} {L M : Line} (hDE : Derives cites Γ (neg (.eq D E)))
      (hD : Derives cites Γ (pos (.onLine D L))) (hE : Derives cites Γ (pos (.onLine E L)))
      (hDM : Derives cites Γ (pos (.onLine D M))) (hFM : Derives cites Γ (pos (.onLine F M)))
      (hside : Derives cites Γ (pos (.sameSide P F L)))
      (hang : Derives cites Γ (pos (.angle E D P E D F)))
      (cite : Cited.rayOfAngle ∈ cites := by decide) :
      Derives cites Γ (pos (.onLine P M))
  /-- **One ray for one angle**, its side (cited). Under the same hypotheses, `D` is not
  between `P` and `F`: `P` lies on the ray from `D` through `F`. -/
  | ray_of_angle_side {D E F P : V} {L M : Line} (hDE : Derives cites Γ (neg (.eq D E)))
      (hD : Derives cites Γ (pos (.onLine D L))) (hE : Derives cites Γ (pos (.onLine E L)))
      (hDM : Derives cites Γ (pos (.onLine D M))) (hFM : Derives cites Γ (pos (.onLine F M)))
      (hside : Derives cites Γ (pos (.sameSide P F L)))
      (hang : Derives cites Γ (pos (.angle E D P E D F)))
      (cite : Cited.rayOfAngle ∈ cites := by decide) :
      Derives cites Γ (neg (.between P D F))
  /-- **I.7** (cited). Two points `C`, `D` on one side of the straight line `L` through `A`
  and `B`, with `CA` equal to `DA` and `CB` to `DB`, are one point. -/
  | prop7 {A B C D : V} {L : Line} (hAB : Derives cites Γ (neg (.eq A B)))
      (hA : Derives cites Γ (pos (.onLine A L))) (hB : Derives cites Γ (pos (.onLine B L)))
      (hside : Derives cites Γ (pos (.sameSide C D L)))
      (hCA : Derives cites Γ (pos (.len C A D A))) (hCB : Derives cites Γ (pos (.len C B D B)))
      (cite : Cited.prop7 ∈ cites := by decide) :
      Derives cites Γ (pos (.eq C D))

namespace Derives

variable {V : Type} {cites : List Cited} {Γ : List (Lit V)}

/-- **Soundness, point by point.** If the laws cited hold, then whatever a derivation
proves holds of the very points its names stand for, under any assignment `σ` that makes
the context true. No step needs a point that the names do not already stand for. The proof
uses the cited laws and logic, and nothing else. -/
theorem sound (hcites : ∀ c ∈ cites, c.Law) (σ : V → Point) (hΓ : ∀ ℓ ∈ Γ, ℓ.Holds σ)
    {ℓ : Lit V} (d : Derives cites Γ ℓ) : ℓ.Holds σ := by
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
  | len_congr _ _ ih₁ ih₂ => exact CommonNotion4 ih₁ ih₂
  | angle_congr _ _ _ ih₁ ih₂ ih₃ => exact CommonNotion4.angle ih₁ ih₂ ih₃
  | area_congr _ _ _ ih₁ ih₂ ih₃ => exact CommonNotion4.triangle ih₁ ih₂ ih₃
  | @len_comm P Q cite => exact hcites _ cite (σ P) (σ Q)
  | angle_comm _ _ cite ih₁ ih₂ => exact hcites _ cite ih₁ ih₂
  | ne_of_len _ _ cite ih₁ ih₂ => exact hcites _ cite ih₁ ih₂
  | area_of_congruent _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
    exact hcites _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆
  | ray_unique _ _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ =>
    exact hcites _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇
  | ray_of_angle _ _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ =>
    exact (hcites _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇).1
  | ray_of_angle_side _ _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ =>
    exact (hcites _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇).2
  | prop7 _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
    exact hcites _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆

end Derives

end Elements.Superposition
