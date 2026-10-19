import Staging.Superposition.Formulas
import Elements.Figure.Incidence

/-!
# Superposition, restricted: the laws and the derivations

The steps a hypothetical placement may take, as a datatype ([brief
0009](../../docs/briefs/0009-superposition.md)). `Derives cites Γ ℓ` says that the literal
`ℓ` follows from the literals `Γ`, all over the same symbols, by the rules below. Astra's
third answer asks for exactly this: a checked judgment, not an arbitrary Lean function, with
its hypotheses, its theorem applications and its conclusions controlled.

**A law is data.** A law the derivation may cite (`Law`) is a list of premises and one
conclusion, literals written in a fixed alphabet of letters (`Letter`, `LineLetter`). What
it asserts (`Law.Holds`) is that, whatever points and straight lines the letters stand for,
if the premises hold so does the conclusion. A law therefore asserts no existence: it has
no field in which an existential claim could be written.

**What a step may do.** There are two kinds of rule, and neither introduces a symbol.

* **Logic.** Equality of points, of lengths, of angles and of triangles is reflexive,
  symmetric and transitive, and Common Notion 4 puts one point for another that coincides
  with it. These hold of anything, by logic alone.
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
proof, a universal statement proved outside it, may. Every law here but I.7 is proved with
no rule that constructs (`Cited.holds_of_drawsNothing`; brief 0009 lists the axioms). The
law of one ray for one angle names all three of its straight lines, the third the one
through the point it speaks of, so that its proof draws nothing: in I.4 that straight line
is the side AC laid down, which the placement supplies. I.7's proof draws the six straight
lines joining its points, produces two and cites I.5; Euclid's I.8 uses I.7 inside the
placement (brief 0009, open question 4).

`Derives.sound` shows that every step holds of the very points its symbols stand for, under
any valuation that makes the context true: the derivation needs no point and no straight
line beyond those its symbols stand for.
-/

namespace Elements.Superposition

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

/-- What a law asserts: whatever points and straight lines its letters stand for, if its
premises hold, its conclusion holds. -/
def Law.Holds (law : Law) : Prop :=
  ∀ v : Val Letter LineLetter, (∀ ℓ ∈ law.premises, ℓ.Holds v) → law.conclusion.Holds v

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

/-- What a cited law asserts. -/
def Cited.Holds (c : Cited) : Prop := c.law.Holds

/-- **A cited law asserts no existence.** It says that, whatever points and straight lines
its letters stand for, its premises give its conclusion: a universal statement about
primitive relations, with nothing to construct. -/
theorem Cited.holds_iff (c : Cited) :
    c.Holds ↔ ∀ v : Val Letter LineLetter, (∀ ℓ ∈ c.law.premises, ℓ.Holds v) →
      c.law.conclusion.Holds v :=
  Iff.rfl

/-- The laws whose proofs here draw nothing: every law but I.7, whose proof the theorem
citing it supplies. -/
def Cited.drawsNothing : Cited → Bool
  | prop7 => false
  | _ => true

/-! ## The laws, from the foundations

Each law but I.7 is proved here from Book Zero and the foundations, without superposition and
with no rule that constructs: none of these proofs draws a straight line or a circle, or
takes a point. I.7 is a proposition of Book I; the theorem citing it supplies it. -/

open Tacit

/-- **One ray for one angle**, with its three straight lines named: D and E on L, D and F on
M, D and P on N. If P is on F's side of L and the angle EDP is the angle EDF, then P is on M.
Book Zero's `onRay_of_angle_eq` draws its straight lines; here they are given, so the proof
draws nothing. Otherwise either P would lie within the angle EDF, or F within the angle
EDP (Triple incidence 2 says which), and either way an angle would be a part of an angle
equal to it (Diagram-angle 1 and 2, with C.N. 5). -/
theorem onLine_of_angle_eq_named {D E F P : Point} {L M N : Line} (hDE : D ≠ E)
    (hD : OnLine D L) (hE : OnLine E L) (hDM : OnLine D M) (hFM : OnLine F M)
    (hDN : OnLine D N) (hPN : OnLine P N) (hPF : SameSide P F L) (h : ∠ E D P = ∠ E D F) :
    OnLine P M := by
  have hP_L : ¬ OnLine P L := not_on_line_of_same_side hPF
  have hF_L : ¬ OnLine F L := not_on_line_of_same_side (same_side_symm hPF)
  have hDF : D ≠ F := fun e => hF_L (e ▸ hD)
  have hPD : P ≠ D := fun e => hP_L (e ▸ hD)
  have hLM : L ≠ M := fun e => hF_L (e ▸ hFM)
  refine Classical.byContradiction fun hP_M => ?_
  /- Off M, the point P makes some angle with DF (Diagram-angle 1). -/
  have hFDP : 0 < ∠ F D P := Magnitude.pos_of_ne_zero fun h0 =>
    hP_M (same_ray_of_angle_eq_zero hDF hPD.symm hDM hFM h0).1
  by_cases hs : SameSide E P M
  · /- P lies within the angle EDF: the part would be equal to the whole. -/
    have hadd : ∠ E D F = ∠ E D P + ∠ P D F :=
      angle_add_of_inside hD hDM hE hFM hDE hDF hP_L hP_M hLM hs (same_side_symm hPF)
    rw [h, angle_symm hPD hDF.symm] at hadd
    have hlt := CommonNotion5 (a := ∠ E D F) hFDP
    rw [← hadd] at hlt
    exact lt_irrefl _ hlt
  · /- F lies within the angle EDP (Triple incidence 2, along the named N): again the part
       would be equal to the whole. -/
    have hEF_N : SameSide E F N :=
      triple_incidence2 hD hDM hDN hE hFM hPN (same_side_symm hPF) hs hP_M hDE.symm
    have hF_N : ¬ OnLine F N := fun hF_N => hP_M (line_unique hDF hDN hF_N hDM hFM ▸ hPN)
    have hLN : L ≠ N := fun e => hP_L (e ▸ hPN)
    have hadd : ∠ E D P = ∠ E D F + ∠ F D P :=
      angle_add_of_inside hD hDN hE hPN hDE hPD.symm hF_L hF_N hLN hEF_N hPF
    rw [h] at hadd
    have hlt := CommonNotion5 (a := ∠ E D F) hFDP
    rw [← hadd] at hlt
    exact lt_irrefl _ hlt

/-- Metric 3, as `Tacit.len_symm` states it. -/
theorem Cited.holds_lenSymm : Cited.lenSymm.Holds := fun v _ => len_symm (v.pt .A) (v.pt .B)

/-- Metric 4, as `Tacit.angle_symm` states it. -/
theorem Cited.holds_angleSymm : Cited.angleSymm.Holds := by
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  exact angle_symm h.1 h.2.1

/-- Metric 9, as `Tacit.area_congruent` states it. -/
theorem Cited.holds_areaCongruent : Cited.areaCongruent.Holds := by
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := h
  exact area_congruent h₁ h₂ h₃ h₄ h₅ h₆

/-- Book Zero's `ne_of_len_eq`. -/
theorem Cited.holds_neOfLen : Cited.neOfLen.Holds := by
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  exact ne_of_len_eq h.1 h.2.1

/-- Book Zero's `OnRay.eq_of_len_eq`, with the straight line named. -/
theorem Cited.holds_rayUnique : Cited.rayUnique.Holds := by
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  obtain ⟨hAB, hPA, hA, hB, hP, hPAB, hlen, -⟩ := h
  exact OnRay.eq_of_len_eq ⟨hAB, hPA, ⟨_, hA, hB, hP⟩, hPAB⟩ hlen

/-- One ray for one angle, its straight line: `onLine_of_angle_eq_named`. -/
theorem Cited.holds_rayOfAngle : Cited.rayOfAngle.Holds := by
  intro v h
  simp only [Cited.law, rayOfAnglePremises, List.forall_mem_cons] at h
  obtain ⟨hDE, hD, hE, hDM, hFM, hDN, hPN, hPF, hang, -⟩ := h
  exact onLine_of_angle_eq_named hDE hD hE hDM hFM hDN hPN hPF hang

/-- One ray for one angle, its side: D is not between P and F, for they are on one side of L
(Pasch 3). -/
theorem Cited.holds_rayOfAngleSide : Cited.rayOfAngleSide.Holds := by
  intro v h
  simp only [Cited.law, rayOfAnglePremises, List.forall_mem_cons] at h
  obtain ⟨-, hD, -, -, -, -, -, hPF, -, -⟩ := h
  exact fun hb => pasch3 hb hD hPF

/-- I.7, as the library states it, gives the law: "on the same side of AB" is the same side
of the straight line L through A and B, however it is named. -/
theorem Cited.holds_prop7
    (h7 : ∀ {A B C D : Point}, SameSideOf C D A B → ‖C A‖ = ‖D A‖ → ‖C B‖ = ‖D B‖ → C = D) :
    Cited.prop7.Holds := by
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  obtain ⟨hAB, hA, hB, hside, hCA, hCB, -⟩ := h
  exact h7 (SameSideOf.of_line hAB hA hB hside) hCA hCB

/-- **Every law that draws nothing holds**, from the proofs above. `#print axioms` for this
theorem lists every axiom those proofs use; brief 0009 records that none of them constructs. -/
theorem Cited.holds_of_drawsNothing : ∀ c : Cited, c.drawsNothing = true → c.Holds
  | .lenSymm, _ => Cited.holds_lenSymm
  | .angleSymm, _ => Cited.holds_angleSymm
  | .areaCongruent, _ => Cited.holds_areaCongruent
  | .neOfLen, _ => Cited.holds_neOfLen
  | .rayUnique, _ => Cited.holds_rayUnique
  | .rayOfAngle, _ => Cited.holds_rayOfAngle
  | .rayOfAngleSide, _ => Cited.holds_rayOfAngleSide

open Lit

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
  | len_congr {p q p' q' : P} :
      Derives cites Γ (pos (.eq p p')) → Derives cites Γ (pos (.eq q q')) →
      Derives cites Γ (pos (.len p q p' q'))
  /-- Angles whose points coincide are equal (Common Notion 4). -/
  | angle_congr {p q r p' q' r' : P} :
      Derives cites Γ (pos (.eq p p')) → Derives cites Γ (pos (.eq q q')) →
      Derives cites Γ (pos (.eq r r')) → Derives cites Γ (pos (.angle p q r p' q' r'))
  /-- Triangles whose corners coincide are equal (Common Notion 4). -/
  | area_congr {p q r p' q' r' : P} :
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

/-- **Soundness, symbol by symbol.** If the laws cited hold, then whatever a derivation
proves holds under every valuation that makes the context true. No step needs a point or a
straight line beyond those the symbols stand for. The proof uses the cited laws and logic,
and nothing else. -/
theorem sound (hcites : ∀ c ∈ cites, c.Holds) (v : Val P L) (hΓ : ∀ ℓ ∈ Γ, ℓ.Holds v)
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
  | len_congr _ _ ih₁ ih₂ => exact CommonNotion4 ih₁ ih₂
  | angle_congr _ _ _ ih₁ ih₂ ih₃ => exact CommonNotion4.angle ih₁ ih₂ ih₃
  | area_congr _ _ _ ih₁ ih₂ ih₃ => exact CommonNotion4.triangle ih₁ ih₂ ih₃
  | cite c σ τ _ hc ih =>
    rw [Lit.holds_map]
    exact hcites c hc (v.comap σ τ) fun ℓ hℓ => (Lit.holds_map σ τ v ℓ).1 (ih ℓ hℓ)

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
  | len_congr _ _ ih₁ ih₂ => exact .len_congr ih₁ ih₂
  | angle_congr _ _ _ ih₁ ih₂ ih₃ => exact .angle_congr ih₁ ih₂ ih₃
  | area_congr _ _ _ ih₁ ih₂ ih₃ => exact .area_congr ih₁ ih₂ ih₃
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

end Elements.Superposition
