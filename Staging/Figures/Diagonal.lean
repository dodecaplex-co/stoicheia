import Staging.Figures.Outline
import Staging.Figures.CoverFacts
import Staging.Figures.ArrangementFacts

/-!
# Staging: an interior diagonal of a simple outline

Helper lemmas for the optional diagonal route of brief 0013 (section 8, "The arrangement and
general division"; ledger D5 to D7): `simple_diagonal` and `simple_diagonal_partition` in
`Arrangement.lean`. No proposition of the Elements is cited; through `Outline.lean` this file
imports I.23, which only `outline_bounded` uses. Neither the parallel postulate nor
superposition is used.

* **An interior diagonal** (`diagonal_exists`). A corner V with every other corner strictly
  across a straight line through it is found by wrapping from a point of an enclosing straight
  line (`extreme_corner`). If no corner is inside the triangle of V and its neighbours U and W,
  or strictly between U and W, then UW is the diagonal (`ear_edge`). Otherwise a corner X on a
  straight line across V, strictly between its meetings with VU and VW, with no corner inside
  the smaller triangle it cuts off (`nearest`), gives the diagonal VX. No side meets such a triangle's inside (`clean`), and
  its points are inside the loop, being joined across the side VU to points from which a ray
  crosses nothing (`inside_near`). No parallels are drawn.
* **Two chains and two pieces** (`piece_simple`, `inside_xor`). Read from A, the loop is a chain
  from A to B and a chain back; each piece is one chain closed by the diagonal. Off the sides
  and the diagonal, a good ray crosses the loop as often as both pieces together, less the
  diagonal twice, so inside the loop means inside exactly one piece.
* **Along a chain, the other piece's inside is constant** (`chain_inside_const`). Two finite
  straight lines that do not meet are kept apart by a straight line (`sep_segments`); so a
  finite straight line off a loop's boundary satisfies finitely many conditions that keep a
  point off every side, and both its ends are joined to one point near it by finite straight
  lines through no corner (`seg_const`).
* **The pieces lie apart** (`chains_outside`, `pieces_apart`). Parity alone does not keep them
  apart. Near the diagonal, one point is inside the first piece only and another inside the
  second only (`across_diagonal`); along rays from them, away from the diagonal, the first and
  the last points on a side (`first_hit`, `last_hit`) show each chain outside the other piece.
  Then a point inside both would see, along a good ray, a first point on a side or on the
  diagonal, and neither can be.

Natural numbers count corners, sides and crossings; they measure nothing.
-/

namespace Elements.Figures

open Tacit

namespace Diag

/-! ## Corners and sides of a simple loop -/

/-- A corner on a side of a simple loop is one of its ends. -/
theorem corner_on_side {ps : List Point} (h : SimpleLoop ps) {V : Point} (hV : V ∈ ps)
    {s : Point × Point} (hs : s ∈ sides ps) (hVs : OnFiniteLine V s.1 s.2) :
    V = s.1 ∨ V = s.2 := by
  obtain ⟨E, hE⟩ := outgoing_side hV
  by_cases he : s = (V, E)
  · exact Or.inl (by rw [he])
  · exact (Parity.side_meet h hs hE he V hVs (Or.inl rfl)).1

/-- No two sides of a list of distinct corners end at one corner. -/
theorem sides_pairwise_snd {ps : List Point} (h : ps.Nodup) :
    (sides ps).Pairwise (fun s t => s.2 ≠ t.2) := by
  have hm : ((sides ps).map Prod.snd).Nodup := (Parity.sides_map_snd_perm ps).nodup_iff.mpr h
  exact List.pairwise_map.mp hm

/-- Two sides of a list of distinct corners that end at one corner are one side. -/
theorem sides_snd_inj {ps : List Point} (h : ps.Nodup) {s t : Point × Point}
    (hs : s ∈ sides ps) (ht : t ∈ sides ps) (he : s.2 = t.2) : s = t := by
  rcases LoopFacts.pairwise_mem (sides_pairwise_snd h) hs ht with e | e | e
  · exact e
  · exact False.elim (e he)
  · exact False.elim (e he.symm)

/-- The only sides at a corner V are the one coming in from U and the one going on to W. -/
theorem side_at {ps : List Point} (h : ps.Nodup) {U V W : Point} (hUV : (U, V) ∈ sides ps)
    (hVW : (V, W) ∈ sides ps) {t : Point × Point} (ht : t ∈ sides ps)
    (hV : V = t.1 ∨ V = t.2) : t = (U, V) ∨ t = (V, W) := by
  rcases hV with e | e
  · exact Or.inr (LoopFacts.sides_fst_inj h ht hVW e.symm)
  · exact Or.inl (sides_snd_inj h ht hUV e.symm)

/-- Reading a list from a later point is a rotation. -/
theorem rotate_split {ps us vs : List Point} (he : ps = us ++ vs) (hv : vs ≠ [])
    (hlen : 2 ≤ ps.length) : ps.rotateLeft us.length = vs ++ us := by
  have hlt : us.length < ps.length := by
    rw [he, List.length_append]
    have : vs.length ≠ 0 := fun h0 => hv (List.eq_nil_of_length_eq_zero h0)
    omega
  unfold List.rotateLeft
  dsimp only
  split
  · omega
  · rw [Nat.mod_eq_of_lt hlt, he, List.drop_left, List.take_left]

/-- Some corner of a simple loop is off any given straight line: three of them make a
triangle (`LoopFacts.simple_frame`). -/
theorem corner_off {ps : List Point} (h : SimpleLoop ps) (L : Line) :
    ∃ C ∈ ps, ¬ OnLine C L := by
  obtain ⟨A, hA, B, hB, C, hC, hABC⟩ := LoopFacts.simple_frame h
  by_cases hAL : OnLine A L
  · by_cases hBL : OnLine B L
    · exact ⟨C, hC, hABC.off_line hAL hBL⟩
    · exact ⟨B, hB, hBL⟩
  · exact ⟨A, hA, hAL⟩

/-! ## Keeping away from the sides that miss a corner -/

/-- **A point off a finite straight line is kept off it by one straight line**, with the
point strictly on one side: every point on that side is off the finite straight line. If the
point is off the straight line ab, take that line; if on it, beyond a say, take a straight line
through a and a point C off ab. -/
theorem sep_finite {a b V C : Point} {L : Line} (hab : a ≠ b) (ha : OnLine a L)
    (hb : OnLine b L) (hC : ¬ OnLine C L) (hV : ¬ OnFiniteLine V a b) :
    ∃ K : Line, ¬ OnLine V K ∧ ∀ Y : Point, SameSide Y V K → ¬ OnFiniteLine Y a b := by
  have hVa : V ≠ a := fun e => hV (Or.inl e)
  have hVb : V ≠ b := fun e => hV (Or.inr (Or.inl e))
  by_cases hVL : OnLine V L
  · /- Beyond one end: a straight line through that end other than ab. -/
    have beyond {a b : Point} (ha : OnLine a L) (hb : OnLine b L) (hVa : V ≠ a)
        (hVab : Between V a b) :
        ∃ K : Line, ¬ OnLine V K ∧ ∀ Y : Point, SameSide Y V K → ¬ OnFiniteLine Y a b := by
      have haC : a ≠ C := fun e => hC (e ▸ ha)
      obtain ⟨K, haK, hCK⟩ := Postulate1 a C haC
      have hVK : ¬ OnLine V K := fun hVK =>
        hC (line_unique hVa hVL ha hVK haK ▸ hCK)
      have hVb' : ¬ SameSide V b K := pasch3 hVab haK
      refine ⟨K, hVK, fun Y hY hYab => ?_⟩
      rcases hYab with e | e | hb'
      · exact not_on_line_of_same_side hY (e ▸ haK)
      · exact hVb' (by rw [← e]; exact same_side_symm hY)
      · exact hVb' (same_side_trans hY (pasch2 hb' haK
          (fun hYK => not_on_line_of_same_side hY hYK)))
    rcases between_cases hVa hab hVb hVL ha hb with h' | h' | h'
    · exact beyond ha hb hVa h'
    · exact absurd (Or.inr (Or.inr h')) hV
    · obtain ⟨K, hK, hKY⟩ := beyond hb ha hVb h'
      exact ⟨K, hK, fun Y hY hYab => hKY Y hY (LoopFacts.onFiniteLine_comm.mp hYab)⟩
  · refine ⟨L, hVL, fun Y hY hYab => ?_⟩
    exact not_on_line_of_same_side hY (LoopFacts.onFiniteLine_onLine hYab ha hb)

/-- **The conditions at a corner.** Finitely many straight lines, each with the corner V
strictly on one side, such that a point on V's side of all of them is on no side of the loop
that does not end at V. -/
theorem conditions {ps : List Point} (h : SimpleLoop ps) {V : Point} (hV : V ∈ ps) :
    ∃ hs : List (Point × Line), (∀ p ∈ hs, p.1 = V ∧ ¬ OnLine V p.2) ∧
      ∀ t ∈ sides ps, V ≠ t.1 → V ≠ t.2 → ∀ Y : Point,
        (∀ p ∈ hs, SameSide Y p.1 p.2) → ¬ OnFiniteLine Y t.1 t.2 := by
  suffices key : ∀ ts : List (Point × Point), (∀ t ∈ ts, t ∈ sides ps) →
      ∃ hs : List (Point × Line), (∀ p ∈ hs, p.1 = V ∧ ¬ OnLine V p.2) ∧
        ∀ t ∈ ts, V ≠ t.1 → V ≠ t.2 → ∀ Y : Point,
          (∀ p ∈ hs, SameSide Y p.1 p.2) → ¬ OnFiniteLine Y t.1 t.2 from
    key (sides ps) fun _ ht => ht
  intro ts
  induction ts with
  | nil => exact fun _ => ⟨[], by simp, by simp⟩
  | cons t ts ih =>
    intro hts
    obtain ⟨hs, h1, h2⟩ := ih fun u hu => hts u (List.mem_cons_of_mem _ hu)
    have ht := hts t List.mem_cons_self
    by_cases hVt : V = t.1 ∨ V = t.2
    · refine ⟨hs, h1, fun u hu hu1 hu2 => ?_⟩
      rcases List.mem_cons.mp hu with rfl | hu
      · exact absurd hVt (by rintro (e | e) <;> contradiction)
      · exact h2 u hu hu1 hu2
    · have hne := h.2.2.1 t ht
      obtain ⟨L, h₁, h₂⟩ := Postulate1 t.1 t.2 hne
      obtain ⟨C, -, hC⟩ := corner_off h L
      have hVoff : ¬ OnFiniteLine V t.1 t.2 := fun hon => hVt (corner_on_side h hV ht hon)
      obtain ⟨K, hVK, hK⟩ := sep_finite hne h₁ h₂ hC hVoff
      refine ⟨(V, K) :: hs, ?_, fun u hu hu1 hu2 Y hY => ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨rfl, hVK⟩
        · exact h1 p hp
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact hK Y (hY _ List.mem_cons_self)
        · exact h2 u hu hu1 hu2 Y fun p hp => hY p (List.mem_cons_of_mem _ hp)

/-- The conditions hold at their corner. -/
theorem conditions_self {hs : List (Point × Line)} {V : Point}
    (h : ∀ p ∈ hs, p.1 = V ∧ ¬ OnLine V p.2) : ∀ p ∈ hs, SameSide V p.1 p.2 := by
  intro p hp
  rw [(h p hp).1]
  exact same_side_refl (h p hp).2

/-- Conditions holding at two points hold between them. -/
theorem conds_between {hs : List (Point × Line)} {X Y Z : Point}
    (hX : ∀ p ∈ hs, SameSide X p.1 p.2) (hZ : ∀ p ∈ hs, SameSide Z p.1 p.2)
    (hb : Between X Y Z) : ∀ p ∈ hs, SameSide Y p.1 p.2 :=
  fun p hp => Avoid.same_side_between hb (hX p hp) (hZ p hp)

/-! ## A corner with all the others strictly on one side of a straight line -/

/-- **A straight line with every corner strictly on one side**: a side line of a convex cell
holding all the corners strictly inside it (`Arr.enclose_list`, `Arr.strict_enclosure`). -/
theorem enclosing_line {ps : List Point} (h : SimpleLoop ps) :
    ∃ (K : Line) (R : Point), ∀ C ∈ ps, SameSide C R K := by
  obtain ⟨A, -, B, -, C, -, hABC⟩ := LoopFacts.simple_frame h
  obtain ⟨ds, hds, -, hps⟩ := Arr.enclose_list ps (Ext.triangle_outline hABC)
  obtain ⟨Q, hQ⟩ := Arr.strict_enclosure ⟨ds, hds⟩
  obtain ⟨a, b, c, rest, he⟩ := CellFacts.three_corners Q.convex
  have hnd := Q.convex.2.1
  rw [he] at hnd
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  have hab : (a, b) ∈ sides Q.corners := by rw [he]; simp [sides, segments]
  have hc : c ∈ Q.corners := by rw [he]; simp
  obtain ⟨K, haK, hbK⟩ := Postulate1 a b hnd.1.1
  refine ⟨K, c, fun V hV => ?_⟩
  exact (hQ V (hps V hV) (a, b) hab c hc (Ne.symm hnd.1.2.1) (Ne.symm hnd.2.1.1)).sameSide
    haK hbK

/-- **A point of a straight line in general position**: a point O of K, and another E, with O
on no straight line through two different corners. -/
theorem generic_point {ps : List Point} {K : Line} (hoff : ∀ C ∈ ps, ¬ OnLine C K) :
    ∃ O E : Point, OnLine O K ∧ OnLine E K ∧ O ≠ E ∧
      ∀ C ∈ ps, ∀ D ∈ ps, C ≠ D → ¬ Collinear O C D := by
  obtain ⟨P₁, hP₁, -⟩ := exists_point_on_line K []
  obtain ⟨P₂, hP₂, hP₂₁⟩ := exists_point_on_line K [P₁]
  have h12 : P₁ ≠ P₂ := fun e => hP₂₁ (e ▸ List.mem_singleton_self P₁)
  let ls : List Line := ps.flatMap fun C => CoverFacts.joins C ps
  have hls : ∀ L ∈ ls, ∃ C ∈ ps, ∃ D ∈ ps, L = Classical.choose (collinear_of_two C D) := by
    intro L hL
    obtain ⟨C, hC, hL⟩ := List.mem_flatMap.mp hL
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hL
    exact ⟨C, hC, D, hD, rfl⟩
  obtain ⟨O, hO, hOa⟩ := Arr.between_avoiding ls h12 (by
    rintro L hL ⟨h1, h2⟩
    obtain ⟨C, hC, D, -, rfl⟩ := hls L hL
    have hspec := Classical.choose_spec (collinear_of_two C D)
    exact hoff C hC (line_unique h12 h1 h2 hP₁ hP₂ ▸ hspec.1))
  refine ⟨O, P₁, on_line_of_between_ends hO hP₁ hP₂, hP₁, (ne_of_between hO).symm,
    fun C hC D hD hCD => ?_⟩
  rintro ⟨M, hOM, hCM, hDM⟩
  have hspec := Classical.choose_spec (collinear_of_two C D)
  have he := line_unique hCD hspec.1 hspec.2 hCM hDM
  exact hOa _ (List.mem_flatMap.mpr ⟨C, hC, List.mem_map_of_mem hD⟩) (he ▸ hOM)

section Wrap

variable {K : Line} {O E R : Point}

/-- **Turning towards E.** With O and E on K, and D and V strictly on R's side of K: if D is
on E's side of the straight line OV, then V is across the straight line OD from E. The ray
OD crosses the finite straight line EV (the crossbar). -/
theorem turn {D V : Point} {M N : Line} (hOK : OnLine O K) (hEK : OnLine E K) (hOE : O ≠ E)
    (hD : SameSide D R K) (hV : SameSide V R K) (hOM : OnLine O M) (hVM : OnLine V M)
    (hON : OnLine O N) (hDN : OnLine D N) (hVN : ¬ OnLine V N) (hDE : SameSide D E M) :
    OppositeSides V E N := by
  have hOV : O ≠ V := fun e => not_on_line_of_same_side hV (e ▸ hOK)
  obtain ⟨X, hEXV, hX⟩ := crossbar (A := O) (B := E) (C := V) (D := D)
    (SameSideOf.of_line hOE hOK hEK (same_side_trans (same_side_symm hD) (same_side_symm hV)))
    (SameSideOf.of_line hOV hOM hVM hDE)
  have hOD : O ≠ D := fun e => not_on_line_of_same_side hD (e ▸ hOK)
  have hEN : ¬ OnLine E N := fun hEN =>
    not_on_line_of_same_side hD (line_unique hOE hON hEN hOK hEK ▸ hDN)
  exact ⟨hVN, hEN, pasch3 (between_symm hEXV) (hX.onLine hON hDN)⟩

/-- **Turning further.** If C is across OV from E, and V across OD from E, all three strictly
on R's side of K, then C is across OD from E. The finite straight line EC crosses OV at a
point G on V's side of OD. -/
theorem turn_trans {C V : Point} {M N : Line} (hOK : OnLine O K) (hEK : OnLine E K)
    (hC : SameSide C R K) (hV : SameSide V R K)
    (hOM : OnLine O M) (hVM : OnLine V M) (hON : OnLine O N)
    (hVN : ¬ OnLine V N) (hCN : ¬ OnLine C N)
    (hCM : OppositeSides C E M) (hVE : OppositeSides V E N) : OppositeSides C E N := by
  obtain ⟨G, hGM, hCGE⟩ := hCM.exists_between
  have hMK : ¬ OnLine V K := not_on_line_of_same_side hV
  have hGK : ¬ OnLine G K := by
    intro hGK
    have hGO : G = O := Classical.byContradiction fun hne =>
      hMK (line_unique hne hGK hOK hGM hOM ▸ hVM)
    rw [hGO] at hCGE
    exact not_on_line_of_same_side hC (on_line_of_between (between_symm hCGE) hEK hOK)
  have hGC : SameSide G C K := pasch2 (between_symm hCGE) hEK hGK
  have hCV : SameSide C V K := same_side_trans (same_side_symm hC) (same_side_symm hV)
  have hGV' : SameSide G V K := same_side_trans (same_side_symm hGC) hCV
  /- G is on V's side of OD: O, where OV meets OD, is not between them. -/
  have hGV : SameSide G V N := by
    by_cases hGV : G = V
    · rw [hGV]; exact same_side_refl hVN
    have hMN : N ≠ M := fun e => hVN (e ▸ hVM)
    have hGO : G ≠ O := fun e => hGK (e ▸ hOK)
    have hVO : V ≠ O := fun e => hMK (e ▸ hOK)
    refine Classical.byContradiction fun hn => ?_
    exact pasch3 (pasch4 hMN hON hOM hGM hVM hGV hGO hVO hn) hOK hGV'
  have hGE : ¬ SameSide G E N := fun hGE => hVE.2.2 (same_side_trans hGV hGE)
  refine ⟨hCN, hVE.2.1, fun hCE => hGE ?_⟩
  exact Avoid.same_side_between hCGE hCE (same_side_refl hVE.2.1)

/-- **Gift wrapping**: among finitely many corners strictly on R's side of K, one, V, has all
the others across the straight line OV from E. Take the corners one by one; a new corner on
E's side of OV takes V's place (`turn`, `turn_trans`). -/
theorem wrap {ps : List Point} (hOK : OnLine O K) (hEK : OnLine E K) (hOE : O ≠ E)
    (hR : ∀ C ∈ ps, SameSide C R K) (hgen : ∀ C ∈ ps, ∀ D ∈ ps, C ≠ D → ¬ Collinear O C D) :
    ∀ l : List Point, (∀ C ∈ l, C ∈ ps) → l ≠ [] →
      ∃ V ∈ l, ∀ C ∈ l, C ≠ V → OppositeSidesOf C E O V := by
  have hOC {C : Point} (hC : C ∈ ps) : O ≠ C := fun e =>
    not_on_line_of_same_side (hR C hC) (e ▸ hOK)
  intro l
  induction l with
  | nil => exact fun _ h => absurd rfl h
  | cons D l ih =>
    intro hl _
    have hDps := hl D List.mem_cons_self
    by_cases hl0 : l = []
    · subst hl0
      refine ⟨D, List.mem_cons_self, fun C hC hCD => ?_⟩
      exact absurd (List.mem_singleton.mp hC) hCD
    obtain ⟨V, hV, hVall⟩ := ih (fun C hC => hl C (List.mem_cons_of_mem _ hC)) hl0
    have hVps := hl V (List.mem_cons_of_mem _ hV)
    obtain ⟨M, hOM, hVM⟩ := Postulate1 O V (hOC hVps)
    by_cases hkeep : D = V ∨ OppositeSidesOf D E O V
    · refine ⟨V, List.mem_cons_of_mem _ hV, fun C hC hCV => ?_⟩
      rcases List.mem_cons.mp hC with rfl | hC
      · rcases hkeep with e | hk
        · exact absurd e hCV
        · exact hk
      · exact hVall C hC hCV
    · rw [not_or] at hkeep
      obtain ⟨hDV, hDo⟩ := hkeep
      have hDM : ¬ OnLine D M := fun hDM => hgen V hVps D hDps (Ne.symm hDV) ⟨M, hOM, hVM, hDM⟩
      have hEM : ¬ OnLine E M := fun hEM =>
        not_on_line_of_same_side (hR V hVps) (line_unique hOE hOM hEM hOK hEK ▸ hVM)
      have hDE : SameSide D E M := Classical.byContradiction fun hn =>
        hDo (OppositeSidesOf.of_line (hOC hVps) hOM hVM ⟨hDM, hEM, hn⟩)
      obtain ⟨N, hON, hDN⟩ := Postulate1 O D (hOC hDps)
      have hVN : ¬ OnLine V N := fun hVN => hgen D hDps V hVps hDV ⟨N, hON, hDN, hVN⟩
      have hVE : OppositeSides V E N :=
        turn hOK hEK hOE (hR D hDps) (hR V hVps) hOM hVM hON hDN hVN hDE
      refine ⟨D, List.mem_cons_self, fun C hC hCD => ?_⟩
      refine OppositeSidesOf.of_line (hOC hDps) hON hDN ?_
      rcases List.mem_cons.mp hC with rfl | hC
      · exact absurd rfl hCD
      by_cases hCV : C = V
      · rw [hCV]; exact hVE
      have hCps := hl C (List.mem_cons_of_mem _ hC)
      have hCN : ¬ OnLine C N := fun hCN => hgen D hDps C hCps (Ne.symm hCD) ⟨N, hON, hDN, hCN⟩
      exact turn_trans hOK hEK (hR C hCps) (hR V hVps) hOM hVM hON hVN hCN
        ((hVall C hC hCV).oppositeSides hOM hVM) hVE

end Wrap

/-- **An extreme corner**: a corner V and a straight line through it with every other corner
strictly on one side, across it from a point E. -/
theorem extreme_corner {ps : List Point} (h : SimpleLoop ps) :
    ∃ V ∈ ps, ∃ (L : Line) (E : Point), OnLine V L ∧ ¬ OnLine E L ∧
      ∀ C ∈ ps, C ≠ V → OppositeSides C E L := by
  obtain ⟨K, R, hR⟩ := enclosing_line h
  obtain ⟨O, E, hOK, hEK, hOE, hgen⟩ :=
    generic_point (ps := ps) (K := K) fun C hC => not_on_line_of_same_side (hR C hC)
  have hne : ps ≠ [] := by
    intro e
    have := h.1
    rw [e] at this
    simp at this
  obtain ⟨V, hV, hall⟩ := wrap hOK hEK hOE hR hgen ps (fun _ h => h) hne
  have hOV : O ≠ V := fun e => not_on_line_of_same_side (hR V hV) (e ▸ hOK)
  obtain ⟨L, hOL, hVL⟩ := Postulate1 O V hOV
  have hEL : ¬ OnLine E L := fun hEL =>
    not_on_line_of_same_side (hR V hV) (line_unique hOE hOL hEL hOK hEK ▸ hVL)
  exact ⟨V, hV, L, E, hVL, hEL, fun C hC hCV => (hall C hC hCV).oppositeSides hOL hVL⟩

/-! ## Leaving a triangle -/

/-- **Leaving past a corner.** If Z is inside the triangle VPQ, and Y₀ is on the straight line
PQ beyond Q, the finite straight line ZY₀ crosses the finite side QV. -/
theorem exit_beyond {V P Q Z Y₀ : Point} (h : Triangle V P Q) (hZ : InsideTriangle Z V P Q)
    (hY₀ : Between P Q Y₀) :
    ∃ Y : Point, Between Z Y Y₀ ∧ OnFiniteLine Y Q V := by
  obtain ⟨N, hPN, hQN⟩ := Postulate1 P Q h.ne₂₃
  obtain ⟨M, hQM, hVM⟩ := Postulate1 Q V h.ne₁₃.symm
  obtain ⟨K, hPK, hVK⟩ := Postulate1 P V h.ne₁₂.symm
  have hY₀N : OnLine Y₀ N := on_line_of_between hY₀ hPN hQN
  have hVN : ¬ OnLine V N := h.bca.off_line hPN hQN
  have hQK : ¬ OnLine Q K := h.bac.off_line hPK hVK
  have hY₀Q : Y₀ ≠ Q := (ne_of_between (between_symm hY₀))
  have hY₀M : ¬ OnLine Y₀ M := fun hY₀M =>
    hVN (line_unique hY₀Q hY₀M hQM hY₀N hQN ▸ hVM)
  have hZM : SameSide Z P M := hZ.2.1.sameSide hQM hVM
  obtain ⟨Y, hYM, hZYY₀⟩ := OppositeSides.exists_between (L := M) (P := Z) (Q := Y₀)
    ⟨not_on_line_of_same_side hZM, hY₀M,
      fun hs => pasch3 hY₀ hQM (same_side_trans hZM hs)⟩
  refine ⟨Y, hZYY₀, ?_⟩
  by_cases hYQ : Y = Q
  · exact Or.inl hYQ
  have hYN : ¬ OnLine Y N := fun hYN => hYQ (Classical.byContradiction fun hne =>
    hVN (line_unique hne hYN hQN hYM hQM ▸ hVM))
  have hYV : SameSide Y V N :=
    same_side_trans (same_side_symm (pasch2 (between_symm hZYY₀) hY₀N hYN))
      (hZ.1.sameSide hPN hQN)
  have hYQK : SameSide Y Q K := Avoid.same_side_between hZYY₀ (hZ.2.2.sameSide hVK hPK)
    (same_side_symm (pasch2 hY₀ hPK hQK))
  have hYV' : Y ≠ V := fun e => not_on_line_of_same_side hYQK (e ▸ hVK)
  rcases between_cases (Ne.symm hYQ) hYV' h.ne₁₃.symm hQM hYM hVM with hb | hb | hb
  · exact Or.inr (Or.inr hb)
  · exact absurd hYV (pasch3 hb hQN)
  · exact absurd (same_side_symm hYQK) (pasch3 hb hVK)

/-- **Leaving across the side PQ.** A finite straight line from a point Z inside the triangle
VPQ to a point S not strictly on V's side of PQ meets the triangle's boundary, at S or before
it. -/
theorem exit_side {V P Q Z S : Point} (h : Triangle V P Q) (hZ : InsideTriangle Z V P Q)
    (hS : ¬ SameSideOf S V P Q) :
    ∃ Y : Point, (Y = S ∨ Between Z Y S) ∧
      (OnFiniteLine Y V P ∨ OnFiniteLine Y P Q ∨ OnFiniteLine Y Q V) := by
  obtain ⟨N, hPN, hQN⟩ := Postulate1 P Q h.ne₂₃
  have hZN : SameSide Z V N := hZ.1.sameSide hPN hQN
  obtain ⟨Y₀, hY₀N, hY₀S⟩ : ∃ Y₀ : Point, OnLine Y₀ N ∧ (Y₀ = S ∨ Between Z Y₀ S) := by
    by_cases hSN : OnLine S N
    · exact ⟨S, hSN, Or.inl rfl⟩
    · obtain ⟨Y₀, hY₀N, hb⟩ := OppositeSides.exists_between (L := N) (P := Z) (Q := S)
        ⟨not_on_line_of_same_side hZN, hSN, fun hs =>
          hS (SameSideOf.of_line h.ne₂₃ hPN hQN (same_side_trans hs hZN))⟩
      exact ⟨Y₀, hY₀N, Or.inr hb⟩
  have conv {Y : Point} (hY : Between Z Y Y₀) : Y = S ∨ Between Z Y S := by
    rcases hY₀S with e | hb
    · exact Or.inr (e ▸ hY)
    · exact Or.inr (between_of_between_left hb hY)
  by_cases hP : Y₀ = P
  · exact ⟨Y₀, hY₀S, Or.inr (Or.inl (Or.inl hP))⟩
  by_cases hQ : Y₀ = Q
  · exact ⟨Y₀, hY₀S, Or.inr (Or.inl (Or.inr (Or.inl hQ)))⟩
  rcases between_cases h.ne₂₃ (Ne.symm hQ) (Ne.symm hP) hPN hQN hY₀N with hb | hb | hb
  · obtain ⟨Y, hY, hYQV⟩ := exit_beyond h hZ hb
    exact ⟨Y, conv hY, Or.inr (Or.inr hYQV)⟩
  · obtain ⟨Y, hY, hYPV⟩ := exit_beyond h.acb ⟨hZ.1.swap, hZ.2.2.swap, hZ.2.1.swap⟩ hb
    exact ⟨Y, conv hY, Or.inl (LoopFacts.onFiniteLine_comm.mp hYPV)⟩
  · exact ⟨Y₀, hY₀S, Or.inr (Or.inl (Or.inr (Or.inr hb)))⟩

/-- **Leaving a triangle.** A finite straight line from a point inside a triangle to a point
not inside it meets the triangle's boundary, at that point or before it. -/
theorem exit {V P Q Z S : Point} (h : Triangle V P Q) (hZ : InsideTriangle Z V P Q)
    (hS : ¬ InsideTriangle S V P Q) :
    ∃ Y : Point, (Y = S ∨ Between Z Y S) ∧
      (OnFiniteLine Y V P ∨ OnFiniteLine Y P Q ∨ OnFiniteLine Y Q V) := by
  by_cases h₁ : SameSideOf S V P Q
  · by_cases h₂ : SameSideOf S P Q V
    · have h₃ : ¬ SameSideOf S Q V P := fun h₃ => hS ⟨h₁, h₂, h₃⟩
      obtain ⟨Y, hY, hb⟩ := exit_side h.cab ⟨hZ.2.2, hZ.1, hZ.2.1⟩ h₃
      refine ⟨Y, hY, ?_⟩
      rcases hb with hb | hb | hb
      · exact Or.inr (Or.inr hb)
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
    · obtain ⟨Y, hY, hb⟩ := exit_side h.bca ⟨hZ.2.1, hZ.2.2, hZ.1⟩ h₂
      refine ⟨Y, hY, ?_⟩
      rcases hb with hb | hb | hb
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hb)
      · exact Or.inl hb
  · exact exit_side h hZ h₁

/-- Points reached from Z towards two points on either side of it are different. -/
theorem ray_opposite {a b Z Y Y' : Point} (hb : Between a Z b) (hY : Y = a ∨ Between Z Y a)
    (hY' : Y' = b ∨ Between Z Y' b) : Y ≠ Y' := by
  have toRay {c Y : Point} (hZc : Z ≠ c) (hY : Y = c ∨ Between Z Y c) : OnRay c Z Y := by
    rcases hY with rfl | hY
    · exact OnRay.self hZc
    · exact (OnRay.of_between hY).symm
  intro e
  subst e
  exact OnRay.not_between (toRay (ne_of_between hb).symm hY)
    (toRay (ne_of_between (between_symm hb)).symm hY') hb

/-- A point of the finite straight line from V to a point U' of the side VU is on that side. -/
theorem sub_finite {U V U' Y : Point} (hU' : U' = U ∨ Between V U' U)
    (hY : OnFiniteLine Y V U') : OnFiniteLine Y U V := by
  rcases hU' with rfl | hU'
  · exact LoopFacts.onFiniteLine_comm.mp hY
  rcases hY with e | e | hb
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (e ▸ between_symm hU'))
  · exact Or.inr (Or.inr (between_symm (between_of_between_left hU' hb)))

/-- A point U' of the side VU, other than U, does not have U between V and it. -/
theorem end_not_within {U V U' : Point} (hU' : U' = U ∨ Between V U' U)
    (hY : OnFiniteLine U V U') (hUV : U ≠ V) : U' = U := by
  rcases hU' with e | hU'
  · exact e
  rcases hY with e | e | hb
  · exact absurd e hUV
  · exact e.symm
  · exact absurd (between_symm hU') (not_between_of_between (between_symm hb))

/-- A point of the closed side VU' lies on the straight line VU. -/
theorem onLine_sub {U V U' : Point} {L : Line} (hU' : U' = U ∨ Between V U' U)
    (hV : OnLine V L) (hU : OnLine U L) : OnLine U' L := by
  rcases hU' with rfl | hU'
  · exact hU
  · exact on_line_of_between_ends hU' hV hU

/-- **A triangle at a corner with no corner inside it meets no side inside.** Let U' be on the
side VU and W' on the side VW, at the corner V of a simple loop. A side through a point Z
inside the triangle VU'W', with no corner inside it, leaves the triangle both ways; each time
it meets the boundary on U'W', for it cannot cross VU or VW but at their ends; then the side's
straight line is U'W', which Z is off. -/
theorem clean {ps : List Point} (h : SimpleLoop ps) {U V W U' W' : Point}
    (hUV : (U, V) ∈ sides ps) (hVW : (V, W) ∈ sides ps)
    (hU' : U' = U ∨ Between V U' U) (hW' : W' = W ∨ Between V W' W)
    (hT : Triangle V U' W') (hno : ∀ C ∈ ps, ¬ InsideTriangle C V U' W') :
    ∀ Z : Point, InsideTriangle Z V U' W' → ¬ loopBoundary ps Z := by
  rintro Z hZ ⟨t, ht, hZt⟩
  have hb : Between t.1 Z t.2 := by
    rcases hZt with e | e | hb
    · exact absurd hZ (hno _ (e ▸ (LoopFacts.side_mem ht).1))
    · exact absurd hZ (hno _ (e ▸ (LoopFacts.side_mem ht).2))
    · exact hb
  have hUV' : U ≠ V := h.2.2.1 _ hUV
  have hVW' : V ≠ W := h.2.2.1 _ hVW
  obtain ⟨LU, hVLU, hULU⟩ := Postulate1 V U hUV'.symm
  obtain ⟨LW, hVLW, hWLW⟩ := Postulate1 V W hVW'
  have hU'LU := onLine_sub hU' hVLU hULU
  have hW'LW := onLine_sub hW' hVLW hWLW
  have hZLU : ¬ OnLine Z LU := not_on_line_of_same_side (hZ.2.2.sameSide hVLU hU'LU)
  have hZLW : ¬ OnLine Z LW := not_on_line_of_same_side (hZ.2.1.sameSide hW'LW hVLW)
  /- The side is not one of the two at V. -/
  have hnot : t ≠ (U, V) ∧ t ≠ (V, W) := by
    constructor
    · rintro rfl
      exact hZLU (on_line_of_between_ends hb hULU hVLU)
    · rintro rfl
      exact hZLW (on_line_of_between_ends hb hVLW hWLW)
  have hVt : V ≠ t.1 ∧ V ≠ t.2 := by
    constructor <;> intro e
    · rcases side_at h.2.1 hUV hVW ht (Or.inl e) with e' | e'
      · exact hnot.1 e'
      · exact hnot.2 e'
    · rcases side_at h.2.1 hUV hVW ht (Or.inr e) with e' | e'
      · exact hnot.1 e'
      · exact hnot.2 e'
  /- Leaving towards either end, the side meets the boundary on U'W'. -/
  have key {s : Point} (hs : s = t.1 ∨ s = t.2) :
      ∃ Y : Point, (Y = s ∨ Between Z Y s) ∧ OnFiniteLine Y U' W' ∧
        OnFiniteLine Y t.1 t.2 := by
    have hsm : s ∈ ps := by
      rcases hs with rfl | rfl
      · exact (LoopFacts.side_mem ht).1
      · exact (LoopFacts.side_mem ht).2
    obtain ⟨Y, hY, hbd⟩ := exit hT hZ (hno s hsm)
    have hYt : OnFiniteLine Y t.1 t.2 := by
      rcases hs with rfl | rfl
      · rcases hY with e | hY
        · exact Or.inl e
        · exact Or.inr (Or.inr (between_of_between_left hb (between_symm hY)))
      · rcases hY with e | hY
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (between_symm
            (between_of_between_left (between_symm hb) (between_symm hY))))
    refine ⟨Y, hY, ?_, hYt⟩
    rcases hbd with hbd | hbd | hbd
    · obtain ⟨h₁, h₂⟩ := Parity.side_meet h hUV ht (Ne.symm hnot.1) Y (sub_finite hU' hbd) hYt
      rcases h₁ with e | e
      · have e : Y = U := e
        have hUU' : U' = U := end_not_within hU' (by rw [← e]; exact hbd) hUV'
        exact Or.inl (e.trans hUU'.symm)
      · have e : Y = V := e
        rcases h₂ with e' | e'
        · exact absurd (e.symm.trans e') hVt.1
        · exact absurd (e.symm.trans e') hVt.2
    · exact hbd
    · have hbd' : OnFiniteLine Y V W' := LoopFacts.onFiniteLine_comm.mp hbd
      obtain ⟨h₁, h₂⟩ := Parity.side_meet h hVW ht (Ne.symm hnot.2) Y
        (LoopFacts.onFiniteLine_comm.mp (sub_finite hW' hbd')) hYt
      rcases h₁ with e | e
      · have e : Y = V := e
        rcases h₂ with e' | e'
        · exact absurd (e.symm.trans e') hVt.1
        · exact absurd (e.symm.trans e') hVt.2
      · have e : Y = W := e
        have hWW' : W' = W := end_not_within hW' (by rw [← e]; exact hbd') hVW'.symm
        exact Or.inr (Or.inl (e.trans hWW'.symm))
  obtain ⟨Y₁, hY₁, hY₁m, hY₁t⟩ := key (Or.inl rfl)
  obtain ⟨Y₂, hY₂, hY₂m, hY₂t⟩ := key (Or.inr rfl)
  have hne := ray_opposite hb hY₁ hY₂
  obtain ⟨M, hU'M, hW'M⟩ := Postulate1 U' W' hT.ne₂₃
  obtain ⟨N, h₁N, h₂N⟩ := Postulate1 t.1 t.2 (h.2.2.1 t ht)
  have he := line_unique hne (LoopFacts.onFiniteLine_onLine hY₁t h₁N h₂N)
    (LoopFacts.onFiniteLine_onLine hY₂t h₁N h₂N) (LoopFacts.onFiniteLine_onLine hY₁m hU'M hW'M)
    (LoopFacts.onFiniteLine_onLine hY₂m hU'M hW'M)
  exact not_on_line_of_same_side (hZ.1.sameSide hU'M hW'M)
    (he ▸ on_line_of_between_ends hb h₁N h₂N)

/-! ## The corner nearest V -/

/-- **A straight line through a point inside, across the corner V.** Through a point X inside
the triangle VUW passes a straight line meeting VU and VW strictly between their ends: produce
WX to P on VU, take U₁ between P and U, and produce U₁X to VW (`inside_through`). -/
theorem across {V U W X : Point} (h : Triangle V U W) (hX : InsideTriangle X V U W) :
    ∃ U₁ W₁ : Point, Between V U₁ U ∧ Between V W₁ W ∧ Between U₁ X W₁ := by
  obtain ⟨P, hWXP, hVPU⟩ := inside_through (A := V) (B := W) (C := U) (D := X)
    ⟨hX.1.swap, hX.2.2.swap, hX.2.1.swap⟩
  obtain ⟨LU, hVL, hUL⟩ := Postulate1 V U h.ne₁₂
  have hPL := on_line_of_between_ends hVPU hVL hUL
  obtain ⟨U₁, hU₁L, hPU₁U, -⟩ :=
    exists_point_between hPL hUL (ne_of_between (between_symm hVPU)).symm []
  have hVPU₁ : Between V P U₁ := between_cut hVPU hPU₁U
  have hVU₁U : Between V U₁ U :=
    between_symm (between_of_between_left (between_symm hVPU) (between_symm hPU₁U))
  have hT : Triangle W V U₁ :=
    (Triangle.of_line hVL hU₁L (ne_of_between hVU₁U) (h.off_line hVL hUL)).cab
  have hX' := Avoid.inside_of_between hT hVPU₁ hWXP
  obtain ⟨W₁, hU₁XW₁, hVW₁W⟩ := inside_through (A := V) (B := U₁) (C := W) (D := X)
    ⟨hX'.2.1, hX'.2.2, hX'.1⟩
  exact ⟨U₁, W₁, hVU₁U, hVW₁W, hU₁XW₁⟩

/-- A filter keeping fewer members: one test implying another, which some member passes and
the first fails. -/
theorem filter_lt {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
      (l.filter p).length < (l.filter q).length
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, hpq, ⟨x, hx, hqx, hpx⟩ => by
    have hle : ∀ m : List α, (∀ x ∈ m, p x = true → q x = true) →
        (m.filter p).length ≤ (m.filter q).length := by
      intro m hm
      induction m with
      | nil => simp
      | cons b m ih =>
        have ih' := ih fun y hy => hm y (List.mem_cons_of_mem _ hy)
        have hb := hm b List.mem_cons_self
        simp only [List.filter_cons]
        cases hp : p b <;> cases hq : q b <;> simp [hp, hq] at hb ⊢ <;> omega
    have hpq' : ∀ y ∈ l, p y = true → q y = true := fun y hy => hpq y (List.mem_cons_of_mem _ hy)
    have ha := hpq a List.mem_cons_self
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [List.filter_cons, hqx, hpx]
      simp
      exact Nat.lt_succ_of_le (hle l hpq')
    · have ih := filter_lt p q l hpq' ⟨x, hx, hqx, hpx⟩
      simp only [List.filter_cons]
      cases hp : p a <;> cases hq : q a <;> simp [hp, hq] at ha ⊢ <;> omega

open Classical in
/-- **A corner on a cut across V, with no corner in the triangle cut off.** No distance is
compared. Inside the triangle VUW lies a corner; cut the triangle by a straight line through it
across V (`across`), and repeat with a corner inside the smaller triangle, while there is one.
Each time fewer corners are inside, so this stops: at a corner X on a straight line U'W' across
V, with no corner inside the triangle VU'W'. -/
theorem nearest {ps : List Point} {V : Point} :
    ∀ (n : Nat) {U W X : Point}, Triangle V U W →
      (ps.filter fun C => decide (InsideTriangle C V U W)).length ≤ n →
      X ∈ ps → InsideTriangle X V U W →
      ∃ U' W' X' : Point, Between V U' U ∧ Between V W' W ∧ X' ∈ ps ∧ Between U' X' W' ∧
        ∀ C ∈ ps, ¬ InsideTriangle C V U' W' := by
  intro n
  induction n with
  | zero =>
    intro U W X _ hn hX hXin
    have hpos : 0 < (ps.filter fun C => decide (InsideTriangle C V U W)).length :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨hX, decide_eq_true hXin⟩)
    omega
  | succ n ih =>
    intro U W X h hn hX hXin
    obtain ⟨U₁, W₁, hVU₁U, hVW₁W, hU₁XW₁⟩ := across h hXin
    obtain ⟨h₁, hsub⟩ := Avoid.corner_triangle h hVU₁U hVW₁W
    by_cases hCex : ∃ C ∈ ps, InsideTriangle C V U₁ W₁
    · obtain ⟨C, hC, hCin⟩ := hCex
      have hlt := filter_lt (fun C => decide (InsideTriangle C V U₁ W₁))
        (fun C => decide (InsideTriangle C V U W)) ps
        (fun Y _ hY => decide_eq_true (hsub Y (of_decide_eq_true hY)))
        ⟨X, hX, decide_eq_true hXin, by
          rw [decide_eq_false_iff_not]
          intro hX₁
          obtain ⟨M, hU₁M, hW₁M⟩ := Postulate1 U₁ W₁ h₁.ne₂₃
          exact not_on_line_of_same_side (hX₁.1.sameSide hU₁M hW₁M)
            (on_line_of_between_ends hU₁XW₁ hU₁M hW₁M)⟩
      obtain ⟨U', W', X', hU', hW', hX', hb, hno⟩ := ih h₁ (by omega) hC hCin
      exact ⟨U', W', X', between_of_between_left hVU₁U hU',
        between_of_between_left hVW₁W hW', hX', hb, hno⟩
    · exact ⟨U₁, W₁, X, hVU₁U, hVW₁W, hX, hU₁XW₁, fun C hC hCin => hCex ⟨C, hC, hCin⟩⟩

/-! ## An ear -/

/-- Three sides closing up after three corners leave a loop of three corners. -/
theorem three_cycle {ps : List Point} (h : SimpleLoop ps) {U V W : Point}
    (hUV : (U, V) ∈ sides ps) (hVW : (V, W) ∈ sides ps) (hWU : (W, U) ∈ sides ps) :
    ps.length = 3 := by
  obtain ⟨us, vs, rest, rfl, hrot⟩ := Parity.rotate_to h.2.1 h.1 hUV hVW
  have hperm := LoopFacts.sides_rotate_perm us vs
  have hnd : (vs ++ us).Nodup := List.perm_append_comm.nodup_iff.mp h.2.1
  have hWU' : (W, U) ∈ sides (vs ++ us) := hperm.mem_iff.mp hWU
  rw [hrot] at hnd hWU'
  have hlen : (us ++ vs).length = (vs ++ us).length := by simp [Nat.add_comm]
  rw [hlen, hrot]
  cases rest with
  | nil => rfl
  | cons d rest =>
    have hWd : (W, d) ∈ sides (U :: V :: W :: d :: rest) := by simp [sides, segments]
    have he := LoopFacts.sides_fst_inj hnd hWU' hWd rfl
    rw [Prod.mk.injEq] at he
    rw [← he.2] at hnd
    simp at hnd

/-- A corner P on the straight line of a finite straight line ab, with no corner strictly
within ab, on the ray from a point Z within ab towards a, is a, when Z is between P and Q and
no corner is strictly between P and Q. -/
theorem ray_end {ps : List Point} {a b Z P Q : Point} (hcorner : ∀ C ∈ ps, ¬ Between a C b)
    (hb : Between a Z b) (hPQ : Between P Z Q) (hP : P ∈ ps)
    (hon : ∀ C ∈ ps, ¬ Between P C Q) (ha : a ∈ ps) (hray : OnRay P Z a) : P = a := by
  obtain ⟨-, hPZ, ⟨L, hZL, haL, hPL⟩, hn⟩ := hray
  refine Classical.byContradiction fun hPa => ?_
  rcases between_cases hPZ.symm hPa (ne_of_between hb).symm hZL hPL haL with h' | h' | h'
  · exact hcorner P hP (between_of_between_left hb (between_symm h'))
  · exact hn h'
  · exact hon a ha (between_of_between_left hPQ (between_symm h'))

/-- **The open base of an ear meets no side.** With no corner inside the triangle VUW, at
the corner V, and none between U and W, a side through a point Z between U and W either runs
along UW, when its ends, corners on that straight line, are U and W, and the loop has three
corners; or it crosses UW at Z, and a point of it a little way towards its end on V's side is
inside the triangle, which no side meets (`clean`). -/
theorem ear_edge {ps : List Point} (h : SimpleLoop ps) (hlen : 4 ≤ ps.length) {U V W : Point}
    (hUV : (U, V) ∈ sides ps) (hVW : (V, W) ∈ sides ps) (hT : Triangle V U W)
    (hin : ∀ C ∈ ps, ¬ InsideTriangle C V U W) (hon : ∀ C ∈ ps, ¬ Between U C W) :
    ∀ Z : Point, Between U Z W → ¬ loopBoundary ps Z := by
  have hclean := clean h hUV hVW (Or.inl rfl) (Or.inl rfl) hT hin
  rintro Z hZ ⟨t, ht, hZt⟩
  have hU := (LoopFacts.side_mem hUV).1
  have hW := (LoopFacts.side_mem hVW).2
  have h₁ := (LoopFacts.side_mem ht).1
  have h₂ := (LoopFacts.side_mem ht).2
  have hb : Between t.1 Z t.2 := by
    rcases hZt with e | e | hb
    · exact absurd (e ▸ hZ) (hon _ h₁)
    · exact absurd (e ▸ hZ) (hon _ h₂)
    · exact hb
  obtain ⟨M, hUM, hWM⟩ := Postulate1 U W hT.ne₂₃
  have hZM : OnLine Z M := on_line_of_between_ends hZ hUM hWM
  obtain ⟨N, h₁N, h₂N⟩ := Postulate1 t.1 t.2 (h.2.2.1 t ht)
  have hZN : OnLine Z N := on_line_of_between_ends hb h₁N h₂N
  have hcorner : ∀ C ∈ ps, ¬ Between t.1 C t.2 := fun C hC hbC => by
    rcases corner_on_side h hC ht (Or.inr (Or.inr hbC)) with e | e
    · exact ne_of_between hbC e.symm
    · exact ne_of_between (between_symm hbC) e.symm
  have hcorner' : ∀ C ∈ ps, ¬ Between t.2 C t.1 := fun C hC hbC =>
    hcorner C hC (between_symm hbC)
  have hon' : ∀ C ∈ ps, ¬ Between W C U := fun C hC hbC => hon C hC (between_symm hbC)
  by_cases hNM : N = M
  · /- Along UW: U and W are the ends of the side, and the loop closes after three corners. -/
    subst hNM
    have hUe : U = t.1 ∨ U = t.2 := by
      rcases OnRay.cases_of_between hb h₁N h₂N hUM (ne_of_between hZ) with hr | hr
      · exact Or.inl (ray_end hcorner hb hZ hU hon h₁ hr)
      · exact Or.inr (ray_end hcorner' (between_symm hb) hZ hU hon h₂ hr)
    have hWe : W = t.1 ∨ W = t.2 := by
      rcases OnRay.cases_of_between hb h₁N h₂N hWM (ne_of_between (between_symm hZ)) with
        hr | hr
      · exact Or.inl (ray_end hcorner hb (between_symm hZ) hW hon' h₁ hr)
      · exact Or.inr (ray_end hcorner' (between_symm hb) (between_symm hZ) hW hon' h₂ hr)
    have hUW : U ≠ W := hT.ne₂₃
    rcases hUe with e₁ | e₁ <;> rcases hWe with e₂ | e₂
    · exact hUW (e₁.trans e₂.symm)
    · have he : (U, V) = t := LoopFacts.sides_fst_inj h.2.1 hUV ht e₁
      rw [← he] at e₂
      exact hT.ne₁₃ e₂.symm
    · have hWU : (W, U) ∈ sides ps := by
        have : t = (W, U) := Prod.ext e₂.symm e₁.symm
        rw [← this]
        exact ht
      have := three_cycle h hUV hVW hWU
      omega
    · exact hUW (e₁.trans e₂.symm)
  · /- Across UW: a point of the side a little way from Z towards V's side is inside. -/
    have hVM : ¬ OnLine V M := hT.bca.off_line hUM hWM
    have hoff {P : Point} (hPN : OnLine P N) (hPZ : P ≠ Z) : ¬ OnLine P M := fun hPM =>
      hNM (line_unique hPZ hPN hZN hPM hZM)
    have h₁M := hoff h₁N (ne_of_between hb)
    have h₂M := hoff h₂N (ne_of_between (between_symm hb))
    obtain ⟨s, hs, hsV, hsZ⟩ : ∃ s : Point, (s = t.1 ∨ s = t.2) ∧ SameSide s V M ∧
        ∀ Y : Point, Between Z Y s → Between t.1 Y t.2 := by
      rcases same_side_or h₁M h₂M hVM (pasch3 hb hZM) with hs | hs
      · exact ⟨t.1, Or.inl rfl, hs, fun Y hY => between_of_between_left hb (between_symm hY)⟩
      · exact ⟨t.2, Or.inr rfl, hs, fun Y hY =>
          between_symm (between_of_between_left (between_symm hb) (between_symm hY))⟩
    obtain ⟨LU, hVLU, hULU⟩ := Postulate1 V U hT.ne₁₂
    obtain ⟨LW, hVLW, hWLW⟩ := Postulate1 V W hT.ne₁₃
    have hZLU : ¬ OnLine Z LU := fun hZL =>
      hVM (line_unique (ne_of_between hZ).symm hZL hULU hZM hUM ▸ hVLU)
    have hZLW : ¬ OnLine Z LW := fun hZL =>
      hVM (line_unique (ne_of_between (between_symm hZ)).symm hZL hWLW hZM hWM ▸ hVLW)
    have hconds : ∀ p ∈ [(W, LU), (U, LW)], SameSide Z p.1 p.2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨pasch2 hZ hULU hZLU, pasch2 (between_symm hZ) hWLW hZLW⟩
    have hsM : ¬ OnLine s M := not_on_line_of_same_side hsV
    have hZs : Z ≠ s := fun e => hsM (e ▸ hZM)
    obtain ⟨Z', hZZ's, hZ'c⟩ := Avoid.shorten_sides hZs _ hconds
    have hZ'M : ¬ OnLine Z' M := fun hZ'M => hsM (on_line_of_between hZZ's hZM hZ'M)
    have hZ'V : SameSide Z' V M :=
      same_side_trans (same_side_symm (pasch2 hZZ's hZM hZ'M)) hsV
    have hZ'in : InsideTriangle Z' V U W :=
      ⟨SameSideOf.of_line hT.ne₂₃ hUM hWM hZ'V,
        SameSideOf.of_line hT.ne₁₃.symm hWLW hVLW (hZ'c (U, LW) (by simp)),
        SameSideOf.of_line hT.ne₁₂ hVLU hULU (hZ'c (W, LU) (by simp))⟩
    exact hclean Z' hZ'in ⟨t, ht, Or.inr (Or.inr (hsZ Z' hZZ's))⟩

/-! ## Inside, near the extreme corner -/

/-- The neighbours of a corner with every other corner strictly on one side of a straight line
through it make a triangle with it: were they on one straight line with it, it would lie
between them (`LoopFacts.straight_of_collinear`), and they on opposite sides. -/
theorem neighbours_triangle {ps : List Point} (h : SimpleLoop ps) {U V W : Point} {L : Line}
    (hUV : (U, V) ∈ sides ps) (hVW : (V, W) ∈ sides ps) (hVL : OnLine V L)
    (hUW : SameSide U W L) : Triangle V U W := by
  rintro ⟨M, hVM, hUM, hWM⟩
  have hne₁ := h.2.2.1 _ hUV
  have hne₂ := h.2.2.1 _ hVW
  have hst : (U, V) ≠ (V, W) := fun e => hne₁ (Prod.mk.inj e).1
  have hb := LoopFacts.straight_of_collinear (Parity.side_meet h hUV hVW hst) hne₁ hne₂
    ⟨M, hUM, hVM, hWM⟩
  exact pasch3 hb hVL hUW

/-- With every corner but V strictly across L from E, and V on L, no point of a side is on
E's side of L. -/
theorem side_not_far {ps : List Point} (h : SimpleLoop ps) {V E : Point} {L : Line}
    (hVL : OnLine V L) (hext : ∀ C ∈ ps, C ≠ V → OppositeSides C E L)
    {t : Point × Point} (ht : t ∈ sides ps) {Y : Point} (hY : OnFiniteLine Y t.1 t.2) :
    ¬ SameSide Y E L := by
  have corner {C : Point} (hC : C ∈ ps) : ¬ SameSide C E L := by
    by_cases hCV : C = V
    · rw [hCV]
      exact fun hs => not_on_line_of_same_side hs hVL
    · exact (hext C hC hCV).2.2
  have h₁ := (LoopFacts.side_mem ht).1
  have h₂ := (LoopFacts.side_mem ht).2
  rcases hY with e | e | hb
  · exact e ▸ corner h₁
  · exact e ▸ corner h₂
  intro hYE
  have hYL : ¬ OnLine Y L := not_on_line_of_same_side hYE
  by_cases h1V : t.1 = V
  · have h2V : t.2 ≠ V := fun e => h.2.2.1 t ht (h1V.trans e.symm)
    exact (hext _ h₂ h2V).2.2
      (same_side_trans (pasch2 hb (h1V ▸ hVL) hYL) hYE)
  by_cases h2V : t.2 = V
  · exact (hext _ h₁ h1V).2.2
      (same_side_trans (pasch2 (between_symm hb) (h2V ▸ hVL) hYL) hYE)
  have o₁ := hext _ h₁ h1V
  have o₂ := hext _ h₂ h2V
  have h12 : SameSide t.1 t.2 L := same_side_of_opposite_sides ⟨o₁.2.1, o₁.1,
    fun s => o₁.2.2 (same_side_symm s)⟩ ⟨o₂.2.1, o₂.1, fun s => o₂.2.2 (same_side_symm s)⟩
  exact o₁.2.2 (same_side_trans (same_side_symm (pasch1 hb h12)) hYE)

/-- **Inside, near the extreme corner.** Let V be a corner with every other corner strictly
across a straight line L through it from E; U and W its neighbours, U' on VU and W' on VW, with
no side meeting the inside of the triangle VU'W'. Then every point of that triangle, within or
on it, off the boundary, is inside the loop. A finite straight line from a point Z₁ inside the
triangle crosses VU at one point M to a point Z₂ just across it, where a ray towards E's side
of L meets no side, so that Z₂ is outside (`inside_flip`); and the triangle joins Z₁ to the
point (`inside_of_segment`). -/
theorem inside_near {ps : List Point} (h : SimpleLoop ps) {U V W U' W' E : Point} {L : Line}
    (hUV : (U, V) ∈ sides ps) (hVW : (V, W) ∈ sides ps) (hVL : OnLine V L)
    (hext : ∀ C ∈ ps, C ≠ V → OppositeSides C E L)
    (hU' : U' = U ∨ Between V U' U) (hW' : W' = W ∨ Between V W' W) (hT : Triangle V U' W')
    (hclean : ∀ Z : Point, InsideTriangle Z V U' W' → ¬ loopBoundary ps Z)
    {X : Point} (hXb : ¬ loopBoundary ps X) (hX : OnOrInsideTriangle X V U' W') :
    loopInside ps X := by
  have hV : V ∈ ps := (LoopFacts.side_mem hVW).1
  have hU : U ∈ ps := (LoopFacts.side_mem hUV).1
  have hW : W ∈ ps := (LoopFacts.side_mem hVW).2
  have hUVne : U ≠ V := h.2.2.1 _ hUV
  have hVWne : V ≠ W := h.2.2.1 _ hVW
  have hUE := hext U hU hUVne
  have hWE := hext W hW hVWne.symm
  have hUW : SameSide U W L := same_side_of_opposite_sides ⟨hUE.2.1, hUE.1,
    fun s => hUE.2.2 (same_side_symm s)⟩ ⟨hWE.2.1, hWE.1, fun s => hWE.2.2 (same_side_symm s)⟩
  have hVUW := neighbours_triangle h hUV hVW hVL hUW
  obtain ⟨LU, hVLU, hULU⟩ := Postulate1 V U hUVne.symm
  have hU'LU := onLine_sub hU' hVLU hULU
  have hWLU : ¬ OnLine W LU := hVUW.off_line hVLU hULU
  have hW'W : SameSide W' W LU := by
    rcases hW' with rfl | hb
    · exact same_side_refl hWLU
    · refine pasch2 hb hVLU fun hW'LU => hWLU ?_
      exact on_line_of_between hb hVLU hW'LU
  /- The conditions at V, keeping off the sides that miss V. -/
  obtain ⟨hs, hs1, hs2⟩ := conditions h hV
  have hsV := conditions_self hs1
  have off_sides {Y : Point} (hY1 : ¬ OnLine Y LU) (hY2 : ¬ SameSide Y W LU)
      (hY3 : ∀ p ∈ hs, SameSide Y p.1 p.2) : ¬ loopBoundary ps Y := by
    rintro ⟨t, ht, hYt⟩
    by_cases hVt : V ≠ t.1 ∧ V ≠ t.2
    · exact hs2 t ht hVt.1 hVt.2 Y hY3 hYt
    have hVt' : V = t.1 ∨ V = t.2 := by
      by_cases h1 : V = t.1
      · exact Or.inl h1
      · exact Or.inr (Classical.byContradiction fun h2 => hVt ⟨h1, h2⟩)
    rcases side_at h.2.1 hUV hVW ht hVt' with rfl | rfl
    · exact hY1 (LoopFacts.onFiniteLine_onLine hYt hULU hVLU)
    · rcases hYt with e | e | hb
      · exact hY1 (e ▸ hVLU)
      · exact hY2 (e ▸ same_side_refl hWLU)
      · exact hY2 (pasch2 hb hVLU hY1)
  /- M, strictly within VU', near V. -/
  obtain ⟨M, hVMU', hMs⟩ := Avoid.shorten_sides hT.ne₁₂ hs hsV
  have hVMU : Between V M U := by
    rcases hU' with rfl | hb
    · exact hVMU'
    · exact between_of_between_left hb hVMU'
  have hMLU : OnLine M LU := on_line_of_between_ends hVMU hVLU hULU
  have hMps : M ∉ ps := fun hM => by
    rcases corner_on_side h hM hUV (Or.inr (Or.inr (between_symm hVMU))) with e | e
    · exact ne_of_between (between_symm hVMU) e.symm
    · exact ne_of_between hVMU e.symm
  have hML : ¬ OnLine M L := fun hML =>
    hUE.1 (line_unique (ne_of_between hVMU).symm hML hVL hMLU hVLU ▸ hULU)
  have hMU : SameSide M U L := pasch2 hVMU hVL hML
  /- Z₁ inside the triangle, off the straight lines from X and from M to the corners. -/
  obtain ⟨Z₁, hZ₁in, hZ₁a⟩ := triangle_point_avoiding hT
    (CoverFacts.joins X ps ++ CoverFacts.joins M ps)
  have hZ₁b := hclean Z₁ hZ₁in
  have hZ₁W' : SameSide Z₁ W' LU := hZ₁in.2.2.sameSide hVLU hU'LU
  have hZ₁LU : ¬ OnLine Z₁ LU := not_on_line_of_same_side hZ₁W'
  have hZ₁W : SameSide Z₁ W LU := same_side_trans (same_side_symm hZ₁W') hW'W
  have hZ₁M : Z₁ ≠ M := fun e => hZ₁LU (e ▸ hMLU)
  /- Z₂ just across VU from Z₁, through M. -/
  obtain ⟨Y', hZ₁MY'⟩ := produce hZ₁M
  have hMc : ∀ p ∈ (U, L) :: hs, SameSide M p.1 p.2 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hMU
    · exact hMs p hp
  obtain ⟨Z₂, hMZ₂Y', hZ₂c⟩ :=
    Avoid.shorten_sides (ne_of_between (between_symm hZ₁MY')).symm _ hMc
  have hZ₁MZ₂ : Between Z₁ M Z₂ := between_cut hZ₁MY' hMZ₂Y'
  have hZ₂U : SameSide Z₂ U L := hZ₂c (U, L) List.mem_cons_self
  have hZ₂s : ∀ p ∈ hs, SameSide Z₂ p.1 p.2 := fun p hp => hZ₂c p (List.mem_cons_of_mem _ hp)
  /- Beyond M, a point is across VU from W. -/
  have far {Y : Point} (hY : Between Z₁ M Y) : ¬ OnLine Y LU ∧ ¬ SameSide Y W LU := by
    have hYLU : ¬ OnLine Y LU := fun hYLU =>
      hZ₁LU (on_line_of_between (between_symm hY) hYLU hMLU)
    exact ⟨hYLU, fun hYW => pasch3 hY hMLU
      (same_side_trans (same_side_symm hZ₁W) (same_side_symm hYW))⟩
  obtain ⟨hZ₂LU, hZ₂W⟩ := far hZ₁MZ₂
  have hZ₂b : ¬ loopBoundary ps Z₂ := off_sides hZ₂LU hZ₂W hZ₂s
  /- The finite straight line Z₁Z₂ meets the boundary only at M, on VU. -/
  obtain ⟨ℓ, hZ₁ℓ, hMℓ⟩ := Postulate1 Z₁ M hZ₁M
  have hZ₂ℓ : OnLine Z₂ ℓ := on_line_of_between hZ₁MZ₂ hZ₁ℓ hMℓ
  have hoffℓ : ∀ C ∈ ps, ¬ OnLine C ℓ :=
    CoverFacts.joins_off (fun K hK => hZ₁a K (List.mem_append_right _ hK)) hMps hMℓ hZ₁ℓ
  have hMclosed : OnOrInsideTriangle M V U' W' := Or.inr (Or.inl hVMU')
  have atM {t : Point × Point} (ht : t ∈ sides ps) (hMt : OnFiniteLine M t.1 t.2) :
      t = (U, V) := by
    by_cases hVt : V ≠ t.1 ∧ V ≠ t.2
    · exact absurd hMt (hs2 t ht hVt.1 hVt.2 M hMs)
    have hVt' : V = t.1 ∨ V = t.2 := by
      by_cases h1 : V = t.1
      · exact Or.inl h1
      · exact Or.inr (Classical.byContradiction fun h2 => hVt ⟨h1, h2⟩)
    rcases side_at h.2.1 hUV hVW ht hVt' with e | e
    · exact e
    · exfalso
      obtain ⟨LW, hVLW, hWLW⟩ := Postulate1 V W hVWne
      rw [e] at hMt
      have hMLW := LoopFacts.onFiniteLine_onLine hMt hVLW hWLW
      exact hWLU (line_unique (ne_of_between hVMU).symm hMLW hVLW hMLU hVLU ▸ hWLW)
  have hflip : loopInside ps Z₁ ↔ ¬ loopInside ps Z₂ := by
    refine CoverFacts.inside_flip h hUV hZ₁MZ₂ (between_symm hVMU) hZ₁ℓ hZ₂ℓ hoffℓ ?_
    intro Y hY t ht hYt
    rcases (Parity.onFiniteLine_split hZ₁MZ₂).mp hY with hY | hY
    · rcases hY with rfl | rfl | hb
      · exact absurd ⟨t, ht, hYt⟩ hZ₁b
      · exact ⟨rfl, atM ht hYt⟩
      · exact absurd ⟨t, ht, hYt⟩
          (hclean Y (Ext.between_triangle_open hT hMclosed hZ₁in (between_symm hb)))
    · rcases hY with rfl | rfl | hb
      · exact ⟨rfl, atM ht hYt⟩
      · exact absurd ⟨t, ht, hYt⟩ hZ₂b
      · obtain ⟨h1, h2⟩ := far (between_cut hZ₁MZ₂ hb)
        exact absurd ⟨t, ht, hYt⟩ (off_sides h1 h2 (conds_between hMs hZ₂s hb))
  /- Z₂ is outside: a ray from it towards E's side of L, near V across VU from W, meets no
  side. -/
  obtain ⟨P, hWVP⟩ := produce hVWne.symm
  have hEL : ¬ OnLine E L := hUE.2.1
  have hPL : ¬ OnLine P L := fun hPL => hWE.1 (on_line_of_between (between_symm hWVP) hPL hVL)
  have hPE : SameSide P E L := by
    have hWP : OppositeSides W P L := ⟨hWE.1, hPL, pasch3 hWVP hVL⟩
    exact same_side_symm (same_side_of_opposite_sides hWE hWP)
  have hPLU : ¬ OnLine P LU := fun hPLU => hWLU (on_line_of_between (between_symm hWVP) hPLU hVLU)
  have hPW : ¬ SameSide P W LU := fun hs => pasch3 hWVP hVLU (same_side_symm hs)
  obtain ⟨P₀, hVP₀P, hP₀s⟩ := Avoid.shorten_sides (ne_of_between (between_symm hWVP)).symm hs hsV
  have hP₀L : ¬ OnLine P₀ L := fun hP₀L => hPL (on_line_of_between hVP₀P hVL hP₀L)
  have hP₀E : SameSide P₀ E L := same_side_trans (same_side_symm (pasch2 hVP₀P hVL hP₀L)) hPE
  have hP₀LU : ¬ OnLine P₀ LU := fun hP₀LU => hPLU (on_line_of_between hVP₀P hVLU hP₀LU)
  have hP₀W : ¬ SameSide P₀ W LU := fun hs =>
    hPW (same_side_trans (pasch2 hVP₀P hVLU hP₀LU) hs)
  have hP₀c : ∀ p ∈ (E, L) :: (P₀, LU) :: hs, SameSide P₀ p.1 p.2 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hP₀E
    rcases List.mem_cons.mp hp with rfl | hp
    · exact same_side_refl hP₀LU
    · exact hP₀s p hp
  obtain ⟨A, B, C, hP₀in, hall⟩ := small_triangle _ hP₀c
  obtain ⟨P₁, hP₁in, hP₁a⟩ :=
    triangle_point_avoiding hP₀in.1.symm.triangle.cab (CoverFacts.joins Z₂ ps)
  have hP₁c := hall P₁ (Or.inl hP₁in)
  have hP₁E : SameSide P₁ E L := hP₁c (E, L) List.mem_cons_self
  have hP₁P₀ : SameSide P₁ P₀ LU := hP₁c (P₀, LU) (List.mem_cons_of_mem _ List.mem_cons_self)
  have hP₁s : ∀ p ∈ hs, SameSide P₁ p.1 p.2 := fun p hp =>
    hP₁c p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
  have hZ₂P₀ : SameSide Z₂ P₀ LU :=
    ((same_side_or hZ₂LU hWLU hP₀LU hZ₂W).resolve_right fun hs => hP₀W (same_side_symm hs))
  have hUE' : ¬ SameSide U E L := hUE.2.2
  have hZ₂P₁ : Z₂ ≠ P₁ := fun e => hUE' (same_side_trans hZ₂U (by rw [e]; exact hP₁E))
  have hZ₂ps : Z₂ ∉ ps := fun hm => hZ₂b (OutlineFacts.vertex_boundary hm)
  obtain ⟨ℓ₂, hZ₂ℓ₂, hP₁ℓ₂⟩ := Postulate1 Z₂ P₁ hZ₂P₁
  have hgood : GoodRay ps Z₂ P₁ := CoverFacts.goodRay_of_line hZ₂P₁ hZ₂ℓ₂ hP₁ℓ₂
    (CoverFacts.joins_off hP₁a hZ₂ps hZ₂ℓ₂ hP₁ℓ₂)
  have hcount : crossingCount ps Z₂ P₁ = 0 := by
    refine LoopFacts.crossingCount_eq_zero fun t ht ⟨Y, hYray, hYt⟩ => ?_
    have hYt' : OnFiniteLine Y t.1 t.2 := Or.inr (Or.inr hYt)
    have hYℓ₂ : OnLine Y ℓ₂ := hYray.onLine hZ₂ℓ₂ hP₁ℓ₂
    have near_seg (hY : Y = P₁ ∨ Between Z₂ Y P₁) : False := by
      have hYc : (∀ p ∈ hs, SameSide Y p.1 p.2) ∧ SameSide Y P₀ LU := by
        rcases hY with rfl | hb
        · exact ⟨hP₁s, hP₁P₀⟩
        · exact ⟨conds_between hZ₂s hP₁s hb, Avoid.same_side_between hb hZ₂P₀ hP₁P₀⟩
      exact off_sides (not_on_line_of_same_side hYc.2)
        (fun hs => hP₀W (same_side_trans hYc.2 hs)) hYc.1 ⟨t, ht, hYt'⟩
    by_cases hYP : Y = P₁
    · exact near_seg (Or.inl hYP)
    rcases LoopFacts.order_from hZ₂ℓ₂ hYℓ₂ hP₁ℓ₂ hYray.2.1.symm hZ₂P₁ hYP hYray.2.2.2 with
      hb | hb
    · exact near_seg (Or.inr hb)
    · /- Beyond P₁ the ray is on E's side of L, where no side reaches. -/
      refine side_not_far h hVL hext ht hYt' ?_
      have hYL : ¬ OnLine Y L := fun hYL =>
        hUE' (same_side_trans hZ₂U (same_side_trans (pasch2 (between_symm hb) hYL
          (not_on_line_of_same_side hP₁E)) hP₁E))
      refine Classical.byContradiction fun hYE => ?_
      have hYU : SameSide Y U L :=
        (same_side_or hYL hEL hUE.1 hYE).resolve_right fun hs => hUE' (same_side_symm hs)
      exact hUE' (same_side_trans (Avoid.same_side_between hb hZ₂U hYU) hP₁E)
  have hZ₂out : ¬ loopInside ps Z₂ := fun hin => by
    rw [loop_inside_iff h hZ₂b hgood, hcount] at hin
    exact absurd hin (by decide)
  have hZ₁i : loopInside ps Z₁ := hflip.mpr hZ₂out
  /- X is joined to Z₁ inside the triangle. -/
  have hXps : X ∉ ps := fun hm => hXb (OutlineFacts.vertex_boundary hm)
  have hXZ₁ : X ≠ Z₁ := by
    intro e
    have hspec := Classical.choose_spec (collinear_of_two X V)
    exact hZ₁a _ (List.mem_append_left _ (List.mem_map_of_mem (f := fun V =>
      Classical.choose (collinear_of_two X V)) hV)) (e ▸ hspec.1)
  obtain ⟨ℓX, hXℓX, hZ₁ℓX⟩ := Postulate1 X Z₁ hXZ₁
  refine (CoverFacts.inside_of_segment h hXZ₁ hXℓX hZ₁ℓX
    (CoverFacts.joins_off (fun K hK => hZ₁a K (List.mem_append_left _ hK)) hXps hXℓX hZ₁ℓX)
    hXb hZ₁b fun Y hY => hclean Y (Ext.between_triangle_open hT hX hZ₁in hY)).mpr hZ₁i

/-! ## An interior diagonal -/

/-- **Two corners that are not neighbours.** Read from A, a loop of distinct corners in which
neither AB nor BA is a side runs from A through at least one corner to B, and on through at
least one more. -/
theorem diagonal_rotate {ps : List Point} (h : ps.Nodup) {A B : Point} (hA : A ∈ ps)
    (hB : B ∈ ps) (hAB : A ≠ B) (h₁ : (A, B) ∉ sides ps) (h₂ : (B, A) ∉ sides ps) :
    ∃ (n : Nat) (us vs : List Point),
      ps.rotateLeft n = A :: (us ++ B :: vs) ∧ us ≠ [] ∧ vs ≠ [] := by
  obtain ⟨xs, ys, rfl⟩ := List.append_of_mem hA
  have hB' : B ∈ ys ++ xs := by
    rcases List.mem_append.mp hB with hB | hB
    · exact List.mem_append_right _ hB
    · rcases List.mem_cons.mp hB with e | hB
      · exact absurd e.symm hAB
      · exact List.mem_append_left _ hB
  obtain ⟨us, vs, huv⟩ := List.append_of_mem hB'
  have hlen : 2 ≤ (xs ++ A :: ys).length := by
    have : 0 < (ys ++ xs).length := List.length_pos_of_mem hB'
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  have hrot : (xs ++ A :: ys).rotateLeft xs.length = A :: (us ++ B :: vs) := by
    rw [rotate_split rfl (List.cons_ne_nil _ _) hlen, List.cons_append, huv]
  /- The sides read from A are the loop's sides. -/
  have hmem {s : Point × Point} (hs : s ∈ sides (A :: (us ++ B :: vs))) :
      s ∈ sides (xs ++ A :: ys) := by
    have hperm := LoopFacts.sides_rotate_perm xs (A :: ys)
    rw [List.cons_append, huv] at hperm
    exact hperm.mem_iff.mpr hs
  refine ⟨xs.length, us, vs, hrot, ?_, ?_⟩
  · rintro rfl
    exact h₁ (hmem (by simp [sides, segments]))
  · rintro rfl
    refine h₂ (hmem ?_)
    have he : A :: (us ++ [B]) ++ [A] = (A :: us) ++ [B, A] := by simp
    show (B, A) ∈ segments (A :: (us ++ [B]) ++ [A])
    rw [he]
    exact Ext.closing_segment A B (A :: us)

/-- **A simple loop with four corners or more has an interior diagonal.** Take an extreme corner
V, with every other corner strictly across a straight line through it (`extreme_corner`), and
its neighbours U and W. If no corner is inside the triangle VUW or strictly between U and W, the
finite straight line UW, apart from its ends, is inside (`ear_edge`, `inside_near`): an ear.
Otherwise a corner X strictly within a straight line U'W' across V, with no corner inside the
triangle VU'W' (`nearest`, or a corner on UW itself), is joined to V by a finite straight line
inside that triangle, which no side meets (`clean`). -/
theorem diagonal_exists {ps : List Point} (h : SimpleLoop ps) (hn : 4 ≤ ps.length) :
    ∃ A ∈ ps, ∃ B ∈ ps, A ≠ B ∧ (A, B) ∉ sides ps ∧ (B, A) ∉ sides ps ∧
      ∀ X : Point, Between A X B → loopInside ps X := by
  obtain ⟨V, hV, L, E, hVL, -, hext⟩ := extreme_corner h
  obtain ⟨W, hVW⟩ := outgoing_side hV
  obtain ⟨U, hUV⟩ := LoopFacts.incoming_side hV
  have hU : U ∈ ps := (LoopFacts.side_mem hUV).1
  have hW : W ∈ ps := (LoopFacts.side_mem hVW).2
  have hUVne : U ≠ V := h.2.2.1 _ hUV
  have hVWne : V ≠ W := h.2.2.1 _ hVW
  have hUE := hext U hU hUVne
  have hWE := hext W hW hVWne.symm
  have hUW : SameSide U W L := same_side_of_opposite_sides ⟨hUE.2.1, hUE.1,
    fun s => hUE.2.2 (same_side_symm s)⟩ ⟨hWE.2.1, hWE.1, fun s => hWE.2.2 (same_side_symm s)⟩
  have hT := neighbours_triangle h hUV hVW hVL hUW
  by_cases hear : (∀ C ∈ ps, ¬ InsideTriangle C V U W) ∧ ∀ C ∈ ps, ¬ Between U C W
  · /- An ear: the diagonal UW. -/
    refine ⟨U, hU, W, hW, hT.ne₂₃, fun hs => ?_, fun hs => ?_, fun X hX => ?_⟩
    · have he := LoopFacts.sides_fst_inj h.2.1 hs hUV rfl
      exact hVWne (Prod.mk.inj he).2.symm
    · have := three_cycle h hUV hVW hs
      omega
    · exact inside_near h hUV hVW hVL hext (Or.inl rfl) (Or.inl rfl) hT
        (clean h hUV hVW (Or.inl rfl) (Or.inl rfl) hT hear.1)
        (ear_edge h hn hUV hVW hT hear.1 hear.2 X hX) (Or.inr (Or.inr (Or.inl hX)))
  /- A corner X' strictly within U'W', across V, with no corner inside the triangle VU'W'. -/
  obtain ⟨U', W', X', hU', hW', hX', hb, hT', hno⟩ : ∃ U' W' X' : Point,
      (U' = U ∨ Between V U' U) ∧ (W' = W ∨ Between V W' W) ∧ X' ∈ ps ∧ Between U' X' W' ∧
        Triangle V U' W' ∧ ∀ C ∈ ps, ¬ InsideTriangle C V U' W' := by
    by_cases hin : ∃ C ∈ ps, InsideTriangle C V U W
    · obtain ⟨C, hC, hCin⟩ := hin
      obtain ⟨U', W', X', hU', hW', hX', hb, hno⟩ := nearest _ hT (Nat.le_refl _) hC hCin
      exact ⟨U', W', X', Or.inr hU', Or.inr hW', hX', hb,
        (Avoid.corner_triangle hT hU' hW').1, hno⟩
    · have hin' : ∀ C ∈ ps, ¬ InsideTriangle C V U W := fun C hC hCin => hin ⟨C, hC, hCin⟩
      obtain ⟨C, hC, hbC⟩ : ∃ C ∈ ps, Between U C W := Classical.byContradiction fun hno =>
        hear ⟨hin', fun C hC hbC => hno ⟨C, hC, hbC⟩⟩
      exact ⟨U, W, C, Or.inl rfl, Or.inl rfl, hC, hbC, hT, hin'⟩
  have hclean := clean h hUV hVW hU' hW' hT' hno
  /- X' is neither V nor a neighbour of V: it is off both straight lines VU' and VW'. -/
  have hX'V : V ≠ X' := fun e => hT'.bac (e ▸ collinear_of_between hb)
  have off_side {Z Z' : Point} (hZ' : Z' = Z ∨ Between V Z' Z) (hVZ : V ≠ Z)
      (hcol : ∀ {M : Line}, OnLine V M → OnLine Z' M → OnLine X' M → False) : X' ≠ Z := by
    intro e
    obtain ⟨M, hVM, hZM⟩ := Postulate1 V Z hVZ
    exact hcol hVM (onLine_sub hZ' hVM hZM) (e ▸ hZM)
  have hX'W : X' ≠ W := off_side hW' hVWne fun {M} hVM hW'M hX'M =>
    hT' ⟨M, hVM, on_line_of_between (between_symm hb) hW'M hX'M, hW'M⟩
  have hX'U : X' ≠ U := off_side hU' hUVne.symm fun {M} hVM hU'M hX'M =>
    hT' ⟨M, hVM, hU'M, on_line_of_between hb hU'M hX'M⟩
  refine ⟨V, hV, X', hX', hX'V, fun hs => ?_, fun hs => ?_, fun X hX => ?_⟩
  · exact hX'W (Prod.mk.inj (LoopFacts.sides_fst_inj h.2.1 hs hVW rfl)).2
  · exact hX'U (Prod.mk.inj (sides_snd_inj h.2.1 hs hUV rfl)).1
  · have hXin : InsideTriangle X V U' W' := Avoid.inside_of_between hT' hb hX
    exact inside_near h hUV hVW hVL hext hU' hW' hT' hclean (hclean X hXin) (Or.inl hXin)

/-! ## Two chains and two pieces

For `simple_diagonal_partition`. The loop `A :: (us ++ B :: vs)` is read as two chains, from A
through `us` to B and from B through `vs` back to A. The first piece is the first chain closed
by the side BA, `A :: (us ++ [B])`; the second is the second chain closed by AB,
`B :: (vs ++ [A])`. Read from B, the loop has the chains and the pieces exchanged
(`rotate_config`), so what is proved of the first chain and the second piece holds of the
second chain and the first piece. -/

/-- A point of a chain: on one of its finite straight lines. -/
def OnChain (cs : List Point) (X : Point) : Prop := ∃ s ∈ segments cs, OnFiniteLine X s.1 s.2

section Split

variable {A B : Point} {us vs : List Point}

/-- The loop's sides are the two chains'. -/
theorem split_sides (A B : Point) (us vs : List Point) :
    sides (A :: (us ++ B :: vs)) = segments (A :: us ++ [B]) ++ segments (B :: vs ++ [A]) := by
  show segments ((A :: (us ++ B :: vs)) ++ [A]) = _
  rw [show (A :: (us ++ B :: vs)) ++ [A] = (A :: us) ++ B :: (vs ++ [A]) by simp,
    segments_join]
  rfl

/-- A piece's sides are its chain's and the closing side. -/
theorem piece_sides (a b : Point) (l : List Point) :
    sides (a :: (l ++ [b])) = segments (a :: l ++ [b]) ++ [(b, a)] := by
  show segments ((a :: (l ++ [b])) ++ [a]) = _
  rw [show (a :: (l ++ [b])) ++ [a] = (a :: l) ++ b :: [a] by simp, segments_join]
  rfl

/-- The corners of the first piece are corners of the loop. -/
theorem piece_mem₁ {V : Point} (hV : V ∈ A :: (us ++ [B])) : V ∈ A :: (us ++ B :: vs) :=
  (show (A :: (us ++ [B])).Sublist (A :: (us ++ B :: vs)) by simp).subset hV

/-- The corners of the second piece are corners of the loop. -/
theorem piece_mem₂ {V : Point} (hV : V ∈ B :: (vs ++ [A])) : V ∈ A :: (us ++ B :: vs) := by
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hV ⊢
  rcases hV with e | e | e
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr e))
  · exact Or.inl e

/-- A and B are different corners. -/
theorem ends_ne (h : (A :: (us ++ B :: vs)).Nodup) : A ≠ B := by
  intro e
  rw [List.nodup_cons] at h
  exact h.1 (by rw [e]; simp)

/-- The two chains share only the corners A and B. -/
theorem common_corner (h : (A :: (us ++ B :: vs)).Nodup) {V : Point}
    (h₁ : V ∈ A :: us ++ [B]) (h₂ : V ∈ B :: vs ++ [A]) : V = A ∨ V = B := by
  rw [List.nodup_cons, List.nodup_append] at h
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    at h₁ h₂
  rcases h₁ with e | hu | e
  · exact Or.inl e
  · rcases h₂ with e | hv | e
    · exact Or.inr e
    · exact absurd rfl (h.2.2.2 V hu V (List.mem_cons_of_mem _ hv))
    · exact Or.inl e
  · exact Or.inr e

/-- A side of the first chain is a side of the loop. -/
theorem chain₁_side {s : Point × Point} (hs : s ∈ segments (A :: us ++ [B])) :
    s ∈ sides (A :: (us ++ B :: vs)) := by
  rw [split_sides]
  exact List.mem_append_left _ hs

/-- A side of the second chain is a side of the loop. -/
theorem chain₂_side {s : Point × Point} (hs : s ∈ segments (B :: vs ++ [A])) :
    s ∈ sides (A :: (us ++ B :: vs)) := by
  rw [split_sides]
  exact List.mem_append_right _ hs

/-- **The chains meet only at A and B**: two sides of a simple loop meet only at common ends,
and the chains have only A and B in common. -/
theorem chains_meet (h : SimpleLoop (A :: (us ++ B :: vs))) {s t : Point × Point}
    (hs : s ∈ segments (A :: us ++ [B])) (ht : t ∈ segments (B :: vs ++ [A])) {X : Point}
    (hXs : OnFiniteLine X s.1 s.2) (hXt : OnFiniteLine X t.1 t.2) : X = A ∨ X = B := by
  have hst : s ≠ t := by
    have hnd := LoopFacts.sides_nodup h.2.1
    rw [split_sides, List.nodup_append] at hnd
    exact hnd.2.2 s hs t ht
  obtain ⟨h₁, h₂⟩ := Parity.side_meet h (chain₁_side hs) (chain₂_side ht) hst X hXs hXt
  have e₁ : X ∈ A :: us ++ [B] := by
    rcases h₁ with e | e <;> rw [e]
    · exact (segment_corners hs).1
    · exact (segment_corners hs).2
  have e₂ : X ∈ B :: vs ++ [A] := by
    rcases h₂ with e | e <;> rw [e]
    · exact (segment_corners ht).1
    · exact (segment_corners ht).2
  exact common_corner h.2.1 e₁ e₂

/-- A point of a side and of the diagonal AB is A or B, the diagonal's other points being
inside. -/
theorem side_diagonal (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X)
    {s : Point × Point} (hs : s ∈ sides (A :: (us ++ B :: vs))) {X : Point}
    (hXs : OnFiniteLine X s.1 s.2) (hX : OnFiniteLine X A B) : X = A ∨ X = B := by
  rcases hX with e | e | hb
  · exact Or.inl e
  · exact Or.inr e
  · exact absurd ⟨s, hs, hXs⟩ (hd X hb).1

/-- The loop's boundary is the two chains. -/
theorem boundary_split (X : Point) :
    loopBoundary (A :: (us ++ B :: vs)) X ↔
      OnChain (A :: us ++ [B]) X ∨ OnChain (B :: vs ++ [A]) X := by
  unfold loopBoundary OnChain
  rw [split_sides]
  simp only [List.mem_append]
  constructor
  · rintro ⟨s, hs | hs, hX⟩
    · exact Or.inl ⟨s, hs, hX⟩
    · exact Or.inr ⟨s, hs, hX⟩
  · rintro (⟨s, hs, hX⟩ | ⟨s, hs, hX⟩)
    · exact ⟨s, Or.inl hs, hX⟩
    · exact ⟨s, Or.inr hs, hX⟩

/-- A piece's boundary is its chain and the diagonal. -/
theorem boundary_piece (a b : Point) (l : List Point) (X : Point) :
    loopBoundary (a :: (l ++ [b])) X ↔ OnChain (a :: l ++ [b]) X ∨ OnFiniteLine X a b := by
  unfold loopBoundary OnChain
  rw [piece_sides]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨s, hs | rfl, hX⟩
    · exact Or.inl ⟨s, hs, hX⟩
    · exact Or.inr (LoopFacts.onFiniteLine_comm.mp hX)
  · rintro (⟨s, hs, hX⟩ | hX)
    · exact ⟨s, Or.inl hs, hX⟩
    · exact ⟨(b, a), Or.inr rfl, LoopFacts.onFiniteLine_comm.mp hX⟩

/-- A corner is on the boundary. -/
theorem corner_boundary {ps : List Point} {V : Point} (hV : V ∈ ps) : loopBoundary ps V := by
  obtain ⟨E, hE⟩ := outgoing_side hV
  exact ⟨(V, E), hE, Or.inl rfl⟩

/-- **The first piece is simple.** Its sides are sides of the loop, and the side BA, which
meets a side of the first chain only at A or B: the diagonal's other points are inside the
loop, off every side. -/
theorem piece_simple (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ [])
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) :
    SimpleLoop (A :: (us ++ [B])) := by
  have hA : A ∈ A :: (us ++ B :: vs) := List.mem_cons_self
  have hB : B ∈ A :: (us ++ B :: vs) := by simp
  refine ⟨?_, h.2.1.sublist (by simp), ?_, ?_⟩
  · obtain ⟨u, us', rfl⟩ := List.exists_cons_of_ne_nil hu
    simp
  · intro s hs
    rw [piece_sides] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact h.2.2.1 s (chain₁_side hs)
    · rw [List.mem_singleton.mp hs]
      exact Ne.symm (ends_ne h.2.1)
  · rw [piece_sides, List.pairwise_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · have hpw := h.2.2.2
      rw [split_sides, List.pairwise_append] at hpw
      exact hpw.1
    · intro s hs t ht X hXs hXt
      rw [List.mem_singleton.mp ht] at hXt ⊢
      have hs' := chain₁_side (vs := vs) hs
      rcases side_diagonal hd hs' hXs (LoopFacts.onFiniteLine_comm.mp hXt) with e | e
      · subst e
        exact ⟨corner_on_side h hA hs' hXs, Or.inr rfl⟩
      · subst e
        exact ⟨corner_on_side h hB hs' hXs, Or.inl rfl⟩

/-- **Read from B**, the loop is simple, with every point strictly between B and A inside:
the same configuration, with the chains exchanged. -/
theorem rotate_config (h : SimpleLoop (A :: (us ++ B :: vs)))
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) :
    SimpleLoop (B :: (vs ++ A :: us)) ∧
      ∀ X : Point, Between B X A → loopInside (B :: (vs ++ A :: us)) X := by
  obtain ⟨hs, hb, hg⟩ := loop_rotate (A :: us) (B :: vs) h
  refine ⟨hs, fun X hX => ?_⟩
  have hi := hd X (between_symm hX)
  rcases (hg X).mpr (Or.inr hi) with hb' | hin
  · exact absurd ((hb X).mp hb') hi.1
  · exact hin

/-- The second piece is simple. -/
theorem piece_simple₂ (h : SimpleLoop (A :: (us ++ B :: vs))) (hv : vs ≠ [])
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) :
    SimpleLoop (B :: (vs ++ [A])) :=
  piece_simple (rotate_config h hd).1 hv (rotate_config h hd).2

/-- **A ray crosses the loop as often as the two pieces together, less the diagonal twice.**
The pieces' sides are the loop's and the diagonal, once each way round. -/
theorem count_split (X R : Point) :
    crossingCount (A :: (us ++ B :: vs)) X R % 2 =
      (crossingCount (A :: (us ++ [B])) X R + crossingCount (B :: (vs ++ [A])) X R) % 2 := by
  have hc : RayCrosses X R (B, A) ↔ RayCrosses X R (A, B) :=
    ⟨fun ⟨Y, hY, hb⟩ => ⟨Y, hY, between_symm hb⟩, fun ⟨Y, hY, hb⟩ => ⟨Y, hY, between_symm hb⟩⟩
  unfold crossingCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter, split_sides, piece_sides, piece_sides, List.countP_append,
    List.countP_append, List.countP_append]
  simp only [List.countP_cons, List.countP_nil]
  split <;> split <;> rename_i h₁ h₂ <;> simp only [decide_eq_true_eq] at h₁ h₂
  all_goals first | omega | exact absurd (hc.mp h₁) h₂ | exact absurd (hc.mpr h₂) h₁

/-- **Off the diagonal, inside the loop means inside exactly one piece**: a good ray of the loop
is good for both pieces, and crosses the loop as often as both, less the diagonal twice. -/
theorem inside_xor (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ [])
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) {X : Point}
    (hX : ¬ loopBoundary (A :: (us ++ B :: vs)) X) (hXd : ¬ OnFiniteLine X A B) :
    loopInside (A :: (us ++ B :: vs)) X ↔
      (loopInside (A :: (us ++ [B])) X ↔ ¬ loopInside (B :: (vs ++ [A])) X) := by
  have hP := piece_simple h hu hd
  have hQ := piece_simple₂ h hv hd
  obtain ⟨R, hR⟩ := good_ray_exists h hX
  have hRP : GoodRay (A :: (us ++ [B])) X R := ⟨hR.1, fun V hV => hR.2 V (piece_mem₁ hV)⟩
  have hRQ : GoodRay (B :: (vs ++ [A])) X R := ⟨hR.1, fun V hV => hR.2 V (piece_mem₂ hV)⟩
  have hXP : ¬ loopBoundary (A :: (us ++ [B])) X := by
    rw [boundary_piece]
    rintro (hc | hc)
    · exact hX ((boundary_split X).mpr (Or.inl hc))
    · exact hXd hc
  have hXQ : ¬ loopBoundary (B :: (vs ++ [A])) X := by
    rw [boundary_piece]
    rintro (hc | hc)
    · exact hX ((boundary_split X).mpr (Or.inr hc))
    · exact hXd (LoopFacts.onFiniteLine_comm.mp hc)
  rw [loop_inside_iff h hX hR, loop_inside_iff hP hXP hRP, loop_inside_iff hQ hXQ hRQ]
  have hc := count_split (A := A) (B := B) (us := us) (vs := vs) X R
  generalize crossingCount (A :: (us ++ B :: vs)) X R = a at hc ⊢
  generalize crossingCount (A :: (us ++ [B])) X R = b at hc ⊢
  generalize crossingCount (B :: (vs ++ [A])) X R = c at hc ⊢
  omega

end Split

/-! ## Along a finite straight line off the boundary -/

/-- A point beyond Y' from Y is not on the finite straight line YY'. -/
theorem beyond_off {Y Y' G : Point} (h : Between Y Y' G) : ¬ OnFiniteLine G Y Y' := by
  rintro (e | e | hb)
  · exact ne_of_between_ends h e.symm
  · exact ne_of_between (between_symm h) e
  · exact ne_of_between (between_symm (between_of_between_left h hb)) rfl

/-- **Two finite straight lines that do not meet are kept apart by a straight line**: the first
strictly on one side of it, and every point of that side off the second. If the first is on one
side of the second's straight line, that line serves. Otherwise the second's straight line meets
the first at a point W, beyond an end c of the second; a straight line through c, other than
the second's, that misses the first has W, and so the whole first, on one side, and the second's
other end on the other. -/
theorem sep_segments {Y Y' a b : Point} (hYY' : Y ≠ Y') (hab : a ≠ b)
    (hdis : ∀ Z : Point, OnFiniteLine Z Y Y' → ¬ OnFiniteLine Z a b) :
    ∃ K : Line, ¬ OnLine Y K ∧ SameSide Y' Y K ∧
      ∀ Z : Point, SameSide Z Y K → ¬ OnFiniteLine Z a b := by
  obtain ⟨n, han, hbn⟩ := Postulate1 a b hab
  by_cases h₁ : SameSide Y Y' n
  · refine ⟨n, not_on_line_of_same_side h₁, same_side_symm h₁, fun Z hZ hZab => ?_⟩
    exact not_on_line_of_same_side hZ (LoopFacts.onFiniteLine_onLine hZab han hbn)
  obtain ⟨W, hWn, hW⟩ : ∃ W : Point, OnLine W n ∧ OnFiniteLine W Y Y' := by
    by_cases hY : OnLine Y n
    · exact ⟨Y, hY, Or.inl rfl⟩
    by_cases hY' : OnLine Y' n
    · exact ⟨Y', hY', Or.inr (Or.inl rfl)⟩
    obtain ⟨W, hWn, hb⟩ := OppositeSides.exists_between ⟨hY, hY', h₁⟩
    exact ⟨W, hWn, Or.inr (Or.inr hb)⟩
  have hWab := hdis W hW
  /- The step, with c the end nearer W and e the other. -/
  have key : ∀ c e : Point, OnLine c n → OnLine e n → c ≠ e → OnFiniteLine c a b →
      Between W c e → ∃ K : Line, ¬ OnLine Y K ∧ SameSide Y' Y K ∧
        ∀ Z : Point, SameSide Z Y K → ¬ OnFiniteLine Z c e := by
    intro c e hcn hen hce hc hWce
    /- A straight line through c, other than n, missing the finite straight line YY'. -/
    obtain ⟨K, hcK, hKn, hmiss⟩ : ∃ K : Line, OnLine c K ∧ K ≠ n ∧
        ∀ Z : Point, OnFiniteLine Z Y Y' → ¬ OnLine Z K := by
      by_cases hboth : OnLine Y n ∧ OnLine Y' n
      · /- All on one straight line: any other straight line through c. -/
        obtain ⟨C, hC, -⟩ := exists_off_line hce []
        obtain ⟨K, hcK, hCK⟩ := Postulate1 c C hC.ne₁₃
        refine ⟨K, hcK, fun e' => hC ⟨n, hcn, hen, e' ▸ hCK⟩, fun Z hZ hZK => ?_⟩
        have hZn : OnLine Z n := LoopFacts.onFiniteLine_onLine hZ hboth.1 hboth.2
        have hZc : Z = c := Classical.byContradiction fun hne =>
          hC ⟨n, hcn, hen, line_unique hne hZK hcK hZn hcn ▸ hCK⟩
        exact hdis Z hZ (hZc ▸ hc)
      · /- Through c and a point G beyond Y' on the straight line YY'. -/
        obtain ⟨m, hYm, hY'm⟩ := Postulate1 Y Y' hYY'
        have hmn : m ≠ n := fun e' => hboth ⟨e' ▸ hYm, e' ▸ hY'm⟩
        have hWm : OnLine W m := LoopFacts.onFiniteLine_onLine hW hYm hY'm
        have hcm : ¬ OnLine c m := fun hcm =>
          hmn (line_unique (ne_of_between hWce).symm hcm hWm hcn hWn)
        obtain ⟨G, hYY'G⟩ := produce hYY'
        have hGm : OnLine G m := on_line_of_between hYY'G hYm hY'm
        have hcG : c ≠ G := fun e' => hcm (e' ▸ hGm)
        obtain ⟨K, hcK, hGK⟩ := Postulate1 c G hcG
        have hGn : ¬ OnLine G n := by
          intro hGn
          have hGW : G = W := Classical.byContradiction fun hne =>
            hmn (line_unique hne hGm hWm hGn hWn)
          exact beyond_off hYY'G (hGW ▸ hW)
        refine ⟨K, hcK, fun e' => hGn (e' ▸ hGK), fun Z hZ hZK => ?_⟩
        have hZm := LoopFacts.onFiniteLine_onLine hZ hYm hY'm
        have hZG : Z = G := Classical.byContradiction fun hne =>
          hcm (line_unique hne hZK hGK hZm hGm ▸ hcK)
        exact beyond_off hYY'G (hZG ▸ hZ)
    have hYK : ¬ OnLine Y K := hmiss Y (Or.inl rfl)
    have hY'K : ¬ OnLine Y' K := hmiss Y' (Or.inr (Or.inl rfl))
    have hYY'K : SameSide Y Y' K := Classical.byContradiction fun hn => by
      obtain ⟨Z, hZK, hb⟩ := OppositeSides.exists_between ⟨hYK, hY'K, hn⟩
      exact hmiss Z (Or.inr (Or.inr hb)) hZK
    have hWY : SameSide W Y K := by
      rcases hW with e' | e' | hb
      · rw [e']
        exact same_side_refl hYK
      · rw [e']
        exact same_side_symm hYY'K
      · exact Avoid.same_side_between hb (same_side_refl hYK) (same_side_symm hYY'K)
    have heK : ¬ OnLine e K := fun heK => hKn (line_unique hce hcK heK hcn hen)
    have heY : ¬ SameSide e Y K := fun h' =>
      pasch3 hWce hcK (same_side_trans (same_side_symm hWY) (same_side_symm h'))
    refine ⟨K, hYK, same_side_symm hYY'K, fun Z hZ hZce => ?_⟩
    rcases hZce with rfl | rfl | hb
    · exact not_on_line_of_same_side hZ hcK
    · exact heY hZ
    · exact heY (same_side_trans (pasch2 hb hcK (not_on_line_of_same_side hZ)) hZ)
  have hWa : W ≠ a := fun e' => hWab (Or.inl e')
  have hWb : W ≠ b := fun e' => hWab (Or.inr (Or.inl e'))
  rcases between_cases hWa hab hWb hWn han hbn with h' | h' | h'
  · exact key a b han hbn hab (Or.inl rfl) h'
  · exact absurd (Or.inr (Or.inr h')) hWab
  · obtain ⟨K, h1, h2, h3⟩ := key b a hbn han hab.symm (Or.inr (Or.inl rfl)) h'
    exact ⟨K, h1, h2, fun Z hZ hZab => h3 Z hZ (LoopFacts.onFiniteLine_comm.mp hZab)⟩

/-- **The conditions along a finite straight line off the boundary**: finitely many straight
lines, with both ends of it strictly on one side of each, such that a point on that side of
all of them is on no side. -/
theorem seg_conditions {R : List Point} (hR : SimpleLoop R) {Y Y' : Point}
    (hseg : ∀ Z : Point, OnFiniteLine Z Y Y' → ¬ loopBoundary R Z) :
    ∃ hs : List (Point × Line), (∀ p ∈ hs, SameSide Y p.1 p.2 ∧ SameSide Y' p.1 p.2) ∧
      ∀ Z : Point, (∀ p ∈ hs, SameSide Z p.1 p.2) → ¬ loopBoundary R Z := by
  suffices key : ∀ ts : List (Point × Point), (∀ t ∈ ts, t ∈ sides R) →
      ∃ hs : List (Point × Line), (∀ p ∈ hs, SameSide Y p.1 p.2 ∧ SameSide Y' p.1 p.2) ∧
        ∀ t ∈ ts, ∀ Z : Point, (∀ p ∈ hs, SameSide Z p.1 p.2) → ¬ OnFiniteLine Z t.1 t.2 by
    obtain ⟨hs, h1, h2⟩ := key (sides R) fun _ ht => ht
    exact ⟨hs, h1, fun Z hZ ⟨t, ht, hZt⟩ => h2 t ht Z hZ hZt⟩
  intro ts
  induction ts with
  | nil => exact fun _ => ⟨[], by simp, by simp⟩
  | cons t ts ih =>
    intro hts
    obtain ⟨hs, h1, h2⟩ := ih fun u hu => hts u (List.mem_cons_of_mem _ hu)
    have ht := hts t List.mem_cons_self
    have hne := hR.2.2.1 t ht
    obtain ⟨K, hYK, hY'K, hK⟩ : ∃ K : Line, ¬ OnLine Y K ∧ SameSide Y' Y K ∧
        ∀ Z : Point, SameSide Z Y K → ¬ OnFiniteLine Z t.1 t.2 := by
      by_cases hYY' : Y = Y'
      · subst hYY'
        obtain ⟨L, h₁, h₂⟩ := Postulate1 t.1 t.2 hne
        obtain ⟨C, -, hC⟩ := corner_off hR L
        obtain ⟨K, hK, hKZ⟩ :=
          sep_finite hne h₁ h₂ hC fun hYt => hseg Y (Or.inl rfl) ⟨t, ht, hYt⟩
        exact ⟨K, hK, same_side_refl hK, hKZ⟩
      · exact sep_segments hYY' hne fun Z hZ hZt => hseg Z hZ ⟨t, ht, hZt⟩
    refine ⟨(Y, K) :: hs, ?_, fun u hu Z hZ => ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨same_side_refl hYK, hY'K⟩
      · exact h1 p hp
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact hK Z (hZ _ List.mem_cons_self)
      · exact h2 u hu Z fun p hp => hZ p (List.mem_cons_of_mem _ hp)

/-- **Along a finite straight line off the boundary, inside is constant**, whatever corners its
straight line passes through. Join both ends to a point near one end that keeps the conditions
(`seg_conditions`) and is off the straight lines from either end to the corners. -/
theorem seg_const {R : List Point} (hR : SimpleLoop R) {Y Y' : Point}
    (hseg : ∀ Z : Point, OnFiniteLine Z Y Y' → ¬ loopBoundary R Z) :
    loopInside R Y ↔ loopInside R Y' := by
  obtain ⟨hs, h1, h2⟩ := seg_conditions hR hseg
  obtain ⟨a, b, c, hYin, hall⟩ := small_triangle hs fun p hp => (h1 p hp).1
  obtain ⟨Z, hZin, hZa⟩ := triangle_point_avoiding hYin.1.symm.triangle.cab
    (CoverFacts.joins Y R ++ CoverFacts.joins Y' R)
  have hZ : ∀ p ∈ hs, SameSide Z p.1 p.2 := hall Z (Or.inl hZin)
  obtain ⟨V, hV⟩ : ∃ V : Point, V ∈ R := by
    have hlen := hR.1
    cases R with
    | nil => simp at hlen
    | cons V _ => exact ⟨V, List.mem_cons_self⟩
  /- From each end to Z, a finite straight line meeting no side, its straight line through
  no corner. -/
  have along {X : Point} (hXb : ¬ loopBoundary R X) (hX : ∀ p ∈ hs, SameSide X p.1 p.2)
      (hXa : Avoid (CoverFacts.joins X R) Z) : loopInside R X ↔ loopInside R Z := by
    have hXZ : X ≠ Z := by
      intro e
      have hspec := Classical.choose_spec (collinear_of_two X V)
      exact hXa _ (List.mem_map_of_mem (f := fun V => Classical.choose (collinear_of_two X V))
        hV) (e ▸ hspec.1)
    obtain ⟨ℓ, hXℓ, hZℓ⟩ := Postulate1 X Z hXZ
    have hXR : X ∉ R := fun hm => hXb (corner_boundary hm)
    exact CoverFacts.inside_of_segment hR hXZ hXℓ hZℓ (CoverFacts.joins_off hXa hXR hXℓ hZℓ)
      hXb (h2 Z hZ) fun U hU => h2 U (conds_between hX hZ hU)
  exact (along (hseg Y (Or.inl rfl)) (fun p hp => (h1 p hp).1)
      (fun L hL => hZa L (List.mem_append_left _ hL))).trans
    (along (hseg Y' (Or.inr (Or.inl rfl))) (fun p hp => (h1 p hp).2)
      (fun L hL => hZa L (List.mem_append_right _ hL))).symm

/-- **Along a chain**, a property constant along every finite straight line of points
satisfying G is the same at every corner, when every point of the chain satisfies G. -/
theorem chain_const {f G : Point → Prop}
    (hseg : ∀ Y Y' : Point, (∀ Z : Point, OnFiniteLine Z Y Y' → G Z) → (f Y ↔ f Y')) :
    ∀ (l : List Point) (a : Point),
      (∀ s ∈ segments (a :: l), ∀ Z : Point, OnFiniteLine Z s.1 s.2 → G Z) →
        ∀ x ∈ l, f x ↔ f a
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | b :: l, a, hG, x, hx => by
    have hab : f b ↔ f a := hseg b a fun Z hZ =>
      hG (a, b) List.mem_cons_self Z (LoopFacts.onFiniteLine_comm.mp hZ)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hab
    · exact (chain_const hseg l b (fun s hs => hG s (List.mem_cons_of_mem _ hs)) x hx).trans hab

/-- From a point of a finite straight line to one end, the points are on it. -/
theorem onFinite_sub {p q Y Z : Point} (hY : OnFiniteLine Y p q) (hZ : OnFiniteLine Z Y q) :
    OnFiniteLine Z p q := by
  rcases hY with rfl | rfl | hb
  · exact hZ
  · rcases hZ with e | e | hb'
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inl e)
    · exact absurd rfl (ne_of_between_ends hb')
  · rcases hZ with e | e | hb'
    · rw [e]
      exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (between_symm
        (between_of_between_left (between_symm hb) (between_symm hb'))))

/-- From a point of a finite straight line other than its end p to its end q, the points are
not p. -/
theorem far_end {p q Y Z : Point} (hpq : p ≠ q) (hY : OnFiniteLine Y p q) (hYp : Y ≠ p)
    (hZ : OnFiniteLine Z Y q) : Z ≠ p := by
  rintro rfl
  rcases hZ with e | e | hb
  · exact hYp e.symm
  · exact hpq e
  · rcases hY with e | e | hb'
    · exact hYp e
    · rw [e] at hb
      exact ne_of_between_ends hb rfl
    · exact not_between_of_between hb' hb

/-- Each side of a chain through at least one corner has an end among those corners. -/
theorem chain_end {a b : Point} {l : List Point} (hl : l ≠ []) {s : Point × Point}
    (hs : s ∈ segments (a :: l ++ [b])) : s.1 ∈ l ∨ s.2 ∈ l := by
  obtain ⟨c, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  rcases List.mem_cons.mp hs with rfl | hs
  · exact Or.inr List.mem_cons_self
  · left
    rw [← LoopFacts.segments_map_fst c l' b]
    exact List.mem_map_of_mem hs

section Split

variable {A B : Point} {us vs : List Point}

/-- **A point of the first chain, other than A and B, is off the second piece's boundary**: the
chains meet only at A and B, and a side meets the diagonal only there. -/
theorem chain_off (h : SimpleLoop (A :: (us ++ B :: vs)))
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X)
    {s : Point × Point} (hs : s ∈ segments (A :: us ++ [B])) {Z : Point}
    (hZ : OnFiniteLine Z s.1 s.2) (hZA : Z ≠ A) (hZB : Z ≠ B) :
    ¬ loopBoundary (B :: (vs ++ [A])) Z := by
  rw [boundary_piece]
  rintro (⟨t, ht, hZt⟩ | hZd)
  · rcases chains_meet h hs ht hZ hZt with e | e
    · exact hZA e
    · exact hZB e
  · rcases side_diagonal hd (chain₁_side hs) hZ (LoopFacts.onFiniteLine_comm.mp hZd) with e | e
    · exact hZA e
    · exact hZB e

/-- **Along the first chain, the second piece's inside is constant.** The first chain, but for
A and B, is off the second piece's boundary (`chain_off`); along each of its finite straight
lines inside is constant (`seg_const`), so from corner to corner of `us` (`chain_const`), and
from any point of a side to an end of it among `us`. -/
theorem chain_inside_const (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ [])
    (hv : vs ≠ []) (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X)
    {Y Y' : Point} (hY : OnChain (A :: us ++ [B]) Y) (hYA : Y ≠ A) (hYB : Y ≠ B)
    (hY' : OnChain (A :: us ++ [B]) Y') (hY'A : Y' ≠ A) (hY'B : Y' ≠ B) :
    loopInside (B :: (vs ++ [A])) Y ↔ loopInside (B :: (vs ++ [A])) Y' := by
  have hQ := piece_simple₂ h hv hd
  have hA : A ∈ A :: (us ++ B :: vs) := List.mem_cons_self
  have hB : B ∈ A :: (us ++ B :: vs) := by simp
  have hnd := h.2.1
  rw [List.nodup_cons, List.nodup_append] at hnd
  have hAus : A ∉ us := fun hm => hnd.1 (List.mem_append_left _ hm)
  have hBus : B ∉ us := fun hm => hnd.2.2.2 B hm B List.mem_cons_self rfl
  have hseg : ∀ Y Y' : Point, (∀ Z : Point, OnFiniteLine Z Y Y' →
      ¬ loopBoundary (B :: (vs ++ [A])) Z) →
      (loopInside (B :: (vs ++ [A])) Y ↔ loopInside (B :: (vs ++ [A])) Y') :=
    fun _ _ h' => seg_const hQ h'
  /- A or B on a side with both ends among `us` would be one of those ends. -/
  have not_end {s : Point × Point} (hs : s ∈ sides (A :: (us ++ B :: vs))) {V Z : Point}
      (hV : V ∈ A :: (us ++ B :: vs)) (hVus : V ∉ us) (hZ : OnFiniteLine Z s.1 s.2)
      (hZV : Z = V) (h₁ : s.1 ∈ us) (h₂ : s.2 ∈ us) : False := by
    subst hZV
    rcases corner_on_side h hV hs hZ with e | e
    · exact hVus (e ▸ h₁)
    · exact hVus (e ▸ h₂)
  obtain ⟨u₀, us', rfl⟩ := List.exists_cons_of_ne_nil hu
  /- The corners of `us` agree with the first. -/
  have corners : ∀ x ∈ u₀ :: us', loopInside (B :: (vs ++ [A])) x ↔
      loopInside (B :: (vs ++ [A])) u₀ := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Iff.rfl
    · refine chain_const hseg us' u₀ (fun s hs Z hZ => ?_) x hx
      have hs₁ : s ∈ segments (A :: (u₀ :: us') ++ [B]) :=
        List.mem_cons_of_mem _ (segment_mem_append hs [B])
      have hs' := chain₁_side (vs := vs) hs₁
      have h₁ := (segment_corners hs).1
      have h₂ := (segment_corners hs).2
      exact chain_off h hd hs₁ hZ (fun e => not_end hs' hA hAus hZ e h₁ h₂)
        (fun e => not_end hs' hB hBus hZ e h₁ h₂)
  /- A point of a side agrees with an end of it among `us`. -/
  have point : ∀ Y : Point, OnChain (A :: (u₀ :: us') ++ [B]) Y → Y ≠ A → Y ≠ B →
      (loopInside (B :: (vs ++ [A])) Y ↔ loopInside (B :: (vs ++ [A])) u₀) := by
    rintro Y ⟨s, hs, hYs⟩ hYA hYB
    have hs' := chain₁_side (vs := vs) hs
    have hne := h.2.2.1 s hs'
    /- From Y to the end q among `us`, along the side from its other end p. -/
    have to_end {p q : Point} (hpq : p ≠ q) (hY : OnFiniteLine Y p q) (hq : q ∈ u₀ :: us')
        (hside : ∀ Z : Point, OnFiniteLine Z p q → OnFiniteLine Z s.1 s.2)
        (hends : ∀ V : Point, (V = s.1 ∨ V = s.2) → V = p ∨ V = q) :
        loopInside (B :: (vs ++ [A])) Y ↔ loopInside (B :: (vs ++ [A])) u₀ := by
      refine (hseg Y q fun Z hZ => ?_).trans (corners q hq)
      have hZs := hside Z (onFinite_sub hY hZ)
      /- A or B there would be an end of the side, not q, so p, which Y is not. -/
      have away {V : Point} (hV : V ∈ A :: (u₀ :: us' ++ B :: vs)) (hVus : V ∉ u₀ :: us')
          (hYV : Y ≠ V) (hZV : Z = V) : False := by
        subst hZV
        rcases hends Z (corner_on_side h hV hs' hZs) with e | e
        · exact far_end hpq hY (e ▸ hYV) hZ e
        · exact hVus (e ▸ hq)
      exact chain_off h hd hs hZs (fun e => away hA hAus hYA e) (fun e => away hB hBus hYB e)
    rcases chain_end (List.cons_ne_nil u₀ us') hs with hq | hq
    · exact to_end hne.symm (LoopFacts.onFiniteLine_comm.mp hYs) hq
        (fun Z hZ => LoopFacts.onFiniteLine_comm.mp hZ) fun V hV => hV.symm
    · exact to_end hne hYs hq (fun Z hZ => hZ) fun V hV => hV
  exact (point Y hY hYA hYB).trans (point Y' hY' hY'A hY'B).symm

end Split

/-! ## The first and the last boundary point along a ray -/

/-- A point of the ray from z through a point W of the ray from z through Q is on the latter. -/
theorem onRay_trans {z Q W U : Point} (hW : OnRay W z Q) (hU : OnRay U z W) : OnRay U z Q := by
  obtain ⟨hzQ, -, ⟨L, hzL, hQL, hWL⟩, hn⟩ := hW
  refine ⟨hzQ, hU.2.1, ⟨L, hzL, hQL, hU.onLine hzL hWL⟩, fun hb => hn ?_⟩
  exact between_symm (OnRay.between hU.symm (between_symm hb))

/-- Two different points of a ray are in order from its start. -/
theorem ray_order {z Q W W' : Point} (hW : OnRay W z Q) (hW' : OnRay W' z Q) (hne : W ≠ W') :
    Between z W W' ∨ Between z W' W := by
  obtain ⟨L, hzL, hQL, -⟩ := hW.2.2.1
  exact LoopFacts.order_from hzL (hW.onLine hzL hQL) (hW'.onLine hzL hQL) hW.2.1.symm
    hW'.2.1.symm hne (OnRay.not_between hW hW')

/-- A straight line meets a finite straight line with an end off it at one point at most. -/
theorem meets_once {W W' a b : Point} {ρ : Line} (hW : OnLine W ρ) (hW' : OnLine W' ρ)
    (ha : ¬ OnLine a ρ) (hWs : OnFiniteLine W a b) (hW's : OnFiniteLine W' a b) : W = W' := by
  refine Classical.byContradiction fun hne => ?_
  have hab : a ≠ b := by
    rintro rfl
    rcases hWs with e | e | hb
    · exact ha (e ▸ hW)
    · exact ha (e ▸ hW)
    · exact ne_of_between_ends hb rfl
  obtain ⟨N, haN, hbN⟩ := Postulate1 a b hab
  exact ha (line_unique hne (LoopFacts.onFiniteLine_onLine hWs haN hbN)
    (LoopFacts.onFiniteLine_onLine hW's haN hbN) hW hW' ▸ haN)

/-- The points of a ray on finitely many finite straight lines, each with an end off the ray's
straight line, are finitely many: one for each finite straight line at most. -/
theorem ray_points {z Q : Point} {ρ : Line} (hz : OnLine z ρ) (hQ : OnLine Q ρ) :
    ∀ ss : List (Point × Point), (∀ s ∈ ss, ¬ OnLine s.1 ρ) →
      ∃ pts : List Point, ∀ W : Point,
        W ∈ pts ↔ OnRay W z Q ∧ ∃ s ∈ ss, OnFiniteLine W s.1 s.2
  | [], _ => ⟨[], fun W => by simp⟩
  | s :: ss, hss => by
    obtain ⟨pts, hpts⟩ := ray_points hz hQ ss fun t ht => hss t (List.mem_cons_of_mem _ ht)
    have hs1 := hss s List.mem_cons_self
    by_cases hex : ∃ W : Point, OnRay W z Q ∧ OnFiniteLine W s.1 s.2
    · obtain ⟨W, hWr, hWs⟩ := hex
      refine ⟨W :: pts, fun W' => ?_⟩
      rw [List.mem_cons, hpts]
      constructor
      · rintro (rfl | ⟨hr, t, ht, hWt⟩)
        · exact ⟨hWr, s, List.mem_cons_self, hWs⟩
        · exact ⟨hr, t, List.mem_cons_of_mem _ ht, hWt⟩
      · rintro ⟨hr, t, ht, hWt⟩
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Or.inl (meets_once (hr.onLine hz hQ) (hWr.onLine hz hQ) hs1 hWt hWs)
        · exact Or.inr ⟨hr, t, ht, hWt⟩
    · refine ⟨pts, fun W' => ?_⟩
      rw [hpts]
      constructor
      · rintro ⟨hr, t, ht, hWt⟩
        exact ⟨hr, t, List.mem_cons_of_mem _ ht, hWt⟩
      · rintro ⟨hr, t, ht, hWt⟩
        rcases List.mem_cons.mp ht with rfl | ht
        · exact absurd ⟨W', hr, hWt⟩ hex
        · exact ⟨hr, t, ht, hWt⟩

/-- Of finitely many points of a ray, one is nearest its start. -/
theorem ray_min {z Q : Point} : ∀ pts : List Point, pts ≠ [] → (∀ W ∈ pts, OnRay W z Q) →
    ∃ W ∈ pts, ∀ W' ∈ pts, W' = W ∨ Between z W W'
  | [], hne, _ => absurd rfl hne
  | W :: rest, _, hr => by
    by_cases hrest : rest = []
    · subst hrest
      exact ⟨W, List.mem_cons_self, fun W' hW' => Or.inl (List.mem_singleton.mp hW')⟩
    obtain ⟨M, hM, hMmin⟩ := ray_min rest hrest fun V hV => hr V (List.mem_cons_of_mem _ hV)
    by_cases hWM : W = M
    · refine ⟨W, List.mem_cons_self, fun W' hW' => ?_⟩
      rcases List.mem_cons.mp hW' with e | hW'
      · exact Or.inl e
      · exact hWM ▸ hMmin W' hW'
    rcases ray_order (hr W List.mem_cons_self) (hr M (List.mem_cons_of_mem _ hM)) hWM with
      hb | hb
    · refine ⟨W, List.mem_cons_self, fun W' hW' => ?_⟩
      rcases List.mem_cons.mp hW' with e | hW'
      · exact Or.inl e
      · rcases hMmin W' hW' with e | hb'
        · rw [e]
          exact Or.inr hb
        · exact Or.inr (between_of_between_left hb' hb)
    · refine ⟨M, List.mem_cons_of_mem _ hM, fun W' hW' => ?_⟩
      rcases List.mem_cons.mp hW' with e | hW'
      · rw [e]
        exact Or.inr hb
      · exact hMmin W' hW'

/-- Of finitely many points of a ray, one is farthest from its start. -/
theorem ray_max {z Q : Point} : ∀ pts : List Point, pts ≠ [] → (∀ W ∈ pts, OnRay W z Q) →
    ∃ W ∈ pts, ∀ W' ∈ pts, W' = W ∨ Between z W' W
  | [], hne, _ => absurd rfl hne
  | W :: rest, _, hr => by
    by_cases hrest : rest = []
    · subst hrest
      exact ⟨W, List.mem_cons_self, fun W' hW' => Or.inl (List.mem_singleton.mp hW')⟩
    obtain ⟨M, hM, hMmax⟩ := ray_max rest hrest fun V hV => hr V (List.mem_cons_of_mem _ hV)
    by_cases hWM : W = M
    · refine ⟨W, List.mem_cons_self, fun W' hW' => ?_⟩
      rcases List.mem_cons.mp hW' with e | hW'
      · exact Or.inl e
      · exact hWM ▸ hMmax W' hW'
    rcases ray_order (hr W List.mem_cons_self) (hr M (List.mem_cons_of_mem _ hM)) hWM with
      hb | hb
    · refine ⟨M, List.mem_cons_of_mem _ hM, fun W' hW' => ?_⟩
      rcases List.mem_cons.mp hW' with e | hW'
      · rw [e]
        exact Or.inr hb
      · exact hMmax W' hW'
    · refine ⟨W, List.mem_cons_self, fun W' hW' => ?_⟩
      rcases List.mem_cons.mp hW' with e | hW'
      · exact Or.inl e
      · rcases hMmax W' hW' with e | hb'
        · rw [e]
          exact Or.inr hb
        · exact Or.inr (between_of_between_left hb hb')

/-- Two points of a straight line cannot each be between its start and the other. -/
theorem not_both {z U W : Point} (h₁ : Between z U W) (h₂ : Between z W U) : False :=
  ne_of_between (between_symm (between_of_between_left h₁ h₂)) rfl

/-- **The first point** of a ray on finitely many finite straight lines, each with an end off
the ray's straight line, if there is one: before it, the ray meets none of them. -/
theorem first_point {z Q : Point} {ρ : Line} (hz : OnLine z ρ) (hQ : OnLine Q ρ)
    {ss : List (Point × Point)} (hss : ∀ s ∈ ss, ¬ OnLine s.1 ρ)
    (hex : ∃ W : Point, OnRay W z Q ∧ ∃ s ∈ ss, OnFiniteLine W s.1 s.2) :
    ∃ W : Point, OnRay W z Q ∧ (∃ s ∈ ss, OnFiniteLine W s.1 s.2) ∧
      ∀ U : Point, Between z U W → ∀ s ∈ ss, ¬ OnFiniteLine U s.1 s.2 := by
  obtain ⟨pts, hpts⟩ := ray_points hz hQ ss hss
  obtain ⟨W₀, hW₀⟩ := hex
  obtain ⟨W, hW, hmin⟩ := ray_min pts (List.ne_nil_of_mem ((hpts W₀).mpr hW₀))
    fun V hV => ((hpts V).mp hV).1
  obtain ⟨hWr, hWs⟩ := (hpts W).mp hW
  refine ⟨W, hWr, hWs, fun U hU s hs hUs => ?_⟩
  rcases hmin U ((hpts U).mpr ⟨onRay_trans hWr (OnRay.of_between hU), s, hs, hUs⟩) with e | hb
  · exact ne_of_between (between_symm hU) e.symm
  · exact not_both hU hb

/-- **The last point** of a ray on finitely many finite straight lines, each with an end off the
ray's straight line, if there is one: beyond it, the ray meets none of them. -/
theorem last_point {z Q : Point} {ρ : Line} (hz : OnLine z ρ) (hQ : OnLine Q ρ)
    {ss : List (Point × Point)} (hss : ∀ s ∈ ss, ¬ OnLine s.1 ρ)
    (hex : ∃ W : Point, OnRay W z Q ∧ ∃ s ∈ ss, OnFiniteLine W s.1 s.2) :
    ∃ W : Point, OnRay W z Q ∧ (∃ s ∈ ss, OnFiniteLine W s.1 s.2) ∧
      ∀ U : Point, Between z W U → ∀ s ∈ ss, ¬ OnFiniteLine U s.1 s.2 := by
  obtain ⟨pts, hpts⟩ := ray_points hz hQ ss hss
  obtain ⟨W₀, hW₀⟩ := hex
  obtain ⟨W, hW, hmax⟩ := ray_max pts (List.ne_nil_of_mem ((hpts W₀).mpr hW₀))
    fun V hV => ((hpts V).mp hV).1
  obtain ⟨hWr, hWs⟩ := (hpts W).mp hW
  refine ⟨W, hWr, hWs, fun U hU s hs hUs => ?_⟩
  rcases hmax U ((hpts U).mpr ⟨onRay_trans hWr (OnRay.of_beyond hU), s, hs, hUs⟩) with e | hb
  · exact ne_of_between (between_symm hU) e
  · exact not_both hU hb

/-- A good ray from a point inside a loop crosses one of its sides. -/
theorem crosses_of_inside {R : List Point} (hR : SimpleLoop R) {X Q : Point}
    (hQ : GoodRay R X Q) (hin : loopInside R X) : ∃ t ∈ sides R, RayCrosses X Q t := by
  refine Classical.byContradiction fun hno => ?_
  have h0 := LoopFacts.crossingCount_eq_zero (ps := R) (X := X) (Q := Q)
    fun t ht hc => hno ⟨t, ht, hc⟩
  have hodd := (loop_inside_iff hR hin.1 hQ).mp hin
  rw [h0] at hodd
  exact absurd hodd (by decide)

section Split

variable {A B : Point} {us vs : List Point}

/-- A point of a piece's side is on a side of the loop or on AB. -/
theorem piece_on₁ {t : Point × Point} (ht : t ∈ sides (A :: (us ++ [B]))) {U : Point}
    (hU : OnFiniteLine U t.1 t.2) :
    ∃ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], OnFiniteLine U s.1 s.2 := by
  rw [piece_sides] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact ⟨t, List.mem_append_left _ (chain₁_side ht), hU⟩
  · rw [List.mem_singleton.mp ht] at hU
    exact ⟨(A, B), List.mem_append_right _ List.mem_cons_self,
      LoopFacts.onFiniteLine_comm.mp hU⟩

/-- A point of the second piece's side is on a side of the loop or on AB. -/
theorem piece_on₂ {t : Point × Point} (ht : t ∈ sides (B :: (vs ++ [A]))) {U : Point}
    (hU : OnFiniteLine U t.1 t.2) :
    ∃ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], OnFiniteLine U s.1 s.2 := by
  rw [piece_sides] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact ⟨t, List.mem_append_left _ (chain₂_side ht), hU⟩
  · rw [List.mem_singleton.mp ht] at hU
    exact ⟨(A, B), List.mem_append_right _ List.mem_cons_self, hU⟩

/-- **Where a straight line through no corner meets the sides or AB**: strictly between A and B,
or at a point of one chain, at neither A nor B, off the other piece's boundary. -/
theorem hit_cases (h : SimpleLoop (A :: (us ++ B :: vs)))
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) {W : Point}
    {ρ : Line} (hWρ : OnLine W ρ) (hoff : ∀ V ∈ A :: (us ++ B :: vs), ¬ OnLine V ρ)
    (hW : ∃ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], OnFiniteLine W s.1 s.2) :
    Between A W B ∨
      (OnChain (A :: us ++ [B]) W ∧ W ≠ A ∧ W ≠ B ∧ ¬ loopBoundary (B :: (vs ++ [A])) W) ∨
      (OnChain (B :: vs ++ [A]) W ∧ W ≠ A ∧ W ≠ B ∧ ¬ loopBoundary (A :: (us ++ [B])) W) := by
  have hWA : W ≠ A := fun e => hoff A List.mem_cons_self (e ▸ hWρ)
  have hWB : W ≠ B := fun e => hoff B (by simp) (e ▸ hWρ)
  obtain ⟨s, hs, hWs⟩ := hW
  rcases List.mem_append.mp hs with hs | hs
  · rw [split_sides] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact Or.inr (Or.inl ⟨⟨s, hs, hWs⟩, hWA, hWB, chain_off h hd hs hWs hWA hWB⟩)
    · refine Or.inr (Or.inr ⟨⟨s, hs, hWs⟩, hWA, hWB, ?_⟩)
      have rc := rotate_config h hd
      exact chain_off rc.1 rc.2 hs hWs hWB hWA
  · rw [List.mem_singleton.mp hs] at hWs
    rcases hWs with e | e | hb
    · exact absurd e hWA
    · exact absurd e hWB
    · exact Or.inl hb

/-- **The first point on a side or on AB**, along a ray from a point X off them, its straight
line through no corner: either it is strictly between A and B, and X is inside the loop; or it
is on one chain, at neither A nor B, and inside the other piece exactly when X is. Before it the
ray meets no side and not AB (`first_point`, `inside_of_segment`). -/
theorem first_hit (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ [])
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) {X Q : Point}
    {ρ : Line} (hXρ : OnLine X ρ) (hQρ : OnLine Q ρ)
    (hoff : ∀ V ∈ A :: (us ++ B :: vs), ¬ OnLine V ρ)
    (hXb : ¬ loopBoundary (A :: (us ++ B :: vs)) X) (hXd : ¬ OnFiniteLine X A B)
    (hex : ∃ W : Point, OnRay W X Q ∧
      ∃ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], OnFiniteLine W s.1 s.2) :
    ∃ W : Point, OnRay W X Q ∧
      ((Between A W B ∧ loopInside (A :: (us ++ B :: vs)) X) ∨
        (OnChain (A :: us ++ [B]) W ∧ W ≠ A ∧ W ≠ B ∧
          (loopInside (B :: (vs ++ [A])) W ↔ loopInside (B :: (vs ++ [A])) X)) ∨
        (OnChain (B :: vs ++ [A]) W ∧ W ≠ A ∧ W ≠ B ∧
          (loopInside (A :: (us ++ [B])) W ↔ loopInside (A :: (us ++ [B])) X))) := by
  have hss : ∀ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], ¬ OnLine s.1 ρ := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hoff _ (LoopFacts.side_mem hs).1
    · rw [List.mem_singleton.mp hs]
      exact hoff A List.mem_cons_self
  obtain ⟨W, hWr, hWs, hfree⟩ := first_point hXρ hQρ hss hex
  have hWρ : OnLine W ρ := hWr.onLine hXρ hQρ
  have hXW : X ≠ W := hWr.2.1.symm
  /- Strictly before W, no side and not AB. -/
  have hfb : ∀ U : Point, Between X U W → ¬ loopBoundary (A :: (us ++ B :: vs)) U :=
    fun U hU ⟨s, hs, hUs⟩ => hfree U hU s (List.mem_append_left _ hs) hUs
  have hfd : ∀ U : Point, Between X U W → ¬ OnFiniteLine U A B :=
    fun U hU hUd => hfree U hU (A, B) (List.mem_append_right _ List.mem_cons_self) hUd
  /- Off the loop's boundary and AB means off both pieces' boundaries. -/
  have offP {U : Point} (hb : ¬ loopBoundary (A :: (us ++ B :: vs)) U)
      (hd' : ¬ OnFiniteLine U A B) : ¬ loopBoundary (A :: (us ++ [B])) U := by
    rw [boundary_piece]
    rintro (hc | hc)
    · exact hb ((boundary_split U).mpr (Or.inl hc))
    · exact hd' hc
  have offQ {U : Point} (hb : ¬ loopBoundary (A :: (us ++ B :: vs)) U)
      (hd' : ¬ OnFiniteLine U A B) : ¬ loopBoundary (B :: (vs ++ [A])) U := by
    rw [boundary_piece]
    rintro (hc | hc)
    · exact hb ((boundary_split U).mpr (Or.inr hc))
    · exact hd' (LoopFacts.onFiniteLine_comm.mp hc)
  refine ⟨W, hWr, ?_⟩
  rcases hit_cases h hd hWρ hoff hWs with hb | ⟨hc, hWA, hWB, hWQ⟩ | ⟨hc, hWA, hWB, hWP⟩
  · refine Or.inl ⟨hb, (CoverFacts.inside_of_segment h hXW hXρ hWρ hoff hXb (hd W hb).1
      hfb).mpr (hd W hb)⟩
  · refine Or.inr (Or.inl ⟨hc, hWA, hWB, (CoverFacts.inside_of_segment (piece_simple₂ h hv hd)
      hXW hXρ hWρ (fun V hV => hoff V (piece_mem₂ hV)) (offQ hXb hXd) hWQ
      fun U hU => offQ (hfb U hU) (hfd U hU)).symm⟩)
  · refine Or.inr (Or.inr ⟨hc, hWA, hWB, (CoverFacts.inside_of_segment (piece_simple h hu hd)
      hXW hXρ hWρ (fun V hV => hoff V (piece_mem₁ hV)) (offP hXb hXd) hWP
      fun U hU => offP (hfb U hU) (hfd U hU)).symm⟩)

/-- **The last point on a side or on AB**, along a ray whose straight line passes through no
corner: either it is strictly between A and B, or it is on one chain, at neither A nor B, and
outside the other piece, since the ray beyond it crosses nothing (`last_point`). -/
theorem last_hit (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ [])
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) {X Q : Point}
    {ρ : Line} (hXρ : OnLine X ρ) (hQρ : OnLine Q ρ)
    (hoff : ∀ V ∈ A :: (us ++ B :: vs), ¬ OnLine V ρ)
    (hex : ∃ W : Point, OnRay W X Q ∧
      ∃ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], OnFiniteLine W s.1 s.2) :
    ∃ W : Point, OnRay W X Q ∧
      (Between A W B ∨
        (OnChain (A :: us ++ [B]) W ∧ W ≠ A ∧ W ≠ B ∧ ¬ loopInside (B :: (vs ++ [A])) W) ∨
        (OnChain (B :: vs ++ [A]) W ∧ W ≠ A ∧ W ≠ B ∧ ¬ loopInside (A :: (us ++ [B])) W)) := by
  have hss : ∀ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], ¬ OnLine s.1 ρ := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hoff _ (LoopFacts.side_mem hs).1
    · rw [List.mem_singleton.mp hs]
      exact hoff A List.mem_cons_self
  obtain ⟨W, hWr, hWs, hfree⟩ := last_point hXρ hQρ hss hex
  have hWρ : OnLine W ρ := hWr.onLine hXρ hQρ
  /- Beyond W the ray from W crosses no side of a piece, so W is outside it. -/
  have outside {R : List Point} (hR : SimpleLoop R) (hRV : ∀ V ∈ R, ¬ OnLine V ρ)
      (hRs : ∀ t ∈ sides R, ∀ U : Point, OnFiniteLine U t.1 t.2 →
        ∃ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], OnFiniteLine U s.1 s.2)
      (hWb : ¬ loopBoundary R W) : ¬ loopInside R W := by
    obtain ⟨Q', hXWQ'⟩ := produce hWr.2.1.symm
    have hQ'ρ : OnLine Q' ρ := on_line_of_between hXWQ' hXρ hWρ
    have hg : GoodRay R W Q' := CoverFacts.goodRay_of_line
      (ne_of_between (between_symm hXWQ')).symm hWρ hQ'ρ hRV
    have h0 : crossingCount R W Q' = 0 := by
      refine LoopFacts.crossingCount_eq_zero fun t ht ⟨U, hU, hUt⟩ => ?_
      obtain ⟨s, hs, hUs⟩ := hRs t ht U (Or.inr (Or.inr hUt))
      exact hfree U (OnRay.between hU hXWQ') s hs hUs
    intro hin
    have hodd := (loop_inside_iff hR hWb hg).mp hin
    rw [h0] at hodd
    exact absurd hodd (by decide)
  refine ⟨W, hWr, ?_⟩
  rcases hit_cases h hd hWρ hoff hWs with hb | ⟨hc, hWA, hWB, hWQ⟩ | ⟨hc, hWA, hWB, hWP⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inl ⟨hc, hWA, hWB, outside (piece_simple₂ h hv hd)
      (fun V hV => hoff V (piece_mem₂ hV)) (fun t ht U hU => piece_on₂ ht hU) hWQ⟩)
  · exact Or.inr (Or.inr ⟨hc, hWA, hWB, outside (piece_simple h hu hd)
      (fun V hV => hoff V (piece_mem₁ hV)) (fun t ht U hU => piece_on₁ ht hU) hWP⟩)

/-- **Across the diagonal.** A finite straight line zz' through a point d strictly between A and
B, its straight line through no corner, near d and meeting no side: z and z' are inside the loop,
as d is; across AB the first piece's inside changes (`inside_flip`), so one of them is inside the
first piece only, and the other inside the second only (`inside_xor`). -/
theorem across_diagonal (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ [])
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) :
    ∃ (z z' d : Point) (ρ ℓ : Line), OnLine A ℓ ∧ OnLine B ℓ ∧ OnLine d ℓ ∧ OnLine d ρ ∧
      OnLine z ρ ∧ OnLine z' ρ ∧ (∀ V ∈ A :: (us ++ B :: vs), ¬ OnLine V ρ) ∧
      ¬ OnLine z ℓ ∧ ¬ OnLine z' ℓ ∧ z ≠ d ∧ z' ≠ d ∧
      ¬ loopBoundary (A :: (us ++ B :: vs)) z ∧ ¬ loopBoundary (A :: (us ++ B :: vs)) z' ∧
      (¬ loopInside (A :: (us ++ [B])) z ∧ loopInside (B :: (vs ++ [A])) z) ∧
      (loopInside (A :: (us ++ [B])) z' ∧ ¬ loopInside (B :: (vs ++ [A])) z') := by
  have hP := piece_simple h hu hd
  have hA : A ∈ A :: (us ++ B :: vs) := List.mem_cons_self
  obtain ⟨ℓ, hAℓ, hBℓ⟩ := Postulate1 A B (ends_ne h.2.1)
  obtain ⟨d, hdℓ, hAdB, -⟩ := exists_point_between hAℓ hBℓ (ends_ne h.2.1) []
  have hdin := hd d hAdB
  have hdps : d ∉ A :: (us ++ B :: vs) := fun hm => hdin.1 (corner_boundary hm)
  /- Conditions at d keeping off every side. -/
  obtain ⟨hs, hs1, hs2⟩ := seg_conditions h (Y := d) (Y' := d) fun Z hZ => by
    have hZd : Z = d := by
      rcases hZ with e | e | hb
      · exact e
      · exact e
      · exact absurd rfl (ne_of_between_ends hb)
    rw [hZd]
    exact hdin.1
  have hds : ∀ p ∈ hs, SameSide d p.1 p.2 := fun p hp => (hs1 p hp).1
  obtain ⟨a₁, a₂, a₃, hdT, hT⟩ := small_triangle hs hds
  obtain ⟨z, hzT, hza⟩ :=
    triangle_point_avoiding hdT.1.symm.triangle.cab (ℓ :: CoverFacts.joins d (A :: (us ++ B :: vs)))
  have hzℓ : ¬ OnLine z ℓ := hza ℓ List.mem_cons_self
  have hzd : z ≠ d := fun e => hzℓ (e ▸ hdℓ)
  have hzs : ∀ p ∈ hs, SameSide z p.1 p.2 := hT z (Or.inl hzT)
  obtain ⟨ρ, hzρ, hdρ⟩ := Postulate1 z d hzd
  have hoff : ∀ V ∈ A :: (us ++ B :: vs), ¬ OnLine V ρ :=
    CoverFacts.joins_off (fun L hL => hza L (List.mem_cons_of_mem _ hL)) hdps hdρ hzρ
  obtain ⟨y', hzdy'⟩ := produce hzd
  obtain ⟨z', hdz'y', hz's⟩ := Avoid.shorten_sides (ne_of_between (between_symm hzdy')).symm hs hds
  have hzdz' : Between z d z' := between_cut hzdy' hdz'y'
  have hz'ρ : OnLine z' ρ := on_line_of_between hzdz' hzρ hdρ
  have hz'ℓ : ¬ OnLine z' ℓ := fun h' => hzℓ (on_line_of_between (between_symm hzdz') h' hdℓ)
  have hz'd : z' ≠ d := ne_of_between (between_symm hzdz')
  /- Every point of zz' keeps the conditions, so is on no side. -/
  have hseg : ∀ U : Point, OnFiniteLine U z z' → ¬ loopBoundary (A :: (us ++ B :: vs)) U := by
    intro U hU
    refine hs2 U ?_
    rcases hU with rfl | rfl | hb
    · exact hzs
    · exact hz's
    · exact conds_between hzs hz's hb
  have hzb := hseg z (Or.inl rfl)
  have hz'b := hseg z' (Or.inr (Or.inl rfl))
  /- z and z' are inside the loop, as d is. -/
  have hzi : loopInside (A :: (us ++ B :: vs)) z :=
    (CoverFacts.inside_of_segment h hzd hzρ hdρ hoff hzb hdin.1 fun U hU =>
      hseg U (Or.inr (Or.inr (between_of_between_left hzdz' hU)))).mpr hdin
  have hz'i : loopInside (A :: (us ++ B :: vs)) z' :=
    (CoverFacts.inside_of_segment h hz'd hz'ρ hdρ hoff hz'b hdin.1 fun U hU =>
      hseg U (Or.inr (Or.inr (between_symm (between_of_between_left (between_symm hzdz')
        hU))))).mpr hdin
  /- Across AB at d, the first piece's inside changes. -/
  have hflip : loopInside (A :: (us ++ [B])) z ↔ ¬ loopInside (A :: (us ++ [B])) z' := by
    refine CoverFacts.inside_flip hP (s := (B, A)) (by rw [piece_sides]; simp) hzdz'
      (between_symm hAdB) hzρ hz'ρ (fun V hV => hoff V (piece_mem₁ hV)) ?_
    intro U hU t ht hUt
    rw [piece_sides] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact absurd ⟨t, chain₁_side ht, hUt⟩ (hseg U hU)
    · rw [List.mem_singleton.mp ht] at hUt ⊢
      refine ⟨Classical.byContradiction fun hne => ?_, rfl⟩
      exact hoff A hA (line_unique hne (LoopFacts.onFiniteLine_onLine hUt hBℓ hAℓ) hdℓ
        (LoopFacts.onFiniteLine_onLine hU hzρ hz'ρ) hdρ ▸ hAℓ)
  /- Inside the loop, off AB, each is inside exactly one piece. -/
  have offd {Y : Point} (hY : ¬ OnLine Y ℓ) : ¬ OnFiniteLine Y A B := fun h' =>
    hY (LoopFacts.onFiniteLine_onLine h' hAℓ hBℓ)
  have e := (inside_xor h hu hv hd hzb (offd hzℓ)).mp hzi
  have e' := (inside_xor h hu hv hd hz'b (offd hz'ℓ)).mp hz'i
  by_cases h₁ : loopInside (A :: (us ++ [B])) z
  · refine ⟨z', z, d, ρ, ℓ, hAℓ, hBℓ, hdℓ, hdρ, hz'ρ, hzρ, hoff, hz'ℓ, hzℓ, hz'd, hzd, hz'b,
      hzb, ⟨hflip.mp h₁, ?_⟩, ⟨h₁, e.mp h₁⟩⟩
    exact Classical.byContradiction fun h₂ => hflip.mp h₁ (e'.mpr h₂)
  · have h₁' : loopInside (A :: (us ++ [B])) z' :=
      Classical.byContradiction fun h' => h₁ (hflip.mpr h')
    exact ⟨z, z', d, ρ, ℓ, hAℓ, hBℓ, hdℓ, hdρ, hzρ, hz'ρ, hoff, hzℓ, hz'ℓ, hzd, hz'd, hzb, hz'b,
      ⟨h₁, Classical.byContradiction fun h₂ => h₁ (e.mpr h₂)⟩, ⟨h₁', e'.mp h₁'⟩⟩

/-- **Each chain is outside the other piece**, but for A and B. Along each chain the other
piece's inside is constant (`chain_inside_const`). Near the diagonal, a point z inside the
second piece only and a point z' inside the first only (`across_diagonal`); rays from them away
from AB keep off it. From z, the first point on a side is on the first chain inside the second
piece, or on the second chain outside the first; the last is outside the other piece, whichever
chain it is on; from z', the first is on the first chain outside the second piece, or on the
second chain inside the first (`first_hit`, `last_hit`). Only the chains outside the other
pieces fit all three. -/
theorem chains_outside (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ [])
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) :
    (∀ Y : Point, OnChain (A :: us ++ [B]) Y → Y ≠ A → Y ≠ B →
      ¬ loopInside (B :: (vs ++ [A])) Y) ∧
    (∀ Y : Point, OnChain (B :: vs ++ [A]) Y → Y ≠ A → Y ≠ B →
      ¬ loopInside (A :: (us ++ [B])) Y) := by
  have hP := piece_simple h hu hd
  have hQ := piece_simple₂ h hv hd
  have rc := rotate_config h hd
  obtain ⟨z, z', d, ρ, ℓ, hAℓ, hBℓ, hdℓ, hdρ, hzρ, hz'ρ, hoff, hzℓ, hz'ℓ, hzd, hz'd, hzb, hz'b,
    ⟨hz₁, hz₂⟩, ⟨hz'₁, hz'₂⟩⟩ := across_diagonal h hu hv hd
  /- From a point near d, the ray away from d keeps off AB. -/
  have ray {Y : Point} (hYρ : OnLine Y ρ) (hYℓ : ¬ OnLine Y ℓ) (hYd : Y ≠ d) :
      ∃ Q : Point, OnLine Q ρ ∧ Y ≠ Q ∧ ∀ W : Point, OnRay W Y Q → ¬ OnFiniteLine W A B := by
    obtain ⟨Q, hdYQ⟩ := produce hYd.symm
    refine ⟨Q, on_line_of_between hdYQ hdρ hYρ, (ne_of_between (between_symm hdYQ)).symm,
      fun W hW hWd => ?_⟩
    have hs := pasch2 (OnRay.between hW hdYQ) hdℓ hYℓ
    exact not_on_line_of_same_side (same_side_symm hs)
      (LoopFacts.onFiniteLine_onLine hWd hAℓ hBℓ)
  have hzd' : ¬ OnFiniteLine z A B := fun h' => hzℓ (LoopFacts.onFiniteLine_onLine h' hAℓ hBℓ)
  have hz'd' : ¬ OnFiniteLine z' A B := fun h' =>
    hz'ℓ (LoopFacts.onFiniteLine_onLine h' hAℓ hBℓ)
  obtain ⟨Q, hQρ, hzQ, hzr⟩ := ray hzρ hzℓ hzd
  obtain ⟨Q', hQ'ρ, hz'Q', hz'r⟩ := ray hz'ρ hz'ℓ hz'd
  /- Each ray crosses a side: from z one of the second piece, from z' one of the first. -/
  have hexz : ∃ W : Point, OnRay W z Q ∧
      ∃ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], OnFiniteLine W s.1 s.2 := by
    obtain ⟨t, ht, U, hU, hUt⟩ := crosses_of_inside hQ (CoverFacts.goodRay_of_line hzQ hzρ hQρ
      fun V hV => hoff V (piece_mem₂ hV)) hz₂
    exact ⟨U, hU, piece_on₂ ht (Or.inr (Or.inr hUt))⟩
  have hexz' : ∃ W : Point, OnRay W z' Q' ∧
      ∃ s ∈ sides (A :: (us ++ B :: vs)) ++ [(A, B)], OnFiniteLine W s.1 s.2 := by
    obtain ⟨t, ht, U, hU, hUt⟩ := crosses_of_inside hP (CoverFacts.goodRay_of_line hz'Q' hz'ρ
      hQ'ρ fun V hV => hoff V (piece_mem₁ hV)) hz'₁
    exact ⟨U, hU, piece_on₁ ht (Or.inr (Or.inr hUt))⟩
  /- Points of each chain, but for A and B, agree about the other piece. -/
  have H₁ := @chain_inside_const A B us vs h hu hv hd
  have H₂ := @chain_inside_const B A vs us rc.1 hv hu rc.2
  let E₁ : Prop := ∃ Y : Point, OnChain (A :: us ++ [B]) Y ∧ Y ≠ A ∧ Y ≠ B ∧
    ¬ loopInside (B :: (vs ++ [A])) Y
  let I₁ : Prop := ∃ Y : Point, OnChain (A :: us ++ [B]) Y ∧ Y ≠ A ∧ Y ≠ B ∧
    loopInside (B :: (vs ++ [A])) Y
  let E₂ : Prop := ∃ Y : Point, OnChain (B :: vs ++ [A]) Y ∧ Y ≠ A ∧ Y ≠ B ∧
    ¬ loopInside (A :: (us ++ [B])) Y
  let I₂ : Prop := ∃ Y : Point, OnChain (B :: vs ++ [A]) Y ∧ Y ≠ A ∧ Y ≠ B ∧
    loopInside (A :: (us ++ [B])) Y
  have n₁ : E₁ → ¬ I₁ := fun ⟨Y, hY, hYA, hYB, hYo⟩ ⟨Y', hY', hY'A, hY'B, hY'i⟩ =>
    hYo ((H₁ hY hYA hYB hY' hY'A hY'B).mpr hY'i)
  have n₂ : E₂ → ¬ I₂ := fun ⟨Y, hY, hYA, hYB, hYo⟩ ⟨Y', hY', hY'A, hY'B, hY'i⟩ =>
    hYo ((H₂ hY hYB hYA hY' hY'B hY'A).mpr hY'i)
  /- The three rays. -/
  have zf : I₁ ∨ E₂ := by
    obtain ⟨W, hWr, hW⟩ := first_hit h hu hv hd hzρ hQρ hoff hzb hzd' hexz
    rcases hW with ⟨hb, -⟩ | ⟨hc, hWA, hWB, he⟩ | ⟨hc, hWA, hWB, he⟩
    · exact absurd (Or.inr (Or.inr hb)) (hzr W hWr)
    · exact Or.inl ⟨W, hc, hWA, hWB, he.mpr hz₂⟩
    · exact Or.inr ⟨W, hc, hWA, hWB, fun hi => hz₁ (he.mp hi)⟩
  have zl : E₁ ∨ E₂ := by
    obtain ⟨W, hWr, hW⟩ := last_hit h hu hv hd hzρ hQρ hoff hexz
    rcases hW with hb | ⟨hc, hWA, hWB, ho⟩ | ⟨hc, hWA, hWB, ho⟩
    · exact absurd (Or.inr (Or.inr hb)) (hzr W hWr)
    · exact Or.inl ⟨W, hc, hWA, hWB, ho⟩
    · exact Or.inr ⟨W, hc, hWA, hWB, ho⟩
  have z'f : E₁ ∨ I₂ := by
    obtain ⟨W, hWr, hW⟩ := first_hit h hu hv hd hz'ρ hQ'ρ hoff hz'b hz'd' hexz'
    rcases hW with ⟨hb, -⟩ | ⟨hc, hWA, hWB, he⟩ | ⟨hc, hWA, hWB, he⟩
    · exact absurd (Or.inr (Or.inr hb)) (hz'r W hWr)
    · exact Or.inl ⟨W, hc, hWA, hWB, fun hi => hz'₂ (he.mp hi)⟩
    · exact Or.inr ⟨W, hc, hWA, hWB, he.mpr hz'₁⟩
  have hE : E₁ ∧ E₂ := by
    by_cases hE₁ : E₁
    · exact ⟨hE₁, zf.resolve_left (n₁ hE₁)⟩
    · have hE₂ := zl.resolve_left hE₁
      exact absurd (z'f.resolve_left hE₁) (n₂ hE₂)
  obtain ⟨⟨Y₁, hY₁, hY₁A, hY₁B, hY₁o⟩, ⟨Y₂, hY₂, hY₂A, hY₂B, hY₂o⟩⟩ := hE
  exact ⟨fun Y hY hYA hYB hi => hY₁o ((H₁ hY₁ hY₁A hY₁B hY hYA hYB).mpr hi),
    fun Y hY hYA hYB hi => hY₂o ((H₂ hY₂ hY₂B hY₂A hY hYB hYA).mpr hi)⟩

/-- **The pieces' insides do not meet.** A point inside both is off every side and off AB; along
a good ray from it, the first point on a side or on AB would be strictly between A and B, where
the point would be inside the loop, though inside both pieces it is outside (`inside_xor`); or
on one chain inside the other piece, which `chains_outside` excludes. -/
theorem pieces_apart (h : SimpleLoop (A :: (us ++ B :: vs))) (hu : us ≠ []) (hv : vs ≠ [])
    (hd : ∀ X : Point, Between A X B → loopInside (A :: (us ++ B :: vs)) X) {X : Point}
    (h₁ : loopInside (A :: (us ++ [B])) X) (h₂ : loopInside (B :: (vs ++ [A])) X) : False := by
  have hP := piece_simple h hu hd
  obtain ⟨ho₁, ho₂⟩ := chains_outside h hu hv hd
  have hXb : ¬ loopBoundary (A :: (us ++ B :: vs)) X := by
    rw [boundary_split]
    rintro (hc | hc)
    · exact h₁.1 ((boundary_piece A B us X).mpr (Or.inl hc))
    · exact h₂.1 ((boundary_piece B A vs X).mpr (Or.inl hc))
  have hXd : ¬ OnFiniteLine X A B := fun hc => h₁.1 ((boundary_piece A B us X).mpr (Or.inr hc))
  obtain ⟨R, hR⟩ := good_ray_exists h hXb
  obtain ⟨ρ, hXρ, hRρ⟩ := Postulate1 X R hR.1
  have hoff : ∀ V ∈ A :: (us ++ B :: vs), ¬ OnLine V ρ := fun V hV hVρ =>
    hR.2 V hV ⟨ρ, hXρ, hRρ, hVρ⟩
  obtain ⟨t, ht, U, hU, hUt⟩ := crosses_of_inside hP
    ⟨hR.1, fun V hV => hR.2 V (piece_mem₁ hV)⟩ h₁
  obtain ⟨W, -, hW⟩ := first_hit h hu hv hd hXρ hRρ hoff hXb hXd
    ⟨U, hU, piece_on₁ ht (Or.inr (Or.inr hUt))⟩
  rcases hW with ⟨-, hi⟩ | ⟨hc, hWA, hWB, he⟩ | ⟨hc, hWA, hWB, he⟩
  · exact ((inside_xor h hu hv hd hXb hXd).mp hi).mp h₁ h₂
  · exact ho₁ W hc hWA hWB (he.mpr h₂)
  · exact ho₂ W hc hWA hWB (he.mpr h₁)

end Split

end Diag

end Elements.Figures
