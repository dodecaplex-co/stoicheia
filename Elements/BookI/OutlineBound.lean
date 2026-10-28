import Elements.Figure.Outlines.OutlineFacts
import Elements.Figure.Sums
import Elements.BookI.Prop23

/-!
# Book I: a figure given by its outline lies within a triangle

`outline_bounded`, one of brief 0013's bridges for a figure given by its outline (section 2,
and section 8, "The routes taken"), with the lemmas, in the namespace `OutlineBound`, that
find a triangle holding finitely many points; `OutlineFacts.bounded_of_enclosure`, in Book
Zero (`Figure/Outlines/OutlineFacts.lean`), does the rest, for a triangle that holds every
corner holds the whole region. The statement can fail without Postulate 5, which enters
here, and an angle is copied by I.23, the one proposition of the *Elements* the proof
cites. So it cannot stand in Book Zero: it stands in Book I, after I.29, where Euclid first
uses Postulate 5. I.23 reaches superposition only through I.4 and I.8, the two places
FORMALIZATION (section 7) allows it; nothing here names superposition. No other proof uses
`outline_bounded`: the division of an outline uses a convex enclosure, whose proof does not
use Postulate 5 (`convex_enclosure`, `outline_enclosure`).

* **Finitely many points in one angle.** Finitely many points lie on one side of a straight
  line (`line_one_side`), so within an angle at a point beyond it (`cone_of_line`); these use
  neither Postulate 5 nor I.23.
* **A triangle cut off from the angle.** Through a point within an angle a straight line meets
  both arms (`angle_triangle`): there Postulate 5 enters, twice, with an angle copied from one
  point to another by I.23 (`copy_angle`). Moving the corners out along the arms, one triangle
  holds every point (`angle_enclosure`, `enclosing_triangle`).
-/

namespace Elements.Figures

open Tacit

namespace OutlineBound

/-! ## Finitely many points in one angle

None of this uses Postulate 5. A finite straight line through a point of a straight line,
produced past it, takes its two ends to the far side of every point within the angle they
make there; so finitely many points lie on one side of some straight line, and, seen from a
point beyond it, within one angle. -/

/-- Finitely many points of a straight line lie between two of its points. A point beyond the
two ends so far replaces the nearer end. -/
theorem line_span {ℓ : Line} : ∀ xs : List Point, (∀ X ∈ xs, OnLine X ℓ) →
    ∃ B C : Point, OnLine B ℓ ∧ OnLine C ℓ ∧ B ≠ C ∧ ∀ X ∈ xs, Between B X C
  | [], _ => by
    obtain ⟨B, hB, -⟩ := exists_point_on_line ℓ []
    obtain ⟨C, hC, hCB⟩ := exists_point_on_line ℓ [B]
    exact ⟨B, C, hB, hC, fun e => hCB (e ▸ List.mem_singleton_self B),
      fun _ h => absurd h List.not_mem_nil⟩
  | X :: xs, h => by
    obtain ⟨B, C, hB, hC, hBC, hxs⟩ := line_span xs fun Y hY => h Y (List.mem_cons_of_mem _ hY)
    have hX : OnLine X ℓ := h X List.mem_cons_self
    /- Moving the end B out beyond it, or the end C, keeps every point between. -/
    have outB : ∀ {B' : Point}, Between C B B' → ∀ Y ∈ xs, Between B' Y C := fun hCBB' Y hY =>
      between_symm (between_of_between_left hCBB' (between_symm (hxs Y hY)))
    have outC : ∀ {C' : Point}, Between B C C' → ∀ Y ∈ xs, Between B Y C' := fun hBCC' Y hY =>
      between_of_between_left hBCC' (hxs Y hY)
    have newB : ∀ {B' : Point}, Between C B B' → Between B' X C → ∃ B C : Point,
        OnLine B ℓ ∧ OnLine C ℓ ∧ B ≠ C ∧ ∀ Y ∈ X :: xs, Between B Y C := by
      intro B' hCBB' hB'XC
      refine ⟨B', C, on_line_of_between hCBB' hC hB, hC, ne_of_between_ends hB'XC, fun Y hY => ?_⟩
      rcases List.mem_cons.mp hY with rfl | hY
      · exact hB'XC
      · exact outB hCBB' Y hY
    have newC : ∀ {C' : Point}, Between B C C' → Between B X C' → ∃ B C : Point,
        OnLine B ℓ ∧ OnLine C ℓ ∧ B ≠ C ∧ ∀ Y ∈ X :: xs, Between B Y C := by
      intro C' hBCC' hBXC'
      refine ⟨B, C', hB, on_line_of_between hBCC' hB hC, ne_of_between_ends hBXC', fun Y hY => ?_⟩
      rcases List.mem_cons.mp hY with rfl | hY
      · exact hBXC'
      · exact outC hBCC' Y hY
    by_cases hXB : X = B
    · subst hXB
      obtain ⟨B', hCXB'⟩ := produce hBC.symm
      exact newB hCXB' (between_symm hCXB')
    by_cases hXC : X = C
    · subst hXC
      obtain ⟨C', hBXC'⟩ := produce hBC
      exact newC hBXC' hBXC'
    rcases between_cases (Ne.symm hXB) hXC hBC hB hX hC with hBXC | hXBC | hBCX
    · exact ⟨B, C, hB, hC, hBC, fun Y hY => by
        rcases List.mem_cons.mp hY with rfl | hY
        · exact hBXC
        · exact hxs Y hY⟩
    · obtain ⟨B', hCXB'⟩ := produce (Ne.symm hXC)
      exact newB (between_of_between_left hCXB' (between_symm hXBC)) (between_symm hCXB')
    · obtain ⟨C', hBXC'⟩ := produce (Ne.symm hXB)
      exact newC (between_of_between_left hBXC' hBCX) hBXC'

/-- **An angle from beyond a straight line.** Points none of which is on the side of a
straight line where O is lie within one angle at O whose arms run to two points of that
straight line: each is seen from O through a point of the straight line, and those points lie
between two of its points. -/
theorem cone_of_line {O : Point} {ℓ : Line} (hO : ¬ OnLine O ℓ) (ws : List Point)
    (hws : ∀ W ∈ ws, ¬ SameSide W O ℓ) :
    ∃ B C : Point, OnLine B ℓ ∧ OnLine C ℓ ∧ Triangle O B C ∧
      ∀ W ∈ ws, SameSideOf W C O B ∧ SameSideOf W B O C := by
  /- Where each point is seen through the straight line. -/
  have seen : ∀ ws : List Point, (∀ W ∈ ws, ¬ SameSide W O ℓ) →
      ∃ xs : List Point, (∀ X ∈ xs, OnLine X ℓ) ∧
        ∀ W ∈ ws, ∃ X ∈ xs, X = W ∨ Between O X W := by
    intro ws
    induction ws with
    | nil => exact fun _ => ⟨[], fun _ h => absurd h List.not_mem_nil,
        fun _ h => absurd h List.not_mem_nil⟩
    | cons W ws ih =>
      intro h
      obtain ⟨xs, hxs, hws⟩ := ih fun V hV => h V (List.mem_cons_of_mem _ hV)
      obtain ⟨X, hXℓ, hX⟩ : ∃ X, OnLine X ℓ ∧ (X = W ∨ Between O X W) := by
        by_cases hW : OnLine W ℓ
        · exact ⟨W, hW, Or.inl rfl⟩
        · obtain ⟨X, hX, hb⟩ := OppositeSides.exists_between
            ⟨hO, hW, fun hs => h W List.mem_cons_self (same_side_symm hs)⟩
          exact ⟨X, hX, Or.inr hb⟩
      refine ⟨X :: xs, fun Y hY => ?_, fun V hV => ?_⟩
      · rcases List.mem_cons.mp hY with rfl | hY
        · exact hXℓ
        · exact hxs Y hY
      · rcases List.mem_cons.mp hV with rfl | hV
        · exact ⟨X, List.mem_cons_self, hX⟩
        · obtain ⟨Y, hY, h'⟩ := hws V hV
          exact ⟨Y, List.mem_cons_of_mem _ hY, h'⟩
  obtain ⟨xs, hxs, hseen⟩ := seen ws hws
  obtain ⟨B, C, hB, hC, hBC, hspan⟩ := line_span xs hxs
  have hOBC : Triangle O B C := (Triangle.of_line hB hC hBC hO).cab
  have hOB : O ≠ B := hOBC.ne₁₂
  have hOC : O ≠ C := hOBC.ne₁₃
  obtain ⟨LB, hO_B, hB_B⟩ := Postulate1 O B hOB
  obtain ⟨LC, hO_C, hC_C⟩ := Postulate1 O C hOC
  /- A point of the straight line between B and C is within the angle. -/
  have within : ∀ X ∈ xs, SameSideOf X C O B ∧ SameSideOf X B O C := by
    intro X hX
    have hBXC := hspan X hX
    have hXB : ¬ OnLine X LB := fun h => hOBC.off_line hO_B hB_B
      (on_line_of_between hBXC hB_B h)
    have hXC : ¬ OnLine X LC := fun h => hOBC.acb.off_line hO_C hC_C
      (on_line_of_between (between_symm hBXC) hC_C h)
    exact ⟨SameSideOf.of_line hOB hO_B hB_B (pasch2 hBXC hB_B hXB),
      SameSideOf.of_line hOC hO_C hC_C (pasch2 (between_symm hBXC) hC_C hXC)⟩
  refine ⟨B, C, hB, hC, hOBC, fun W hW => ?_⟩
  obtain ⟨X, hX, e | hOXW⟩ := hseen W hW
  · subst e
    exact within _ hX
  · have hray : OnRay W O X := OnRay.of_beyond hOXW
    exact ⟨SameSideOf.of_onRay hray (within X hX).1, SameSideOf.of_onRay hray (within X hX).2⟩

/-- **Behind the corner of an angle.** Produce the arms BO, CO beyond O to B'', C'';
every point within the angle BOC is on O's side of the straight line B''C'', which does not
pass through O. A point not on that side would be seen from O through a point of the
straight line within the angle; but that straight line meets the angle's arms, produced, only at
B'' and C'', behind O. -/
theorem cone_side {O B C B'' C'' : Point} (hOBC : Triangle O B C) (hB : Between B O B'')
    (hC : Between C O C'') {m : Line} (hBm : OnLine B'' m) (hCm : OnLine C'' m) :
    ¬ OnLine O m ∧ ∀ X : Point, SameSideOf X C O B → SameSideOf X B O C → SameSide X O m := by
  obtain ⟨LB, hO_B, hB_B⟩ := Postulate1 O B hOBC.ne₁₂
  obtain ⟨LC, hO_C, hC_C⟩ := Postulate1 O C hOBC.ne₁₃
  have hCB : ¬ OnLine C LB := hOBC.off_line hO_B hB_B
  have hBC : ¬ OnLine B LC := hOBC.acb.off_line hO_C hC_C
  have hB''B : OnLine B'' LB := on_line_of_between hB hB_B hO_B
  have hC''C : OnLine C'' LC := on_line_of_between hC hC_C hO_C
  have hOB'' : O ≠ B'' := (ne_of_between (between_symm hB)).symm
  have hB''C : ¬ OnLine B'' LC := fun h =>
    hBC (on_line_of_between (between_symm hB) h hO_C)
  have hC''B : ¬ OnLine C'' LB := fun h =>
    hCB (on_line_of_between (between_symm hC) h hO_B)
  have hOm : ¬ OnLine O m := fun h =>
    hC''B (line_unique hOB'' h hBm hO_B hB''B ▸ hCm)
  refine ⟨hOm, fun X hXC hXB => Classical.byContradiction fun hn => ?_⟩
  have hXC' : SameSide X C LB := hXC.sameSide hO_B hB_B
  have hXB' : SameSide X B LC := hXB.sameSide hO_C hC_C
  /- Take a point of m within the angle. -/
  obtain ⟨Y, hYm, hYC, hYB⟩ : ∃ Y, OnLine Y m ∧ SameSide Y C LB ∧ SameSide Y B LC := by
    by_cases hX : OnLine X m
    · exact ⟨X, hX, hXC', hXB'⟩
    · obtain ⟨Y, hY, hOYX⟩ :=
        OppositeSides.exists_between ⟨hOm, hX, fun hs => hn (same_side_symm hs)⟩
      have hray : OnRay Y O X := OnRay.of_between hOYX
      exact ⟨Y, hY, (SameSideOf.of_onRay hray hXC).sameSide hO_B hB_B,
        (SameSideOf.of_onRay hray hXB).sameSide hO_C hC_C⟩
  have hYLB : ¬ OnLine Y LB := not_on_line_of_same_side hYC
  have hYLC : ¬ OnLine Y LC := not_on_line_of_same_side hYB
  have hB''Y : B'' ≠ Y := fun e => hYLB (e ▸ hB''B)
  have hYC'' : Y ≠ C'' := fun e => hYLC (e ▸ hC''C)
  have hB''C'' : B'' ≠ C'' := fun e => hB''C (e ▸ hC''C)
  have oppC : ¬ SameSide C C'' LB := pasch3 hC hO_B
  have oppB : ¬ SameSide B B'' LC := pasch3 hB hO_C
  rcases between_cases hB''Y hYC'' hB''C'' hBm hYm hCm with h | h | h
  · exact oppC (same_side_trans hYC (pasch2 h hB''B hYLB))
  · exact oppB (same_side_trans hYB (same_side_symm (pasch2 (between_symm h) hC''C hB''C)))
  · exact oppC (same_side_trans hYC (same_side_symm (pasch2 h hB''B hC''B)))

/-- From a point beyond a straight line, take the angle of `cone_of_line` and the straight line
behind its corner of `cone_side`: every point not on that point's side is on that point's side
of the new straight line. -/
theorem cone_line {O : Point} {ℓ : Line} (hO : ¬ OnLine O ℓ) (ws : List Point)
    (hws : ∀ W ∈ ws, ¬ SameSide W O ℓ) :
    ∃ m : Line, ¬ OnLine O m ∧ ∀ W ∈ ws, SameSide W O m := by
  obtain ⟨B, C, -, -, hOBC, hin⟩ := cone_of_line hO ws hws
  obtain ⟨B'', hB⟩ := produce hOBC.ne₁₂.symm
  obtain ⟨C'', hC⟩ := produce hOBC.ne₁₃.symm
  have hB''C'' : B'' ≠ C'' := by
    rintro rfl
    obtain ⟨L, hO, hB''⟩ := Postulate1 O B'' (ne_of_between (between_symm hB)).symm
    exact hOBC ⟨L, hO, on_line_of_between (between_symm hB) hB'' hO,
      on_line_of_between (between_symm hC) hB'' hO⟩
  obtain ⟨m, hBm, hCm⟩ := Postulate1 B'' C'' hB''C''
  obtain ⟨hOm, hside⟩ := cone_side hOBC hB hC hBm hCm
  exact ⟨m, hOm, fun W hW => hside W (hin W hW).1 (hin W hW).2⟩

/-- **Finitely many points on one side of a straight line.** A point not on the side of the
straight line found so far is taken as the corner of `cone_line`, or, if on that straight line,
a point beyond it is. -/
theorem line_one_side : ∀ vs : List Point,
    ∃ (ℓ : Line) (R : Point), ¬ OnLine R ℓ ∧ ∀ V ∈ vs, SameSide V R ℓ
  | [] => by
    obtain ⟨A, -⟩ := exists_point []
    obtain ⟨B, hB⟩ := exists_point [A]
    have hAB : A ≠ B := fun e => hB (e ▸ List.mem_singleton_self A)
    obtain ⟨L, hA, hBL⟩ := Postulate1 A B hAB
    obtain ⟨R, hR, -⟩ := exists_off_line hAB []
    exact ⟨L, R, hR.off_line hA hBL, fun _ h => absurd h List.not_mem_nil⟩
  | V :: vs => by
    obtain ⟨ℓ, R, hR, hvs⟩ := line_one_side vs
    by_cases hV : SameSide V R ℓ
    · exact ⟨ℓ, R, hR, fun W hW => by
        rcases List.mem_cons.mp hW with rfl | hW
        · exact hV
        · exact hvs W hW⟩
    by_cases hVℓ : OnLine V ℓ
    · obtain ⟨O, hO, -⟩ := exists_point_opposite_side hR []
      obtain ⟨m, hOm, hm⟩ := cone_line hO.1 (V :: vs) fun W hW hWO => by
        rcases List.mem_cons.mp hW with rfl | hW
        · exact not_on_line_of_same_side hWO hVℓ
        · exact hO.2.2 (same_side_trans hWO (hvs W hW))
      exact ⟨m, O, hOm, hm⟩
    · obtain ⟨m, hVm, hm⟩ := cone_line hVℓ vs fun W hW hWV =>
        hV (same_side_trans hWV (hvs W hW))
      exact ⟨m, V, hVm, fun W hW => by
        rcases List.mem_cons.mp hW with rfl | hW
        · exact same_side_refl hVm
        · exact hm W hW⟩

/-! ## An enclosing triangle: where Postulate 5 enters

`outline_bounded` can fail without Postulate 5 (brief 0013, section 8), and here it enters,
in `angle_triangle` alone, twice. Its hypothesis compares angles at two different points, and
the foundations relate such angles only through superposition and Postulate 4. So an angle at
one point is copied to another, once, by I.23 (`copy_angle`), which reaches superposition only
through I.4 and I.8. -/

/-- **An angle copied to another corner.** The angle POC set up at P on the straight line
PO, on the side of it where H is: I.23 sets it up on the ray from P through O, and an
angle depends only on the rays of its arms. -/
theorem copy_angle {O P C H : Point} (hOPC : Triangle O P C) {L : Line} (hP : OnLine P L)
    (hO : OnLine O L) (hH : ¬ OnLine H L) : ∃ V : Point, SameSide V H L ∧ ∠ O P V = ∠ P O C := by
  obtain ⟨V, G, hG, hVH, hang⟩ :=
    Elements.BookI.Prop23 hOPC.ne₁₂.symm hOPC.bac (Triangle.of_line hP hO hOPC.ne₁₂.symm hH)
  have hVP : V ≠ P := hVH.triangle.ne₁₃.symm
  refine ⟨V, hVH.sameSide hP hO, ?_⟩
  rw [angle_symm hOPC.ne₁₂ hVP, ← angle_onRay_right hG hVP]
  exact hang

/-- **Through a point within an angle, a straight line meeting both arms**, so that the point is
within a triangle cut off from the angle. Set up at P on PO, towards B, the angle POC
(`copy_angle`, by I.23). Its arm and OB make with PO angles less than two right angles, for
together they are the angle BOC; so they meet, at B₂ (Postulate 5). Take B₁ beyond B₂,
and produce B₁P beyond P to W'. The angles W'PO and POC are together the angle W'PB₂,
for POC is OPB₂; so B₁P produced meets OC, at C₂ (Postulate 5 again), and P is
between B₁ and C₂. Beyond C₂ take C₁: P is within the triangle OB₁C₁. -/
theorem angle_triangle {O B C P : Point} (hPC : SameSideOf P C O B) (hPB : SameSideOf P B O C) :
    ∃ B₁ C₁ : Point, OnRay B₁ O B ∧ OnRay C₁ O C ∧ InsideTriangle P O B₁ C₁ := by
  have hOB : O ≠ B := hPC.1
  have hOC : O ≠ C := hPB.1
  obtain ⟨LB, hO_B, hB_B⟩ := Postulate1 O B hOB
  obtain ⟨LC, hO_C, hC_C⟩ := Postulate1 O C hOC
  have hP_B : SameSide P C LB := hPC.sameSide hO_B hB_B
  have hP_C : SameSide P B LC := hPB.sameSide hO_C hC_C
  have hPLB : ¬ OnLine P LB := not_on_line_of_same_side hP_B
  have hPLC : ¬ OnLine P LC := not_on_line_of_same_side hP_C
  have hCLB : ¬ OnLine C LB := not_on_line_of_same_side (same_side_symm hP_B)
  have hOP : O ≠ P := fun e => hPLB (e ▸ hO_B)
  obtain ⟨LP, hO_P, hP_P⟩ := Postulate1 O P hOP
  have hBLP : ¬ OnLine B LP := fun h => hPLB (line_unique hOB hO_P h hO_B hB_B ▸ hP_P)
  have hCLP : ¬ OnLine C LP := fun h => hPLC (line_unique hOC hO_P h hO_C hC_C ▸ hP_P)
  have hLBLC : ∀ {X : Point}, OnLine X LB → OnLine X LC → X = O := fun hXB hXC =>
    Classical.byContradiction fun hXO => hCLB (line_unique hXO hXB hO_B hXC hO_C ▸ hC_C)
  /- B and C are on opposite sides of OP (the crossbar). -/
  have hBC : ¬ SameSide B C LP := by
    obtain ⟨X, hBXC, hX⟩ := crossbar hPC hPB
    exact pasch3 hBXC (hX.onLine hO_P hP_P)
  have hBOC : Triangle B O C := hPC.symm.triangle.bac
  have hOPC : Triangle O P C := (Triangle.of_line hO_C hC_C hOC hPLC).acb
  /- A point of the straight line OB on B's side of OP is on the ray OB. -/
  have rayB : ∀ {X : Point}, OnLine X LB → SameSide X B LP → OnRay X O B := fun hX hXB =>
    OnRay.of_sameSideOf (SameSideOf.of_line hOP hO_P hP_P hXB) ⟨LB, hO_B, hB_B, hX⟩
      fun e => not_on_line_of_same_side hXB (e ▸ hO_P)
  have rayC : ∀ {X : Point}, OnLine X LC → SameSide X C LP → OnRay X O C := fun hX hXC =>
    OnRay.of_sameSideOf (SameSideOf.of_line hOP hO_P hP_P hXC) ⟨LC, hO_C, hC_C, hX⟩
      fun e => not_on_line_of_same_side hXC (e ▸ hO_P)
  /- Copy the angle POC at P, towards B. -/
  obtain ⟨V, hVB, hcopy⟩ := copy_angle hOPC hP_P hO_P hBLP
  have hVP : V ≠ P := fun e => not_on_line_of_same_side hVB (e ▸ hP_P)
  obtain ⟨LV, hP_V, hV_V⟩ := Postulate1 P V hVP.symm
  have hsum₁ : ∠ V P O + ∠ P O B < ∟ + ∟ := by
    have hadd : ∠ B O C = ∠ B O P + ∠ P O C := angle_add_of_within hPC hPB
    rw [angle_symm hVP hOP, hcopy, angle_symm hOP.symm hOB.symm, add_comm (∠ P O C), ← hadd]
    exact BookI.Prop13.angle_lt_two_right hBOC
  /- Postulate 5: the arm PV meets OB, at B₂. -/
  obtain ⟨B₂, hB₂V, hB₂B, hB₂side⟩ :=
    Postulate5 hV_V hP_V hP_P hO_P hO_B hB_B hOP.symm hVB hsum₁
  have hB₂b : SameSide B₂ B LP := same_side_trans (same_side_symm hB₂side) hVB
  have hB₂LP : ¬ OnLine B₂ LP := not_on_line_of_same_side hB₂b
  have hOB₂ : O ≠ B₂ := fun e => hB₂LP (e ▸ hO_P)
  have hPB₂ : P ≠ B₂ := fun e => hB₂LP (e ▸ hP_P)
  have hang₂ : ∠ O P B₂ = ∠ P O C := by
    have hray : OnRay B₂ P V := OnRay.of_sameSideOf
      (SameSideOf.of_line hOP.symm hP_P hO_P hB₂side) ⟨LV, hP_V, hV_V, hB₂V⟩
      hPB₂.symm
    rw [angle_onRay_right hray hOP]
    exact hcopy
  /- B₁ beyond B₂, and the straight line B₁P, produced beyond P to W'. -/
  obtain ⟨B₁, hOB₂B₁⟩ := produce hOB₂
  have hB₁B : OnLine B₁ LB := on_line_of_between hOB₂B₁ hO_B hB₂B
  have hB₁b : SameSide B₁ B LP := same_side_trans (pasch2 hOB₂B₁ hO_P hB₂LP) hB₂b
  have hB₁LP : ¬ OnLine B₁ LP := not_on_line_of_same_side hB₁b
  have hB₁P : B₁ ≠ P := fun e => hB₁LP (e ▸ hP_P)
  have hB₂B₁ : B₂ ≠ B₁ := (ne_of_between (between_symm hOB₂B₁)).symm
  obtain ⟨ℓ, hB₁ℓ, hPℓ⟩ := Postulate1 B₁ P hB₁P
  have hB₂ℓ : ¬ OnLine B₂ ℓ := fun h => hPLB (line_unique hB₂B₁ h hB₁ℓ hB₂B hB₁B ▸ hPℓ)
  obtain ⟨W', hB₁PW'⟩ := produce hB₁P
  have hW'ℓ : OnLine W' ℓ := on_line_of_between hB₁PW' hB₁ℓ hPℓ
  have hPW' : P ≠ W' := ne_of_between (between_symm hB₁PW') |>.symm
  have hW'LP : ¬ OnLine W' LP := fun h => hB₁LP (on_line_of_between (between_symm hB₁PW') h hP_P)
  have hW'c : SameSide W' C LP := by
    have h₁ : OppositeSides B₁ W' LP := ⟨hB₁LP, hW'LP, pasch3 hB₁PW' hP_P⟩
    have h₂ : OppositeSides B₁ C LP :=
      ⟨hB₁LP, hCLP, fun hs => hBC (same_side_trans hB₁b hs)⟩
    exact same_side_of_opposite_sides h₁ h₂
  /- O is within the angle W'PB₂. -/
  obtain ⟨K, hP_K, hB₂_K⟩ := Postulate1 P B₂ hPB₂
  have hKB : ∀ {X : Point}, OnLine X K → OnLine X LB → X = B₂ := fun hXK hXB =>
    Classical.byContradiction fun hX => hPLB (line_unique hX hXK hB₂_K hXB hB₂B ▸ hP_K)
  have hB₁K : ¬ OnLine B₁ K := fun h => hB₂B₁ (hKB h hB₁B).symm
  have hOK : ¬ OnLine O K := fun h => hOB₂ (hKB h hO_B)
  have hW'K : ¬ OnLine W' K := fun h =>
    hB₂ℓ (line_unique hPW' hP_K h hPℓ hW'ℓ ▸ hB₂_K)
  have hOW' : SameSide O W' K := same_side_of_opposite_sides
    ⟨hB₁K, hOK, fun hs => pasch3 hOB₂B₁ hB₂_K (same_side_symm hs)⟩
    ⟨hB₁K, hW'K, pasch3 hB₁PW' hP_K⟩
  have hsum₂ : ∠ W' P O + ∠ P O C < ∟ + ∟ := by
    have hadd : ∠ W' P B₂ = ∠ W' P O + ∠ O P B₂ := angle_add_of_within
      (SameSideOf.of_line hPW' hPℓ hW'ℓ (same_side_symm (pasch2 (between_symm hOB₂B₁) hB₁ℓ hB₂ℓ)))
      (SameSideOf.of_line hPB₂ hP_K hB₂_K hOW')
    rw [← hang₂, ← hadd]
    exact BookI.Prop13.angle_lt_two_right (Triangle.of_line hW'ℓ hPℓ hPW'.symm hB₂ℓ)
  /- Postulate 5: B₁P produced meets OC, at C₂. -/
  obtain ⟨C₂, hC₂ℓ, hC₂C, hC₂side⟩ :=
    Postulate5 hW'ℓ hPℓ hP_P hO_P hO_C hC_C hOP.symm hW'c hsum₂
  have hC₂c : SameSide C₂ C LP := same_side_trans (same_side_symm hC₂side) hW'c
  have hC₂LP : ¬ OnLine C₂ LP := not_on_line_of_same_side hC₂c
  have hOC₂ : O ≠ C₂ := fun e => hC₂LP (e ▸ hO_P)
  have hℓLP : LP ≠ ℓ := fun e => hB₁LP (e ▸ hB₁ℓ)
  have hB₁C₂ : ¬ SameSide B₁ C₂ LP := fun hs =>
    hBC (same_side_trans hB₁b (same_side_trans (same_side_symm hs) hC₂c))
  have hB₁PC₂ : Between B₁ P C₂ := pasch4 hℓLP hP_P hPℓ hB₁ℓ hC₂ℓ
    (fun e => hB₁C₂ (by rw [← e]; exact same_side_refl hB₁LP)) hB₁P
    (fun e => hC₂LP (e ▸ hP_P)) hB₁C₂
  /- Take C₁ beyond C₂. -/
  obtain ⟨C₁, hOC₂C₁⟩ := produce hOC₂
  have hC₁C : OnLine C₁ LC := on_line_of_between hOC₂C₁ hO_C hC₂C
  have hC₁c : SameSide C₁ C LP := same_side_trans (pasch2 hOC₂C₁ hO_P hC₂LP) hC₂c
  have hB₁ray : OnRay B₁ O B := rayB hB₁B hB₁b
  have hC₁ray : OnRay C₁ O C := rayC hC₁C hC₁c
  have hB₁C₁ : B₁ ≠ C₁ := fun e => hBC (same_side_trans hB₁b (e ▸ hC₁c))
  obtain ⟨K', hB₁K', hC₁K'⟩ := Postulate1 B₁ C₁ hB₁C₁
  have hC₂C₁ : C₂ ≠ C₁ := (ne_of_between (between_symm hOC₂C₁)).symm
  have hC₂K' : ¬ OnLine C₂ K' := fun h =>
    hB₁ray.2.1 (hLBLC hB₁B (line_unique hC₂C₁ h hC₁K' hC₂C hC₁C ▸ hB₁K'))
  have hPK' : ¬ OnLine P K' := fun h => by
    have e := line_unique hB₁P hB₁K' h hB₁ℓ hPℓ
    have hC₁ℓ : OnLine C₁ ℓ := e ▸ hC₁K'
    exact hPLC (line_unique hC₂C₁ hC₂ℓ hC₁ℓ hC₂C hC₁C ▸ hPℓ)
  refine ⟨B₁, C₁, hB₁ray, hC₁ray, ?_, ?_, ?_⟩
  · exact SameSideOf.of_line hB₁C₁ hB₁K' hC₁K'
      (same_side_trans (same_side_symm (pasch2 hB₁PC₂ hB₁K' hPK'))
        (pasch2 (between_symm hOC₂C₁) hC₁K' hC₂K'))
  · exact SameSideOf.of_line hC₁ray.2.1 hC₁C hO_C
      ((SameSideOf.of_onRay hB₁ray hPB.symm).symm.sameSide hO_C hC_C)
  · exact SameSideOf.of_line hB₁ray.2.1.symm hO_B hB₁B
      ((SameSideOf.of_onRay hC₁ray hPC.symm).symm.sameSide hO_B hB_B)

/-- A point within a triangle is within it still when one corner is moved out along its side
from another: within the angle at C, it is seen from C through a point between O and B,
so between O and B'. -/
theorem inside_beyond {P O B C B' : Point} (h : InsideTriangle P O B C) (hB : Between O B B') :
    InsideTriangle P O B' C := by
  obtain ⟨LB, hO_B, hB_B⟩ := Postulate1 O B (ne_of_between hB)
  have hB'B : OnLine B' LB := on_line_of_between hB hO_B hB_B
  have hOB' : O ≠ B' := ne_of_between_ends hB
  have hray : OnRay B' O B := OnRay.of_beyond hB
  have h₃ : SameSideOf P C O B' := SameSideOf.of_line hOB' hO_B hB'B (h.2.2.sameSide hO_B hB_B)
  have h₂ : SameSideOf P B' C O := (SameSideOf.of_onRay hray h.2.1.symm.swap).symm.swap
  obtain ⟨X, hOXB, hX⟩ := crossbar h.2.1 h.1.swap
  have hOXB' : Between O X B' := between_of_between_left hB hOXB
  have hCLB : ¬ OnLine C LB :=
    not_on_line_of_same_side (same_side_symm (h.2.2.sameSide hO_B hB_B))
  have hB'C : B' ≠ C := fun e => hCLB (e ▸ hB'B)
  obtain ⟨K, hB'K, hCK⟩ := Postulate1 B' C hB'C
  have hXB : OnLine X LB := on_line_of_between_ends hOXB hO_B hB_B
  have hXB' : X ≠ B' := (ne_of_between (between_symm hOXB')).symm
  have hXK : ¬ OnLine X K := fun hXK => hCLB (line_unique hXB' hXK hB'K hXB hB'B ▸ hCK)
  have hXO : SameSideOf X O C B' :=
    SameSideOf.of_line hB'C.symm hCK hB'K (pasch2 (between_symm hOXB') hB'K hXK)
  exact ⟨(SameSideOf.of_onRay hX.symm hXO).swap, h₂, h₃⟩

/-- The same, moving the third corner out along its side. -/
theorem inside_beyond' {P O B C C' : Point} (h : InsideTriangle P O B C) (hC : Between O C C') :
    InsideTriangle P O B C' := by
  have h' := inside_beyond (B := C) (C := B) ⟨h.1.swap, h.2.2.swap, h.2.1.swap⟩ hC
  exact ⟨h'.1.swap, h'.2.2.swap, h'.2.1.swap⟩

/-- Two points of one ray from O both lie between O and a third point of it. -/
theorem beyond_both {O U V X : Point} (hU : OnRay U O X) (hV : OnRay V O X) :
    ∃ W : Point, OnRay W O X ∧ Between O U W ∧ Between O V W := by
  obtain ⟨L, hO, hX⟩ := Postulate1 O X hU.1
  have hUL : OnLine U L := hU.onLine hO hX
  have hVL : OnLine V L := hV.onLine hO hX
  have out : ∀ {Y W : Point}, OnRay Y O X → Between O Y W → OnRay W O X := by
    intro Y W hY hOYW
    refine ⟨hY.1, (ne_of_between_ends hOYW).symm,
      ⟨L, hO, hX, on_line_of_between hOYW hO (hY.onLine hO hX)⟩, fun hWOX => ?_⟩
    exact hY.2.2.2 (between_symm (between_cut (between_symm hWOX) hOYW))
  by_cases e : U = V
  · subst e
    obtain ⟨W, hW⟩ := produce hU.2.1.symm
    exact ⟨W, out hU hW, hW, hW⟩
  rcases between_cases hU.2.1.symm e hV.2.1.symm hO hUL hVL with h | h | h
  · obtain ⟨W, hW⟩ := produce hV.2.1.symm
    exact ⟨W, out hV hW, between_of_between_left hW h, hW⟩
  · exact absurd h (OnRay.not_between hU hV)
  · obtain ⟨W, hW⟩ := produce hU.2.1.symm
    exact ⟨W, out hU hW, hW, between_of_between_left hW h⟩

/-- **Finitely many points within an angle lie within one triangle cut off from it**: within
the triangle of `angle_triangle` for each, so within one whose corners on the arms lie beyond all
of those. -/
theorem angle_enclosure {O B C : Point} (hOB : O ≠ B) (hOC : O ≠ C) : ∀ vs : List Point,
    (∀ V ∈ vs, SameSideOf V C O B ∧ SameSideOf V B O C) →
    ∃ B' C' : Point, OnRay B' O B ∧ OnRay C' O C ∧ ∀ V ∈ vs, InsideTriangle V O B' C'
  | [], _ => ⟨B, C, OnRay.self hOB, OnRay.self hOC, fun _ h => absurd h List.not_mem_nil⟩
  | V :: vs, h => by
    obtain ⟨B', C', hB', hC', hvs⟩ :=
      angle_enclosure hOB hOC vs fun U hU => h U (List.mem_cons_of_mem _ hU)
    obtain ⟨B₁, C₁, hB₁, hC₁, hV⟩ := angle_triangle (h V List.mem_cons_self).1
      (h V List.mem_cons_self).2
    obtain ⟨B'', hB'', h₁, h₂⟩ := beyond_both hB' hB₁
    obtain ⟨C'', hC'', h₃, h₄⟩ := beyond_both hC' hC₁
    refine ⟨B'', C'', hB'', hC'', fun U hU => ?_⟩
    rcases List.mem_cons.mp hU with rfl | hU
    · exact inside_beyond' (inside_beyond hV h₂) h₄
    · exact inside_beyond' (inside_beyond (hvs U hU) h₁) h₃

/-- **An enclosing triangle for finitely many points.** They lie on one side of a straight line
(`line_one_side`), so within an angle at a point beyond it (`cone_of_line`), so within a triangle
cut off from that angle (`angle_enclosure`, by Postulate 5 and I.23). -/
theorem enclosing_triangle (vs : List Point) :
    ∃ A B C : Point, Triangle A B C ∧ ∀ V ∈ vs, InsideTriangle V A B C := by
  obtain ⟨ℓ, R, hR, hvs⟩ := line_one_side vs
  obtain ⟨O, hO, -⟩ := exists_point_opposite_side hR []
  obtain ⟨B, C, -, -, hOBC, hin⟩ := cone_of_line hO.1 vs fun V hV hVO =>
    hO.2.2 (same_side_trans hVO (hvs V hV))
  obtain ⟨B', C', hB', hC', hall⟩ := angle_enclosure hOBC.ne₁₂ hOBC.ne₁₃ vs hin
  obtain ⟨LB, hO_B, hB_B⟩ := Postulate1 O B hOBC.ne₁₂
  obtain ⟨LC, hO_C, hC_C⟩ := Postulate1 O C hOBC.ne₁₃
  have hC'B : ¬ OnLine C' LB := fun h =>
    hOBC.off_line hO_B hB_B (line_unique hC'.2.1 h hO_B (hC'.onLine hO_C hC_C) hO_C ▸ hC_C)
  exact ⟨O, B', C', Triangle.of_line hO_B (hB'.onLine hO_B hB_B) hB'.2.1.symm hC'B, hall⟩

end OutlineBound

/-- **A figure given by its outline is bounded**: some triangle holds its whole region. -/
theorem outline_bounded (F : Outline) :
    ∃ A B C : Point, Triangle A B C ∧
      ∀ X : Point, F.Region X → InsideTriangle X A B C := by
  /- The corners lie on one side of a straight line, so within an angle at a point beyond it,
  and so within a triangle cut off from that angle, by Postulate 5, with an angle copied by
  I.23 (`OutlineBound.enclosing_triangle`). A triangle holding every corner holds the
  whole region (`OutlineFacts.bounded_of_enclosure`). -/
  obtain ⟨A, B, C, h, hin⟩ := OutlineBound.enclosing_triangle F.loops.flatten
  exact ⟨A, B, C, h, OutlineFacts.bounded_of_enclosure F fun ps hps V hV =>
    hin V (List.mem_flatten.mpr ⟨ps, hps, hV⟩)⟩

end Elements.Figures
