import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop02
import Elements.BookI.Prop08
import Elements.BookI.HelpersTriangles
import Elements.BookIII.MixedAngles
import Elements.BookIII.Prop09
import Elements.BookI.Prop04
import Elements.BookIII.Prop02
import Elements.BookIII.Prop20
import Elements.BookIII.Prop22
import Elements.BookIII.Prop24

/-!
# Book III, Proposition 26

Euclid's text, in Heath's translation: [`heath/III/26.md`](../../heath/III/26.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Each clause concludes that the circumferences are equal in measure and congruent
(`Arc.Congruent`): "equal circumferences" is read as both, which says more than Heath's
words, equal circumferences being read through Common Notion 4 as circumferences that
coincide. So "in equal circles" does real work: in unequal circles equal angles give no
congruence.

Heath: "As in III. 21, if Euclid's proof is to cover all cases, it requires us to take
cognisance of 'angles at the centre' which are equal to or greater than two right angles.
Otherwise we must deal separately with the cases where the angle at the circumference is
equal to or greater than a right angle" (vol. 2, p. 57). Here the angles at the centres are
`angleAtCentre`, with III.20 in `Elements/BookIII/Prop20.lean`, and may be two right angles
or more, a reading that is ours, after Heath's notes, and not Euclid's. The proof follows
Euclid's steps with the additional cases at I.4 described below. Equal angles at the circumferences give equal angles at the
centres, their doubles (III.20); the bases are equal by I.4; the segments are similar and on
equal straight lines, so equal [III. 24], and their circumferences equal in measure
(`Prop24.equalMeasure`); and the circumferences that remain are equal in measure, the wholes
being equal [C.N. 3]. One division into cases stays, at I.4, labelled where it stands: where
the angles at the centres are two right angles, BC and EF are diameters, and there are no
triangles for I.4; where they are greater, I.4 applies to the angles BGC, EHF that remain of
four right angles. The whole circle is four right angles (`Circumference.whole`). The
congruence of the remainders BKC, ELF follows by the same subtraction. The given map of
BAC onto EDF extends radially from an interior neighbourhood to a distance-preserving
map of the plane, onto by the reverse construction (`Prop26.extend_places`). III.9
identifies the image of the centre; Definition I.15 and the radius comparisons carry the
whole circle and disk across (`Prop26.extend`). The same map keeps the sides of the chord,
so restricting it to the remaining segments proves their congruence (`Prop26.remainder`).
No comparison of angles in the remaining segments is needed. The obtuse inscribed-angle
case still differs from Euclid's written argument: I.4 uses the ordinary angles left from
the reflex central angles, as Heath's discussion on p. 57 requires.
-/

namespace Elements.BookIII

open Tacit

/-- A small circle within the segment supplies short rays for the application of the
whole circle in III.26. III.2 puts an interior point between an end and a point of the arc;
the neighbourhood rules keep it within the circle and on the required side. -/
theorem Prop26.segment_surrounds {A B C : Point} {α : Circle}
    (hB : OnCircle B α) (hC : OnCircle C α) (hA : Triangle B C A) :
    ∃ O, Surrounds (InSegment · ⟨α, B, C, A⟩) O := by
  obtain ⟨X, hX, hXA⟩ := Prop2.sameSide hB hC hA
  obtain ⟨L, hBL, hXL⟩ := Postulate1 B X hXA.triangle.ne₁₃
  obtain ⟨O, -, hBOX, -⟩ := exists_point_between hBL hXL hXA.triangle.ne₁₃ []
  have hO := Prop2 hB hX O hBOX
  obtain ⟨N, hBN, hCN⟩ := Postulate1 B C hA.ne₁₂
  have hOA := SameSideOf.of_between_line ⟨N, hBN, hCN, hBN⟩ hXA hBOX
  obtain ⟨δ, hδ, hs⟩ := (surrounds_inside hO).and (surrounds_sameSideOf hOA)
  exact ⟨O, δ, hδ, fun P hP => ⟨Or.inl (hs P hP).1, Or.inl (hs P hP).2⟩⟩

/-- Distances decide a ray as well as its straight line, by I.20's collinear cases.
This carries short rays of the given segment into the corresponding segment before
extending their lengths for III.26's whole-circle application. -/
theorem Prop26.ray_congr {O X P O' X' P' : Point}
    (hOX : ‖O X‖ = ‖O' X'‖) (hOP : ‖O P‖ = ‖O' P'‖)
    (hXP : ‖X P‖ = ‖X' P'‖) : OnRay P O X ↔ OnRay P' O' X' := by
  have hne : ∀ {U V U' V' : Point}, ‖U V‖ = ‖U' V'‖ → (U ≠ V ↔ U' ≠ V') := by
    intro U V U' V' h
    constructor
    · intro hn he
      exact hn (eq_of_len_eq_zero (by rw [h, he, len_self]))
    · intro hn he
      exact hn (eq_of_len_eq_zero (by rw [← h, he, len_self]))
  have hb : Between P O X ↔ Between P' O' X' :=
    BookI.Prop20.between_congr (by simpa only [len_symm] using hXP)
      (by simpa only [len_symm] using hOP) (by simpa only [len_symm] using hOX)
  exact and_congr (hne hOX) (and_congr (by simpa only [ne_comm] using hne hOP)
    (and_congr (BookI.Prop20.collinear_congr hOX hOP hXP) (not_congr hb)))

/-- Two lengths laid along one ray keep the distance between their ends. The nearer
end is between the start and the farther end, so Common Notion 3 supplies the distance.
This treats coincident directions in III.26's radial extension. -/
theorem Prop26.same_ray_distance {O X P Q O' X' P' Q' : Point}
    (hP : OnRay P O X) (hQ : OnRay Q O X)
    (hP' : OnRay P' O' X') (hQ' : OnRay Q' O' X')
    (hp : ‖O P‖ = ‖O' P'‖) (hq : ‖O Q‖ = ‖O' Q'‖) :
    ‖P Q‖ = ‖P' Q'‖ := by
  have step : ∀ {P Q P' Q' : Point}, OnRay P O X → OnRay Q O X →
      OnRay P' O' X' → OnRay Q' O' X' → ‖O P‖ = ‖O' P'‖ →
      ‖O Q‖ = ‖O' Q'‖ → ‖O P‖ < ‖O Q‖ → ‖P Q‖ = ‖P' Q'‖ := by
    intro P Q P' Q' hP hQ hP' hQ' hp hq hlt
    have hb := hP.between_of_len_lt hQ hlt
    have hb' := hP'.between_of_len_lt hQ' (by rw [← hp, ← hq]; exact hlt)
    apply CommonNotion3 (c := ‖O P‖) (d := ‖O' P'‖) _ hp
    rw [add_comm, len_add_of_between hb, hq, add_comm, len_add_of_between hb']
  rcases lt_trichotomy ‖O P‖ ‖O Q‖ with hlt | heq | hgt
  · exact step hP hQ hP' hQ' hp hq hlt
  · have e := (hP.of_sameRay hQ).eq_of_len_eq heq
    have e' := (hP'.of_sameRay hQ').eq_of_len_eq (hp.symm.trans (heq.trans hq))
    rw [e, e', len_self, len_self]
  · simpa only [len_symm] using step hQ hP hQ' hP' hq hp hgt

/-- Extending two short rays keeps the distance between their ends: I.8 supplies their
angle and I.4 supplies the new base. Collinear rays use addition or subtraction of
lengths. This is the distance calculation needed when III.26 applies a whole circle. -/
theorem Prop26.radial_distance {O X Y P Q O' X' Y' P' Q' : Point}
    (hP : OnRay P O X) (hQ : OnRay Q O Y)
    (hP' : OnRay P' O' X') (hQ' : OnRay Q' O' Y')
    (hx : ‖O X‖ = ‖O' X'‖) (hy : ‖O Y‖ = ‖O' Y'‖)
    (hxy : ‖X Y‖ = ‖X' Y'‖)
    (hp : ‖O P‖ = ‖O' P'‖) (hq : ‖O Q‖ = ‖O' Q'‖) :
    ‖P Q‖ = ‖P' Q'‖ := by
  by_cases ht : Collinear O X Y
  · by_cases hb : Between Y O X
    · have hb' : Between Y' O' X' :=
        (BookI.Prop20.between_congr (by simpa only [len_symm] using hxy)
          (by simpa only [len_symm] using hy)
          (by simpa only [len_symm] using hx)).mp hb
      have b := hQ.between (between_symm (hP.between hb))
      have b' := hQ'.between (between_symm (hP'.between hb'))
      rw [← len_add_of_between b, ← len_add_of_between b', len_symm P O,
        len_symm P' O', hp, hq]
    · have hr : OnRay Y O X := ⟨hP.1, hQ.1.symm, ht, hb⟩
      have hr' := (Prop26.ray_congr hx hy hxy).mp hr
      exact Prop26.same_ray_distance hP (hQ.of_sameRay hr.symm)
        hP' (hQ'.of_sameRay hr'.symm) hp hq
  · have ht' : Triangle O' X' Y' := fun h => ht ((BookI.Prop20.collinear_congr hx hy hxy).mpr h)
    have triangle : ∀ {O X Y P Q : Point}, Triangle O X Y →
        OnRay P O X → OnRay Q O Y → Triangle O P Q := by
      intro O X Y P Q ht hP hQ hc
      obtain ⟨L, hO, hP_L, hQ_L⟩ := hc
      exact ht ⟨L, hO, hP.symm.onLine hO hP_L, hQ.symm.onLine hO hQ_L⟩
    exact (BookI.Prop4 (triangle ht hP hQ) (triangle ht' hP' hQ') hp hq
      ((angle_eq_of_onRay hP hQ).trans
        ((BookI.Prop8 ht ht' hx hy hxy).trans (angle_eq_of_onRay hP' hQ').symm))).1

/-- The map of a segment extends radially from a point surrounded by that segment.
Short representatives determine each direction, I.2 supplies the required length, and
I.8 with I.4 keep all distances. This supplies the distance-preserving application
needed before III.26 subtracts the equal parts; surjectivity is proved separately. -/
theorem Prop26.radial_extension {S : Point → Prop} {f : Point → Point} {O : Point}
    (hs : Surrounds S O)
    (hd : ∀ P Q, S P → S Q → ‖(f P) (f Q)‖ = ‖P Q‖) :
    ∃ g : Point → Point, (∀ P Q, ‖(g P) (g Q)‖ = ‖P Q‖) ∧
      ∀ P, S P → g P = f P := by
  classical
  obtain ⟨δ, hδ, hδS⟩ := hs
  have hO : S O := hδS O (centre_inside hδ)
  have hne : ∀ {P Q}, S P → S Q → P ≠ Q → f P ≠ f Q := by
    intro P Q hP hQ hn e
    exact hn (eq_of_len_eq_zero (by rw [← hd P Q hP hQ, e, len_self]))
  have choose_image : ∀ P, P ≠ O → ∃ R, ∃ X,
      S X ∧ OnRay X O P ∧ OnRay R (f O) (f X) ∧ ‖(f O) R‖ = ‖O P‖ := by
    intro P hPO
    obtain ⟨X, hX, hXin⟩ := exists_onRay_inside hδ hPO.symm
    have hXS := hδS X hXin
    obtain ⟨U, hU⟩ := BookI.Prop2 (f O) O P hPO.symm
    have hOU : f O ≠ U := fun e => hPO.symm (eq_of_len_eq_zero (by rw [← hU, e, len_self]))
    obtain ⟨R, hR, hlen⟩ := OnRay.exists_len_eq hOU (hne hO hXS hX.2.1.symm)
    exact ⟨R, X, hXS, hX, hR, hlen.trans hU⟩
  let g : Point → Point := fun P => if h : P = O then f O else (choose_image P h).choose
  have gO : g O = f O := by simp only [g, dite_eq_left rfl]
  have spec : ∀ P, P ≠ O → ∃ X, S X ∧ OnRay X O P ∧
      OnRay (g P) (f O) (f X) ∧ ‖(f O) (g P)‖ = ‖O P‖ := by
    intro P hn
    simpa only [g, dite_eq_right hn] using (choose_image P hn).choose_spec
  have distance : ∀ P Q, ‖(g P) (g Q)‖ = ‖P Q‖ := by
    intro P Q
    by_cases hp : P = O
    · subst P
      rw [gO]
      by_cases hq : Q = O
      · subst Q; rw [gO, len_self, len_self]
      · exact (spec Q hq).choose_spec.2.2.2
    by_cases hq : Q = O
    · subst Q
      rw [gO, len_symm (g P), len_symm P]
      exact (spec P hp).choose_spec.2.2.2
    obtain ⟨X, hXS, hX, hP', hp'⟩ := spec P hp
    obtain ⟨Y, hYS, hY, hQ', hq'⟩ := spec Q hq
    exact (Prop26.radial_distance hX.symm hY.symm hP' hQ'
      (hd O X hO hXS).symm (hd O Y hO hYS).symm (hd X Y hXS hYS).symm
      hp'.symm hq'.symm).symm
  refine ⟨g, distance, ?_⟩
  intro P hPS
  by_cases hp : P = O
  · subst P; exact gO
  obtain ⟨X, hXS, hX, hP', hp'⟩ := spec P hp
  have hr : OnRay (f P) (f O) (f X) :=
    (Prop26.ray_congr (hd O X hO hXS).symm (hd O P hO hPS).symm
      (hd X P hXS hPS).symm).mp hX.symm
  exact (hP'.of_sameRay hr).eq_of_len_eq (hp'.trans (hd O P hO hPS).symm)

/-- An application fixing a neighbourhood fixes every point. The short point on the
ray to a given point stays fixed; I.20 carries that ray across and its distance fixes
the endpoint. This makes the two radial applications inverse in III.26. -/
theorem Prop26.fixed_of_surrounds {S : Point → Prop} {f : Point → Point} {O : Point}
    (hs : Surrounds S O) (hd : ∀ P Q, ‖(f P) (f Q)‖ = ‖P Q‖)
    (hf : ∀ P, S P → f P = P) : ∀ P, f P = P := by
  obtain ⟨δ, hδ, hδS⟩ := hs
  have eO := hf O (hδS O (centre_inside hδ))
  intro P
  by_cases hp : P = O
  · subst P; exact eO
  obtain ⟨X, hX, hXin⟩ := exists_onRay_inside hδ (Ne.symm hp)
  have eX := hf X (hδS X hXin)
  have hr := (Prop26.ray_congr (hd O X).symm (hd O P).symm (hd X P).symm).mp hX.symm
  rw [eO, eX] at hr
  exact (hr.of_sameRay hX.symm).eq_of_len_eq (by simpa only [eO] using hd O P)

/-- The given application and its inverse both extend to the plane. Their composite on the target
fixes a neighbourhood and hence all points, so the extension is onto. This justifies
using one application for both the whole circles and their removed parts in III.26. -/
theorem Prop26.extend_places {S T : Point → Prop} {f : Point → Point}
    (hf : Places f S T) (hS : ∃ O, Surrounds S O) (hT : ∃ O, Surrounds T O) :
    ∃ g : Point → Point, Places g (fun _ => True) (fun _ => True) ∧
      ∀ P, S P → g P = f P := by
  classical
  obtain ⟨O, hO⟩ := hS
  obtain ⟨O', hO'⟩ := hT
  obtain ⟨g, gd, gf⟩ := Prop26.radial_extension hO hf.2.2
  haveI : Nonempty Point := ⟨O⟩
  let k : Point → Point := fun Q => Classical.epsilon (fun P => S P ∧ f P = Q)
  have hk : ∀ Q, T Q → S (k Q) ∧ f (k Q) = Q := by
    intro Q hQ
    exact Classical.epsilon_spec (hf.2.1 Q hQ)
  have kd : ∀ P Q, T P → T Q → ‖(k P) (k Q)‖ = ‖P Q‖ := by
    intro P Q hP hQ
    rw [← hf.2.2 (k P) (k Q) (hk P hP).1 (hk Q hQ).1, (hk P hP).2, (hk Q hQ).2]
  obtain ⟨j, jd, jk⟩ := Prop26.radial_extension hO' kd
  have gj : ∀ Q, g (j Q) = Q := by
    apply Prop26.fixed_of_surrounds hO'
      (fun P Q => (gd (j P) (j Q)).trans (jd P Q))
    intro Q hQ
    rw [jk Q hQ, gf (k Q) (hk Q hQ).1, (hk Q hQ).2]
  exact ⟨g, ⟨fun _ _ => True.intro, fun Q _ => ⟨j Q, True.intro, gj Q⟩,
    fun P Q _ _ => gd P Q⟩, gf⟩

/-- The whole-plane application keeps the sides of a chord. I.20 carries collinearity
and betweenness across; a crossing of the chord would give a crossing before the
application. This identifies the part to be removed in III.26's subtraction. -/
theorem Prop26.same_side {f : Point → Point}
    (hf : Places f (fun _ => True) (fun _ => True)) {A B P Q : Point}
    (hAB : A ≠ B) : SameSideOf P Q A B ↔ SameSideOf (f P) (f Q) (f A) (f B) := by
  have hd : ∀ X Y, ‖(f X) (f Y)‖ = ‖X Y‖ := fun X Y => hf.2.2 X Y trivial trivial
  have hAB' : f A ≠ f B := fun e => hAB (eq_of_len_eq_zero (by rw [← hd A B, e, len_self]))
  have hc : ∀ X, Collinear A B X ↔ Collinear (f A) (f B) (f X) := fun X =>
    BookI.Prop20.collinear_congr (hd A B).symm (hd A X).symm (hd B X).symm
  have hb : ∀ X, Between P X Q ↔ Between (f P) (f X) (f Q) := fun X =>
    BookI.Prop20.between_congr (hd P Q).symm (hd P X).symm (hd Q X).symm
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hAB
  obtain ⟨M, hAM, hBM⟩ := Postulate1 (f A) (f B) hAB'
  constructor
  · intro hs
    apply Classical.byContradiction
    intro hn
    have hP' : Triangle (f A) (f B) (f P) := fun h => hs.triangle ((hc P).mpr h)
    have hQ' : Triangle (f A) (f B) (f Q) := fun h => hs.symm.triangle ((hc Q).mpr h)
    have ho := oppositeSidesOf_of_not_sameSideOf hP' (sameSideOf_self hQ') hn
    obtain ⟨Y, hYM, hPYQ⟩ := (ho.oppositeSides hAM hBM).exists_between
    obtain ⟨X, -, rfl⟩ := hf.2.1 Y trivial
    have hXL := onLine_of_collinear hAB ((hc X).mpr ⟨M, hAM, hBM, hYM⟩) hAL hBL
    exact pasch3 ((hb X).mpr hPYQ) hXL (hs.sameSide hAL hBL)
  · intro hs
    apply Classical.byContradiction
    intro hn
    have hP : Triangle A B P := fun h => hs.triangle ((hc P).mp h)
    have hQ : Triangle A B Q := fun h => hs.symm.triangle ((hc Q).mp h)
    have ho := oppositeSidesOf_of_not_sameSideOf hP (sameSideOf_self hQ) hn
    obtain ⟨X, hXL, hPXQ⟩ := (ho.oppositeSides hAL hBL).exists_between
    have hXM := onLine_of_collinear hAB' ((hc X).mp ⟨L, hAL, hBL, hXL⟩) hAM hBM
    exact pasch3 ((hb X).mp hPXQ) hXM (hs.sameSide hAM hBM)

/-- The closed side of the remaining segment is what remains on removing the open side
of the first segment. The base belongs to both closed segments. -/
theorem Prop26.remaining_side {A B C K P : Point} (hAK : OppositeSidesOf A K B C) :
    OnSideOrLine P K B C ↔ ¬ SameSideOf P A B C := by
  constructor
  · rintro (hPK | hline) hPA
    · obtain ⟨N, hB, hC⟩ := Postulate1 B C hAK.1
      exact (hAK.oppositeSides hB hC).2.2 ((hPA.symm.trans hPK).sameSide hB hC)
    · exact hPA.triangle hline
  · intro hPA
    by_cases hline : Collinear B C P
    · exact Or.inr hline
    · have hPA' := oppositeSidesOf_of_not_sameSideOf hline (sameSideOf_self hAK.triangle) hPA
      exact Or.inl (OppositeSidesOf.sameSideOf hPA'.symm hAK)

/-- **The whole circles placed together with the equal parts.** Euclid subtracts BAC
and EDF from their equal circles (Heath, vol. 2, pp. 56–57). Extend their given congruence
radially from an interior neighbourhood, using I.2, I.4, I.8 and I.20. The reverse
construction makes the extension onto. Three points of the given arc then identify the
image of its centre by III.9; Definition I.15 and the radius rules carry the whole circle
and disk across. Collinearity and betweenness keep the sides of the chord.

The given congruence controls its witness only on the segment and arc. This constructs a
new map agreeing there, and proves the whole-circle application that the subtraction takes
for granted. It compares no angles of the remaining segments. -/
theorem Prop26.extend {A B C D E F : Point} {ABC DEF : Circle}
    (hB : OnCircle B ABC) (hC : OnCircle C ABC)
    (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hA : Triangle B C A) (hD : Triangle E F D)
    (hseg : Arc.Congruent ⟨ABC, B, C, A⟩ ⟨DEF, E, F, D⟩) :
    ∃ f : Point → Point, f B = E ∧ f C = F ∧
      Places f (fun P => InsideCircle P ABC ∨ OnCircle P ABC)
        (fun P => InsideCircle P DEF ∨ OnCircle P DEF) ∧
      Places f (OnCircle · ABC) (OnCircle · DEF) ∧
      (∀ P, SameSideOf P A B C ↔ SameSideOf (f P) D E F) := by
  obtain ⟨f, hfB, hfC, hsegment, harc⟩ := hseg
  obtain ⟨g, hg, hgf⟩ := Prop26.extend_places hsegment
    (Prop26.segment_surrounds hB hC hA) (Prop26.segment_surrounds hE hF hD)
  have hd : ∀ P Q, ‖(g P) (g Q)‖ = ‖P Q‖ := fun P Q => hg.2.2 P Q trivial trivial
  obtain ⟨N, hBN, hCN⟩ := Postulate1 B C hA.ne₁₂
  have hBa : InSegment B ⟨ABC, B, C, A⟩ := ⟨Or.inr hB, Or.inr ⟨N, hBN, hCN, hBN⟩⟩
  have hCa : InSegment C ⟨ABC, B, C, A⟩ := ⟨Or.inr hC, Or.inr ⟨N, hBN, hCN, hCN⟩⟩
  have hgB : g B = E := (hgf B hBa).trans hfB
  have hgC : g C = F := (hgf C hCa).trans hfC
  obtain ⟨X, hX, hXA⟩ := Prop2.sameSide hB hC hA
  have hXs : InSegment X ⟨ABC, B, C, A⟩ := ⟨Or.inr hX, Or.inl hXA⟩
  have hXarc : OnArc (g X) ⟨DEF, E, F, D⟩ := by
    rw [hgf X hXs]
    exact harc.1 X ⟨hX, Or.inl hXA⟩
  have hXtri : Triangle E F (g X) := by
    rw [← hgB, ← hgC]
    exact fun h => hXA.triangle
      ((BookI.Prop20.collinear_congr (hd B C).symm (hd B X).symm (hd C X).symm).mpr h)
  have hXD : SameSideOf (g X) D E F := hXarc.2.resolve_right hXtri
  obtain ⟨O, hO⟩ := exists_centre ABC
  have hcentre : Centre (g O) DEF := by
    apply Prop9 hE hF hXarc.1 hXtri.ne₁₂ hXtri.ne₂₃ hXtri.ne₁₃
    · rw [← hgB, ← hgC, hd, hd]
      exact Definition15 hO hB hC
    · rw [← hgC, hd, hd]
      exact Definition15 hO hC hX
  have hcircle : ∀ P, OnCircle P ABC ↔ OnCircle (g P) DEF := by
    intro P
    constructor
    · intro hP
      apply on_circle_of_len_eq hcentre hE
      rw [← hgB, hd, hd]
      exact Definition15 hO hP hB
    · intro hP
      apply on_circle_of_len_eq hO hB
      rw [← hd O P, ← hd O B, hgB]
      exact Definition15 hcentre hP hE
  have hinside : ∀ P, InsideCircle P ABC ↔ InsideCircle (g P) DEF := by
    intro P
    constructor
    · intro hP
      apply inside_of_len_lt hcentre hE
      rw [← hgB, hd, hd]
      exact len_lt_of_inside hO hB hP
    · intro hP
      apply inside_of_len_lt hO hB
      rw [← hd O P, ← hd O B, hgB]
      exact len_lt_of_inside hcentre hE hP
  refine ⟨g, hgB, hgC, ⟨?_, ?_, fun P Q _ _ => hd P Q⟩,
    ⟨fun P hP => (hcircle P).mp hP, ?_, fun P Q _ _ => hd P Q⟩, ?_⟩
  · intro P hP
    exact (or_congr (hinside P) (hcircle P)).mp hP
  · intro Q hQ
    obtain ⟨P, -, rfl⟩ := hg.2.1 Q trivial
    exact ⟨P, (or_congr (hinside P) (hcircle P)).mpr hQ, rfl⟩
  · intro Q hQ
    obtain ⟨P, -, rfl⟩ := hg.2.1 Q trivial
    exact ⟨P, (hcircle P).mpr hQ, rfl⟩
  · intro P
    have hs := Prop26.same_side hg (P := P) (Q := X) hA.ne₁₂
    rw [hgB, hgC] at hs
    exact ⟨fun h => ((hs.mp (h.trans hXA.symm)).trans hXD),
      fun h => (hs.mpr (h.trans hXD.symm)).trans hXA⟩

/-- Equal parts removed from whole circles placed together leave congruent remainders.
The restriction of the common map, including its surjectivity and preservation of
distances, supplies both the remaining segments and their circumferences. -/
theorem Prop26.remainder {A B C D E F K L : Point} {ABC DEF : Circle}
    (hB : OnCircle B ABC) (hC : OnCircle C ABC)
    (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F)
    (hseg : Arc.Congruent ⟨ABC, B, C, A⟩ ⟨DEF, E, F, D⟩) :
    Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩ := by
  obtain ⟨f, hfB, hfC, hdisk, hcircle, hside⟩ :=
    Prop26.extend hB hC hE hF hAK.triangle hDL.triangle hseg
  have hremaining : ∀ P, OnSideOrLine P K B C ↔ OnSideOrLine (f P) L E F := by
    intro P
    rw [Prop26.remaining_side hAK, Prop26.remaining_side hDL]
    exact not_congr (hside P)
  refine ⟨f, hfB, hfC, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rintro P ⟨hP, hPK⟩
    exact ⟨hdisk.1 P hP, (hremaining P).mp hPK⟩
  · rintro Q ⟨hQ, hQL⟩
    obtain ⟨P, hP, rfl⟩ := hdisk.2.1 Q hQ
    exact ⟨P, ⟨hP, (hremaining P).mpr hQL⟩, rfl⟩
  · intro P Q hP hQ
    exact hdisk.2.2 P Q hP.1 hQ.1
  · rintro P ⟨hP, hPK⟩
    exact ⟨hcircle.1 P hP, (hremaining P).mp hPK⟩
  · rintro Q ⟨hQ, hQL⟩
    obtain ⟨P, hP, rfl⟩ := hcircle.2.1 Q hQ
    exact ⟨P, ⟨hP, (hremaining P).mpr hQL⟩, rfl⟩
  · intro P Q hP hQ
    exact hcircle.2.2 P Q hP.1 hQ.1


/-- **Equal angles at the centres lie alike.** If the angle at the centre G standing on
the circumference BKC is equal to the angle at the centre H standing on ELF, then G and H
lie alike: both on the other sides of BC and EF from K and L, both on BC and EF, or both
on K's and L's sides. For an angle at the centre is less than two right angles, two right
angles, or greater, as its centre lies (`angleAtCentre.size`). Euclid's figure draws the
first; this is the step that tells us which case we are in: I.4 on the angles at the
centres, no triangles at all, or I.4 on what remains of four right angles. -/
theorem Prop26.alike {B C E F G H K L : Point} {α β : Circle} (hG : Centre G α)
    (hB : OnCircle B α) (hC : OnCircle C α) (hK : Triangle B C K) (hH : Centre H β)
    (hE : OnCircle E β) (hF : OnCircle F β) (hL : Triangle E F L)
    (h : angleAtCentre α B K C = angleAtCentre β E L F) :
    (OppositeSidesOf G K B C ∧ OppositeSidesOf H L E F) ∨ (Between B G C ∧ Between E H F) ∨
      (SameSideOf G K B C ∧ SameSideOf H L E F) := by
  rcases angleAtCentre.size hG hB hC hK with ⟨hG', h₁⟩ | ⟨hG', h₁⟩ | ⟨hG', h₁⟩ <;>
    rcases angleAtCentre.size hH hE hF hL with ⟨hH', h₂⟩ | ⟨hH', h₂⟩ | ⟨hH', h₂⟩
  · exact Or.inl ⟨hG', hH'⟩
  · rw [h, h₂] at h₁; exact absurd h₁ (lt_irrefl _)
  · rw [h] at h₁; exact absurd (lt_trans h₁ h₂) (lt_irrefl _)
  · rw [← h, h₁] at h₂; exact absurd h₂ (lt_irrefl _)
  · exact Or.inr (Or.inl ⟨hG', hH'⟩)
  · rw [← h, h₁] at h₂; exact absurd h₂ (lt_irrefl _)
  · rw [h] at h₁; exact absurd (lt_trans h₁ h₂) (lt_irrefl _)
  · rw [h, h₂] at h₁; exact absurd h₁ (lt_irrefl _)
  · exact Or.inr (Or.inr ⟨hG', hH'⟩)

/-- In equal circles equal angles stand on equal circumferences, whether they stand at the centres
or at the circumferences. -/
theorem Prop26 {A B C D E F G H K L : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :
    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩) ∧
    (∠ B A C = ∠ E D F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩) := by
  -- Let ABC, DEF be equal circles, and in them let there be equal angles, namely at the
  -- centres the angles BGC, EHF, and at the circumferences the angles BAC, EDF;
  -- I say that the circumference BKC is equal to the circumference ELF.
  /- As Euclid sets it out, we take both pairs of equal angles together. "The angles BGC,
     EHF" at the centres are the angles at the centres standing on the circumferences BKC
     and ELF (`angleAtCentre`), of any size: if Euclid's proof is to cover all cases, Heath
     says, "it requires us to take cognisance of 'angles at the centre' which are equal to
     or greater than two right angles" (vol. 2, p. 57). Our statement gives one pair at a
     time, and the other comes from III.20 at the end, under "Therefore etc." -/
  have euclid : angleAtCentre ABC B K C = angleAtCentre DEF E L F → ∠ B A C = ∠ E D F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩ := by
    intro hGH hAD
    -- For let BC, EF be joined.
    have hBCA : Triangle B C A := hAK.triangle
    have hEFD : Triangle E F D := hDL.triangle
    -- Now, since the circles ABC, DEF are equal,
    -- the radii are equal.
    have hGB : ‖G B‖ = ‖H E‖ := hcircles.radii hG hH hB hE
    have hGC : ‖G C‖ = ‖H F‖ := hcircles.radii hG hH hC hF
    -- Thus the two straight lines BG, GC are equal to the two straight lines EH, HF;
    -- and the angle at G is equal to the angle at H;
    /- "Thus …" gathers the radii just found, which I.4 uses below. The angles at G and
       H, being equal, are alike: both less than two right angles, both two right angles,
       or both greater, and so G and H lie alike (`Prop26.alike`). Euclid's figure has the
       first. -/
    have halike := Prop26.alike hG hB hC hAK.symm.triangle hH hE hF hDL.symm.triangle hGH
    -- therefore the base BC is equal to the base EF. [I. 4]
    have hBC : ‖B C‖ = ‖E F‖ := by
      rcases halike with ⟨hGK, hHL⟩ | ⟨hBGC, hEHF⟩ | ⟨hGK, hHL⟩
      · /- Euclid's figure: the angles at the centres are the angles BGC, EHF of the
           triangles GBC, HEF (`angleAtCentre.within`), and I.4 gives the bases. -/
        have hang : ∠ B G C = ∠ E H F := by
          rw [← angleAtCentre.within hG hB hC hGK, ← angleAtCentre.within hH hE hF hHL]
          exact hGH
        exact (BookI.Prop4 hGK.triangle.cab hHL.triangle.cab hGB hGC hang).1
      · /- A case Euclid's figure leaves aside: the angles at the centres are two right
           angles, G is on BC and H on EF, and there are no triangles for I.4. BC and EF
           are diameters, each two radii, and so equal. -/
        rw [← len_add_of_between hBGC, ← len_add_of_between hEHF, len_symm B G, hGB, hGC,
          len_symm E H]
      · /- A case Euclid's figure leaves aside: the angles at the centres are greater than
           two right angles, and G and H lie beyond BC and EF. The angles BGC, EHF of the
           triangles GBC, HEF are what remains when the angles at the centres are taken
           from four right angles (`angleAtCentre.reflex`), and so are equal [C.N. 3];
           I.4 applies to them. -/
        have hang : ∠ B G C = ∠ E H F :=
          CommonNotion3
            (by rw [add_comm (∠ B G C), angleAtCentre.reflex hG hB hC hGK,
              add_comm (∠ E H F), angleAtCentre.reflex hH hE hF hHL]) hGH
        exact (BookI.Prop4 hGK.triangle.cab hHL.triangle.cab hGB hGC hang).1
    -- And, since the angle at A is equal to the angle at D,
    -- the segment BAC is similar to the segment EDF; [III. Def. 11]
    -- and they are upon equal straight lines.
    -- But similar segments of circles on equal straight lines are equal to one
    -- another; [III. 24]
    -- therefore the segment BAC is equal to EDF.
    have seg : Arc.Congruent ⟨ABC, B, C, A⟩ ⟨DEF, E, F, D⟩ :=
      Prop24 hB hC hA hE hF hD hBCA hEFD hBC hAD
    /- So their circumferences are equal in measure (`Prop24.equalMeasure`). -/
    have hBAC : circumference ABC B A C = circumference DEF E D F :=
      Prop24.equalMeasure (a := ⟨ABC, B, C, A⟩) (b := ⟨DEF, E, F, D⟩)
        ⟨hB, hC, hBCA⟩
        ⟨hE, hF, hEFD⟩ seg
    -- But the whole circle ABC is also equal to the whole circle DEF;
    have w₁ := Circumference.whole hB hC hAK
    have w₂ := Circumference.whole hE hF hDL
    -- therefore the circumference BKC which remains is equal to the circumference ELF.
    have hKL : circumference ABC B K C = circumference DEF E L F :=
      CommonNotion3 (w₁.trans w₂.symm) hBAC
    /- The same subtraction for congruence restricts the common application of the whole
       circles (`Prop26.extend`) to the remaining segments (`Prop26.remainder`). -/
    exact ⟨hKL, Prop26.remainder hB hC hE hF hAK hDL seg⟩
  -- Therefore etc.
  /- Our statement takes the two pairs of equal angles one at a time, as the enunciation's
     "whether they stand at the centres or at the circumferences" does, and III.20 gives
     the other pair: each angle at the centre is double of the angle at the circumference
     standing on the same circumference, whatever its size. Given at the centres, the
     circumferences BKC, ELF are less than semicircles, and the angles at the centres are
     the angles BGC, EHF themselves (`angleAtCentre.within`); the angles at A and D are
     their halves, and so equal. Given at the circumferences, the angles at the centres
     are their doubles, and so equal. -/
  have h₁ : angleAtCentre ABC B K C = ∠ B A C + ∠ B A C :=
    Prop20 hA hB hC hAK
  have h₂ : angleAtCentre DEF E L F = ∠ E D F + ∠ E D F :=
    Prop20 hD hE hF hDL
  refine ⟨fun hGK hHL h => ?_, fun h => euclid (by rw [h₁, h₂, h]) h⟩
  have hGH : angleAtCentre ABC B K C = angleAtCentre DEF E L F := by
    rw [angleAtCentre.within hG hB hC hGK, angleAtCentre.within hH hE hF hHL, h]
  exact euclid hGH (Magnitude.eq_of_add_self_eq (h₁.symm.trans (hGH.trans h₂)))
  -- Q. E. D.

/-- The check: the equal measures alone, in each clause, follow from `Prop26` by the first
conjunct of each (checked by Lean). -/
example {A B C D E F G H K L : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :
    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      circumference ABC B K C = circumference DEF E L F) ∧
    (∠ B A C = ∠ E D F → circumference ABC B K C = circumference DEF E L F) :=
  ⟨fun hGK hHL h => ((Prop26 hcircles hG hH hA hB hC hD hE hF hAK hDL).1 hGK hHL h).1,
    fun h => ((Prop26 hcircles hG hH hA hB hC hD hE hF hAK hDL).2 h).1⟩

end Elements.BookIII
