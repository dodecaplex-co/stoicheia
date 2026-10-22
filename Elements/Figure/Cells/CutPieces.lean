import Elements.Figure.Cells.CutHelpers

/-!
# Staging: the two pieces of a genuine cut

Helpers for `convex_cut_pieces` (route C1 of brief 0013). A straight line with corners of a
convex outline strictly on both sides of it meets the outline corner to corner, corner to
side, or side to side. The corners strictly on one side come in one unbroken run, read
cyclically: four corners in order whose diagonals cross cannot alternate between the sides
(`no_alternation`), since the diagonals' common point would be on both. Each run, closed by
the line's points on the outline, is the outline of a convex piece (`piece`), whose region
is the outline's region on that closed side and whose inside is its inside on that open
side. No proposition of the Elements is cited, and neither Postulate 5 nor superposition is
used. With thanks to David Hilbert, whose theory of content guides this route.
-/

namespace Elements.Figures.Pieces

open Tacit

/-! ## Sides of a straight line -/

/-- Off a straight line, a point is on the side of one or the other of two points on
opposite sides of it. -/
theorem side_cases {A B Z : Point} {L : Line} (h : OppositeSides A B L) (hZ : ¬ OnLine Z L) :
    SameSide Z A L ∨ SameSide Z B L := by
  rcases same_side_or h.1 h.2.1 hZ h.2.2 with hz | hz
  · exact Or.inl (same_side_symm hz)
  · exact Or.inr (same_side_symm hz)

/-- No point is on the sides of two points on opposite sides. -/
theorem not_both {A B Z : Point} {L : Line} (h : OppositeSides A B L)
    (hA : SameSide Z A L) (hB : SameSide Z B L) : False :=
  h.2.2 (same_side_trans hA hB)

/-- A point not strictly on `A`'s side is on the closed side of `B`. -/
theorem half_of_not {A B Z : Point} {L : Line} (h : OppositeSides A B L)
    (hZ : ¬ SameSide Z A L) : Half Z B L := by
  by_cases hz : OnLine Z L
  · exact Or.inl hz
  · exact Or.inr ((side_cases h hz).resolve_left hZ)

/-- Points on the sides of two points on opposite sides are on opposite sides. -/
theorem opposite_of {A B C D : Point} {L : Line} (h : OppositeSides A B L)
    (hC : SameSide C A L) (hD : SameSide D B L) : OppositeSides C D L :=
  ⟨not_on_line_of_same_side hC, not_on_line_of_same_side hD, fun hCD =>
    h.2.2 (same_side_trans (same_side_symm (same_side_trans hC hCD)) hD)⟩

/-- Opposite sides, the other way round. -/
theorem opposite_symm {A B : Point} {L : Line} (h : OppositeSides A B L) :
    OppositeSides B A L :=
  ⟨h.2.1, h.1, fun hs => h.2.2 (same_side_symm hs)⟩

/-- On the closed side towards `G`, and `W` on `G`'s side: on the closed side towards `W`. -/
theorem half_trans {Z G W : Point} {M : Line} (hZ : Half Z G M) (hW : SameSide W G M) :
    Half Z W M := by
  rcases hZ with hZ | hZ
  · exact Or.inl hZ
  · exact Or.inr (same_side_trans (same_side_symm hZ) (same_side_symm hW))

/-- The crossing point of two finite straight lines cannot be strictly on `A`'s side by the
first and on the closed side of `B` by the second. -/
theorem cross_contra {A B P Q R S Z : Point} {L : Line} (hAB : OppositeSides A B L)
    (h₁ : Between P Z Q) (h₂ : Between R Z S) (hP : SameSide P A L) (hQ : SameSide Q A L)
    (hR : Half R B L) (hS : Half S B L) : False := by
  have hZA : SameSide Z A L := same_side_between h₁ hP hQ
  rcases half_between hR hS h₂ with hZ | hZ
  · exact not_on_line_of_same_side hZA hZ
  · exact not_both hAB hZA hZ

/-! ## The sides of a convex outline -/

/-- A corner off a side is off its straight line. -/
theorem corner_off {cs : List Point} (h : ConvexOutline cs) {s : Point × Point}
    (hs : s ∈ sides cs) {M : Line} (h₁ : OnLine s.1 M) (h₂ : OnLine s.2 M)
    {W : Point} (hW : W ∈ cs) (hW₁ : W ≠ s.1) (hW₂ : W ≠ s.2) : ¬ OnLine W M :=
  not_on_line_of_same_side ((h.2.2 s hs W hW W hW hW₁ hW₂ hW₁ hW₂).sameSide h₁ h₂)

/-- A point of the region is on the closed side of each side towards a corner off it. -/
theorem region_half {cs : List Point} (h : ConvexOutline cs) {s : Point × Point}
    (hs : s ∈ sides cs) {M : Line} (h₁ : OnLine s.1 M) (h₂ : OnLine s.2 M)
    {G : Point} (hG : G ∈ cs) (hG₁ : G ≠ s.1) (hG₂ : G ≠ s.2)
    {Z : Point} (hZ : ConvexRegion cs Z) : Half Z G M :=
  (closedSide_iff_half (convex_side_ne h hs) h₁ h₂).mp (hZ s hs G hG hG₁ hG₂)

/-- A point of the region is on the closed side of each side towards any point of the
region off its straight line. -/
theorem region_half_of {cs : List Point} (h : ConvexOutline cs) {s : Point × Point}
    (hs : s ∈ sides cs) {M : Line} (h₁ : OnLine s.1 M) (h₂ : OnLine s.2 M)
    {W Z : Point} (hW : ConvexRegion cs W) (hWM : ¬ OnLine W M) (hZ : ConvexRegion cs Z) :
    Half Z W M := by
  obtain ⟨G, hG, hG₁, hG₂⟩ := convex_third h s
  exact half_trans (region_half h hs h₁ h₂ hG hG₁ hG₂ hZ)
    ((region_half h hs h₁ h₂ hG hG₁ hG₂ hW).resolve_left hWM)

/-- A point inside the outline is strictly on the side of each side towards any point of
the region off its straight line. -/
theorem core_side_of {cs : List Point} (h : ConvexOutline cs) {s : Point × Point}
    (hs : s ∈ sides cs) {M : Line} (h₁ : OnLine s.1 M) (h₂ : OnLine s.2 M)
    {W Z : Point} (hW : ConvexRegion cs W) (hWM : ¬ OnLine W M)
    (hZ : ∀ s ∈ sides cs, ∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → SameSideOf Z A s.1 s.2) :
    SameSide Z W M := by
  obtain ⟨G, hG, hG₁, hG₂⟩ := convex_third h s
  have hw := (region_half h hs h₁ h₂ hG hG₁ hG₂ hW).resolve_left hWM
  exact same_side_trans (same_side_symm ((hZ s hs G hG hG₁ hG₂).sameSide h₁ h₂))
    (same_side_symm hw)

/-! ## The region is convex -/

/-- The region holds every closed triangle on three of its points. -/
theorem region_triangle {cs : List Point} (h : ConvexOutline cs) {A B C X : Point}
    (hA : ConvexRegion cs A) (hB : ConvexRegion cs B) (hC : ConvexRegion cs C)
    (hX : OnOrInsideTriangle X A B C) : ConvexRegion cs X := by
  intro s hs G hG hG₁ hG₂
  have hne := convex_side_ne h hs
  obtain ⟨M, h₁, h₂⟩ := Postulate1 s.1 s.2 hne
  have conv {Y : Point} (hY : ConvexRegion cs Y) : Half Y G M :=
    (closedSide_iff_half hne h₁ h₂).mp (hY s hs G hG hG₁ hG₂)
  exact (closedSide_iff_half hne h₁ h₂).mpr (closed_in_half (conv hA) (conv hB) (conv hC) hX)

/-- A convex outline whose corners are in a region has its own region in it. -/
theorem region_subset {cs qs : List Point} (h : ConvexOutline cs) (hq : ConvexOutline qs)
    (hW : ∀ W ∈ qs, ConvexRegion cs W) {Z : Point} (hZ : ConvexRegion qs Z) :
    ConvexRegion cs Z := by
  obtain ⟨t, ht, hZt⟩ := (fan_covers hq Z).mpr hZ
  obtain ⟨h₁, h₂, h₃⟩ := Extreme.fan_mem ht
  exact region_triangle h (hW _ h₁) (hW _ h₂) (hW _ h₃) hZt

/-- A region within another has its inside within the other's inside. -/
theorem core_mono {cs qs : List Point} (h : ConvexOutline cs)
    (hsub : ∀ Y, ConvexRegion qs Y → ConvexRegion cs Y) {Z : Point}
    (hZ : ∀ s ∈ sides qs, ∀ A ∈ qs, A ≠ s.1 → A ≠ s.2 → SameSideOf Z A s.1 s.2) :
    ∀ s ∈ sides cs, ∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → SameSideOf Z A s.1 s.2 := by
  intro t ht G hG hG₁ hG₂
  obtain ⟨D, E, F, hi, htri⟩ := cut_core_neighbourhood hZ
  have hne := convex_side_ne h ht
  obtain ⟨M, h₁, h₂⟩ := Postulate1 t.1 t.2 hne
  have hh {Y : Point} (hY : OnOrInsideTriangle Y D E F) : Half Y G M :=
    region_half h ht h₁ h₂ hG hG₁ hG₂ (hsub Y (htri Y hY))
  exact SameSideOf.of_line hne h₁ h₂ (cut_inside_closed_half
    (hh (by simp [OnOrInsideTriangle])) (hh (by simp [OnOrInsideTriangle]))
    (hh (by simp [OnOrInsideTriangle])) hi)

/-! ## Reading an outline from another corner -/

/-- Moving a prefix to the end keeps the sides. -/
theorem mem_sides_rotate_prefix (us vs : List Point) (s : Point × Point) :
    s ∈ sides (vs ++ us) ↔ s ∈ sides (us ++ vs) := by
  induction us generalizing vs with
  | nil => simp
  | cons A us ih =>
    have hi : s ∈ sides (vs ++ A :: us) ↔ s ∈ sides ((us ++ vs) ++ [A]) := by
      simpa [List.append_assoc] using ih (vs ++ [A])
    exact hi.trans (mem_sides_rotate A (us ++ vs) s)

/-- Moving a prefix to the end keeps the inside. -/
theorem core_rotate_prefix (us vs : List Point) (Z : Point) :
    (∀ s ∈ sides (vs ++ us), ∀ A ∈ vs ++ us, A ≠ s.1 → A ≠ s.2 → SameSideOf Z A s.1 s.2) ↔
      (∀ s ∈ sides (us ++ vs), ∀ A ∈ us ++ vs, A ≠ s.1 → A ≠ s.2 →
        SameSideOf Z A s.1 s.2) := by
  have hm (A : Point) : A ∈ vs ++ us ↔ A ∈ us ++ vs := by
    simp only [List.mem_append, or_comm]
  constructor <;> intro h s hs A hA
  · exact h s ((mem_sides_rotate_prefix us vs s).mpr hs) A ((hm A).mpr hA)
  · exact h s ((mem_sides_rotate_prefix us vs s).mp hs) A ((hm A).mp hA)

/-! ## Consecutive corners -/

/-- Two corners next to each other in a chain make one of its segments. -/
theorem pair_mem_segments (pre post : List Point) (x y : Point) :
    (x, y) ∈ segments (pre ++ x :: y :: post) := by
  rw [segments_join]
  exact List.mem_append_right _ List.mem_cons_self

/-- The segments of a piece of a chain are segments of the chain. -/
theorem segments_infix (pre mid post : List Point) {s : Point × Point}
    (hs : s ∈ segments mid) : s ∈ segments (pre ++ mid ++ post) := by
  cases mid with
  | nil => simp [segments] at hs
  | cons b bs =>
    rw [List.append_assoc, List.cons_append, segments_join]
    exact List.mem_append_right _ (by simpa using segment_mem_append hs post)

/-- The sides of an outline whose first two corners are named. -/
theorem mem_sides_two {S₁ S₂ : Point} {ws : List Point} {s : Point × Point} :
    s ∈ sides (S₁ :: S₂ :: ws) ↔ s = (S₁, S₂) ∨ s ∈ segments (S₂ :: (ws ++ [S₁])) := by
  change s ∈ (S₁, S₂) :: segments (S₂ :: (ws ++ [S₁])) ↔ _
  exact List.mem_cons

/-- A chain from `S₂` through the corners `ws` to `S₁`: its first segment, a segment of
`ws`, or its last. -/
theorem mem_chain {S₁ S₂ f l : Point} {ws ws₁ ws₂ : List Point} (hf : ws = f :: ws₁)
    (hl : ws = ws₂ ++ [l]) {s : Point × Point} (hs : s ∈ segments (S₂ :: (ws ++ [S₁]))) :
    s = (S₂, f) ∨ s ∈ segments ws ∨ s = (l, S₁) := by
  have e₁ : segments (S₂ :: (ws ++ [S₁])) = (S₂, f) :: segments (ws ++ [S₁]) := by
    subst hf
    rfl
  have e₂ : segments (ws ++ [S₁]) = segments ws ++ [(l, S₁)] := by
    rw [hl, List.append_assoc, List.singleton_append, segments_join]
    rfl
  rw [e₁, e₂] at hs
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hs
  exact hs

/-! ## A piece of a convex outline -/

/-- `qs` is the outline of what is left of the convex outline `cs` on `R`'s side of the
straight line `L`: a convex outline, whose region is the region of `cs` on the closed side
of `L` towards `R`, and whose inside is the inside of `cs` on the open side. -/
def IsPiece (cs : List Point) (L : Line) (R : Point) (qs : List Point) : Prop :=
  ConvexOutline qs ∧
    (∀ Z : Point, ConvexRegion qs Z ↔ ConvexRegion cs Z ∧ Half Z R L) ∧
    (∀ Z : Point,
      (∀ s ∈ sides qs, ∀ A ∈ qs, A ≠ s.1 → A ≠ s.2 → SameSideOf Z A s.1 s.2) ↔
        (∀ s ∈ sides cs, ∀ A ∈ cs, A ≠ s.1 → A ≠ s.2 → SameSideOf Z A s.1 s.2) ∧
          SameSide Z R L)

/-- A piece read from another corner is a piece. -/
theorem IsPiece.rotate {cs : List Point} {L : Line} {R : Point} {us vs : List Point}
    (h : IsPiece cs L R (us ++ vs)) : IsPiece cs L R (vs ++ us) :=
  ⟨Extreme.convex_rotate_prefix us vs h.1,
    fun Z => (Extreme.region_rotate_prefix us vs Z).trans (h.2.1 Z),
    fun Z => (core_rotate_prefix us vs Z).trans (h.2.2 Z)⟩

/-- A piece of an outline read from another corner is a piece of the outline. -/
theorem IsPiece.rotate_whole {us vs : List Point} {L : Line} {R : Point} {qs : List Point}
    (h : IsPiece (vs ++ us) L R qs) : IsPiece (us ++ vs) L R qs := by
  refine ⟨h.1, fun Z => ?_, fun Z => ?_⟩
  · rw [h.2.1 Z, Extreme.region_rotate_prefix us vs Z]
  · rw [h.2.2 Z, core_rotate_prefix us vs Z]

/-- **A piece of a convex outline.** Take the corners `ws` of a convex outline that run, in
order, from `f` to `l`, all strictly on `R`'s side of the straight line `L`; the corner `a`
before them and the corner `b` after them. Let `S₂` be `a`, or a point between `a` and `f`,
and `S₁` be `b`, or a point between `l` and `b`, two different points of `L`. Then `S₁`,
`S₂` and `ws`, in that order, make the outline of what is left on `R`'s side. -/
theorem piece {cs : List Point} (h : ConvexOutline cs) {L : Line} {R : Point}
    {S₁ S₂ a b f l : Point} {ws ws₁ ws₂ : List Point}
    (hf : ws = f :: ws₁) (hl : ws = ws₂ ++ [l]) (hnd : ws.Nodup)
    (hch : ∀ s ∈ segments (a :: (ws ++ [b])), s ∈ sides cs)
    (hmem : ∀ w ∈ a :: (ws ++ [b]), w ∈ cs)
    (hS₁ : OnLine S₁ L) (hS₂ : OnLine S₂ L) (hne : S₁ ≠ S₂)
    (hR : ∀ w ∈ ws, SameSide w R L)
    (ha : S₂ = a ∨ Between a S₂ f) (hb : S₁ = b ∨ Between l S₁ b) :
    IsPiece cs L R (S₁ :: S₂ :: ws) := by
  have hfw : f ∈ ws := by rw [hf]; exact List.mem_cons_self
  have hlw : l ∈ ws := by rw [hl]; simp
  have hfR := hR f hfw
  have hlR := hR l hlw
  have off_ws {W : Point} (hW : W ∈ ws) : ¬ OnLine W L := not_on_line_of_same_side (hR W hW)
  have hS₁ws : S₁ ∉ ws := fun hm => off_ws hm hS₁
  have hS₂ws : S₂ ∉ ws := fun hm => off_ws hm hS₂
  have ha_cs : a ∈ cs := hmem a List.mem_cons_self
  have hb_cs : b ∈ cs := hmem b (by simp)
  have hw_cs {W : Point} (hW : W ∈ ws) : W ∈ cs := hmem W (by simp [hW])
  have haws : a ∉ ws := by
    intro hm
    rcases ha with he | hab
    · exact hS₂ws (he ▸ hm)
    · exact not_on_line_of_same_side (same_side_between hab (hR a hm) hfR) hS₂
  have hbws : b ∉ ws := by
    intro hm
    rcases hb with he | hlb
    · exact hS₁ws (he ▸ hm)
    · exact not_on_line_of_same_side (same_side_between hlb hlR (hR b hm)) hS₁
  have haf : (a, f) ∈ sides cs := hch _ (by rw [hf]; exact List.mem_cons_self)
  have hlb : (l, b) ∈ sides cs := hch _ (by
    rw [hl]
    simpa using pair_mem_segments (a :: ws₂) [] l b)
  have hws_sides {s : Point × Point} (hs : s ∈ segments ws) : s ∈ sides cs :=
    hch s (by simpa using segments_infix [a] ws [b] hs)
  have hreg_ws {W : Point} (hW : W ∈ ws) : ConvexRegion cs W := Extreme.corner_region h (hw_cs hW)
  have hreg_S₂ : ConvexRegion cs S₂ := by
    rcases ha with he | hab
    · rw [he]
      exact Extreme.corner_region h ha_cs
    · exact convex_region_between h (Extreme.corner_region h ha_cs) (hreg_ws hfw) hab
  have hreg_S₁ : ConvexRegion cs S₁ := by
    rcases hb with he | hlb'
    · rw [he]
      exact Extreme.corner_region h hb_cs
    · exact convex_region_between h (hreg_ws hlw) (Extreme.corner_region h hb_cs) hlb'
  have hregQ : ∀ W ∈ S₁ :: S₂ :: ws, ConvexRegion cs W := by
    intro W hW
    rcases List.mem_cons.mp hW with he | hW
    · rw [he]
      exact hreg_S₁
    rcases List.mem_cons.mp hW with he | hW
    · rw [he]
      exact hreg_S₂
    · exact hreg_ws hW
  /- Each side of the piece but the one on `L` lies on the straight line of a side of the
  outline, with the piece's other corners off it. -/
  have good : ∀ s ∈ segments (S₂ :: (ws ++ [S₁])), s.1 ≠ s.2 ∧ ∃ t ∈ sides cs, ∃ M : Line,
      OnLine t.1 M ∧ OnLine t.2 M ∧ OnLine s.1 M ∧ OnLine s.2 M ∧
        ∀ W ∈ S₁ :: S₂ :: ws, W ≠ s.1 → W ≠ s.2 → ¬ OnLine W M := by
    intro s hs
    rcases mem_chain hf hl hs with hs | hs | hs
    · subst hs
      obtain ⟨M, haM, hfM⟩ := Postulate1 a f (convex_side_ne h haf)
      have hS₂M : OnLine S₂ M := by
        rcases ha with he | hab
        · rw [he]
          exact haM
        · exact on_line_of_between_ends hab haM hfM
      have hS₂f : S₂ ≠ f := fun e => off_ws hfw (by rw [← e]; exact hS₂)
      refine ⟨hS₂f, (a, f), haf, M, haM, hfM, hS₂M, hfM, ?_⟩
      intro W hW hW₁ hW₂
      rcases List.mem_cons.mp hW with he | hW
      · intro hWM
        have hLM : L = M := line_unique hne hS₁ hS₂ (he ▸ hWM) hS₂M
        exact off_ws hfw (by rw [hLM]; exact hfM)
      rcases List.mem_cons.mp hW with he | hW
      · exact absurd he hW₁
      · exact corner_off h haf haM hfM (hw_cs hW)
          (fun e => haws (by have e' : W = a := e; rw [← e']; exact hW)) hW₂
    · have hts := hws_sides hs
      have hne' := convex_side_ne h hts
      obtain ⟨M, h₁, h₂⟩ := Postulate1 s.1 s.2 hne'
      refine ⟨hne', s, hts, M, h₁, h₂, h₁, h₂, ?_⟩
      have hs₁ws := (segment_corners hs).1
      have hs₂ws := (segment_corners hs).2
      intro W hW hW₁ hW₂
      rcases List.mem_cons.mp hW with he | hW
      · rw [he]
        have hbM := corner_off h hts h₁ h₂ hb_cs (fun e => hbws (e ▸ hs₁ws))
          (fun e => hbws (e ▸ hs₂ws))
        rcases hb with he' | hlb'
        · rw [he']
          exact hbM
        · have hl_half : Half l b M := corner_half h hts hb_cs (fun e => hbws (e ▸ hs₁ws))
            (fun e => hbws (e ▸ hs₂ws)) (hw_cs hlw) h₁ h₂
          exact not_on_line_of_same_side
            (Extreme.between_half_open hl_half (same_side_refl hbM) hlb')
      rcases List.mem_cons.mp hW with he | hW
      · rw [he]
        have haM := corner_off h hts h₁ h₂ ha_cs (fun e => haws (e ▸ hs₁ws))
          (fun e => haws (e ▸ hs₂ws))
        rcases ha with he' | hab
        · rw [he']
          exact haM
        · have hf_half : Half f a M := corner_half h hts ha_cs (fun e => haws (e ▸ hs₁ws))
            (fun e => haws (e ▸ hs₂ws)) (hw_cs hfw) h₁ h₂
          exact not_on_line_of_same_side
            (Extreme.between_half_open hf_half (same_side_refl haM) (between_symm hab))
      · exact corner_off h hts h₁ h₂ (hw_cs hW) hW₁ hW₂
    · subst hs
      obtain ⟨M, hlM, hbM⟩ := Postulate1 l b (convex_side_ne h hlb)
      have hS₁M : OnLine S₁ M := by
        rcases hb with he | hlb'
        · rw [he]
          exact hbM
        · exact on_line_of_between_ends hlb' hlM hbM
      have hlS₁ : l ≠ S₁ := fun e => off_ws hlw (by rw [e]; exact hS₁)
      refine ⟨hlS₁, (l, b), hlb, M, hlM, hbM, hlM, hS₁M, ?_⟩
      intro W hW hW₁ hW₂
      rcases List.mem_cons.mp hW with he | hW
      · exact absurd he hW₂
      rcases List.mem_cons.mp hW with he | hW
      · intro hWM
        have hLM : L = M := line_unique hne hS₁ hS₂ hS₁M (he ▸ hWM)
        exact off_ws hlw (by rw [hLM]; exact hlM)
      · exact corner_off h hlb hlM hbM (hw_cs hW) hW₁
          (fun e => hbws (by have e' : W = b := e; rw [← e']; exact hW))
  have hf₁ : f ≠ S₁ := fun e => hS₁ws (e ▸ hfw)
  have hf₂ : f ≠ S₂ := fun e => hS₂ws (e ▸ hfw)
  have hfQ : f ∈ S₁ :: S₂ :: ws := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hfw)
  have first : (S₁, S₂) ∈ sides (S₁ :: S₂ :: ws) := mem_sides_two.mpr (Or.inl rfl)
  have in_ws {W : Point} (hW : W ∈ S₁ :: S₂ :: ws) (hW₁ : W ≠ S₁) (hW₂ : W ≠ S₂) : W ∈ ws := by
    rcases List.mem_cons.mp hW with he | hW
    · exact absurd he hW₁
    rcases List.mem_cons.mp hW with he | hW
    · exact absurd he hW₂
    · exact hW
  have hQ : ConvexOutline (S₁ :: S₂ :: ws) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hf]
      simp
    · simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨hne, hS₁ws⟩, hS₂ws, hnd⟩
    · intro s hs P hP Q hQ hP₁ hP₂ hQ₁ hQ₂
      rcases mem_sides_two.mp hs with hs | hs
      · subst hs
        have hPw := in_ws hP hP₁ hP₂
        have hQw := in_ws hQ hQ₁ hQ₂
        exact SameSideOf.of_line hne hS₁ hS₂
          (same_side_trans (same_side_symm (hR P hPw)) (same_side_symm (hR Q hQw)))
      · obtain ⟨hne', t, ht, M, ht₁, ht₂, hs₁, hs₂, hoff⟩ := good s hs
        have hPQ : SameSide P Q M := (region_half_of h ht ht₁ ht₂ (hregQ Q hQ)
          (hoff Q hQ hQ₁ hQ₂) (hregQ P hP)).resolve_left (hoff P hP hP₁ hP₂)
        exact SameSideOf.of_line hne' hs₁ hs₂ hPQ
  have hsub : ∀ Y, ConvexRegion (S₁ :: S₂ :: ws) Y → ConvexRegion cs Y :=
    fun Y hY => region_subset h hQ hregQ hY
  refine ⟨hQ, fun Z => ⟨fun hZ => ⟨hsub Z hZ, ?_⟩, fun hZ => ?_⟩,
    fun Z => ⟨fun hZ => ⟨core_mono h hsub hZ, ?_⟩, fun hZ => ?_⟩⟩
  · have hc := (closedSide_iff_half hne hS₁ hS₂).mp (hZ (S₁, S₂) first f hfQ hf₁ hf₂)
    exact half_trans hc (same_side_symm hfR)
  · intro s hs W hW hW₁ hW₂
    rcases mem_sides_two.mp hs with hs | hs
    · subst hs
      exact (closedSide_iff_half hne hS₁ hS₂).mpr
        (half_trans hZ.2 (hR W (in_ws hW hW₁ hW₂)))
    · obtain ⟨hne', t, ht, M, ht₁, ht₂, hs₁, hs₂, hoff⟩ := good s hs
      exact (closedSide_iff_half hne' hs₁ hs₂).mpr
        (region_half_of h ht ht₁ ht₂ (hregQ W hW) (hoff W hW hW₁ hW₂) hZ.1)
  · have hc := (hZ (S₁, S₂) first f hfQ hf₁ hf₂).sameSide hS₁ hS₂
    exact same_side_trans (same_side_symm hc) hfR
  · intro s hs W hW hW₁ hW₂
    rcases mem_sides_two.mp hs with hs | hs
    · subst hs
      exact SameSideOf.of_line hne hS₁ hS₂ (same_side_trans (same_side_symm hZ.2)
        (same_side_symm (hR W (in_ws hW hW₁ hW₂))))
    · obtain ⟨hne', t, ht, M, ht₁, ht₂, hs₁, hs₂, hoff⟩ := good s hs
      exact SameSideOf.of_line hne' hs₁ hs₂
        (core_side_of h ht ht₁ ht₂ (hregQ W hW) (hoff W hW hW₁ hW₂) hZ.1)

/-! ## Four corners in order -/

/-- Leaving out the first corner of a convex outline of four corners or more leaves a convex
outline. -/
theorem convex_erase_head {a : Point} {rest : List Point} (h : ConvexOutline (a :: rest))
    (hl : 3 ≤ rest.length) : ConvexOutline rest := by
  obtain ⟨init, z, rfl⟩ := Extreme.split_last rest (by rintro rfl; simp at hl)
  have hr : ConvexOutline (z :: a :: init) := by
    simpa using Extreme.convex_rotate_prefix (a :: init) [z] (by simpa using h)
  cases init with
  | nil => simp at hl
  | cons i init =>
    have hc := cut_convex hr (by rintro rfl; simp at hl)
    simpa using Extreme.convex_rotate_prefix [z] (i :: init) hc

/-- Leaving out any corner of a convex outline of four corners or more leaves a convex
outline. -/
theorem convex_erase {pre post : List Point} {a : Point} (h : ConvexOutline (pre ++ a :: post))
    (hl : 3 ≤ (pre ++ post).length) : ConvexOutline (pre ++ post) := by
  have h₁ : ConvexOutline (a :: (post ++ pre)) := by
    simpa using Extreme.convex_rotate_prefix pre (a :: post) h
  have h₂ := convex_erase_head h₁ (by simp only [List.length_append] at hl ⊢; omega)
  exact Extreme.convex_rotate_prefix post pre h₂

/-- Three or more corners of a convex outline, taken in order, make a convex outline. -/
theorem convex_sublist (pre : List Point) {l₁ l₂ : List Point} (hs : l₁.Sublist l₂)
    (h : ConvexOutline (pre ++ l₂)) (hl : 3 ≤ (pre ++ l₁).length) :
    ConvexOutline (pre ++ l₁) := by
  induction hs generalizing pre with
  | slnil => exact h
  | cons a hs ih =>
    have hle := hs.length_le
    exact ih pre (convex_erase h (by simp only [List.length_append] at hl ⊢; omega)) hl
  | cons_cons a hs ih =>
    have hi := ih (pre ++ [a]) (by simpa using h) (by simpa using hl)
    simpa using hi

/-- The diagonals of four corners of a convex outline, taken in order, cross. -/
theorem quad_cross {cs : List Point} (h : ConvexOutline cs) {a b c d : Point}
    (hs : [a, b, c, d].Sublist cs) : ∃ Z : Point, Between a Z c ∧ Between b Z d := by
  have hq : ConvexOutline [a, b, c, d] := by
    simpa using convex_sublist [] hs (by simpa using h) (by simp)
  obtain ⟨h₁, h₂⟩ := hq.fan_cross (c, d) (by simp [segments])
  exact diagonals_cross h₁ h₂

/-- **No alternation**: four corners of a convex outline, taken in order, are not first and
third strictly on `A`'s side of a straight line, second and fourth on the closed side of
`B`, the other side. -/
theorem no_alternation {cs : List Point} (h : ConvexOutline cs) {L : Line} {A B : Point}
    (hAB : OppositeSides A B L) {a b c d : Point} (hs : [a, b, c, d].Sublist cs)
    (ha : SameSide a A L) (hb : Half b B L) (hc : SameSide c A L) (hd : Half d B L) :
    False := by
  obtain ⟨Z, hac, hbd⟩ := quad_cross h hs
  exact cross_contra hAB hac hbd ha hc hb hd

/-- No alternation, the other way round: second and fourth strictly on `A`'s side. -/
theorem no_alternation' {cs : List Point} (h : ConvexOutline cs) {L : Line} {A B : Point}
    (hAB : OppositeSides A B L) {a b c d : Point} (hs : [a, b, c, d].Sublist cs)
    (ha : Half a B L) (hb : SameSide b A L) (hc : Half c B L) (hd : SameSide d A L) :
    False := by
  obtain ⟨Z, hac, hbd⟩ := quad_cross h hs
  exact cross_contra hAB hbd hac hb hd ha hc

/-- No side of a convex outline lies on a straight line with corners strictly on both sides
of it. -/
theorem side_on_line {cs : List Point} (h : ConvexOutline cs) {L : Line} {A B : Point}
    (hAB : OppositeSides A B L) {s : Point × Point} (hs : s ∈ sides cs)
    (h₁ : OnLine s.1 L) (h₂ : OnLine s.2 L) {P Q : Point} (hP : P ∈ cs) (hQ : Q ∈ cs)
    (hPA : SameSide P A L) (hQB : SameSide Q B L) : False := by
  have offP := not_on_line_of_same_side hPA
  have offQ := not_on_line_of_same_side hQB
  have hPQ := (h.2.2 s hs P hP Q hQ (fun e => offP (by rw [e]; exact h₁))
    (fun e => offP (by rw [e]; exact h₂)) (fun e => offQ (by rw [e]; exact h₁))
    (fun e => offQ (by rw [e]; exact h₂))).sameSide h₁ h₂
  exact not_both hAB (same_side_trans hPQ hPA) hQB

/-- Two corners next to each other make a side. -/
theorem pair_mem_sides (pre post : List Point) (x y : Point) :
    (x, y) ∈ sides (pre ++ x :: y :: post) := by
  cases pre with
  | nil => exact List.mem_cons_self
  | cons c pre =>
    change (x, y) ∈ segments (c :: (pre ++ x :: y :: post) ++ [c])
    simpa using pair_mem_segments (c :: pre) (post ++ [c]) x y

/-! ## One unbroken run -/

/-- A rotation of a rotation is a rotation. -/
theorem rotate_compose {cs pre post l₁ l₂ : List Point} (hc : cs = pre ++ post)
    (hr : post ++ pre = l₁ ++ l₂) :
    ∃ pre' post' : List Point, cs = pre' ++ post' ∧ post' ++ pre' = l₂ ++ l₁ := by
  rcases List.append_eq_append_iff.mp hr with ⟨a', h₁, h₂⟩ | ⟨c', h₁, h₂⟩
  · exact ⟨a', l₂ ++ post, by rw [hc, h₂]; simp, by rw [h₁]; simp⟩
  · exact ⟨pre ++ l₁, c', by rw [hc, h₁]; simp, by rw [h₂]; simp⟩

/-- The first member of a list that fails a test. -/
theorem first_fail {α : Type} (p : α → Prop) :
    ∀ l : List α, (∃ x ∈ l, ¬ p x) →
      ∃ (T : List α) (x : α) (D : List α), l = T ++ x :: D ∧ (∀ y ∈ T, p y) ∧ ¬ p x
  | [], ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, ⟨x, hx, hpx⟩ => by
    by_cases ha : p a
    · have hxl : x ∈ l := (List.mem_cons.mp hx).resolve_left (fun e => hpx (e ▸ ha))
      obtain ⟨T, y, D, he, hT, hy⟩ := first_fail p l ⟨x, hxl, hpx⟩
      refine ⟨a :: T, y, D, by rw [he]; rfl, fun z hz => ?_, hy⟩
      rcases List.mem_cons.mp hz with e | hz
      · exact e ▸ ha
      · exact hT z hz
    · exact ⟨[], a, l, rfl, fun _ h => absurd h List.not_mem_nil, ha⟩

/-- Four members, one from each of four lists, are in order in the lists joined. -/
theorem sub4 {α : Type} {a b c d : α} {l₁ l₂ l₃ l₄ : List α} (ha : a ∈ l₁) (hb : b ∈ l₂)
    (hc : c ∈ l₃) (hd : d ∈ l₄) : [a, b, c, d].Sublist (l₁ ++ l₂ ++ l₃ ++ l₄) := by
  have hs := (((List.singleton_sublist.mpr ha).append (List.singleton_sublist.mpr hb)).append
    (List.singleton_sublist.mpr hc)).append (List.singleton_sublist.mpr hd)
  simpa using hs

/-- **One unbroken run.** If no four members of a list, in order, alternate between passing
and failing a test, and some pass and some fail, then the list, read from a suitable member,
is a run that passes followed by a run that fails. -/
theorem block {α : Type} (p : α → Prop) (l : List α) (hp : ∃ x ∈ l, p x)
    (hn : ∃ x ∈ l, ¬ p x)
    (h₁ : ∀ a b c d, [a, b, c, d].Sublist l → p a → ¬ p b → p c → ¬ p d → False)
    (h₂ : ∀ a b c d, [a, b, c, d].Sublist l → ¬ p a → p b → ¬ p c → p d → False) :
    ∃ pre post Ps Ns : List α, l = pre ++ post ∧ post ++ pre = Ps ++ Ns ∧ Ps ≠ [] ∧
      Ns ≠ [] ∧ (∀ x ∈ Ps, p x) ∧ ∀ x ∈ Ns, ¬ p x := by
  obtain ⟨T, x, D, hl, hT, hx⟩ := first_fail p l hn
  cases T with
  | cons t T =>
    have ht := hT t List.mem_cons_self
    by_cases hD : ∃ y ∈ D, p y
    · obtain ⟨N, y, D₂, hD', hN, hy⟩ := first_fail (fun z => ¬ p z) D (by
        obtain ⟨y, hy, hpy⟩ := hD
        exact ⟨y, hy, Classical.not_not.mpr hpy⟩)
      have hy' : p y := Classical.not_not.mp hy
      have hD₂ : ∀ z ∈ D₂, p z := by
        intro z hz
        by_cases hpz : p z
        · exact hpz
        · exfalso
          apply h₁ t x y z _ ht hx hy' hpz
          rw [hl, hD']
          simpa using sub4 (l₁ := t :: T) (l₂ := x :: N) (l₃ := [y]) (l₄ := D₂)
            List.mem_cons_self List.mem_cons_self List.mem_cons_self hz
      refine ⟨t :: T ++ x :: N, y :: D₂, y :: D₂ ++ t :: T, x :: N, ?_, by simp,
        by simp, by simp, ?_, ?_⟩
      · rw [hl, hD']
        simp
      · intro z hz
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hz
        rcases hz with e | hz | e | hz
        · exact e ▸ hy'
        · exact hD₂ z hz
        · exact e ▸ ht
        · exact hT z (List.mem_cons_of_mem _ hz)
      · intro z hz
        rcases List.mem_cons.mp hz with e | hz
        · exact e ▸ hx
        · exact hN z hz
    · refine ⟨[], t :: T ++ x :: D, t :: T, x :: D, by simp [hl], by simp, by simp, by simp,
        hT, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with e | hz
      · exact e ▸ hx
      · exact fun hpz => hD ⟨z, hz, hpz⟩
  | nil =>
    simp only [List.nil_append] at hl
    obtain ⟨N, y, D₂, hD', hN, hy⟩ := first_fail (fun z => ¬ p z) D (by
      obtain ⟨y, hy, hpy⟩ := hp
      rw [hl] at hy
      rcases List.mem_cons.mp hy with e | hy
      · exact absurd (e ▸ hpy) hx
      · exact ⟨y, hy, Classical.not_not.mpr hpy⟩)
    have hy' : p y := Classical.not_not.mp hy
    by_cases hD₂ : ∃ z ∈ D₂, ¬ p z
    · obtain ⟨Q, z, D₃, hD₂', hQ, hz⟩ := first_fail p D₂ hD₂
      have hD₃ : ∀ w ∈ D₃, ¬ p w := by
        intro w hw hpw
        apply h₂ x y z w _ hx hy' hz hpw
        rw [hl, hD', hD₂']
        simpa using sub4 (l₁ := [x]) (l₂ := N ++ [y]) (l₃ := Q ++ [z]) (l₄ := D₃)
          List.mem_cons_self (by simp) (by simp) hw
      refine ⟨x :: N, y :: Q ++ z :: D₃, y :: Q, z :: D₃ ++ x :: N, ?_, by simp,
        by simp, by simp, ?_, ?_⟩
      · rw [hl, hD', hD₂']
        simp
      · intro w hw
        rcases List.mem_cons.mp hw with e | hw
        · exact e ▸ hy'
        · exact hQ w hw
      · intro w hw
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hw
        rcases hw with e | hw | e | hw
        · exact e ▸ hz
        · exact hD₃ w hw
        · exact e ▸ hx
        · exact hN w hw
    · refine ⟨x :: N, y :: D₂, y :: D₂, x :: N, ?_, by simp, by simp, by simp, ?_, ?_⟩
      · rw [hl, hD']
        simp
      · intro w hw
        rcases List.mem_cons.mp hw with e | hw
        · exact e ▸ hy'
        · by_cases hpw : p w
          · exact hpw
          · exact absurd ⟨w, hw, hpw⟩ hD₂
      · intro w hw
        rcases List.mem_cons.mp hw with e | hw
        · exact e ▸ hx
        · exact hN w hw

/-! ## The three kinds of cut -/

/-- The segments of a piece of the outline, closed by its first corner, are sides. -/
theorem sides_of_infix {c : Point} {rest pre mid post : List Point}
    (he : c :: rest ++ [c] = pre ++ mid ++ post) {s : Point × Point}
    (hs : s ∈ segments mid) : s ∈ sides (c :: rest) := by
  change s ∈ segments (c :: rest ++ [c])
  rw [he]
  exact segments_infix pre mid post hs

/-- A piece of a list without repeats has none. -/
theorem nodup_mid {pre mid post : List Point} (h : (pre ++ mid ++ post).Nodup) : mid.Nodup :=
  h.sublist (List.infix_append pre mid post).sublist

/-- **Corner to corner.** The straight line through the corners `X` and `Y` cuts the outline
into the corners from `X` to `Y` one way round and the corners from `Y` to `X` the other. -/
theorem form_corner_corner {cs : List Point} (h : ConvexOutline cs) {L : Line} {R₁ R₂ : Point}
    {X Y : Point} {us vs : List Point} (he : cs = X :: (us ++ Y :: vs))
    (hX : OnLine X L) (hY : OnLine Y L) (hus : us ≠ []) (hvs : vs ≠ [])
    (hu : ∀ u ∈ us, SameSide u R₁ L) (hv : ∀ v ∈ vs, SameSide v R₂ L) :
    IsPiece cs L R₁ (X :: (us ++ [Y])) ∧ IsPiece cs L R₂ (X :: Y :: vs) := by
  subst he
  have hnd := h.2.1
  have hXY : X ≠ Y := fun e => (List.nodup_cons.mp hnd).1 (by rw [e]; simp)
  have hclose : X :: (us ++ Y :: vs) ++ [X] = X :: (us ++ Y :: (vs ++ [X])) := by simp
  constructor
  · obtain ⟨f, ws₁, hf⟩ := List.exists_cons_of_ne_nil hus
    obtain ⟨ws₂, l, hl⟩ := Extreme.split_last us hus
    have hp := piece (cs := X :: (us ++ Y :: vs)) h (R := R₁) (S₁ := Y) (S₂ := X) (a := X)
      (b := Y) hf hl (nodup_mid (pre := [X]) (post := Y :: vs) (by simpa using hnd))
      (fun s hs => sides_of_infix (pre := []) (post := vs ++ [X]) (by simp) hs)
      (by intro w hw; simp at hw ⊢; grind) hY hX (Ne.symm hXY) hu (Or.inl rfl) (Or.inl rfl)
    simpa using hp.rotate (us := [Y]) (vs := X :: us)
  · obtain ⟨f, ws₁, hf⟩ := List.exists_cons_of_ne_nil hvs
    obtain ⟨ws₂, l, hl⟩ := Extreme.split_last vs hvs
    exact piece (cs := X :: (us ++ Y :: vs)) h (R := R₂) (S₁ := X) (S₂ := Y) (a := Y)
      (b := X) hf hl (nodup_mid (pre := X :: us ++ [Y]) (post := []) (by simpa using hnd))
      (fun s hs => sides_of_infix (pre := X :: us) (post := []) (by simp) hs)
      (by intro w hw; simp at hw ⊢; grind) hX hY hXY hv (Or.inl rfl) (Or.inl rfl)

/-- **Corner to side.** The straight line through the corner `X` that crosses the side `CD`
at `Y` cuts the outline into the corners from `X` to `C` with `Y`, and `Y` with the corners
from `D` round to `X`. -/
theorem form_corner_side {cs : List Point} (h : ConvexOutline cs) {L : Line} {R₁ R₂ : Point}
    {X C D Y : Point} {us vs : List Point} (he : cs = X :: (us ++ C :: D :: vs))
    (hX : OnLine X L) (hY : OnLine Y L) (hCYD : Between C Y D)
    (hu : ∀ u ∈ us ++ [C], SameSide u R₁ L) (hv : ∀ v ∈ D :: vs, SameSide v R₂ L) :
    IsPiece cs L R₁ (X :: (us ++ [C, Y])) ∧ IsPiece cs L R₂ (X :: Y :: D :: vs) := by
  subst he
  have hnd := h.2.1
  have hXY : X ≠ Y := by
    intro e
    rw [← e] at hCYD
    exact Extreme.corner_not_between h (by simp) (Extreme.corner_region h (by simp))
      (Extreme.corner_region h (by simp)) hCYD
  constructor
  · have hne : us ++ [C] ≠ [] := by simp
    obtain ⟨f, ws₁, hf⟩ := List.exists_cons_of_ne_nil hne
    have hp := piece (cs := X :: (us ++ C :: D :: vs)) h (R := R₁) (S₁ := Y) (S₂ := X)
      (a := X) (b := D) (ws₂ := us) (l := C) hf rfl
      (nodup_mid (pre := [X]) (post := D :: vs) (by simpa using hnd))
      (fun s hs => sides_of_infix (pre := []) (post := vs ++ [X]) (by simp) hs)
      (by intro w hw; simp at hw ⊢; grind) hY hX (Ne.symm hXY) hu (Or.inl rfl) (Or.inr hCYD)
    simpa using hp.rotate (us := [Y]) (vs := X :: (us ++ [C]))
  · obtain ⟨ws₂, l, hl⟩ := Extreme.split_last (D :: vs) (by simp)
    exact piece (cs := X :: (us ++ C :: D :: vs)) h (R := R₂) (S₁ := X) (S₂ := Y) (a := C)
      (b := X) (f := D) (ws₁ := vs) rfl hl
      (nodup_mid (pre := X :: us ++ [C]) (post := []) (by simpa using hnd))
      (fun s hs => sides_of_infix (pre := X :: us) (post := []) (by simp) hs)
      (by intro w hw; simp at hw ⊢; grind) hX hY hXY hv (Or.inr hCYD) (Or.inl rfl)

/-- **Side to side.** The straight line that crosses the side `EF` at `X` and the side `CD`
at `Y` cuts the outline into `X`, the corners from `F` to `C` and `Y`, and `X`, `Y` and the
corners from `D` round to `E`. -/
theorem form_side_side {cs : List Point} (h : ConvexOutline cs) {L : Line} {R₁ R₂ : Point}
    (hR : OppositeSides R₁ R₂ L) {E F C D X Y : Point} {ps us vs : List Point}
    (he : cs = E :: F :: ps) (hps : F :: ps = us ++ C :: D :: vs)
    (hX : OnLine X L) (hY : OnLine Y L) (hEXF : Between E X F) (hCYD : Between C Y D)
    (hu : ∀ u ∈ us ++ [C], SameSide u R₁ L) (hv : ∀ v ∈ D :: vs ++ [E], SameSide v R₂ L) :
    IsPiece cs L R₁ (X :: (us ++ [C, Y])) ∧ IsPiece cs L R₂ (X :: Y :: (D :: vs ++ [E])) := by
  have hF : ∃ ws₁, us ++ [C] = F :: ws₁ := by
    cases us with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hps
      exact ⟨[], by simp [hps.1]⟩
    | cons u us =>
      simp only [List.cons_append, List.cons.injEq] at hps
      exact ⟨us ++ [C], by simp [hps.1]⟩
  obtain ⟨ws₁, hf⟩ := hF
  have hFu : F ∈ us ++ [C] := by rw [hf]; exact List.mem_cons_self
  have hEF : (E, F) ∈ sides cs := by rw [he]; exact List.mem_cons_self
  have he' : cs = E :: (us ++ C :: D :: vs) := by rw [he, hps]
  subst he'
  have hnd := h.2.1
  have hDE : D ≠ E := fun e => (List.nodup_cons.mp hnd).1 (by rw [← e]; simp)
  have hDF : D ≠ F := fun e =>
    not_both hR (hu F hFu) (by rw [← e]; exact hv D List.mem_cons_self)
  have hXY : X ≠ Y := by
    intro e
    rw [← e] at hCYD
    obtain ⟨M, hEM, hFM⟩ := Postulate1 E F (convex_side_ne h hEF)
    have hDoff := corner_off h hEF hEM hFM (by simp) hDE hDF
    have hCh : Half C D M := corner_half h hEF (by simp) hDE hDF (by simp) hEM hFM
    exact not_on_line_of_same_side
      (Extreme.between_half_open hCh (same_side_refl hDoff) hCYD)
      (on_line_of_between_ends hEXF hEM hFM)
  constructor
  · have hp := piece (cs := E :: (us ++ C :: D :: vs)) h (R := R₁) (S₁ := Y) (S₂ := X)
      (a := E) (b := D) (ws₂ := us) (l := C) hf rfl
      (nodup_mid (pre := [E]) (post := D :: vs) (by simpa using hnd))
      (fun s hs => sides_of_infix (pre := []) (post := vs ++ [E]) (by simp) hs)
      (by intro w hw; simp at hw ⊢; grind) hY hX (Ne.symm hXY) hu (Or.inr hEXF) (Or.inr hCYD)
    simpa using hp.rotate (us := [Y]) (vs := X :: (us ++ [C]))
  · have hnd' : (D :: vs ++ [E]).Nodup := by
      have hr : ((D :: vs) ++ (E :: (us ++ [C]))).Nodup :=
        List.perm_append_comm.nodup_iff.mp (by simpa using hnd)
      exact hr.sublist ((List.Sublist.refl (D :: vs)).append
        (List.singleton_sublist.mpr List.mem_cons_self))
    have hch : ∀ s ∈ segments (C :: (D :: vs ++ [E] ++ [F])),
        s ∈ sides (E :: (us ++ C :: D :: vs)) := by
      intro s hs
      have hj : segments (C :: (D :: vs ++ [E] ++ [F])) =
          segments (C :: D :: vs ++ [E]) ++ segments [E, F] := by
        rw [← segments_join]
        simp
      rw [hj] at hs
      rcases List.mem_append.mp hs with hs | hs
      · exact sides_of_infix (pre := E :: us) (post := []) (by simp) hs
      · simp only [segments, List.mem_cons, List.not_mem_nil, or_false] at hs
        rw [hs]
        exact hEF
    have hFm : F ∈ us ++ C :: D :: vs := by rw [← hps]; exact List.mem_cons_self
    have hmem : ∀ w ∈ C :: (D :: vs ++ [E] ++ [F]), w ∈ E :: (us ++ C :: D :: vs) := by
      intro w hw
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hw hFm ⊢
      grind
    obtain ⟨ws₂, l, hl⟩ := Extreme.split_last (D :: vs ++ [E]) (by simp)
    exact piece (cs := E :: (us ++ C :: D :: vs)) h (R := R₂) (S₁ := X) (S₂ := Y) (a := C)
      (b := F) (f := D) (ws₁ := vs ++ [E]) (ws₂ := D :: vs) (l := E) rfl rfl hnd' hch hmem
      hX hY hXY hv (Or.inr hCYD) (Or.inr hEXF)

/-! ## The genuine cut -/

/-- Read from a later corner of a rotation, an outline is still convex, and a piece of the
rotation is a piece of the outline. -/
theorem rotated {cs pre post l₁ l₂ : List Point} (h : ConvexOutline cs)
    (hc : cs = pre ++ post) (hr : post ++ pre = l₁ ++ l₂) :
    ∃ pre' post' : List Point, cs = pre' ++ post' ∧ post' ++ pre' = l₂ ++ l₁ ∧
      ConvexOutline (l₂ ++ l₁) ∧
      ∀ (L : Line) (R : Point) (qs : List Point),
        IsPiece (l₂ ++ l₁) L R qs → IsPiece cs L R qs := by
  obtain ⟨pre', post', hc', hr'⟩ := rotate_compose hc hr
  refine ⟨pre', post', hc', hr', ?_, fun L R qs hq => ?_⟩
  · rw [← hr']
    exact Extreme.convex_rotate_prefix pre' post' (hc' ▸ h)
  · rw [← hr'] at hq
    rw [hc']
    exact hq.rotate_whole

/-- **The pieces of a genuine cut, as outlines.** A straight line with corners of a convex
outline strictly on both sides of it cuts it corner to corner, corner to side, or side to
side, into two pieces, one on each side. -/
theorem cut_lists {cs : List Point} (h : ConvexOutline cs) {L : Line} {A B : Point}
    (hAB : OppositeSides A B L) (hA : ¬ ∀ C ∈ cs, Half C A L)
    (hB : ¬ ∀ C ∈ cs, Half C B L) :
    (∃ (pre post us vs : List Point) (X Y : Point),
      cs = pre ++ post ∧ post ++ pre = X :: (us ++ Y :: vs) ∧
      ((IsPiece cs L A (X :: (us ++ [Y])) ∧ IsPiece cs L B (X :: Y :: vs)) ∨
        (IsPiece cs L B (X :: (us ++ [Y])) ∧ IsPiece cs L A (X :: Y :: vs)))) ∨
    (∃ (pre post us vs : List Point) (X C D Y : Point),
      cs = pre ++ post ∧ post ++ pre = X :: (us ++ C :: D :: vs) ∧ Between C Y D ∧
      ((IsPiece cs L A (X :: (us ++ [C, Y])) ∧ IsPiece cs L B (X :: Y :: D :: vs)) ∨
        (IsPiece cs L B (X :: (us ++ [C, Y])) ∧ IsPiece cs L A (X :: Y :: D :: vs)))) ∨
    (∃ (pre post ps us vs : List Point) (E F C D X Y : Point),
      cs = pre ++ post ∧ post ++ pre = E :: F :: ps ∧
      F :: ps = us ++ C :: D :: vs ∧ Between E X F ∧ Between C Y D ∧
      ((IsPiece cs L A (X :: (us ++ [C, Y])) ∧
          IsPiece cs L B (X :: Y :: (D :: vs ++ [E]))) ∨
        (IsPiece cs L B (X :: (us ++ [C, Y])) ∧
          IsPiece cs L A (X :: Y :: (D :: vs ++ [E]))))) := by
  classical
  have hBA := opposite_symm hAB
  /- A corner strictly on each side. -/
  have strict {R S : Point} (hRS : OppositeSides R S L) (hn : ¬ ∀ C ∈ cs, Half C R L) :
      ∃ c ∈ cs, SameSide c S L := by
    apply Classical.byContradiction
    intro hc
    apply hn
    intro c hcm
    by_cases hon : OnLine c L
    · exact Or.inl hon
    rcases side_cases hRS hon with h' | h'
    · exact Or.inr h'
    · exact absurd ⟨c, hcm, h'⟩ hc
  obtain ⟨cB, hcB, hcBB⟩ := strict hAB hA
  obtain ⟨cA, hcA, hcAA⟩ := strict hBA hB
  /- The corners strictly on `A`'s side make one run. -/
  obtain ⟨pre, post, Ps, Ns, hcs, hrot, hPs, hNs, hPA, hNA⟩ :=
    block (fun c => SameSide c A L) cs ⟨cA, hcA, hcAA⟩
      ⟨cB, hcB, fun h' => not_both hAB h' hcBB⟩
      (fun a b c d hs ha hb hc hd => no_alternation h hAB hs ha (half_of_not hAB hb) hc
        (half_of_not hAB hd))
      (fun a b c d hs ha hb hc hd => no_alternation' h hAB hs (half_of_not hAB ha) hb
        (half_of_not hAB hc) hd)
  have hPA' : ∀ c ∈ Ps, SameSide c A L := hPA
  have hNB : ∀ c ∈ Ns, Half c B L := fun c hc => half_of_not hAB (hNA c hc)
  have h₁ : ConvexOutline (Ps ++ Ns) := hrot ▸ Extreme.convex_rotate_prefix pre post (hcs ▸ h)
  have hmem : ∀ c ∈ cs, c ∈ Ps ++ Ns := by
    intro c hc
    rw [← hrot]
    rw [hcs] at hc
    simp only [List.mem_append] at hc ⊢
    exact hc.symm
  obtain ⟨p₀, Ps₀, hp₀⟩ := List.exists_cons_of_ne_nil hPs
  have hp₀A : SameSide p₀ A L := hPA' p₀ (by rw [hp₀]; exact List.mem_cons_self)
  have hp₀m : p₀ ∈ Ps ++ Ns := by rw [hp₀]; simp
  have hcBN : cB ∈ Ns := by
    rcases List.mem_append.mp (hmem cB hcB) with hc | hc
    · exact absurd hcBB (fun h' => not_both hAB (hPA' cB hc) h')
    · exact hc
  /- In the other run, at most one corner on `L` at each end. -/
  obtain ⟨Z₁, m, rest, hNs', hZ₁, hm⟩ :=
    first_fail (fun c => OnLine c L) Ns ⟨cB, hcBN, not_on_line_of_same_side hcBB⟩
  have hNm {c : Point} (hc : c ∈ Ns) (hoff : ¬ OnLine c L) : SameSide c B L :=
    (hNB c hc).resolve_left hoff
  have hmB : SameSide m B L := hNm (by rw [hNs']; simp) hm
  have hmm : m ∈ Ps ++ Ns := by rw [hNs']; simp
  have hZ₁' : Z₁ = [] ∨ ∃ X, Z₁ = [X] := by
    match Z₁, hZ₁, hNs' with
    | [], _, _ => exact Or.inl rfl
    | [X], _, _ => exact Or.inr ⟨X, rfl⟩
    | z₁ :: z₂ :: Z, hZ, hN =>
      exfalso
      have hs : (z₁, z₂) ∈ sides (Ps ++ Ns) := by
        rw [hN]
        exact pair_mem_sides Ps (Z ++ m :: rest) z₁ z₂
      exact side_on_line h₁ hAB hs (hZ z₁ (by simp)) (hZ z₂ (by simp)) hp₀m hmm hp₀A hmB
  have hrest : (∀ c ∈ rest, SameSide c B L) ∨
      ∃ M' Y, rest = M' ++ [Y] ∧ (∀ c ∈ M', SameSide c B L) ∧ OnLine Y L := by
    by_cases hr : ∃ c ∈ rest, ¬ ¬ OnLine c L
    · obtain ⟨M', Y, R₂, hr', hM', hY⟩ := first_fail (fun c => ¬ OnLine c L) rest hr
      have hY' := Classical.not_not.mp hY
      have hM'B : ∀ c ∈ M', SameSide c B L := fun c hc =>
        hNm (by rw [hNs', hr']; simp [hc]) (hM' c hc)
      cases R₂ with
      | nil => exact Or.inr ⟨M', Y, hr', hM'B, hY'⟩
      | cons w R₃ =>
        exfalso
        have hwN : w ∈ Ns := by rw [hNs', hr']; simp
        by_cases hw : OnLine w L
        · have hs : (Y, w) ∈ sides (Ps ++ Ns) := by
            rw [hNs', hr']
            simpa using pair_mem_sides (Ps ++ Z₁ ++ m :: M') R₃ Y w
          exact side_on_line h₁ hAB hs hY' hw hp₀m hmm hp₀A hmB
        · have hs : [p₀, m, Y, w].Sublist (Ps ++ Ns) := by
            rw [hNs', hr']
            simpa using sub4 (l₁ := Ps) (l₂ := Z₁ ++ m :: M') (l₃ := [Y]) (l₄ := w :: R₃)
              (by rw [hp₀]; exact List.mem_cons_self) (by simp) List.mem_cons_self
              List.mem_cons_self
          exact no_alternation' h₁ hBA hs (Or.inr hp₀A) hmB (Or.inl hY') (hNm hwN hw)
    · refine Or.inl fun c hc => hNm (by rw [hNs']; simp [hc]) ?_
      intro hon
      exact hr ⟨c, hc, Classical.not_not.mpr hon⟩
  /- The length of the outline. -/
  have hlen : 3 ≤ (Ps ++ Ns).length := by
    have hl := h.1
    rw [hcs] at hl
    rw [← hrot]
    simp only [List.length_append] at hl ⊢
    omega
  rcases hZ₁' with hZ | ⟨X, hZ⟩ <;> subst hZ <;> rcases hrest with hrest | ⟨M', Y₀, hr', hM', hY₀⟩
  · /- Side to side. -/
    by_cases hre : rest = []
    · /- One corner strictly on `B`'s side: read from the last corner on `A`'s side. -/
      subst hre
      obtain ⟨Ps', E', hPs'⟩ := Extreme.split_last Ps hPs
      have hPs'ne : Ps' ≠ [] := by
        rintro rfl
        rw [hNs', hPs'] at hlen
        simp at hlen
      obtain ⟨D, vs, hD⟩ := List.exists_cons_of_ne_nil hPs'ne
      obtain ⟨pre', post', hc', hr', hconv, htr⟩ := rotated (l₁ := Ps') (l₂ := [E', m]) h hcs
        (by rw [hrot, hNs', hPs']; simp)
      have hE'A : SameSide E' A L := hPA' E' (by rw [hPs']; simp)
      have hDA : SameSide D A L := hPA' D (by rw [hPs', hD]; simp)
      obtain ⟨X, hXL, hEXF⟩ := (opposite_of hAB hE'A hmB).exists_between
      obtain ⟨Y, hYL, hCYD⟩ := (opposite_of hBA hmB hDA).exists_between
      have hf := form_side_side (R₁ := B) (R₂ := A) hconv hBA (E := E') (F := m) (C := m)
        (D := D) (ps := D :: vs) (us := []) (vs := vs) (by rw [hD]; simp) rfl hXL hYL hEXF
        hCYD (by simpa using hmB) (by
          intro v hv
          apply hPA'
          rw [hPs', hD]
          simpa using hv)
      refine Or.inr (Or.inr ⟨pre', post', D :: vs, [], vs, E', m, m, D, X, Y, hc',
        by rw [hr', hD]; simp, rfl, hEXF, hCYD, Or.inr ⟨htr _ _ _ hf.1, htr _ _ _ hf.2⟩⟩)
    · /- Read from the last corner strictly on `B`'s side. -/
      obtain ⟨M'', E, hrE⟩ := Extreme.split_last rest hre
      obtain ⟨F, Ps₁, hF⟩ := List.exists_cons_of_ne_nil hPs
      obtain ⟨us, C, hC⟩ := Extreme.split_last Ps hPs
      obtain ⟨pre', post', hc', hr', hconv, htr⟩ :=
        rotated (l₁ := Ps ++ m :: M'') (l₂ := [E]) h hcs (by rw [hrot, hNs', hrE]; simp)
      have hEB : SameSide E B L := hrest E (by rw [hrE]; simp)
      have hFA : SameSide F A L := hPA' F (by rw [hF]; simp)
      have hCA : SameSide C A L := hPA' C (by rw [hC]; simp)
      obtain ⟨X, hXL, hEXF⟩ := (opposite_of hBA hEB hFA).exists_between
      obtain ⟨Y, hYL, hCYD⟩ := (opposite_of hAB hCA hmB).exists_between
      have hf := form_side_side (R₁ := A) (R₂ := B) hconv hAB (E := E) (F := F) (C := C)
        (D := m) (ps := Ps₁ ++ m :: M'') (us := us) (vs := M'') (by rw [hF]; simp)
        (by rw [← List.cons_append, ← hF, hC]; simp) hXL hYL hEXF hCYD
        (by intro u hu; apply hPA'; rw [hC]; exact hu)
        (by
          intro v hv
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
            or_false] at hv
          rcases hv with e | hv | e
          · rw [e]; exact hmB
          · exact hrest v (by rw [hrE]; simp [hv])
          · rw [e]; exact hEB)
      refine Or.inr (Or.inr ⟨pre', post', Ps₁ ++ m :: M'', us, M'', E, F, C, m, X, Y, hc',
        by rw [hr', hF]; simp, by rw [← List.cons_append, ← hF, hC]; simp, hEXF, hCYD,
        Or.inl ⟨htr _ _ _ hf.1, htr _ _ _ hf.2⟩⟩)
  · /- Side to corner: read from the corner `Y₀`. -/
    subst hr'
    obtain ⟨us, C, hC⟩ := Extreme.split_last Ps hPs
    obtain ⟨pre', post', hc', hr', hconv, htr⟩ :=
      rotated (l₁ := Ps ++ m :: M') (l₂ := [Y₀]) h hcs (by rw [hrot, hNs']; simp)
    have hCA : SameSide C A L := hPA' C (by rw [hC]; simp)
    obtain ⟨Y, hYL, hCYD⟩ := (opposite_of hAB hCA hmB).exists_between
    have hf := form_corner_side (R₁ := A) (R₂ := B) hconv (X := Y₀) (C := C) (D := m)
      (us := us) (vs := M') (by rw [hC]; simp) hY₀ hYL hCYD
      (by intro u hu; apply hPA'; rw [hC]; exact hu)
      (by
        intro v hv
        rcases List.mem_cons.mp hv with e | hv
        · rw [e]; exact hmB
        · exact hM' v hv)
    exact Or.inr (Or.inl ⟨pre', post', us, M', Y₀, C, m, Y, hc', by rw [hr', hC]; simp,
      hCYD, Or.inl ⟨htr _ _ _ hf.1, htr _ _ _ hf.2⟩⟩)
  · /- Corner to side: read from the corner `X`. -/
    obtain ⟨us, C, hC⟩ := Extreme.split_last (m :: rest) (by simp)
    obtain ⟨D, vs, hD⟩ := List.exists_cons_of_ne_nil hPs
    obtain ⟨pre', post', hc', hr', hconv, htr⟩ :=
      rotated (l₁ := Ps) (l₂ := X :: m :: rest) h hcs (by rw [hrot, hNs']; simp)
    have hCB : SameSide C B L := by
      have hCm : C ∈ m :: rest := by rw [hC]; simp
      rcases List.mem_cons.mp hCm with e | hc
      · rw [e]; exact hmB
      · exact hrest C hc
    have hDA : SameSide D A L := hPA' D (by rw [hD]; simp)
    have key : m :: (rest ++ Ps) = us ++ C :: Ps := by
      rw [← List.cons_append, hC]
      simp
    obtain ⟨Y, hYL, hCYD⟩ := (opposite_of hBA hCB hDA).exists_between
    have hf := form_corner_side (R₁ := B) (R₂ := A) hconv (X := X) (C := C) (D := D)
      (us := us) (vs := vs) (by rw [← hD]; simp [key]) (hZ₁ X List.mem_cons_self) hYL hCYD
      (by
        intro u hu
        rw [← hC] at hu
        rcases List.mem_cons.mp hu with e | hu
        · rw [e]; exact hmB
        · exact hrest u hu)
      (by intro v hv; apply hPA'; rw [hD]; exact hv)
    exact Or.inr (Or.inl ⟨pre', post', us, vs, X, C, D, Y, hc',
      by rw [hr', ← hD]; simp [key], hCYD, Or.inr ⟨htr _ _ _ hf.1, htr _ _ _ hf.2⟩⟩)
  · /- Corner to corner. -/
    subst hr'
    obtain ⟨pre', post', hc', hr', hconv, htr⟩ :=
      rotated (l₁ := Ps) (l₂ := X :: m :: (M' ++ [Y₀])) h hcs (by rw [hrot, hNs']; simp)
    have hf := form_corner_corner (R₁ := B) (R₂ := A) hconv (X := X) (Y := Y₀)
      (us := m :: M') (vs := Ps) (by simp) (hZ₁ X List.mem_cons_self) hY₀ (by simp) hPs
      (by
        intro u hu
        rcases List.mem_cons.mp hu with e | hu
        · rw [e]; exact hmB
        · exact hM' u hu)
      hPA'
    exact Or.inl ⟨pre', post', m :: M', Ps, X, Y₀, hc', by rw [hr']; simp,
      Or.inr ⟨htr _ _ _ hf.1, htr _ _ _ hf.2⟩⟩

end Elements.Figures.Pieces
