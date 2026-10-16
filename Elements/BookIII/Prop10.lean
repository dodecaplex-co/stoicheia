import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop01
import Elements.BookIII.Prop05

/-!
# Book III, Proposition 10

Euclid's text, in Heath's translation: [`heath/III/10.md`](../../heath/III/10.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- A circle does not cut a circle at more points than two. -/
theorem Prop10 {B G H : Point} {ABC DEF : Circle} (hABC : ∃ P : Point, Centre P ABC)
    (hDEF : ∃ P : Point, Centre P DEF) (hB₁ : OnCircle B ABC) (hB₂ : OnCircle B DEF)
    (hG₁ : OnCircle G ABC) (hG₂ : OnCircle G DEF) (hH₁ : OnCircle H ABC)
    (hH₂ : OnCircle H DEF) (hBG : B ≠ G) (hBH : B ≠ H) (hGH : G ≠ H) :
    ABC = DEF := by
  -- For, if possible, let the circle ABC cut the circle DEF at more points than two, namely B,
  -- G, F, H;
  -- let BH, BG be joined and bisected at the points K, L,
  -- and from K, L let KC, LM be drawn at right angles to BH, BG and carried through to the
  -- points A, E.
  -- Then, since in the circle ABC a straight line AC cuts a straight line BH into two equal
  -- parts and at right angles,
  -- the centre of the circle ABC is on AC. [III. 1, Por.]
  -- Again, since in the same circle ABC a straight line NO cuts a straight line BG into two
  -- equal parts and at right angles,
  -- the centre of the circle ABC is on NO.
  -- But it was also proved to be on AC, and the straight lines AC, NO meet at no point except
  -- at P;
  -- therefore the point P is the centre of the circle ABC.
  -- Similarly we can prove that P is also the centre of the circle DEF;
  -- therefore the two circles ABC, DEF which cut one another have the same centre P: which is
  -- impossible. [III. 5]
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
