import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop20
import Elements.BookI.Prop24
import Elements.BookIII.Prop14

/-!
# Book III, Proposition 15

Euclid's text, in Heath's translation: [`heath/III/15.md`](../../heath/III/15.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- Of straight lines in a circle the diameter is greatest, and of the rest the nearer to the centre
is always greater than the more remote. -/
theorem Prop15 {A B C D E F G H K : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hF : OnCircle F ABCD)
    (hG : OnCircle G ABCD) (hE_BC : ¬ Collinear B C E) (hE_FG : ¬ Collinear F G E)
    (hH : Collinear B C H) (hEH : ∀ P : Point, Collinear B C P → P ≠ H → ∠ E H P = ∟)
    (hK : Collinear F G K) (hEK : ∀ P : Point, Collinear F G P → P ≠ K → ∠ E K P = ∟)
    (hnearer : ‖E H‖ < ‖E K‖) :
    ‖B C‖ < ‖A D‖ ∧ ‖F G‖ < ‖B C‖ := by
  -- Let ABCD be a circle, let AD be its diameter and E the centre; and let BC be nearer to the
  -- diameter AD, and FG more remote;
  -- I say that AD is greatest and BC greater than FG.
  -- For from the centre E let EH, EK be drawn perpendicular to BC, FG.
  -- Then, since BC is nearer to the centre and FG more remote, EK is greater than
  -- EH. [III. Def. 5]
  -- Let EL be made equal to EH, through L let LM be drawn at right angles to EK and carried
  -- through to N, and let ME, EN, FE, EG be joined.
  -- Then, since EH is equal to EL,
  -- BC is also equal to MN. [III. 14]
  -- Again, since AE is equal to EM, and ED to EN,
  -- AD is equal to ME, EN.
  -- But ME, EN are greater than MN, [I. 20]
  -- and MN is equal to BC;
  -- therefore AD is greater than BC.
  -- And, since the two sides ME, EN are equal to the two sides FE, EG,
  -- and the angle MEN greater than the angle FEG,
  -- therefore the base MN is greater than the base FG. [I. 24]
  -- But MN was proved equal to BC.
  -- Therefore the diameter AD is greatest and BC greater than FG.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
