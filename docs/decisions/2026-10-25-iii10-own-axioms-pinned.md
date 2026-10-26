- **III.10's own Lean no longer calls Intersections 5, and a pin keeps it so (checks,
  [#476](https://github.com/jackChallis/stoicheia/issues/476)).** The coordinator's orders
  of 25 October 2026 assign card #476, from that day's stand-in review: III.10 called III.2
  twice and `Tacit.line_circle_beyond` three times only to place C and O on the
  perpendiculars to BH and BG. The proof train before this one produces them by Postulate 2
  instead, since the argument needs a second point of each perpendicular and never where
  it meets the circle. This train changes no Lean file, lock, statement, definition,
  record or `--` line; `facts.json` stays as that train left it.

  The orders asked that III.10's pin move in a train of its own before the proof that
  changes it, so that the proof would not land against a pin it breaks. No expectation in
  `tests/certificate_expectations.json` named III.10, so nothing was pinned that the proof
  could break, and the proof landed alone. What the card asks is that the certificate
  expectation follow the proof. The expectation added here fails against the certificate
  of the earlier proof, which is the point of it, and so it lands after the proof, not
  before: landed first, it would have failed `check_fidelity.py` on main.

  The pin reads III.10's `own_axioms`, the axioms its own Lean names, and asks that they
  exclude `Tacit.line_circle_beyond`. It cannot read `axioms` or `inherited`: Intersections
  5 stays among what III.10 rests on, through `Prop2.triangle` and Book Zero lemmas that
  call it, and the change was never meant to take it out of those. On a scratch copy of
  main's `facts.json` at commit 560da15a2, outside the repository,
  `check_fidelity.py --facts` fails, naming III.10 and the rule; on the certificate after
  the proof it passes.

  This entry approves the change to `tests/certificate_expectations.json`, which gains
  one expectation, that III.10's `own_axioms` exclude `Tacit.line_circle_beyond`; no
  expectation or listed name is removed.
