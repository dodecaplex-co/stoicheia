- **Two shared steps of the mixed angles keep their home (Book III, #57).** Under the
  coordinator's orders of 25 October 2026, which rule on item 3 of #57, `len_lt_of_add_lt`
  and `foot_nearest` stay in `Elements/BookIII/MixedAngles.lean`, with the interfaces they
  have now.
  [Brief 0011](../briefs/0011-mixed-angles.md) left their homes open: while
  `Prop20.collinear_iff` and `Foot` were staged, both steps went into the shared module, and
  once those landed the steps "can go beside them, or be derived from them". Both have
  landed: `Prop20.collinear_iff` is proved in `Elements/BookI/HelpersTriangles.lean`, and
  `Foot.exists` and `Foot.unique` in `Elements/BookIII/Squares.lean`.

  The move is declined, for three reasons. It is optional, as the brief says. Stating
  `foot_nearest` through `Foot` would change a shared interface, with its direct callers in
  `Elements/BookIII/MixedAngles.lean`. The staged route in `Staging/Routes/Touching.lean`
  calls `len_lt_of_add_lt` directly; it reaches `foot_nearest` only through
  `surrounds_sameSideOf`, so changing that interface need not change the staged caller.
  And neither move would change what any proposition states or rests on: wherever they
  live, `foot_nearest` cites I.17 and I.19, and `len_lt_of_add_lt` cites I.20, with
  `between_cases` for three points on one straight line. One file keeps the machinery of
  the mixed angles together for a reader, the reason the brief gives for the module.

  The prototype's report, `docs/reports/mixed-angles-prototype.md`, called the two moves
  future work and pending; its section 2 and its condition 3 now say that both steps stay,
  by this entry. No Lean, statement, record or check changes.
