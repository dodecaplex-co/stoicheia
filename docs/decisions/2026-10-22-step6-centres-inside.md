- **III.4, III.13, III.21, III.22 and III.32 without a centre's existence (brief
  0008).** Train C6c carries out [brief 0008](../briefs/0008-centre.md)'s step 6, and
  among its restatements are these five, each of which loses every hypothesis that a
  circle of it has a centre.
  - III.4: in `Elements/BookIII/Prop04.lean`, `Prop4` loses `hABCD`, and its proof takes
    the centre F from III.1 (`Prop1`), where Heath's bracket cites it; III.4's conditions
    `hAC` and `hBD`, said of every centre, stay as they were.
  - III.13: in `Elements/BookIII/Prop13.lean`, `Prop13` loses `hABDC`, `hEBFD` and
    `hACK`; its step for circles touching within takes the centres G and H from the rule
    `Tacit.exists_centre`, and its step for circles touching without, which handed
    `hABDC` and `hACK` on to III.2, has nothing to hand on.
  - III.21: in `Elements/BookIII/Prop21.lean`, `Prop21` loses `hABCD`, and its proof
    takes the centre F from that rule, as Heath's step has no bracket.
  - III.22: in `Elements/BookIII/Prop22.lean`, `Prop22` loses `hABCD`, having nothing to
    hand on, since neither III.2 (`Prop2`, `Prop2.triangle`) nor III.21 now asks for a
    centre.
  - III.32: in `Elements/BookIII/Prop32.lean`, `Prop32` loses `hABCD`, and its lemma
    `Prop32.sameSide` loses `hα`; its proof takes its centre from the rule.

  Brief 0008's section 4 lists each of the five with the hypothesis it drops and where its
  centre comes from, and the coordinator froze the brief on 18 October 2026. The warrant
  is the owner's decision of 18 October 2026 (the coordinator's record is
  [#59](https://github.com/jackChallis/stoicheia/issues/59)), which the brief's section 1
  quotes, checked against their comment there:
  "the statements that only assume a centre exists drop that hypothesis, those that name
  the centre keep it".
