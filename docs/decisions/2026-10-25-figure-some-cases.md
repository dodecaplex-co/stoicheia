- **A figure that draws some of its theorem's cases says so
  ([#251](https://github.com/jackChallis/stoicheia/issues/251)).** The coordinator's
  orders of 25 October 2026 assign card #251: III.35's figure, `figures/III/35.svg`,
  draws Euclid's two cases side by side, both straight lines through the centre and
  neither through it, but its theorem also covers the cases Simson added, one straight
  line through the centre and the other not, which the figure does not draw. The caption
  under it reads "Drawn for one case: …", which is false of a figure that draws two, and
  `every_case`, the key that leads the caption "Drawn for every case: …", would be false
  too, since review/SCHEMA.md gives it only to a figure that draws every case its theorem
  covers. Card #424 records the same lead as a follow-up of Book III's sweep.

  A record's `[figure]` may now give `some_cases = true`, and the caption under the
  figure, and its alternative text, then read "Drawn for some of its cases: …", with the
  `case` naming the cases drawn and the `note` the cases the theorem covers that the
  figure does not draw. `scripts/heath.py` reads the key as a boolean, not required, as it
  reads `every_case`; `load_review` refuses, naming the record, a `some_cases` that is not
  true or false, a `some_cases = true` with no `case` or with no `note`, and a `[figure]`
  that gives `every_case` and `some_cases` together, whatever their values. P8 of
  `scripts/check_acceptance.py`
  is unchanged: it still asks a theorem of several cases for the `case` text.
  `scripts/check_style.py` is unchanged too, since its `review_texts` reads only the
  string keys `REVIEW_SHOWN` names, `case` and `note`. No record uses the key yet, so no
  page changes; III.35's record sets it in a train of its own, after this check lands, as
  WORKFLOW section 10 asks.

  This entry approves `scripts/heath.py` with the new key `some_cases` and its four new
  refusals: a value that is not true or false, a `some_cases = true` with no `case`, one
  with no `note`, and the key beside `every_case`. This entry approves
  `scripts/render.py` with the caption's third
  lead, "Drawn for some of its cases". This entry approves `tests/test_check_style.py`
  with its new cases in `FigureCaption`: the caption with `some_cases`, a record read with
  it, and the records refused. Each of the fourteen new cases passes with this change.
  With main's `scripts/heath.py` and `scripts/render.py`, thirteen failed; the other one,
  a caption with `some_cases = false` that keeps "Drawn for one case", holds what main's
  `scripts/render.py` already wrote. This entry approves `review/SCHEMA.md` with the key's
  row, and `case` and `note` widened to name it, and STYLE, section 7, and the proposition
  template gain the key beside `every_case`.
