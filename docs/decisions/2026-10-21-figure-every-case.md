- **A figure that draws every case says so
  ([#30](https://github.com/jackChallis/stoicheia/issues/30)).** `figure_note` in
  [`scripts/render.py`](../../scripts/render.py) put a record's `[figure] case` after a
  fixed "Drawn for one case:". That is false of a figure that draws every case its theorem
  covers: III.25's, `figures/III/25.svg`, draws Euclid's three cases side by side, as
  Heath's three figures do ([the figures against the scans](../reports/figures-against-scans.md)),
  and III.35's, on main, draws Euclid's two. A record's `[figure]` may now give
  `every_case = true`, and the caption under the figure, and its alternative text, then
  read "Drawn for every case: …" in place of "Drawn for one case: …", with the `case`
  naming the cases drawn. [`scripts/heath.py`](../../scripts/heath.py) reads the key as a
  boolean, not required; `load_review` refuses, naming the record, an `every_case` that is
  not true or false, and `every_case = true` with no `case`, and still refuses a `[figure]`
  with neither `case` nor `note`, whatever its `every_case`. P8 of
  `scripts/check_acceptance.py` is unchanged: it still asks a theorem of several cases for
  the `case` text, which now names the cases drawn where the figure draws them all.
  `scripts/check_style.py` is unchanged too: `REVIEW_SHOWN` lists the texts of `[figure]`
  that the page shows, `case` and `note`, and `review_texts` reads only the keys it lists,
  each only as a string, so a boolean is never read as text.
  [review/SCHEMA.md](../../review/SCHEMA.md) gains the key's row and widens the meaning of
  `case`; [STYLE](../STYLE.md), section 7, asks a figure that draws every case to say so,
  with `every_case`. The protected test file
  [`tests/test_check_style.py`](../../tests/test_check_style.py) gains three tests, each
  failing before the change and passing after it: the caption with and without
  `every_case`, a record read with it, and the record refused. No record uses the key yet,
  so no page changes. This check change lands on its own, before train C6b
  ([WORKFLOW](../WORKFLOW.md), section 10: a check lands first), which gives III.25 its
  three companions and sets `every_case` in its record. Whether III.35 may take it is for
  its own review, since its theorem also covers Simson's cases, which its figure does not
  draw: the key means every case the theorem covers, as review/SCHEMA.md says. The
  protected files changed are
  `scripts/render.py`,
  `scripts/heath.py`,
  `review/SCHEMA.md`,
  `tests/test_check_style.py`.
