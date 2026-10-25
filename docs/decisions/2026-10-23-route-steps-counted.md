- **A modified route says how many steps it changes
  ([#380](https://github.com/jackChallis/stoicheia/issues/380)).** For every route of kind
  `modified`, [`scripts/render.py`](../../scripts/render.py) wrote "one step changed": in
  the line under the enunciation, in the page's Argument row, in the certificate's
  Argument column, and in the book's summary, which heads `book/III/index.md`, Book III's
  section of `CERTIFICATE.md` and its row of `README.md`. That was false of six
  propositions. The review records of III.8, III.16, III.26, III.28 and III.29 each hold
  two passages of kind `different`, and III.24's three, and their pages list each of them
  as "Argued another way". The pages now give the count: "Euclid's, two steps changed" in
  the certificate's column, "Euclid's argument, with two steps changed" under the
  enunciation, and "Euclid's, with three steps changed." in III.24's Argument row, while
  III.2, III.4, III.10, III.17, III.21 and III.27, with one each, still say "one step
  changed". The book's summary says a count when every modified proof shares it, and
  otherwise "one or more steps changed", true of each; so Book III's now says that 12
  follow Euclid's argument with one or more steps changed, and each proof's own count is
  on its page and in the certificate's column. The certificate's key to the table reads
  the label for any count: one step argued another way, two, and so on, each named on the
  page.

  The count is the number of the record's `different` passages because that is how
  [review/SCHEMA.md](../../review/SCHEMA.md) marks a step argued another way: such a
  passage makes the route `modified` or `alternative`, never `euclid`, and the page leads
  its note with "Argued another way", so the number a page states is the number of those
  notes a reader finds on it. No other field of a record counts steps. SCHEMA also lets a
  modified route name its step in the route's note alone, with no `different` passage;
  for such a record the pages say "with a step changed", true without a count, the book's
  summary says "one or more", and the certificate's key names that label only while some
  record uses it. As of 23 October 2026 no record does.

  Nothing is loosened: no check or test is weakened, and no expected value, lock, schema,
  review record, Lean file, statement or line of Heath's changes. Books I and II have no modified
  route, and their pages are unchanged. The regenerated pages differ from main's in the
  route's words alone. The table in brief 0004 and the decisions page's entry "When a
  route is 'one step changed'" are dated records and stay as they are. This closes #380.

  This entry approves the change to `scripts/render.py`, whose new `different_passages`
  and `steps_changed` give the count to `route_word`, the line under the enunciation, the
  Argument row, the book's summary and the certificate's key.

  This entry approves the change to `tests/test_check_style.py`, whose new class
  `RouteSteps` plants records in memory with none, one, two and three passages argued
  another way: each of its three tests fails against main's render.py, which is right
  only where one step changes, and passes after the change.
