- **The test of the limitations allowed reads every line of its section that holds a `|`,
  and holds a made-up row off III.31 (#421).** The coordinator's orders of 24 October 2026
  assign card #421, which security reviews of #214 raised: two places where
  `tests/test_acceptance_limits.py` was safe but not exact. Neither can matter while the
  table of [ACCEPTANCE, "The limitations allowed"](../ACCEPTANCE.md#the-limitations-allowed)
  names no limitation, as it has named none since pull request #414 of 24 October; each
  matters for the first row that comes back.

  First, `test_allowed_limits_and_table` took as a row only a line of that section that
  begins `| I`, so a compact row (`|III.16|partial|…|`) or an indented one was passed over,
  and a row of the table that `ALLOWED_LIMITS` in `scripts/check_acceptance.py` lacks went
  unseen. That failed safe, since P3 reads the script's list and not the table, but the
  page could then name an allowance the check does not give. Now the test reads every line
  of the section that holds a `|`. Each must begin with one once its leading white space is
  stripped, or the test fails, naming the line; the first two must be the header
  (`| Proposition | Scope | Tag | Why |`) and the delimiter row (`|---|---|---|---|`) as
  the table has them today, or it fails, saying that the header has changed; and every
  line after those two is a row, compared with `ALLOWED_LIMITS` as before.

  Second, `test_an_allowed_row_asks_its_scope_and_tag`, which patches `ALLOWED_LIMITS`
  with a made-up row allowing III.16 partial with the tag `mixed-angles-omitted`, checked
  P3's refusals for III.16 alone. Inside the same patch, it now also asks that III.31,
  made partial with that same tag, get the refusal for a limitation the table does not
  name, so that the row is shown not to allow III.31, another proposition with the same
  tag.

  Each was checked by mutation, in memory, with the test's source compiled under its own
  path and no file of the repository changed. With a compact row for III.16 added after
  the delimiter row of the text the test reads, the test as main has it at e044556d passed
  and the new one failed, on the row it now reads; so too with the row indented by two
  spaces, and with it written in a block quote (`> | III.16 | …`), where the new test fails
  on the line that holds a `|` but begins no row. A row written as the table writes its
  rows failed both, as it should. With the header's last two columns swapped, the old test
  passed and the new one failed, with its message. With `check_acceptance.py`'s lookup of
  a proposition's allowance changed so that a row allows every proposition of its book,
  the whole of the old test passed, and of the new one only
  `test_an_allowed_row_asks_its_scope_and_tag` failed, on the new assertion for III.31.
  Unmutated, both pass all seven cases.

  This entry approves `tests/test_acceptance_limits.py` with these two changes: the table's
  test, which reads every line of the section that holds a `|` and checks the header, and
  the case of the made-up row, which now asks that the row not allow III.31.
