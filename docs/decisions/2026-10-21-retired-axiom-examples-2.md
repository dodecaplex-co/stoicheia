- **Wave two's examples made true, and S7 in full on the transfer rules (tooling).** A check
  change of its own for [#119](https://github.com/jackChallis/stoicheia/issues/119), it lands
  straight after the retirement of 31 axioms, the decisions page's entry "Thirty-one more
  axioms retired, 79 to 48", which leaves 49 in the lock once merged with train C6a. Its
  examples hold only from then, and its stricter style scope passes only once that
  retirement has taken S7's last finding out of the transfer rules. Narrowing the law
  allow-list is no longer part of it: the preparation recorded in
  [2026-10-21-retiring-laws-inlined.md](2026-10-21-retiring-laws-inlined.md) did that, and
  landed before the retirement.
  [`Certificate/FIELDS.md`](../../Certificate/FIELDS.md) now gives 11 as the size of III.2's
  `own_axioms`, the count facts.json measures after the retirement, where it gave 17.
  [`review/SCHEMA.md`](../../review/SCHEMA.md) mends two examples in its account of an
  overlap: the one for the `also` key now says that III.6's record listed
  `Tacit.centre_inside` until that rule became a theorem, and those for the kind "gives"
  follow the catalogue's current rows, naming Generalities 4 beside Diagram-segment 2 for
  III.5, and Generalities 3 as well for III.6, and saying that both are theorems now; its
  fields, requirements and worked TOML examples are as they were.
  [`scripts/check_style.py`](../../scripts/check_style.py) no longer lists
  `Elements/Foundations/Tacit/Transfer.lean` in `REACH_PENDING`, so a finding of S7 in that
  file's rendered docstrings now fails the check, where before it was only reported; that
  only makes the check stricter. The retirement moved `on_circle_of_len_eq` out of the
  file, and with it the docstring whose "Definition 15" named no book. The check now finds
  no S7 there, with Lean and without, and with the old line put back it reports the line
  done.
