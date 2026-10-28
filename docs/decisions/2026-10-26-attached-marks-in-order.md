- **A summary of tacit rules names the attached entries in one order, whatever the hash
  seed (tooling, [#539](https://github.com/jackChallis/stoicheia/issues/539)).** Under
  "What it rests on", the summary over a page's list of tacit rules counts the rules found
  only beneath an entry attached to the proposition, its porism or a companion, and names
  those entries, joined by "and", the porism as "its porism": III.25's says "and 1 more
  beneath `Prop25.complete`". In `rests_on`,
  [`scripts/render.py`](../../scripts/render.py) put the names in order with
  `sorted(set(only.values()), key=lambda m: m != "porism")`. The sort is stable and its
  key sets only the porism apart, so every other name kept the order in which Python
  iterates a set of strings, which rests on the hash seed and changes from run to run
  unless PYTHONHASHSEED fixes it. Where two companions or more bring in rules of their
  own, one tree could render the same page two ways: on another train's facts, the summary
  on `book/III/25.md` named III.25's companions one way under the seeds 1 and 2 and the
  other way under 0, 3, 4 and 5, so that the check that the generated pages are current
  could pass on one run and fail on the next.

  The names now keep the order in which their rules are first found:
  `sorted(dict.fromkeys(only.values()), key=lambda m: m != "porism")`. `only` is filled in
  a fixed order, by the entries in the order facts.json attaches them (each proposition's
  `attached` list, read by `attached_entries`) and, within each, by its tacit rules and
  then its other axioms, each in the order facts.json lists them; no set is read or built
  on the way. So the porism is named first, as before, and the companions after it in the
  order they are attached, among those that are the first to bring in a rule the
  proposition's proof does not rest on. The list of rules under the summary is sorted by
  name under each heading, as before.

  The checks keep all their strength: none is weakened, and this train touches no existing
  test's expected values, no lock or schema, no review record, Lean file or statement, and
  not a line of Heath's. On main, no page's summary names more than one attached entry
  (those of III.16, III.18, III.25 and III.30 name one each), so no page changes: rendered
  under the seeds 0 to 3, the edition is the same as main's.

  Approved by this entry: in `scripts/render.py`, the single line of `rests_on` that puts
  the attached entries' names in order, which now reads `dict.fromkeys` where it read
  `set`; no other line of that script changes.

  Approved by this entry as well: in `tests/test_check_style.py`, a new test of the class
  `Wording`, `test_attached_entries_are_named_in_one_order_under_every_hash_seed`, with a
  clause on it added to the class's docstring and to the module's list of cases, and a
  helper, `Wording.entry`, that builds a proved entry of facts.json for it. The test
  renders the summary for a proposition with two companions and a porism, each bringing in
  a rule of its own and the porism attached last, in eight subprocesses under
  PYTHONHASHSEED 0 to 7, and asks that all eight write one page, which names the porism
  first and then the companions in the order they are attached. Against main's line it
  fails, the seeds 0, 3, 4, 6 and 7 naming the companions one way and 1, 2 and 5 the
  other, and with the change it passes.
