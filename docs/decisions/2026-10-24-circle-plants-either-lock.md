- **Two circle plants made to hold whether Circle 3 is locked or proved (checks,
  [#294](https://github.com/jackChallis/stoicheia/issues/294)).** The retirement of
  Circle 3 (`Tacit.outside_of_between`), the next train of #294, takes it out of
  `Certificate/axioms.lock` and proves it after III.2, so that `facts.json` lists it among
  its `proved_rules`, and Circle 2 with it, each citing III.2 in `proved_rule_cites`. Two
  negative plants were written for a lock that holds Circle 3, and would then go wrong.
  `circle_renamed.py` renames the rule in the lock, and with no such line there it stops
  before planting anything. `circle_proved.py` keeps the citations `facts.json` gives
  Circle 2, and with III.2 among them its first case, Circle 2 proved with nothing
  forbidden beneath it, would pass by the route that cites III.2, where the plant wants
  the refusal; its second case, Circle 2 resting on locked Circle 3, would have no locked
  Circle 3 to rest on. This change lands first, in a check change of its own, so that the
  retirement changes no check code.

  Each plant now looks at the lock. While Circle 3 is an axiom, each plants exactly what it
  planted before. Once Circle 3 has left the lock, `circle_renamed.py` renames it in the
  copy's `proved_rules` and `proved_rule_cites`, the tables that keep it then, and wants the
  same refusal, that it is not an axiom in the lock (nor a proved rule); and
  `circle_proved.py` gives Circle 2 an empty `proved_rule_cites` in both cases, and for
  both cases writes Circle 3 back into the lock and into the copy's tables of axioms, with
  the statement it keeps as a theorem, before restoring the lock as it found it. No plant
  is dropped and no expected refusal is loosened: each case wants the words it wanted, and
  the first case of `circle_proved.py` now asks for a citation of nothing in both states,
  as it always meant to. It belongs to #294, within #152.

  This entry approves the change to `scripts/negative/circle_renamed.py`, which renames
  Circle 3 in the lock and the copy's tables of axioms while it is locked, and in the copy's
  tables of proved rules once it is proved.

  This entry approves the change to `scripts/negative/circle_proved.py`, whose Circle 2
  cites nothing in either case, and which locks Circle 3 for both cases when the lock no
  longer holds it.

  This entry approves the change to `tests/test_negative_tests.py`, which tests both plants
  with Circle 3 proved from III.2: the lock and the copy each plant hands the check, and
  the lock restored, and the restoration of a lock that held neither rule; each new test
  fails on the plants as they were, in its retired case.
