- **III.1's `attached` pin lists its companion (Book III,
  [#381](https://github.com/jackChallis/stoicheia/issues/381),
  [#547](https://github.com/jackChallis/stoicheia/issues/547)).** The coordinator's, under
  the owner's decision of 26 October 2026 that the coordinator has recorded on #547: "Yes -
  follow Euclid when possible." This entry claims no further approval of the owner's.

  [The entry of 28 October 2026 on III.2's centre](2026-10-28-iii2-centre.md) registers
  `Prop1.of_circle` as a companion of III.1, "III.1 of_circle", so that facts.json now
  attaches it to III.1 after the porism. The pin in `tests/certificate_expectations.json`
  that held III.1's `attached` list to the porism alone would then fail, though nothing it
  guards has given way. This entry approves the change to `tests/certificate_expectations.json`,
  a protected path, in that one pin: its expected list gains "III.1 of_circle" after "III.1
  Por.", and its reason says why the companion is there. The pin still compares the whole
  list with `equals`, so a companion added or lost later fails it as before; no other pin
  changes, and none is loosened.
