- **Two slow negative plants narrowed, and native_decide folded into forbidden_commands
  (checks, [#581](https://github.com/jackChallis/stoicheia/issues/581)).** On 27 October
  2026 the owner chose, of the options put to them, "Narrow and fold (Recommended)"; card
  #581 is the coordinator's record of it. The aim is a faster landing lane with every
  fault still caught. An independent map of the plants found almost none redundant: the
  time goes in how often the suite runs, up to eleven times for a train that changes a
  check, and in a few slow plants. This train makes two of the slowest faster and drops
  the one plant whose fault another plant already plants, keeping its fixture. The checks
  the plants run (`check_fidelity.py`, `check_style.py` and `tests/test_certificate.py`)
  do not change, no expected refusal is loosened, and no fault case or control is dropped.

  `certificate_constructor_counting.py` counted congruence constructors in a copy of the
  certificate and ran all of `tests/test_certificate.py` against it, then again against the
  restored certificate. The failure it wants, on transformers with no step, is a case of
  `CommonNotion4Tests`, and so are the real-step cases the restored run must pass; the
  file's other classes compile fixtures of their own for other questions. Both runs are now
  of that class alone. The whole file still runs in the check registry, on the certificate
  as committed.

  `merge_conflict_markers.py` copied every tracked file and ran the whole style checker on
  the copy eighteen times: once unplanted, once for each of its thirteen faults, and once
  for each of its four setext headings. It now copies, from Git's tracked files as before,
  only the two files it plants (`CONTRIBUTING.md` and `NOTICE`), the two texts the style
  checker reads in any tree (`README.md` and `docs/reading.md`), and the scripts at the top
  of `scripts/`, among them the checker and the modules it imports. The eighteen runs and
  their expected lines are unchanged. One thing is added: the unplanted copy must pass, so
  that a checker unable to run on the copy cannot pass the four headings by failing as the
  baseline failed. The style check of the whole tree, S23 among its rules, runs in the
  check registry.

  `native_decide.py` planted `theorem planted_native : 2 + 2 = 4 := by native_decide` in
  I.16's file and wanted `check_fidelity.py` to name its file and line;
  `forbidden_commands.py` already planted the same line in a new file of each folder the
  scan reads, and wanted the same words, from the same search. What only the first had was
  its fixture, a proposition's own file, with the theorem inside its namespace. That
  fixture now goes into `forbidden_commands.py`, planted beside the others and judged by
  the same run of the check, which must name I.16's file and the line; and
  `native_decide.py` goes.

  Each narrowed plant was checked against a mutation of what it tests, through the
  runner: with the transformer case taken out of `tests/test_certificate.py`, the
  certificate plant fails; with S23's scan emptied, all thirteen marker faults go uncaught
  and the plant fails; with S23 refusing every seven-equals line, the four headings fail;
  with the copy short of `docs/reading.md`, the unplanted copy fails and the plant with
  it; and with the search for `native_decide` taken out of `check_fidelity.py`, the I.16
  case goes uncaught with the others.

  The whole suite, run on one machine at a similar load, first at main as it stood
  (bef94c2c7) and then with this change on the same commit, took 926 seconds for 48 plants
  and then 601 for 47. Of the difference, the certificate plant gives 158 seconds (177 to
  19), the markers plant 91 (94 to 3) and the dropped plant 3; the rest is the load, which
  moved the untouched plants by a few seconds either way.

  This entry approves the change to `scripts/negative/certificate_constructor_counting.py`,
  whose two runs are now of `CommonNotion4Tests` alone.

  This entry approves the change to `scripts/negative/merge_conflict_markers.py`, which
  copies only the files its checker needs and requires the unplanted copy to pass.

  This entry approves the change to `scripts/negative/forbidden_commands.py`, which plants
  a `native_decide` in I.16's file too.

  This entry approves the removal of `scripts/negative/native_decide.py`, whose fixture
  `forbidden_commands.py` now plants.

  This entry approves the change to `tests/test_negative_tests.py`, whose test of the
  certificate plant's restoration expects the class in the command it runs.
