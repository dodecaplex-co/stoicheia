- **The retiring laws, rewritten within a narrower allow-list (tooling).** Wave two's
  retirement takes the laws of 31 axioms out of both model harnesses, and nine entries of
  the allow-list for law code would then serve no law: the test that each entry is needed
  would fail on them, and a check may not change in the pull request of the content it
  judges. On 21 October 2026 the owner chose, of three options put to them, "A prep PR
  first, no exception"; [#119](https://github.com/jackChallis/stoicheia/issues/119) is the
  coordinator's record of that choice. So this pull request, landing before the
  retirement, rewrites the retiring laws that call those nine names so that none does, and
  narrows the list by exactly the nine. Each rewritten law decides as before on every
  configuration it is given, and draws the same random numbers in the same order; no law
  that survives the retirement changes.
  [`tests/model/search.py`](../../tests/model/search.py) works out the line's value at a
  point and its sign inside `exists_point_same_side` and `exists_point_opposite_side`, the
  centre's value against the radius inside `line_meets_circle_of_inside`, and the six
  incidences inside `triple_incidence1` and `triple_incidence2`, and drops its helper
  `_ti_hyp`, which nothing else called.
  [`tests/model/hyperbolic.py`](../../tests/model/hyperbolic.py) writes out the conic's
  second point inside `exists_point_on_circle`, the least value along the chord inside
  `line_meets_circle_of_inside` and the six incidences inside the two triple incidence
  laws; it samples `pasch4` and those two laws with `gs_convex('pasch4')` and
  `gs_convex('ti')`, into which the draws of `gs_pasch4` and `gs_ti` move unchanged, as
  wave one moved a sampler into `gs_convex('opposite')`; and it drops `_ti_hyp`,
  `line_meets_circle`, `gs_pasch4` and `gs_ti`, which nothing else used.
  [`scripts/safe_push.py`](../../scripts/safe_push.py) takes out of `LAW_GLOBALS` the calls
  `_ti_hyp`, `lval`, `line_meets_circle` and `sgn` for search.py, the calls `pt_on_circle`,
  `_ti_hyp` and `line_meets_circle` for hyperbolic.py, its generator `gs_pasch4` and its
  generator maker `gs_ti`, and nothing more.
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) keeps its case of a
  generator maker called with no argument, which names `gs_convex()` where it named
  `gs_ti()`. Each harness that reads these laws printed the same bytes before the change as
  after it, at the sample sizes and seeds of `run.py --fast` and of `run.py --full`:
  search.py and hyperbolic.py, which run them, and structured.py and exhaustive.py, which
  import search.py's laws, save for exhaustive.py's timings. The allow-list's test passes
  here, and again with the retirement's two harnesses in place, where the nine are no
  longer needed.
