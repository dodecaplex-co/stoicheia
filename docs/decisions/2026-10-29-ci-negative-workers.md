<!-- entry: id=ci-negative-workers cards=607 line="CI's negative job runs the negative tests in four workers, one for each core of the free runner." -->
- **CI's negative job in four workers (checks,
  [#607](https://github.com/dodecaplex-co/stoicheia/issues/607)).** On 28 October 2026 the
  owner said, of the pre-flight's speed: "running on my own hardware is ideal if possible.
  Then the speedup on the free 4 core. then explore 8 core / 16 core"; card #607 is the
  coordinator's record of it. The negative tests can run in N workers since
  [2026-10-28-negative-workers.md](2026-10-28-negative-workers.md), one by default, and had
  never run on Linux in more than one.

  A benchmark measured it on GitHub's free runner (run 40842214599, 29 October 2026): a
  workflow on a branch of its own, never merged, which ran CI's negative job step for step
  and timed `scripts/negative_tests.py` at a given worker count, on main at 1b0235a36.
  Each job was meant to time 1, 2, 3 and 4 workers on one machine, in opposite orders; each
  stopped after its first count, so the measurement is one count on each of two machines of
  the same kind:

  | Workers | Seconds | CPU used | Largest process | Least free memory |
  |---|---|---|---|---|
  | 1 | 714 | 119% | 1.7 GiB | 10.2 GiB |
  | 4 | 434 | 292% | 1.7 GiB | 9.2 GiB |

  Both machines: ubuntu-latest, 4 cores of an AMD EPYC 9V45, 15.6 GiB, image
  ubuntu24-20261026.354.1. CPU used is the run's processor time over its wall time;
  memory is GNU time's peak for the largest process, and vmstat's least free memory every
  five seconds through the run. In both runs every plant was caught; the one failure, the
  same in both, was `path_faults`' check of the unplanted index, which refused the
  benchmark's own file, a `.py` under `.github/`, as it should. Four workers took 39% less
  time, with swap unused and more than half the memory free, though the plants’ recorded
  times totalled about twice the one-worker total and the run used 48% more processor
  time. So four is faster than one; whether two, three or more than four is faster still
  was not measured, and
  GitHub draws the runner's CPU by lot (the same run's third job drew an AMD EPYC 7763), so
  these numbers are for the 9V45.

  So the step that runs the negative tests in ci.yml's `negative` job sets
  `STOICHEIA_NEGATIVE_WORKERS` to 4, the faster of the two counts measured and one worker
  for each core, and `scripts/test_safe_push.py` holds that value in the job's contract,
  so that a change to it is a change to the contract, where review sees it. The cadence's
  run (safe-push-tests.yml), which holds no landing, stays in one worker; the pre-flight's
  count on the lane's machine is not changed here.

  This entry approves the change to `.github/workflows/ci.yml`, which runs the negative
  tests in four workers.

  This entry approves the change to `scripts/test_safe_push.py`, whose contract for the
  `negative` job holds the four workers.
