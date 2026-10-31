<!-- entry: id=trains-retired cards=283 line="Trains are retired: the train check, its tests and the pre-flight's train step are taken out, and every part lands as a pull request of its own." -->
- **Trains retired (landing,
  [#283](https://github.com/dodecaplex-co/stoicheia/issues/283)).** On 30 October 2026
  the coordinator put it to the owner that trains should go, together with their check,
  their tests and their docs, and the owner replied: "Yes take these out." Those are the
  owner's words; what follows is the coordinator's reading of them.

  A train was a pull request from a `train/*` branch that merged several reviewed member
  branches, with a Members table and a What is new section in its body, judged by a check
  of its own at the pre-flight and again at the merge. Work now lands one part at a time,
  so no train is to land, and everything that served trains alone comes out. The queue's
  judge had stopped depending on the train check in the part before this one
  ([the entry](2026-10-30-queue-without-trains.md)); the merge queue itself, its judge
  and the landing tool's queue mode all stay.

  The train check, `scripts/check_train.py`, is deleted. Its tests,
  `tests/test_check_train.py`, are deleted with it. `scripts/safe_push.py` no longer has a
  train step: a `train/*` branch needs no `--body-file`, its pre-flight runs no step
  "3. train", the main-checks cache serves it as it serves any branch, its pull request's
  summary needs no train row to be current, and the merge no longer compares a train's
  body at each of its reads; the harness hands over and copies `safe_push.py` and `heath.py`
  alone, and nothing in the landing tool imports a module through `importlib` any more.
  `scripts/test_safe_push.py` drops its Trains class and the other cases of the train step,
  and its test that no module is imported late now holds for the whole of the landing
  tool, with no exception left for the train check. In `tests/test_check_queue.py` the
  name of the queue-tests step it reads follows the workflow's new name, and the case
  that ran the judge with the train check taken away goes, since every case now runs it
  so. `.github/workflows/ci.yml` stops running the train check's tests in its queue-tests
  job and renames that job's step. The comment on the queue's timeout in
  `.github/workflows/queue-judge.yml` no longer counts the train check's tests in the
  slowest group a merge group can choose. `checks/README.md` says "part" where it said
  "train" for the change that adds or alters a check.

  WORKFLOW.md says that work lands as single parts, in place of its sections on building
  and splitting trains, and its other mentions of trains now name a pull request, an
  entry of the queue or a part; AGENTS.md says "part" too.

  Why: every part now lands alone, as its own pull request
  ([the decision](2026-10-30-single-parts-with-cards.md)), so the train check judged
  nothing that would land, and its tests still took about 2.5 minutes of CI's
  queue-tests job on every pull request.
