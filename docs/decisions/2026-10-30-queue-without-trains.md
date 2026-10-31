<!-- entry: id=queue-without-trains cards=283 line="The merge queue's judge stops using the train check, so that trains can be retired; ordinary queued pull requests are judged alike, while automatic-revert entries keep their separate path." -->
- **The queue's judge without the train check (landing,
  [#283](https://github.com/dodecaplex-co/stoicheia/issues/283)).** On 30 October 2026,
  asked whether to retire trains, with their check, tests and docs, the owner answered:
  "Yes take these out." Those are the owner's words; what follows is the coordinator's
  reading of them.

  The merge queue's judge stays, since the owner plans to turn the queue on, but it
  imported the train check, `scripts/check_train.py`, and could not start without it. So
  the judge stops depending on the train check first, and the trains, their check and its
  tests are retired in the next part. The order matters: the judge runs main's copy of
  its scripts, and were the train check deleted first, main's judge would fail on its
  import.

  `scripts/check_queue.py` now reads what each queued entry changes from that entry's diff
  alone, with a `derive_new` of its own, carried over from the train check and finding
  what it found: the checks, the propositions and the foundations the diff touches. It no
  longer judges an entry on a `train/*` branch by the train check's rules (its Members
  table, the reviews named there and its What is new section), nor adds to the tests it
  chooses those such a section declared beyond the diff. An entry from such a branch is
  judged as every other ordinary entry is: by its pre-flight, by whether the group keeps
  the lines it changed, and by the tests of what its diff changes. Automatic-revert
  entries keep their separate path.

  `tests/test_check_queue.py` builds its groups from single parts, each pull request one
  commit whose body is its pre-flight block, and drops the seven cases that tested only
  the train check's rules or the declarations of a What is new section.

  Why: since 30 October 2026 work lands as single parts
  ([the entry of that day](2026-10-30-single-parts-with-cards.md)), and no train is to
  land, so nothing in the queue should need the train check; and the queue's judge must
  keep working while the train check is taken out.
