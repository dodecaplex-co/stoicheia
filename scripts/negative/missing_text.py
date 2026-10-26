"""A review record with no `text` stamp is not current: I.1's `text` line taken away from
its [review] table, and `check_fidelity.py` must fail, saying that I.1's record has no
`text` and that a reader reads the record and stamps it with `scripts/review_stamp.py
--commit`. The record's words are as they were, so the check must not say that they have
changed since the record was reviewed (edited_note), and must not stop with a traceback.
Then `render.record_current`, by which the status table and `check_acceptance.py`'s P11
to P16 count a record as current, must not count I.1's record current without its
`text`, its other stamps made current in memory.
"""

import re

import negative_tests as nt
import render

BUILDS = False

TEXT_LINE = re.compile(r'(?m)^text = "[^"\n]*"\n')


def plant() -> None:
    path = nt.heath.review_path("I", 1)
    saved = path.read_text()
    if len(TEXT_LINE.findall(saved)) != 1:
        nt.failures.append("a record with no `text` stamp: review/I/01.toml has no one "
                           "`text` line to take away; update this test")
        return
    try:
        path.write_text(TEXT_LINE.sub("", saved))
        nt.expect_failure("a review record with no `text` stamp", nt.fidelity(),
                          "review/I/01.toml: [review]: `text` is missing",
                          "a reader reads the record and stamps it with "
                          "scripts/review_stamp.py --commit",
                          unwanted=("I.1: its record has changed since it was reviewed",
                                    "Traceback"))
    finally:
        path.write_text(saved)

    # The record as saved, its stamps made current in memory, so that on a branch where
    # I.1's statement or Lean file has changed only `text` decides; nothing is written.
    facts = render.load_facts()
    record = nt.heath.load_review("I", 1, require_stamp=False)
    record["statement"]["fingerprint"] = nt.heath.review_fingerprint(
        {"propositions": list(facts.values())}, "I.1")
    record["review"]["lean"] = nt.heath.file_hash(nt.heath.lean_path("I", 1))
    record["review"]["text"] = nt.heath.text_hash(saved)
    if not render.record_current("I.1", record, facts):
        nt.failures.append("render.record_current: I.1's record, every stamp current, is not "
                           "counted current; update this test")
        return
    del record["review"]["text"]
    if render.record_current("I.1", record, facts):
        nt.failures.append("a review record with no `text` stamp: render.record_current "
                           "counts it current")
    else:
        nt.refused("a review record with no `text` stamp: render.record_current does not "
                   "count it current")
