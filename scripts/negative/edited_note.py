"""An edited note in I.1's review record, under a current `text` stamp, makes the record
stale, as a changed Lean file does (stale_lean): `check_fidelity.py` must say that I.1's
record has changed since it was reviewed. A comment added to the record and its stamp
moved, its words as they were, do not: the check must say what it says of the record
unchanged.
"""

import re
from collections import Counter

import negative_tests as nt
import review_stamp

BUILDS = False


def naming_i1(out: str) -> list[str]:
    """The lines of a check's output that name I.1 or its review record."""
    return [line for line in out.splitlines()
            if re.search(r"\bI\.1\b|review/I/01\.toml", line)]


def plant() -> None:
    """An edited note under a current `text` stamp. I.1's record is first given a current
    `text` stamp, written over the one it carries, so the test holds on a branch that has
    edited the record too; then the first letter of its first note changes case,
    and the check must say the record changed. With a comment added and its stamp moved,
    and its words as they were, the check must say what it says of the record unchanged:
    the same outcome, the same lines naming I.1 or its record, and no traceback."""
    path = nt.heath.review_path("I", 1)
    saved = path.read_text()
    stamped = review_stamp.set_stamp(saved, "review", "text", nt.heath.text_hash(saved))
    lines = stamped.split("\n")
    at = next((i for i, line in enumerate(lines) if line.startswith('note = "')), None)
    # One letter changed, not a word added: the note keeps its length, so it stays within
    # heath.NOTE_LIMIT, and the check finds the edit, not the length.
    start = len('note = "')
    planted = None if at is None else \
        lines[at][:start] + lines[at][start:start + 1].swapcase() + lines[at][start + 1:]
    if planted is None or planted == lines[at]:
        nt.failures.append("an edited note: review/I/01.toml has no `note` beginning with a "
                           "letter; update this test")
        return
    edited = lines[:at] + [planted] + lines[at + 1:]
    try:
        path.write_text("\n".join(edited))
        nt.expect_failure("an edited note in a review record", nt.fidelity(),
                          "I.1: its record has changed since it was reviewed")
        # The words as they were, under a current `text` stamp: what the check says then.
        path.write_text(stamped)
        baseline = nt.fidelity()
        before = naming_i1(baseline.stdout + baseline.stderr)
        # The same words with a comment above them and the `text` stamp first in
        # [review]: comments and layout are not the record's text.
        moved = [line for line in lines if not line.startswith("text = ")]
        review = moved.index("[review]")
        moved.insert(review + 1, f'text = "{nt.heath.text_hash(saved)}"')
        moved.insert(0, "# A comment planted by scripts/negative_tests.py.")
        path.write_text("\n".join(moved))
        result = nt.fidelity()
        out = result.stdout + result.stderr
        # On a contributor's branch the baseline may name I.1 too, say for a changed
        # Prop01.lean: the lines naming I.1 must then be the same lines, as many times and
        # in the same order.
        after = naming_i1(out)
        added = list((Counter(after) - Counter(before)).elements())
        missing = list((Counter(before) - Counter(after)).elements())
        if result.returncode != baseline.returncode or after != before or "Traceback" in out:
            detail = []
            if result.returncode != baseline.returncode:
                detail.append(f"exit {result.returncode}, not {baseline.returncode} as with "
                              "the record unchanged")
            if added:
                detail.append(f"also says {added!r}")
            if missing:
                detail.append(f"no longer says {missing!r}")
            if after != before and not added and not missing:
                detail.append("says the same lines in another order")
            if "Traceback" in out:
                detail.append("a traceback")
            nt.failures.append("a comment and a moved stamp in I.1's record: not as the record "
                               f"unchanged ({'; '.join(detail)})")
            print(out[-3000:])
        else:
            print("✓ a comment and a moved stamp in I.1's record: not called a change")
    finally:
        path.write_text(saved)
