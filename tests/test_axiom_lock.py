#!/usr/bin/env python3
"""The axiom lock as `check_fidelity.py --write-lock` writes it (#260): from the committed
facts.json, with no axiom and no word changed, the writer gives back
Certificate/axioms.lock byte for byte, its header and layout included, for the lock's bytes
are pinned by model/lock.sha256, tests/model/lock.sha256 and the model's generated files.
And the comparisons can fail: a header changed by one character is seen, and so is one
word's definition changed in facts.json's data, read into memory.

    python3 -I tests/test_axiom_lock.py

Standard library only; no Lean, Git or network. Each case has a copy of the lock in a
temporary directory of its own and writes only there, never to the lock or facts.json, and
checks that both are as they were.
scripts/negative_tests.py runs it after the risk class regressions, so CI's `negative` job
runs it on every push to main and on every pull request of class R3 and above
(scripts/risk.py), and the cadence runs it on main every six hours.
"""

import contextlib
import io
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import check_fidelity  # noqa: E402

LOCK, FACTS = check_fidelity.LOCK, check_fidelity.FACTS


def parting(written: str, committed: str):
    """Where two locks first differ: (the line's number, counted from 1, the line as the
    written lock has it, as the committed lock has it), each line with its newline and
    empty where that lock has ended; None when they are the same text."""
    if written == committed:
        return None
    new, old = written.splitlines(keepends=True), committed.splitlines(keepends=True)
    index = next((i for i, (a, b) in enumerate(zip(new, old)) if a != b),
                 min(len(new), len(old)))
    return (index + 1, new[index] if index < len(new) else "",
            old[index] if index < len(old) else "")


class AxiomLock(unittest.TestCase):
    def setUp(self):
        self.committed = LOCK.read_bytes()
        self.facts = FACTS.read_bytes()
        # Cleanups run last first: the copy goes, then the lock and facts.json are checked.
        self.addCleanup(self.untouched)
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.copy = Path(temp.name) / "axioms.lock"
        shutil.copyfile(LOCK, self.copy)

    def untouched(self):
        self.assertTrue(LOCK.read_bytes() == self.committed, f"{LOCK} was written")
        self.assertTrue(FACTS.read_bytes() == self.facts, f"{FACTS} was written")

    def write_lock(self, facts):
        """`--write-lock`'s work on the copy of the lock: its exit code, and what it
        printed."""
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = check_fidelity.write_lock(facts, self.copy)
        return code, out.getvalue()

    def assertSameLock(self, written: str, committed: str):
        where = parting(written, committed)
        if where:
            self.fail(f"the lock differs from the committed lock at line {where[0]}: "
                      f"{where[1]!r} where it has {where[2]!r}")

    def test_lock_written_again_is_the_committed_lock(self):
        # The card's done-when (#260): `--write-lock` on main reproduces main's lock exactly.
        code, out = self.write_lock(json.loads(self.facts))
        self.assertEqual(code, 0, out)
        self.assertIn("(no change)", out)
        self.assertSameLock(self.copy.read_bytes().decode("utf-8"),
                            self.committed.decode("utf-8"))
        self.assertTrue(self.copy.read_bytes() == self.committed)

    def test_lock_renders_as_committed(self):
        # The header and the layout are the writer's alone: the lock's own tables, read and
        # rendered again, give back its text, whatever facts.json holds.
        self.assertSameLock(check_fidelity.render_lock(*check_fidelity.read_lock(LOCK)),
                            self.committed.decode("utf-8"))

    def test_a_header_changed_by_one_character_is_seen(self):
        header = check_fidelity.LOCK_HEADER
        middle = len(header) // 2
        while header[middle] == "\n":
            middle += 1
        changed = header[:middle] + ("y" if header[middle] == "x" else "x") + header[middle + 1:]
        line = header[:middle].count("\n") + 1
        committed = self.committed.decode("utf-8")
        with mock.patch.object(check_fidelity, "LOCK_HEADER", changed):
            rendered = check_fidelity.render_lock(*check_fidelity.read_lock(LOCK))
            # The fault of #260 itself: a header the writer has changed, with no axiom and
            # no word changed, is no change to the lock's tables, so the writer reports
            # none; only the bytes show it.
            code, out = self.write_lock(json.loads(self.facts))
        self.assertEqual(check_fidelity.LOCK_HEADER, header)
        where = parting(rendered, committed)
        self.assertIsNotNone(where, "a changed header rendered as the committed lock")
        self.assertEqual(where[0], line, where)
        self.assertEqual(code, 0, out)
        self.assertIn("(no change)", out)
        written = self.copy.read_bytes()
        self.assertFalse(written == self.committed, "a changed header wrote the committed lock")
        self.assertEqual(parting(written.decode("utf-8"), committed)[0], line)

    def test_a_word_changed_is_seen(self):
        facts = json.loads(self.facts)
        name = sorted(facts["vocabulary"])[0]
        self.assertIn(name, check_fidelity.read_lock(LOCK)[1])
        facts["vocabulary"][name] += " (planted)"
        code, out = self.write_lock(facts)
        self.assertEqual(code, 0, out)
        self.assertNotIn("(no change)", out)
        self.assertIn(f"  ~ vocabulary {name}\n", out)
        written = self.copy.read_bytes()
        self.assertFalse(written == self.committed, "a changed word wrote the committed lock")
        # The word's line, and no other, is changed.
        new = written.decode("utf-8").splitlines(keepends=True)
        old = self.committed.decode("utf-8").splitlines(keepends=True)
        self.assertEqual(len(new), len(old))
        changed = [(a, b) for a, b in zip(new, old) if a != b]
        self.assertEqual(len(changed), 1, changed[:3])
        self.assertTrue(changed[0][0].startswith(f"{check_fidelity.toml_string(name)} = "),
                        changed)
        self.assertEqual(changed[0][0], changed[0][1][:-2] + ' (planted)"\n')


if __name__ == "__main__":
    unittest.main()
