"""Without a build, in a scratch copy of I.1's file in a temporary tree, read by the source
scan alone, as in set_option_spellings: `#guard_msgs` under a docstring that pins an error:
closed up, with a remark or a comment between the two, under a filter or an option, with
positions, two errors at once, and `error:` alone on its line: each refused by its file and
line. Not refused: a docstring that pins only an info message or a warning, a theorem's own
docstring holding `error:`, `error:` in a comment or a module docstring before a
`#guard_msgs`, and the words in a comment or a string. Then the same pin alone in a small
tree of its own, at each path of the allow-list, `model/Check/RoundTrip.lean` and
`model/Model/Audit.lean`, must pass, and at a new file beside each of them, at each one's
name in the other's folder, in `Audit/` and in `Staging/`, is refused (#197).
"""

import tempfile
from pathlib import Path

import negative_tests as nt

BUILDS = False

# `#guard_msgs` under a docstring that pins an error (#197), in Lean 4.35's forms: plain,
# closed up, with a comment or a remark between the two, under a filter or an option, with
# positions, two errors at once, and the command closed up to `in`; each is (the command
# check_fidelity.py names, the lines of Lean). GUARD_PIN_KEPT holds what the rule does not
# refuse: a docstring that pins an info message, a theorem's own docstring, `error:` in a
# comment, a module docstring or a remark before a `#guard_msgs`, and a string.
GUARD_PINS = (
    ("#guard_msgs", '/-- error: boom\n⊢ 0 = 1 -/\n#guard_msgs in\n'
     'theorem planted_pin : (0 : Nat) = 1 := by fail "boom"'),
    ("#guard_msgs", '/--error: boom\n⊢ 0 = 1-/#guard_msgs in theorem planted_pin_closed : '
     '(0 : Nat) = 1 := by fail "boom"'),
    ("#guard_msgs", "/-- error: boom\n⊢ 0 = 1 -/\n-- a remark between\n#guard_msgs (error) in\n"
     'theorem planted_pin_comment : (0 : Nat) = 1 := by fail "boom"'),
    ("#guard_msgs", "/-- error: boom ⊢ 0 = 1 -/ /- a remark -/ #guard_msgs (whitespace := lax) "
     'in theorem planted_pin_lax : (0 : Nat) = 1 := by fail "boom"'),
    ("#guard_msgs", "/--\n@ +1:42...53\nerror: boom\n⊢ 0 = 1\n-/\n"
     "#guard_msgs (positions := true) in\n"
     'theorem planted_pin_positions : (0 : Nat) = 1 := by fail "boom"'),
    ("#guard_msgs", "/--\nerror: one\n⊢ 0 = 1\n---\nerror: two\n⊢ 1 = 2\n-/\n"
     "#guard_msgs (ordering := sorted) in\ntheorem planted_pin_two : "
     '(0 : Nat) = 1 ∧ (1 : Nat) = 2 := ⟨by fail "one", by fail "two"⟩'),
    ("#guard_msgs", "/-- error: boom\n⊢ 0 = 1 -/\n#guard_msgsin\n"
     'theorem planted_pin_keyword : (0 : Nat) = 1 := by fail "boom"'),
    ("#guard_msgs", "/--\nerror:\nboom\n⊢ 0 = 1\n-/\n#guard_msgs in\n"
     'theorem planted_pin_break : (0 : Nat) = 1 := by fail "boom"'),
)

GUARD_PIN_KEPT = (
    "/-- info: planted_pin : 0 = 1 -/\n#guard_msgs in #check planted_pin",
    "/-- error: a theorem's own docstring -/\ntheorem planted_pin_doc : True := trivial\n"
    "#guard_msgs in theorem planted_pin_after : True := trivial",
    "-- error: a remark before the command\n"
    "#guard_msgs in theorem planted_pin_remark : True := trivial",
    "/-! error: a module docstring -/\n"
    "#guard_msgs in theorem planted_pin_module : True := trivial",
    "/- /-- error: boom -/ #guard_msgs in -/ theorem planted_pin_words : True := trivial",
    'def plantedKeptPin := "/-- error: boom -/ #guard_msgs in"',
)

# The allow-list of check_fidelity.py's GUARD_ERROR_PINS, written out here so that a change
# to it fails this test; a new file beside each of its files, each of its file names in the
# other's folder, and a new file in Audit/ and in Staging/.
GUARD_PIN_ALLOWED = ("model/Check/RoundTrip.lean", "model/Model/Audit.lean")

GUARD_PIN_REFUSED = ("model/Check/Planted.lean", "model/Model/Planted.lean",
                     "model/Check/Audit.lean", "model/Model/RoundTrip.lean",
                     "Audit/Planted.lean", "Staging/Planted.lean")


def plant() -> None:
    """`#guard_msgs` under a docstring that pins an error, GUARD_PINS, in a scratch copy of
    I.1's file: each refused by its file and line; nothing of GUARD_PIN_KEPT is. Then the
    first pin alone, in a small tree of its own: not refused at each path of
    GUARD_PIN_ALLOWED, refused at each of GUARD_PIN_REFUSED."""
    if nt.check_fidelity.GUARD_ERROR_PINS != set(GUARD_PIN_ALLOWED):
        nt.failures.append("GUARD_ERROR_PINS differs from GUARD_PIN_ALLOWED: a change to the "
                           "allow-list is made in both, with its decision")
    nt.scratch_plants("#guard_msgs under a docstring that pins an error, in each of its forms",
                      GUARD_PINS, GUARD_PIN_KEPT)
    pin = GUARD_PINS[0][1] + "\n"
    line = pin[:pin.index("#guard_msgs")].count("\n") + 1
    for rel in GUARD_PIN_ALLOWED + GUARD_PIN_REFUSED:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            path = root / rel
            path.parent.mkdir(parents=True)
            path.write_text(pin)
            name = f"an error pinned by #guard_msgs's docstring in {rel}"
            if rel in GUARD_PIN_ALLOWED:
                if nt.expect_success(f"{name}, on the allow-list", nt.rules_in(root)):
                    print(f"✓ {name}, on the allow-list: not refused")
            else:
                nt.expect_failure(f"{name}, off the allow-list", nt.rules_in(root),
                                  f"{rel}:{line}: uses `#guard_msgs` under a docstring")
