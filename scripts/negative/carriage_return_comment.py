"""Without a build, the six probes an independent reviewer planted for #207, each a
forbidden command or an axiom hidden behind a carriage-return comment
(`-- a remark\\r"`), in one scratch copy of I.1's file in a temporary tree, read by the
source scan alone (`rules_in`): Lean ends a `--` comment only at a line feed, so a
scan that read the file with Python's universal newlines would end the comment at the
`\\r` and let a string open behind it that hides the command up to a later `"`. Read as
Lean reads the bytes, the lone `\\r` of each is refused by its file and line, and each
command, no longer hidden, is named too, by the rules of #197 for three of them. The
unplanted copy passes, and so does a copy of it with CRLF line endings, which Lean
allows; the check before #207, reading with universal newlines, missed all six.
"""

import tempfile
from pathlib import Path

import negative_tests as nt

BUILDS = False

# The six probes an independent reviewer planted for #207 (its issue lists them), each a
# forbidden command or an axiom hidden behind a carriage-return comment: Lean ends a `--`
# comment only at a line feed, so `-- a remark\r"` is one comment to Lean, the quote among
# it, while a scan that reads the file with Python's universal newlines sees the comment
# end at the `\r` and a string open on the next line, which swallows the command up to the
# `"` of the closing `-- "`. Each is (a short name, the probe's exact bytes). Read as Lean
# reads the bytes (`check_fidelity.lean_text`), the comment hides nothing: the lone `\r`
# of each is refused, and the scan names the command of each, which the comment no longer
# hides.
CARRIAGE_RETURN_PROBES = (
    ("#guard_msgs (drop all)", '-- a remark\r"\n#guard_msgs (drop all) in\n'
     'theorem bad : (0 : Nat) = 1 := rfl\n-- "\n#print axioms bad\n'),
    ("set_option debug.byAsSorry", '-- a remark\r"\nset_option debug.byAsSorry true in\n'
     'theorem bad : (0 : Nat) = 1 := by decide\n-- "\n#print axioms bad\n'),
    ("a pinned error", '-- a remark\r"\n/-- error: boom\n⊢ 0 = 1 -/\n#guard_msgs in\n'
     'theorem bad : (0 : Nat) = 1 := by fail "boom"\n-- "\n#print axioms bad\n'),
    ("#guard_panic", '-- a remark\r"\n#guard_panic in\n'
     'theorem bad : (0 : Nat) = 1 := by fail "PANIC"\n-- "\n#print axioms bad\n'),
    ("set_option debug.skipKernelTC", '-- a remark\r"\nset_option debug.skipKernelTC true in\n'
     'theorem ok : True := trivial\n-- "\n'),
    ("axiom", '-- a remark\r"\naxiom planted : (0 : Nat) = 1\n-- "\n#print axioms planted\n'),
)

# The command check_fidelity.py names in each probe once the carriage-return comment no
# longer hides it: {probe index: (the words it names, the token that begins them in the
# probe)}. The FORBIDDEN regex matches `set_option debug.` up to its dot; the axiom has its
# own message; #197's rules name the `drop`, the pinned error and `#guard_panic`.
CR_COMMANDS = {
    0: ("uses `#guard_msgs (drop all)`", "#guard_msgs"),
    1: ("uses `set_option debug.`", "set_option"),
    2: ("uses `#guard_msgs` under a docstring holding `error:`", "#guard_msgs"),
    3: ("uses `#guard_panic`", "#guard_panic"),
    4: ("uses `set_option debug.`", "set_option"),
    5: ("declares an axiom outside Elements/Foundations/", "axiom"),
}


def plant() -> None:
    """The six CARRIAGE_RETURN_PROBES of #207, in one scratch copy of I.1's file in a
    temporary tree, run through the source scan (`rules_in`): read as Lean reads the bytes,
    the lone `\\r` of each is refused by its file and line, and its command, no longer
    hidden, is named too. The unplanted copy passes, and so does a copy of it with CRLF
    line endings, which Lean allows."""
    rel = "Elements/BookI/Prop01.lean"
    marker = "\nend Elements.BookI\n"
    source = (nt.ROOT / rel).read_text()
    assert source.count(marker) == 1, f"{rel}: expected one {marker!r}; update this test"
    header = "\n/-! Planted by scripts/negative_tests.py (#207). -/\n"
    block = header + "".join(body for _, body in CARRIAGE_RETURN_PROBES)
    planted = source.replace(marker, block + marker)
    cr_message = ("an isolated carriage return (a `\\r` not followed by `\\n`), which Lean "
                  "accepts inside a comment or a literal and a `--` comment does not "
                  "end at")

    def line(offset: int) -> int:
        return planted[:offset].count("\n") + 1

    wanted, at = [], planted.index(block) + len(header)
    for i, (_, body) in enumerate(CARRIAGE_RETURN_PROBES):
        wanted.append(f"{rel}:{line(at + body.index(chr(13)))}: {cr_message}")
        if i in CR_COMMANDS:
            msg, token = CR_COMMANDS[i]
            wanted.append(f"{rel}:{line(at + body.index(token))}: {msg}")
        at += len(body)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        path = root / rel
        path.parent.mkdir(parents=True)
        path.write_text(source)
        if not nt.expect_success("the unplanted scratch copy of I.1 for #207's probes",
                                 nt.rules_in(root)):
            return
        path.write_bytes(source.replace("\n", "\r\n").encode("utf-8"))
        nt.expect_success("the unplanted scratch copy of I.1 for #207's probes, with CRLF "
                          "line endings", nt.rules_in(root))
        path.write_bytes(planted.encode("utf-8"))
        nt.expect_failure("the six #207 probes behind a carriage-return comment",
                          nt.rules_in(root), *wanted)
