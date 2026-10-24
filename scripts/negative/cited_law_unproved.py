"""A new law in `Cited` with no proof: the build of I.8 fails at `Cited.holds_all`, naming
the missing case, and nowhere else. SYNTAX and HOLDS_ALL, the files it plants in and expects
the refusal from, are in scripts/negative_tests.py, where tests/test_negative_tests.py reads
them.
"""

import re

import negative_tests as nt

BUILDS = True


def plant() -> None:
    """A new law in `Cited`, with its statement and no proof: `Cited.holds_all` in I.8's file
    must fail, naming the missing case, and nothing else may. Built to I.8, then restored
    and rebuilt."""
    path = nt.ROOT / nt.SYNTAX
    saved = path.read_bytes()
    text = saved.decode()

    def plant(old: str, new: str) -> None:
        nonlocal text
        assert text.count(old) == 1, f"{nt.SYNTAX}: expected one {old!r}; update this test"
        text = text.replace(old, new)

    plant("  | prop7\n  deriving DecidableEq",
          "  | prop7\n  /-- Planted by scripts/negative_tests.py: a law with no proof. -/\n"
          "  | planted\n  deriving DecidableEq")
    law = "def Cited.law : Cited → Law\n"
    plant(law, law + "  | planted => ⟨[], pos (.eq .A .A)⟩\n")
    outputs = nt.BuildOutputs()
    try:
        path.write_text(text)
        result = nt.run("lake", "build", "Elements.BookI.Prop08")
        name = "a new cited law without a proof"
        nt.expect_failure(name, result, f"error: {nt.HOLDS_ALL}:", "Missing cases",
                          "Cited.planted")
        elsewhere = sorted({f for f in re.findall(r"error: ([^\s:]+\.lean):\d+",
                                                  result.stdout + result.stderr)}
                           - {nt.HOLDS_ALL})
        if elsewhere:
            nt.failures.append(f"{name}: also refused outside {nt.HOLDS_ALL}, in "
                               f"{', '.join(elsewhere)}, so Cited.holds_all is not what "
                               "caught it")
    finally:
        path.write_bytes(saved)
        nt.rebuild_restored("the restored I.8 build", outputs, "Elements.BookI.Prop08")
