"""Without a build, Book Zero's imports (#200): a new file of Book Zero imports a
proposition in each spelling Lean 4.35 accepts that the rule once passed: two
spaces, a line break, a remark, a line comment or a nested remark between the words,
nothing before «…» or a remark, `«Elements»`, `«BookI»` and a second import on one
line. Then the five forms that Lean's header allows after `module`:
`public import`, `meta import`, `public meta import`, `import all` and
`meta import all`. Lean refuses them while the edition's files are not modules, and
these plants keep the rule ready for when they are. Then the name with a part in «…»
that holds a path, in another case and with the Kelvin sign for its k, any of which
Lean may read as the proposition's file; and `Elements.Companions`, which imports
propositions itself. Each is refused by `check_fidelity.py`, naming its file and
line, while a file holding the same import only in a comment, a remark, a string and
a «…» name, beside a Book Zero import of its own, is not named at all. The files are
read, not built, and removed after.
"""

from pathlib import Path

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A new Book Zero file for each of BOOK_ZERO_SPELLINGS, each refused on its file and
    line, and BOOK_ZERO_TEXT's file not named; all removed after."""
    header = "-- Planted by scripts/negative_tests.py: the import below must be caught.\n"
    plants = [(f"Elements/Figure/PlantedImport{n:02}.lean", header + text, what, extra)
              for n, (what, text, *extra) in enumerate(nt.BOOK_ZERO_SPELLINGS, 1)]
    text_rel, text = nt.BOOK_ZERO_TEXT
    planted: list[Path] = []
    try:
        for rel, source in [(text_rel, text)] + [(rel, source) for rel, source, _, _ in plants]:
            path = nt.ROOT / rel
            assert not path.exists() and not path.is_symlink(), f"{rel} exists; update this test"
            path.write_text(source, encoding="utf-8")
            planted.append(path)
        result = nt.fidelity()
        for rel, source, what, extra in plants:
            line = source[:source.rindex("import")].count("\n") + 1
            nt.expect_failure(f"a proposition imported by Book Zero: {what}", result,
                              f"{rel}:{line}: Book Zero must not import a proposition", *extra,
                              unwanted=(f"{text_rel}:",))
    finally:
        for path in planted:
            path.unlink(missing_ok=True)
