<!-- entry: id=documented-declarations-read-by-the-shared-reader cards=349 line="The main theorem of a proposition's file, and the axioms' docstrings that the pages show, are read with the scripts' one reader of Lean, so none is found inside a remark or a string." -->
- **The main theorem and the axioms' docstrings are read as Lean reads them (checks,
  [#349](https://github.com/dodecaplex-co/stoicheia/issues/349)).** The last two of the
  readers #206 left out. The coordinator's ruling of 22 October 23:50 put the scripts' one
  reader of Lean's comments in `scripts/heath.py`, and the landing tool's two readers took
  it up with pull request #432; the coordinator's orders of 29 October 2026, 12:33, assign
  the rest of card #349 to ship TL. This entry claims no decision of the owner's.

  `heath.theorem_span`, which finds a proposition's main theorem for the fidelity check,
  the style check, the pages, the landing tool and the Jev questions, found it with a
  pattern over the raw text: the first `/-- … -/` followed by `theorem PropN`, ending the
  docstring at its first `-/`, and the theorem at the first line beginning `end`,
  `theorem`, `lemma`, `def`, `structure`, `/--`, `/-!` or `@[`. So a documented theorem
  written inside a remark, or inside a string, above the real one was taken for it, and
  the real docstring and `--` lines were then compared with nothing; a remark line
  beginning `theorem`, `def` or `@[` within the proof cut the theorem short; and a block
  nested in a docstring cut its text short. `render.load_axiom_docs`, which reads the
  docstrings of the axioms that the pages show, and `check_style.docstring_span`, which
  finds them again for the style rules, used the same pattern with `axiom`.

  Now `heath.documented` finds each docstring as a comment the shared reader reads
  (`lean_comments`), followed past white space alone, in code as `read_lean` gives it, by
  the declaration; its text runs to the `-/` that closes it. `theorem_span` takes the main
  theorem so and ends it at the first line beginning one of the same words in code, or
  beginning a docstring or a module comment that the reader finds; a line of a remark or
  a string is neither. `render.axiom_docstrings` reads the axioms' docstrings with
  `documented`, and `load_axiom_docs` and `check_style.docstring_span` take them from it,
  so the two cannot read them apart; check_style's copy of the pattern, `AXIOM_DOC`, is
  gone. On the repository nothing changes: the 99 main theorems and the 48 axiom
  docstrings read as before, and `render.py` writes every page as it was.

  `heath.py`'s self-test, the check `python3 scripts/heath.py`, gains five plants: a
  remark holding a fake documented theorem; a remark whose lines begin `theorem`, `def`
  and `@[` within the proof; a string holding a fake documented theorem; a docstring with
  a block nested in it; and a remark holding a fake documented axiom. Main's readers
  misread all five. `tests/test_check_style.py` gains three cases of `docstring_span`: a
  remark holding a fake docstring and axiom on the line asked for, which main's reading
  took, the real docstring below it, and a docstring with a block nested in it, which
  main's reading missed.

  This entry approves the change to `scripts/heath.py`, in `theorem_span`, the new
  `documented` and `Documented`, and its self-test.
  This entry approves the change to `scripts/render.py`, in `load_axiom_docs` and the new
  `axiom_docstrings` and `AXIOM_NAME`.
  This entry approves the change to `scripts/check_style.py`, in `docstring_span`, and the
  removal of `AXIOM_DOC`.
  This entry approves the change to `tests/test_check_style.py`, in its cases of rule S7.
