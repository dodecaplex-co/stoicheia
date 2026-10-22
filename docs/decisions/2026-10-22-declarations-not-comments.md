- **A page lists only what its Lean declares, never a word from a comment
  ([#313](https://github.com/jackChallis/stoicheia/issues/313)).** On train C6c, III.13's
  page said that three lemmas follow the theorem, among them `beside`, but its
  `Elements/BookIII/Prop13.lean` declares two, Prop13.internally and Prop13.externally. A
  reader on the Book III records found it, and we thank them for it. The cause is in
  [`scripts/render.py`](../../scripts/render.py): `lean_parts` looked for a line that
  begins with a declaration's keyword (`theorem`, `lemma`, `def` and the rest) in the raw
  Lean, comments and docstrings included, and a docstring there wrapped so that a line
  began "lemma beside III.13". Train C6c rewraps that docstring; this change removes the
  cause. `lean_parts` now looks only in the Lean's code, the same text with its comments,
  docstrings and string literals blanked by `check_fidelity.without_comments`, which
  `render.py` already uses to find a declaration's uses. The same reading now decides
  whether the text before the main theorem declares anything, and which names a
  proposition's file declares in the table of Lean names. Two files on main have such a
  line, `Elements/BookI/Prop07.lean` and `Elements/Figure/Superposition.lean`, but
  neither reaches a page, so no page changes.

  This entry approves the change to `scripts/render.py`, in `LeanParts`, `lean_parts`
  and the table of Lean names, and nothing else in it.

  This entry approves the change to `tests/test_check_style.py`, which gains the class
  `LeanPartsNames`: two tests, each failing before the change and passing after it, on a
  Lean file whose docstrings and comments have lines that begin with `theorem`, `lemma`
  and `def`.
