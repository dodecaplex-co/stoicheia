- **Book Zero's imports, and a staged file's, are read as Lean reads them
  ([#200](https://github.com/jackChallis/stoicheia/issues/200)).** The rule that Book Zero
  (`Elements/Figure/`) imports no proposition, rule 3 of the fidelity check, looked for
  `import Elements.Book` at the start of a raw line, with one space between the two words.
  In the review of #197 an independent reviewer planted a Book Zero file with five
  spellings of a proposition's import, each accepted by Lean 4.35 and let through by the
  rule: two spaces between the words, a line break between them, a remark between them,
  `«Elements»`, and `«BookI»`. Trials with Lean 4.35 turned up more: the word run straight
  into a «…» part or into a remark, a `--` comment or a remark nested in another standing
  between `import` and the name, and two imports sharing a line. After `module`, Lean's
  header allows five more forms: `import all`, `meta import all`, `public import`, `meta
  import` and `public meta import`. The toolchain's grammar,
  `Lean/Parser/Module/Syntax.lean`, has seven, but the header refuses `public import all`
  and `public meta import all`. No file of the edition is a module, so Lean refuses those
  five here ("cannot import non-`module` Elements.BookI.Prop01 from `module`", tried
  against the built I.1), and the rule is made ready for them all the same. Lean also
  treats a name as a path, so `«Elements/BookI».Prop01` can load a built proposition; on a
  disk that ignores case, as a Mac's does, a module named in other capitals, or with a
  Kelvin sign for its k or a long s for its s, loads as well. And one of the edition's own
  files may bring a proposition in, as `Elements.Companions` does.

  Rule 3 now finds every `import` in the Lean as rule 4's reader, `read_lean`, gives it,
  so that no comment can hide one, and no string, raw string or name in «…» can stand for
  one; and it takes the module named after the word, past an `all`. The import is refused
  when that module, in NFKC and case-folded, lies under `Elements.Book`; when the scan
  cannot read the name for certain, because a part of it is no plain name once its «…» are
  off or no whitespace follows it; and when the module brings a proposition in through the
  edition's files, which the rule follows breadth first (`brought_in`), naming the file
  that imports it, or reaches a symbolic link on the way, which it names without reading
  the target. Where the reader keeps a string's braces as code, since the string's plain
  reading and its reading with holes end in one place, an `import` inside them is read as
  well, so that case fails closed. The rule still lets two forms by, each of which Lean
  rejects with an error, loading no proposition: `import` followed by two module names
  ("unexpected identifier; expected command", which loads the first alone), and a name
  beginning `_root_.` ("unknown module prefix"). Rule 3 reads through the reader as #197
  and #207 corrected it, both now on main: an import on the line after `/-/- -/`, and one
  after `-- remark`, a lone carriage return and a quote, are each refused, in a Book Zero
  file and in a root module that one imports. Every file the rule follows is read from its
  bytes (`lean_text`), as #207 has the scan read its own files, so that a lone carriage
  return in a root module, which the scan neither reads for rule 4 nor refuses, ends no
  `--` comment there. On the merged tree the rule reads the 47 imports of Book Zero's 18
  files, which are exactly their header lines, and refuses none.

  Acceptance items P10 and E6 had the same raw reading: to tell which proposition a staged
  file's declarations are for, they matched `import Elements.Book<book>.Prop<n>` at the
  start of a line. So a staged file importing a proposition in any of the spellings above
  was tied to none, while one holding those words at a line's start inside a block comment
  or a string was tied to one; a comment on #200 of 22 October found this. They now read a
  staged file's imports through the fidelity check's own functions, `imports`,
  `read_lean`, `lean_text` and `folded`, and keep no copy of them; `folded` is a new name
  for the NFKC case-folding, which `proposition` now calls too. A module beneath a
  proposition's ties the file to that proposition, as before, and an import the scan
  cannot read, in a staged file that declares anything, fails E6, naming the file and
  line, since which propositions the file imports cannot then be told; that fails closed,
  and never lets a file pass, and the E6 row of `docs/ACCEPTANCE.md` now says so. On
  main's Staging, each of the 43 staged files is tied to exactly the propositions it was
  tied to before, and none holds an import the scan cannot read.

  This entry approves the change to
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py), whose rule 3 reads Book
  Zero's imports as described here, and whose new `folded` lends that rule's comparison of
  modules to the acceptance check.

  This entry approves the change to
  [`scripts/check_acceptance.py`](../../scripts/check_acceptance.py), whose new
  `staged_imports` reads a staged file's imports for P10 and E6 through the fidelity
  check's functions, and whose new `check_staging` holds the P10 and E6 loop that
  `check_propositions` ran before, unchanged but for the E6 failure on an import the scan
  cannot read.

  This entry approves the change to
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py), which gains an item that
  needs no build: 19 forms, each planted in a Book Zero file of its own, the reviewer's
  five and fourteen found since, `Elements.Companions` among them, and each to be refused
  on its file and line, beside a file in which the same import stands only inside a
  comment, a remark, a string and a name in «…», with a Book Zero import of its own, and
  which must not be named at all. Main's rule before this change passes all 19 and refuses
  only the plain spelling.

  This entry approves the change to
  [`tests/test_negative_tests.py`](../../tests/test_negative_tests.py), which gains
  `BookZeroImportTests`, eleven tests of rule 3 on a small tree without Lean: each planted
  form; text in which an import appears only as words; comments and strings that conceal
  no import; a header with `module` and `prelude`, and imports of Lean's own modules,
  which pass; unreadable names; a proposition reached by way of two files importing one
  another; a symbolic link met on the way to a module, inside the source trees, at the
  root, or past a file outside them; a lone carriage return in a followed root module, a
  test that fails when `brought_in` reads with Python's universal newlines; and a file
  outside Book Zero, which the rule leaves alone.

  This entry approves the change to
  [`tests/test_check_acceptance.py`](../../tests/test_check_acceptance.py), which gains
  `StagedImports`, three tests of P10 and E6 on a small tree without Lean. They take the
  forms from the Book Zero plants themselves, so a form added there is put to P10 too:
  each ties a staged file to I.1, save the path in «…», which fails E6 on its line, and
  `Elements.Companions`, which names no proposition and ties the file to none. The same
  import in a comment, a remark or a string ties the file to nothing; an import of one
  book's proposition, or of a module beneath it, ties the file, and imports of two books'
  propositions of one number tie it to neither. With the old raw reading put back, 23 of
  their cases fail.

  No statement, definition or lock changes, and no check is loosened.
