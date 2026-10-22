- **The source scan ends a name as Lean 4.35 does, and refuses `#time`, `#with_exporting`
  and a declared token ending in a word character (#234).** `check_rules` in
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py) finds each forbidden
  command, and `axiom`, as a whole word, by Python's `\b`, in the Lean as `read_lean`
  gives it. Its reader took any character that Python's `\w` takes for part of a name, and
  read `#` as a token of its own, so closed-up text hid from it a word that Lean reads as
  a command, in three ways. The first is a character that Python counts a letter or a
  digit but that no Lean name holds, as the `¹` of the postfix `⁻¹` (`Init/Notation.lean`):
  Lean reads `1⁻¹set_option` as `1`, `⁻¹` and `set_option`, so
  `1⁻¹set_option«debug».byAsSorry true in theorem …` built on `sorryAx`, and
  `1⁻¹axiom planted : False` declared an axiom, while the scan saw neither. The second is
  `#time` (`Init/Notation.lean`) or `#with_exporting` (`Lean/Parser/Command.lean`), each of
  which wraps the command after it: Lean reads the longest token it knows, so
  `#timeaxiom planted : False` is `#time` and an axiom, and
  `#timeset_option«debug».byAsSorry …` and `#with_exportingaxiom planted : False` build
  too, where the scan read `#` and one name. The third is a token the file declares that
  ends in a character a name can hold: after `infixl:65 " +x " => Nat.add`, Lean reads
  `2 +x1set_option` as `2`, `+x`, `1` and `set_option`, so
  `def k : Nat := 2 +x1set_option«debug».byAsSorry true in theorem T : (0 : Nat) = 1 := by decide`
  builds on `sorryAx`, and so does `2 +_0set_option…` after `" +_ "`, while the scan reads
  `x1set_option` as one name. Each was built in Lean 4.35 as written, in a scratch file
  outside the tree, and each rests on `sorryAx` or declares its axiom.

  The reader now ends a name where Lean does. A name begins with a character of Lean's
  `isIdFirst` and goes on with characters of its `isIdRest` (`Init/Meta/Defs.lean`),
  written out range by range in the script and compared with Lean 4.35 itself over every
  code point, with no difference; any other character that `\w` takes, outside a name, is
  blanked, as a number closed up to a word already is (#197). The scan's name stops
  sooner, though, before any of the 96 symbols of those ranges that `\w` does not take,
  as `℃`: after `infixl:65 " +℃ " => Nat.add`, Lean reads `2 +℃1set_option` as `+℃`, `1`
  and `set_option`, which builds on `sorryAx`, and the scan before this change, which
  never took `℃` into a name, refused the `set_option`. No file uses any of the 96, and
  ending a name early can only show the scan more words.

  The coordinator decided the two refusals that follow on 22 October 2026, as tightenings
  of the scan, which are the coordinator's to decide; #234 holds the coordinator's record
  of them. This entry claims no approval of the owner.

  `#time` and `#with_exporting` join the commands that FORBIDDEN refuses, matched, as
  `#eval` is, with no word boundary after them, so that each is refused wherever it
  stands: closed up to a command, before one, or alone on its line. That closes the
  second way directly; the reader leaves both whole, so that the rule sees them. No
  tracked `.lean` file uses either: `git grep -l -e '#time' -e '#with_exporting'
  origin/main -- '*.lean'` names no file, at origin/main `22cf4f2b`.

  A token the file declares whose text, trimmed as Lean trims it, ends in a letter, a
  digit or `_`, a character `\w` takes, is refused by the line of its literal, in every
  file the scan reads, with no exception. That closes the third way for those tokens.
  `declared_tokens` reads each string literal of `notation`, `infix`, `infixl`, `infixr`,
  `prefix`, `postfix`, `syntax`, `macro`, `elab`, `binder_predicate`,
  `declare_simp_like_tactic` and Mathlib's `notation3`, on any line of the command, as
  Lean reads it, escapes, gaps and raw strings among them: from the command's word to its
  first `=>` outside brackets, or, for `syntax` and `declare_simp_like_tactic`, which have
  none, to the next command, known by a word that Lean's built-in token table holds and
  that begins a command, by `@[` or by a `#` before a letter. A `syntax` may hold a
  literal after a spaced precedence (`syntax "a" term :max " +x " : term`) and on a line
  of its own, as Lean 4.35 accepts, so it is not read only to its first colon. A `&"…"`,
  which declares no token, is read too, and so is a string in the next command when that
  command begins with a word of a library, as Mathlib's `lemma`.

  No tracked file declares a token that ends in a word character: of the 255 files the
  scan reads, under `Elements/`, `Staging/`, `Audit/` and `model/`, 0 declare one, and the
  same holds of origin/main's tracked files at `22cf4f2b`, read by `git show`. The only
  tokens they declare are `‖`, `∠`, `△` and `∟`, by four `notation` commands of
  `Elements/Foundations/Magnitudes.lean`. The command run, from the repository's root,
  prints each declared token and whether it ends in a word character:

  ```sh
  python3 -c 'import sys; sys.path.insert(0, "scripts"); import check_fidelity as cf
  for p in cf.lean_sources():
      s = []; code = cf.read_lean(cf.lean_text(p), s)[0]
      for o, w, t in cf.declared_tokens(code, s):
          t = t.strip(" \t\r\n"); print(p.relative_to(cf.ROOT), w, t, bool(cf.WORD.match(t[-1:])))'
  ```

  It printed five lines, each `Elements/Foundations/Magnitudes.lean notation` with `‖`,
  `‖`, `∠`, `△` or `∟`, and each `False`.

  Over the tree, the findings are unchanged: none before and none after, over all 255
  files, and `Elements/`, `Staging/` and `Audit/` read as they did, byte for byte, so what
  `render.py`, `check_acceptance.py` and the inline counts read from the scan is
  unchanged. Thirteen files of `model/` read differently from origin/main, where Mathlib's
  `-ᵥ`, `≃ᵃⁱ[`, `!₂[` and `ᗮ` now end where Lean ends them.
  [FORMALIZATION](../FORMALIZATION.md), section 7, says what the scan now reads and
  refuses, and what it still does not.

  The scan's negative tests gain plants for each way. `set_option«debug».byAsSorry` and
  `axiom` closed up to `1⁻¹`, and `set_option«debug».byAsSorry` closed up to a declared
  `+℃`, stand beside the other spellings of `set_option`, caught by the reading.
  `#time` and `#with_exporting` closed up to `set_option«debug».byAsSorry` and to
  `axiom`, before a `def`, and `#time` alone on its line before a theorem, stand beside
  the other closed-up commands, and both join the commands planted in each folder the scan
  reads, caught by FORBIDDEN. The declared tokens `+x` and `+_` above, and `+z` on a
  notation's second line, each with `set_option«debug».byAsSorry` closed up to it, are
  caught by the new refusal, by the line of the literal; a token ending in a symbol, a
  string after a notation's `=>`, and a declaration in a comment or a string, are not
  refused; and reader cases pin which literals are read, from which commands. Each new
  plant was built in Lean 4.35 as written. Each is missed by origin/main's scan but the
  `+℃` plant, which origin/main's scan catches and which guards this change's reading of
  a name. With either refusal taken out in a scratch copy, or a name read on through
  `℃`, the plants that it alone catches fail. No check, test, expected value, lock or
  schema is weakened.

  Three cases stay open. Lean's own tokens are not read as Lean reads them:
  `#check1set_option«debug».byAsSorry true in theorem …` builds on `sorryAx`, and the
  scan reads `#` and one name. Tokens that a library a file imports declares, as
  Mathlib's, are not read. And a declared token ending in `'`, `!` or `?`, which a name
  may hold but `\w` does not take, is not refused: after `infixl:65 " +x' " => Nat.add`,
  `2 +x'1set_option«debug».byAsSorry true in theorem …` builds on `sorryAx`, unseen.

  This entry approves the change to [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py),
  whose reader ends a name where Lean 4.35 does, and sooner before a symbol `\w` does not
  take, and which refuses `#time`, `#with_exporting` and a declared token ending in a word
  character.

  This entry approves the change to [`scripts/negative_tests.py`](../../scripts/negative_tests.py),
  which gains the plants of #234 and the reader cases that pin the new reading.
