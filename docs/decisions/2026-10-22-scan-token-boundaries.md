- **The source scan ends a name, and reads `#time` and `#with_exporting`, as Lean 4.35
  does (#234).** `check_rules` in [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py)
  finds each forbidden command, and `axiom`, as a whole word, by Python's `\b`, in the Lean
  as `read_lean` gives it. Its reader took any character that Python's `\w` takes for part
  of a name, and read `#` as a token of its own, so two kinds of closed-up text hid from it
  a word that Lean reads as a command. The first is a character that Python counts a letter
  or a digit but that no Lean name begins with, as the `¹` of the postfix `⁻¹`
  (`Init/Notation.lean`): Lean reads `1⁻¹set_option` as `1`, `⁻¹` and `set_option`, so
  `1⁻¹set_option«debug».byAsSorry true in theorem …` built on `sorryAx`, and
  `1⁻¹axiom planted : False` declared an axiom, while the scan saw neither. The second is
  `#time` (`Init/Notation.lean`) or `#with_exporting` (`Lean/Parser/Command.lean`), each of
  which wraps the command after it: Lean reads the longest token it knows, so
  `#timeaxiom planted : False` is `#time` and an axiom, and
  `#timeset_option«debug».byAsSorry …` and `#with_exportingaxiom planted : False` build
  too, where the scan read `#` and one name.

  The reader now ends a name where Lean does. A name begins with a character of Lean's
  `isIdFirst` and goes on with characters of its `isIdRest` (`Init/Meta/Defs.lean`),
  written out range by range in the script and compared with Lean 4.35 itself over every
  code point, with no difference. Any other character that `\w` takes, outside a name, is
  blanked, as a number closed up to a word already is (#197). And `#time` and
  `#with_exporting` are read as Lean's tokens, blanked when a letter, a digit or `_` follows
  them: asked in Lean 4.35, the token table holds no longer token that begins with either,
  and it parses `#timeaxiom planted : False` as it parses `#time axiom planted : False`.
  The commands the scan forbids, `#eval` and its kin, are never blanked. Neither token is
  refused: read as Lean reads it, the command after it is in plain view of the rules
  already there.

  Over the tree, the findings are unchanged: none before and none after, over all 255
  files the scan reads under `Elements/`, `Staging/`, `Audit/` and `model/`. Thirteen files
  of `model/` read differently, where Mathlib's `-ᵥ`, `≃ᵃⁱ[`, `!₂[` and `ᗮ` now end where
  Lean ends them. `Elements/`, `Staging/` and `Audit/` read the same, byte for byte, so
  what `render.py`, `check_acceptance.py` and the inline counts read from the scan is
  unchanged. [FORMALIZATION](../FORMALIZATION.md), section 7, says what the scan now reads,
  and what it still does not.

  The scan's negative tests gain five plants, each built in Lean 4.35 as written, in a
  scratch file outside the tree, and each missed by the scan before this change:
  `set_option«debug».byAsSorry` and `axiom` closed up to `1⁻¹`, beside the other spellings
  of `set_option`; and `set_option«debug».byAsSorry` closed up to `#time`, and `axiom`
  closed up to `#time` and to `#with_exporting`, beside the other closed-up commands. Reader
  cases pin the new reading: `⁻¹`, `-ᵥ` and `ᗮ` end where Lean ends them, a name keeps its
  subscripts, and `#eval`, `#exit` and `#guard_panic` stay whole. No check, test, expected
  value, lock or schema is weakened, and no refusal is added.

  One case stays open. A token whose last characters could be a name, declared by the file
  or by a library it imports, as `+x` from `infixl:65 " +x " => Nat.add`, still hides the
  word closed up to it: `2 +x1set_option«debug».byAsSorry true in theorem …` builds on
  `sorryAx`, and so does `2 +_0set_option…` after `" +_ "`, while the scan reads
  `x1set_option` as one name. The scan cannot know a token a file declares, so reading does
  not close it; refusing a declared token that ends in a word character would, and that is
  a new refusal, for a decision of its own. No tracked file declares such a token today: the
  only tokens declared in the files the scan reads are `‖`, `∠`, `△` and `∟`, in
  `Elements/Foundations/Magnitudes.lean`.

  This entry approves the change to [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py),
  whose reader ends a name where Lean 4.35 does and reads `#time` and `#with_exporting` as
  the tokens Lean takes them for.

  This entry approves the change to [`scripts/negative_tests.py`](../../scripts/negative_tests.py),
  which gains the five plants of #234 and the reader cases that pin the new reading.
