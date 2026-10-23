- **The source scan ends a name as Lean 4.35 does, refuses a literal closed up to a name
  it may misread, and refuses `#time`, `#with_exporting`, `#guard` and a declared token
  ending in a name's character (#234).** `check_rules` in
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py) finds each forbidden
  command, and `axiom`, as a whole word, by Python's `\b`, in the Lean as `read_lean`
  gives it. Its reader took any character that Python's `\w` takes for part of a name, and
  read `#` as a token of its own, as it still does, so closed-up text hid from it a word
  that Lean reads as a command, in three ways. The first is a character that Python
  counts a letter or a digit but that no Lean name holds, as the `¹` of the postfix `⁻¹`
  (`Init/Notation.lean`): Lean reads `1⁻¹set_option` as `1`, `⁻¹` and `set_option`, so
  `1⁻¹set_option«debug».byAsSorry true in theorem …` built on `sorryAx`, and
  `1⁻¹axiom planted : False` declared an axiom, while the scan saw neither. The second is
  a token of Lean's own that begins with `#`: Lean reads the longest token it knows, so
  `#check1set_option«debug».byAsSorry true in theorem …` is `#check`, `1` and
  `set_option` and builds on `sorryAx`, `#whereaxiom planted : False` declares an axiom,
  and `#time` (`Init/Notation.lean`) and `#with_exporting` (`Lean/Parser/Command.lean`),
  each of which wraps the command after it, let `#timeaxiom planted : False`,
  `#timeset_option«debug».byAsSorry …` and `#with_exportingaxiom planted : False` build
  too, where the scan read `#` and one name. The third is a token the file declares that
  ends in a character a name can hold: after `infixl:65 " +x " => Nat.add`, Lean reads
  `2 +x1set_option` as `2`, `+x`, `1` and `set_option`, so
  `def k : Nat := 2 +x1set_option«debug».byAsSorry true in theorem T : (0 : Nat) = 1 := by decide`
  builds on `sorryAx`, and so do `2 +_0set_option…` after `" +_ "` and `2 +x'1set_option…`
  after `" +x' "`, with `+x!` and `+x?` alike, while the scan reads `x1set_option` as one
  name. Each was built in Lean 4.35 as written, in a scratch file outside the tree, and
  each rests on `sorryAx` or declares its axiom.

  The reader now ends a name where Lean does. A name begins with a character of Lean's
  `isIdFirst` and goes on with characters of its `isIdRest` (`Init/Meta/Defs.lean`),
  written out range by range in the script and compared with Lean 4.35 itself over every
  code point, with no difference; any other character that `\w` takes, outside a name, is
  blanked, as a number closed up to a word already is (#197). The scan's name stops
  sooner, though, before any of the 96 characters of those ranges that `\w` does not take,
  as `℃`: after a token ending in one, as `+℃` after `infixl:65 " +℃ " => Nat.add`, Lean
  reads `2 +℃1set_option` as `+℃`, `1` and `set_option`, which builds on `sorryAx`, and the
  scan before this change, which never took `℃` into a name, refused the `set_option`. No
  file uses any of the 96.

  Ending a name early, or blanking a character, shows the scan more words, and changes
  nothing else, but where a character literal, a raw string, or an `s!`, `m!`, `f!` or
  `throwError` follows closed up. There Lean may read on through the `'`, the `r` or the
  word as part of the name or of a token, while the scan begins something new, and may
  take a `"` or a `}` for a literal's text, or read a plain string with holes. The review
  of this change found the first: after `postfix:max "¹'" => g`,
  `def k : String := s!"{1¹'}'"`, with `set_option«debug».byAsSorry true in theorem …` on
  the next line, builds on `sorryAx`, and the reader, blanking the `¹`, read `'}'` as a
  literal and the `set_option` as a string's text, where the scan before this change,
  which read `¹'` as part of a name, refused it; Mathlib's `⁻¹'` has the same shape. The
  review found an older way of the kind too, which the scan before this change missed as
  well: `def a℃' : Nat := 0`, then `s!"{a℃'}'"`. Two more, found while fixing them and
  missed before this change as well, build on `sorryAx`: a raw string, `def a℃r : Nat := 1` and
  `@[deprecated a℃r"\" x " (since := "2026-10-22")] def old : Nat := 1`, and an `s!`,
  `def a℃s! : Nat := 1` and `@[deprecated a℃s!"{" (since := "2026-10-22")] def old : Nat := 1`,
  each before the `set_option` line. Such a place is known by the run of name characters
  just before it, which holds a character outside ASCII (`closed_up`, one pass over the
  file). There the scan now refuses a character literal or a raw string, by its line,
  and takes no `s!` or its kin to begin an interpolated string, so the string after it is
  refused, as any string is, if Lean could read its braces as holes. The literal's
  refusal is the review's fix; the raw string's and the `s!`'s carry it to the other two.
  No tracked file has such a place.

  The coordinator ruled on the rest on 22 October 2026, in two messages to ship TT;
  #234 is the card. The first decided the refusals of `#time`, `#with_exporting` and a
  declared token ending in a word character; the second widened that token's refusal to
  every character a name may hold, decided the refusal of `#guard`, and decided a reading
  of Lean's own tokens that begin with `#`, to be taken out, and the other two kept, if
  the review of that round found it wider than it looked. Each is a tightening of the
  scan, which is the coordinator's to decide. This entry claims no approval of the owner.

  The reading was taken out after review, as the ruling provided: the review found it
  wider than it looked. It read the 30 such tokens of Lean 4.35's table, with Lean
  imported, in every file, so that `#check1set_option…` and `#whereaxiom…` would be
  refused by their lines.
  But which `#` tokens Lean has depends on what a file imports. In a file that imports no
  more of Lean's library than `Init`, as every file under `Elements/`, `Staging/` and
  `Audit/` does, `#widget` is none: after `def widget' : Nat := 4`, Lean reads
  `def k : String := s!"{5#widget'}'"` with `5#widget'` as a bit-vector literal and the
  `}` closing the hole, where the reading took `#widget` and the literal `'}'`, so that
  `set_option«debug».byAsSorry true in theorem …` on the next line was a string's text to
  it. That builds on `sorryAx`, and an `axiom` there is declared. A token the file
  declares that extends one, as `#check'}`, hid a later command the same way. The scan
  before this change refused both. So the scan reads `#` and the name after it, as it did
  before this change, and `#check1set_option…` stays open, below.

  `#time`, `#with_exporting` and `#guard` join the commands that FORBIDDEN refuses,
  matched, as `#eval` is, with no word boundary after them, so that each is refused
  wherever it stands: closed up to a command, before one, or alone on its line. `#guard`
  runs compiled code while the file is built, as `#eval` does. Lean 4.35's tokens that
  begin `#guard` are `#guard`, `#guard_expr`, `#guard_msgs` and `#guard_panic`: the rule
  refuses `#guard` before anything but `_expr` or `_msgs`, so `#guard_x`, which Lean reads
  as `#guard _x`, is refused, while `#guard_msgs` and `#guard_expr`, which run nothing, are
  not, and `#guard_panic` was refused already. No tracked `.lean` file uses `#time`,
  `#with_exporting` or `#guard` itself: `git grep -l -e '#time' -e '#with_exporting'
  6d06c47b -- '*.lean'` and `git grep -nP '#guard(?!_expr|_msgs|_panic)' 6d06c47b --
  '*.lean'` name no file, at origin/main `6d06c47b`, nor at this change. The only `#guard`
  spelling the tracked files hold is `#guard_msgs`, 239 times, in `Audit/` around
  `#print axioms` and in `model/`.

  A token the file declares whose text, trimmed as Lean trims it, ends in a character a
  name may hold or `\w` takes, a letter, a digit, `_`, `'`, `!`, `?` or `℃` among them, is
  refused by the line of its literal, in every file the scan reads, with no exception.
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
  command begins with a word of a library, as Mathlib's `lemma`. It now takes time that
  grows with the file's length, not with the square of the commands: it finds where each
  command ends from the heights of the brackets, read once. It gave the same literals as
  before over 20,000 random sources and every tracked file, and 4,000 repeats of
  `notation3 "a" `, which took about 21 seconds, take about a hundredth of one.

  No tracked file declares a token that ends in such a character: of the 255 files the
  scan reads, under `Elements/`, `Staging/`, `Audit/` and `model/`, 0 declare one, and the
  same holds of origin/main's tracked files at `6d06c47b`, read by `git show`. The tokens
  they declare are `‖`, `∠`, `△` and `∟`, by four `notation` commands of
  `Elements/Foundations/Magnitudes.lean`. The command run, from the repository's root,
  prints each declared token and whether it ends in such a character:

  ```sh
  python3 -c 'import sys; sys.path.insert(0, "scripts"); import check_fidelity as cf
  for p in cf.lean_sources():
      s = []; code = cf.read_lean(cf.lean_text(p), s)[0]
      for o, w, t in cf.declared_tokens(code, s):
          t = t.strip(" \t\r\n"); print(p.relative_to(cf.ROOT), w, t, bool(cf.NAME_CHAR.match(t[-1:])))'
  ```

  It printed five lines, each `Elements/Foundations/Magnitudes.lean notation` with `‖`,
  `‖`, `∠`, `△` or `∟`, and each `False`.

  Over the tree, the findings are unchanged: none before and none after, over all 255
  files. Each file reads as it did with this change's scan before its fix rounds
  (`b28449b3`, which merged origin/main at `84c71dff`), byte for byte, so the refusals of
  a closed-up literal change no tracked file's reading. Against origin/main at
  `6d06c47b`, `Elements/`, `Staging/` and `Audit/` read as they did, so what `render.py`,
  `check_acceptance.py` and the inline counts read from the scan is unchanged, and
  thirteen files of `model/` read
  differently, where Mathlib's `-ᵥ`, `≃ᵃⁱ[`, `!₂[` and `ᗮ` now end where Lean ends them.
  Of the review's 939,600 spellings, each forbidden command and `axiom` after each kind of
  character the reader blanks or ends a name before, none that the scan before this
  change refuses passes this one; nor does any of a wider set of 397,880, with Lean's `#`
  tokens among those characters, nor of the 540,000 of the review of the first fix round,
  after `#` tokens, after tokens a file declares that begin with one, and after `5#`.
  [FORMALIZATION](../FORMALIZATION.md), section 7, says what the scan now reads and
  refuses, and what it still does not.

  The scan's negative tests gain plants for each way. `set_option«debug».byAsSorry` and
  `axiom` closed up to `1⁻¹`, and `set_option«debug».byAsSorry` closed up to a declared
  `+℃`, stand beside the other spellings of `set_option`, caught by the reading. `#time`
  and `#with_exporting` closed up to `set_option«debug».byAsSorry` and to `axiom`, before
  a `def`, and `#time` alone on its line before a theorem, and `#guard` closed up to
  `true` and to `_plantedTrue`, stand
  beside the other closed-up commands, and all three join the commands planted in each
  folder the scan reads, caught by FORBIDDEN, while `#guard_msgs` and `#guard_expr` are
  not refused. The declared tokens `+x`, `+_`, `+x'`, `+x!` and `+x?`, and `+z` on a
  notation's second line, each with `set_option«debug».byAsSorry` closed up to it, are
  caught by the token's refusal, by the line of the literal; a token ending in a symbol, a
  string after a notation's `=>`, and a declaration in a comment or a string, are not
  refused; and reader cases pin which literals are read, from which commands, a `syntax`
  ended by `@[` or a `#` command and a dotted name's word among them. The four literals
  above, each before the `set_option` line, each alone in a scratch copy, are caught by
  the line of the literal or the string, and reader cases pin which places are marked.
  Each new plant was built in Lean 4.35 as written. Each is missed by origin/main's scan
  at `6d06c47b` but two, which it catches by the `set_option` line: the `+℃` plant, which
  guards this change's reading of a name, and the literal after `¹'`, which this change's
  reading let through until its fix round. With any one rule taken out in a scratch copy,
  `#guard`, the wider token refusal, or the mark on a literal, a raw string or an `s!`,
  the plants and cases that it alone catches fail. No check, test, expected value, lock
  or schema is weakened.

  These stay open, each built in Lean 4.35 as written. Lean's own tokens that begin with
  `#`, but those FORBIDDEN refuses: `#check1set_option«debug».byAsSorry true in theorem …`
  is `#check`, `1` and `set_option`, and builds on `sorryAx`, as `#versionset_option…`
  does, and `#whereaxiom planted : False` declares an axiom, while the scan reads `#` and
  one name; this one is open, and
  [#320](https://github.com/jackChallis/stoicheia/issues/320) holds it. Three older
  routes, which [#317](https://github.com/jackChallis/stoicheia/issues/317) holds: Lean's own `⊕'`,
  `×'` and `]'`, whose `'` the scan takes for a character literal's opening:
  `def T : Type := Nat ⊕'"' "`, with a coercion from `String` to `Type`, and the
  `set_option` line after it build on `sorryAx`, as `×'` does. Lean's own `<-`, `//` and `\/` before a `-`, where the scan
  reads a comment and Lean none: `def S : Type := {x : Int //-1 < x}` and the
  `set_option` line build on `sorryAx`. A token the file declares that ends in a symbol
  but holds a comment's opening or a quote: after `infixl:65 " ⊕-- " => Nat.add`,
  `def k : Nat := 1 ⊕--2set_option«debug».byAsSorry true in theorem …` builds on
  `sorryAx`, and so does a `" ⊕\" "` alike. The scan before this change missed each of
  these too. And tokens of a library a file imports, as Mathlib's, are not read.

  This entry approves the change to [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py),
  whose reader ends a name where Lean 4.35 does, and sooner before a character `\w` does
  not take, and refuses a character literal or a raw string closed up to a name or token
  it may misread, and which refuses `#time`, `#with_exporting`, `#guard` and a declared
  token ending in a character a name may hold.

  This entry approves the change to [`scripts/negative_tests.py`](../../scripts/negative_tests.py),
  which gains the plants of #234 and the reader cases that pin the new reading.
