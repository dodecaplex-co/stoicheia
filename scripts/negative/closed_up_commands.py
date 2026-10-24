"""Without a build, in a scratch copy of I.1's file in a temporary tree, read by the source
scan alone, as in set_option_spellings: `#eval`, `#exit` and `#guard_panic` closed up to the
word after them, which Lean reads as the command and that word (`#evalIO.println`,
`#guard_panicin`), and `#guard_panic` after a remark or a line break: each refused by its
file, line and command, while the words in a comment or a string are not (#197).
`#guard_panic` spaced is among forbidden_commands' commands. With them, `#time` and
`#with_exporting`, which wrap the command after them: closed up to `set_option«debug».…` or
to `axiom` (`#timeaxiom`, `#with_exportingaxiom`), before a `def`, and alone on their line
before a theorem, each refused by its line and command (#234); both spaced are among
forbidden_commands' commands. `#guard`, which runs compiled code, closed up to the word
after it (`#guardtrue`, and `#guard_plantedTrue`, which Lean reads as
`#guard _plantedTrue`): each refused by its line, while `#guard_msgs` and `#guard_expr` are
not; spaced, it is among forbidden_commands' commands. And a token the file declares that
ends in a character a name may hold, after which `set_option«debug».…` closed up to it
builds on `sorryAx` in Lean 4.35 (`infixl:65 " +x " => Nat.add` and `2 +x1set_option…`,
`" +_ "` and `2 +_0set_option…`, `" +z "` on a notation's second line, and `" +x' "`,
`" +x! "` and `" +x? "`): each refused by the line of its literal, while a token ending in a
symbol, a literal after a notation's `=>`, and the words in a comment or a string, are not;
reader cases pin which literals are read, from which commands. And, each alone in its
scratch copy, a character literal, a raw string and an `s!`'s string closed up to a name or
token that holds a character outside ASCII, through which Lean reads on (`{1¹'}'` after a
declared `¹'`, `{plantedC℃'}'`, and `plantedA℃r"\\" x "` and `plantedS℃s!"{"` in a
`deprecated` attribute), each before `set_option«debug».…`, which builds on `sorryAx` in
Lean 4.35: each refused by the line of the literal or the string (#234).
"""

import negative_tests as nt

BUILDS = False

# `#eval`, `#exit` and `#guard_panic` closed up to the word after them, which Lean 4.35
# reads as the command and that word, and `#guard_panic` after a remark or a line break
# (#197); each is (the command check_fidelity.py names, a line of Lean). With them,
# `#time` and `#with_exporting`, which wrap the command after them, closed up to
# `set_option` and to `axiom` (Lean reads the longest token it knows, so `#timeaxiom` is
# `#time` and `axiom`), before a `def`, and alone on their line: each refused as itself,
# wherever it stands (#234). And `#guard`, which runs compiled code, closed up to a word,
# as Lean reads `#guardtrue`, and `#guard_plantedTrue` as `#guard _plantedTrue`, since
# Lean has no token `#guard_plantedTrue` (#234). `#exit` comes last, as it would in a
# file. CLOSED_UP_KEPT holds the same words in a comment and a string, which are not
# refused, and `#guard_msgs` and `#guard_expr`, Lean's other `#guard` tokens.
CLOSED_UP_COMMANDS = (
    ("#eval", '#evalIO.println "planted"'),
    ("#guard_panic",
     '#guard_panicin theorem planted_panic_closed : (0 : Nat) = 1 := by fail "PANIC"'),
    ("#guard_panic", "#guard_panic /- a remark -/ in theorem planted_panic_remark : "
     '(0 : Nat) = 1 := by fail "PANIC"'),
    ("#guard_panic", "#guard_panic\n  in theorem planted_panic_break : (0 : Nat) = 1 := by\n"
     '  trace "PANIC"\n  exact rfl'),
    ("#time", "#timeset_option«debug».byAsSorry true in "
     "theorem planted_time_closed : (0 : Nat) = 1 := by decide"),
    ("#time", "#timeaxiom planted_time_axiom : False"),
    ("#with_exporting", "#with_exportingaxiom planted_exporting_axiom : False"),
    ("#time", "#time def planted_time_def : Nat := 1"),
    ("#with_exporting", "#with_exporting def planted_exporting_def : Nat := 1"),
    ("#time", "#time\ntheorem planted_time_break : True := trivial"),
    ("#guard", "#guardtrue"),
    ("#guard", "def _plantedTrue : Bool := true\n#guard_plantedTrue"),
    ("#exit", "#exitplanted"),
)

CLOSED_UP_KEPT = (
    "-- #guard_panicin, #evalx and #exitx, in a comment",
    'def plantedKeptClosedUp := "#guard_panicin #evalx #exitx"',
    "-- #timeaxiom, #time def and #with_exportingaxiom, in a comment",
    'def plantedKeptTokens := "#timeaxiom #time def #with_exportingaxiom"',
    "#guard_msgs in #check (1 : Nat)",
    "#guard_expr (1 : Nat) = 1",
    "-- #guardfalse, in a comment",
    'def plantedKeptGuard := "#guardfalse"',
)

# A token the file declares that ends in a character a name may hold (#234), each with
# `set_option«debug».byAsSorry` closed up to it, as each builds on `sorryAx` in Lean 4.35:
# `+x` and `+_`, `+z`, the second token of a notation written over two lines, and `+x'`,
# `+x!` and `+x?`, whose last characters a name may hold though `\w` does not take them.
# Each is
# ("literal " and the token's text, the Lean), refused on the line of the token's literal.
# DECLARED_TOKENS_KEPT holds what the rule does not refuse: a token ending
# in a symbol, a string after a notation's `=>`, and a declaration in a comment and in a
# string. DECLARED_TOKEN_READINGS pins which literals `declared_tokens` reads: each is (the
# Lean, the (line, command, text) of each literal). Its token declarations, but Mathlib's
# `notation3`, are as Lean 4.35 accepts them.
DECLARED_TOKEN_READINGS = (
    # Over two lines, the second beginning with the literal; and after a spaced
    # precedence, which Lean takes for `term`'s, so a `syntax` is read to the next command,
    # here a `def` whose string is not read.
    ('syntax "cc"\n" +s " : term\ndef d := "abc"',
     [(1, "syntax", "cc"), (2, "syntax", " +s ")]),
    ('syntax "aa" term :max " +q " : term', [(1, "syntax", "aa"), (1, "syntax", " +q ")]),
    ('syntax plantedAbbrev := " +t " term', [(1, "syntax", " +t ")]),
    # Every literal of a `syntax`, a `&"…"` that declares no token among them.
    ('syntax "dd" &"only" (" +e ")? sepBy(term, " +f ") unicode(" ≤g ", " <=h ") : term',
     [(1, "syntax", w) for w in ("dd", "only", " +e ", " +f ", " ≤g ", " <=h ")]),
    # A raw string, an escape and a gap, read as Lean reads them.
    ('infixl:65 r" +w " => Nat.add', [(1, "infixl", " +w ")]),
    ('infixl:65 " +\\x76 " => Nat.add', [(1, "infixl", " +v ")]),
    ('infixl:65 " +u\\\n   " => Nat.add', [(1, "infixl", " +u")]),
    # To the first `=>` outside brackets, not one in a name; a modifier before the word.
    ('notation3 "∑ "(...)", "r:67:(scoped f => F f) " +n " => r',
     [(1, "notation3", "∑ "), (1, "notation3", ", "), (1, "notation3", " +n ")]),
    ('notation «=>» " +y " b => b', [(1, "notation", " +y ")]),
    ('local notation:50 a " ≺x " b => a < b', [(1, "notation", " ≺x ")]),
    ('binder_predicate x " >> " y:term => `($x > $y)', [(1, "binder_predicate", " >> ")]),
    ('declare_simp_like_tactic plantedSimp "simp+x " (autoUnfold := true)',
     [(1, "declare_simp_like_tactic", "simp+x ")]),
    # A `syntax` read to the next command, begun by `@[` or by a `#` command.
    ('syntax "gg" : term\n@[deprecated "abc" (since := "2026-10-22")] def plantedR := 1',
     [(1, "syntax", "gg")]),
    ('syntax "hh" : term\n#check "abc"', [(1, "syntax", "hh")]),
    # Not the word in a name, a comment or a string.
    ('def a := Lean.Parser.Command.notation "abc"\ndef «syntax» := "abc"', []),
    ('def notation.plantedN := "abc"', []),
    ('-- notation " +c "\ndef d := "notation \\" +c \\" => d"', []),
)

DECLARED_TOKENS = (
    ("literal +x", 'infixl:65 " +x " => Nat.add\ndef k : Nat := 2 +x1set_option«debug».byAsSorry '
     "true in theorem T : (0 : Nat) = 1 := by decide"),
    ("literal +℃", 'infixl:65 " +℃ " => Nat.add\ndef k : Nat := 2 +℃1set_option«debug».byAsSorry '
     "true in theorem T : (0 : Nat) = 1 := by decide"),
    ("literal +_", 'infixl:65 " +_ " => Nat.add\ndef k : Nat := 2 +_0set_option«debug».byAsSorry '
     "true in theorem T : (0 : Nat) = 1 := by decide"),
    ("literal +z", 'notation:65 a:65 " ⊕⊕ " b:66\n  " +z " c:66 => Nat.add a (Nat.add b c)\n'
     "def k : Nat := 1 ⊕⊕ 2 +z3set_option«debug».byAsSorry true in "
     "theorem T : (0 : Nat) = 1 := by decide"),
    ("literal +x'", 'infixl:65 " +x\' " => Nat.add\ndef k : Nat := 2 +x\'1set_option«debug».'
     "byAsSorry true in theorem T : (0 : Nat) = 1 := by decide"),
    ("literal +x!", 'infixl:65 " +x! " => Nat.add\ndef k : Nat := 2 +x!1set_option«debug».'
     "byAsSorry true in theorem T : (0 : Nat) = 1 := by decide"),
    ("literal +x?", 'infixl:65 " +x? " => Nat.add\ndef k : Nat := 2 +x?1set_option«debug».'
     "byAsSorry true in theorem T : (0 : Nat) = 1 := by decide"),
)

APPROXIMATE_DECLARATION_LITERALS = (
    ("literal only", 'syntax &"only" : term'),
    ("literal following", 'syntax "§" : term\n'
     'lemma plantedLibrary : String := "following"\ndef plantedStop : Nat := 0'),
)

DECLARED_TOKENS_KEPT = (
    'infixl:65 " +* " => Nat.add',
    'notation "‖‖" => "planted"',
    '-- infixl:65 " +y " => Nat.add, in a comment',
    'def plantedKeptNotation := "infixl:65 \\" +y \\" => Nat.add"',
)

# A character literal, a raw string, or an `s!`'s string, closed up to a name or token
# that holds a character outside ASCII, through which Lean reads on (#234): after the token
# `¹'` (Mathlib's `⁻¹'` has the same shape), or in the names `plantedC℃'`, `plantedA℃r`
# and `plantedS℃s!`, a hole's `}'`, the `"\"` of a `deprecated` attribute's text, or its
# `"{"`, is no literal or interpolated string to Lean, and a reader that took it for one
# would read the `set_option` after it as a string's text. Each builds on `sorryAx` in
# Lean 4.35, and each is (the finding, the Lean, the text on the line it names): planted
# alone, since a misread literal reads on into what follows.
LITERALS_CLOSED_UP = (
    ("a character literal closed up to",
     'def plantedG (n : Nat) : Nat := n\npostfix:max "¹\'" => plantedG\n'
     'def plantedK : String := s!"{1¹\'}\'"\n'
     "set_option«debug».byAsSorry true in theorem planted_after_prime : (0 : Nat) = 1 := "
     'by decide\ndef plantedM : String := "}"', "¹'}"),
    ("a character literal closed up to",
     "def plantedC℃' : Nat := 0\n"
     'def plantedK2 : String := s!"{plantedC℃\'}\'"\n'
     "set_option«debug».byAsSorry true in theorem planted_after_celsius_prime : (0 : Nat) = 1 "
     ':= by decide\ndef plantedM2 : String := "}"', "℃'}"),
    ("a raw string closed up to",
     "def plantedA℃r : Nat := 1\n"
     '@[deprecated plantedA℃r"\\" x " (since := "2026-10-22")] def plantedOld : Nat := 1\n'
     "set_option«debug».byAsSorry true in theorem planted_after_raw : (0 : Nat) = 1 := "
     'by decide\ndef plantedM3 : String := "\\""', '℃r"'),
    ("a string the scan cannot read for certain",
     "def plantedS℃s! : Nat := 1\n"
     '@[deprecated plantedS℃s!"{" (since := "2026-10-22")] def plantedOld2 : Nat := 1\n'
     "set_option«debug».byAsSorry true in theorem planted_after_interpolation : (0 : Nat) = 1 "
     ':= by decide\ndef plantedM4 : String := "}"', '℃s!"'),
)


def plant() -> None:
    """`#guard_panicin`, `#evalIO.println`, `#timeaxiom` and the other CLOSED_UP_COMMANDS in
    a scratch copy of I.1's file: each refused by its file, line and command; nothing of
    CLOSED_UP_KEPT is. `read_lean` leaves `#time`, `#with_exporting`, `#guard`, `#eval` and
    its kin whole, closed up or not, for FORBIDDEN to see, and `#guard_msgs` for
    GUARD_MSGS. Then DECLARED_TOKENS in another scratch copy: each refused by the line of
    its token's literal; nothing of DECLARED_TOKENS_KEPT is. The non-token strings in
    APPROXIMATE_DECLARATION_LITERALS are refused by their lines with the approximate-span
    diagnostic; and `declared_tokens` reads the literals of DECLARED_TOKEN_READINGS, and
    no others. Then each of LITERALS_CLOSED_UP alone in a scratch copy, refused by its
    line; and `read_lean` marks a character literal or a raw string where the run of name
    characters before it holds a character outside ASCII, and reads an `s!` there as no
    interpolation, and no other."""
    nt.scratch_plants("#eval, #exit and #guard_panic closed up to the word after them, "
                      "#time and #with_exporting closed up, before a def and alone, and #guard "
                      "closed up", CLOSED_UP_COMMANDS, CLOSED_UP_KEPT)
    for source, expected in (
        ("#timeaxiom", "#timeaxiom"),
        ("#with_exportingaxiom", "#with_exportingaxiom"),
        ("#time axiom", "#time axiom"),
        ("#time\naxiom", "#time\naxiom"),
        ("#evalx #exitx #guard_panicin", "#evalx #exitx #guard_panicin"),
        ("#guardtrue #guard_x #guard_msgsin #eval!x",
         "#guardtrue #guard_x #guard_msgsin #eval!x"),
    ):
        read, unsure = nt.check_fidelity.read_lean(source)
        if read != expected or unsure:
            nt.failures.append(f"read_lean({source!r}) returned {(read, unsure)!r}, not "
                               f"{(expected, [])!r}")
    nt.scratch_plants("a declared token ending in a character a name may hold, with set_option "
                      "closed up to it", DECLARED_TOKENS, DECLARED_TOKENS_KEPT,
                      prohibited=("declares the token",))
    nt.scratch_plants("non-token strings in approximate token-declaration spans",
                      APPROXIMATE_DECLARATION_LITERALS,
                      prohibited=("declares the token", "(`syntax`)"))
    for plant in LITERALS_CLOSED_UP:
        nt.scratch_plants("a literal or a string closed up to a name or token holding a "
                          f"character outside ASCII ({plant[2]}), before set_option", (plant,))
    for source, expected in (
        # Marked: after `¹`, which the reader blanks, after `℃`, before which it ends a
        # name, and after a name it may have ended there.
        ("1¹'}' a℃'\"' αb℃1'a' a℃r\"x\"", [2, 8, 16, 22]),
        # An `s!` there is no interpolation, so a string whose braces Lean could read as
        # holes is refused; one whose readings agree is not.
        ('a℃s!"{" ++ "}" a℃s!"{x}"', [4]),
        # Not marked: after ASCII alone, a number, a space or a symbol, or a name Lean
        # reads whole; nor an `s!` there.
        ("1'a' #check'}' x 'a' (c == 'a') ⊕ 'b' α' r\"x\" 1r\"y\" αβ s!\"{x}\"", []),
    ):
        unsure = nt.check_fidelity.read_lean(source)[1]
        if unsure != expected:
            nt.failures.append(f"read_lean({source!r}) marked {unsure!r}, not {expected!r}")
    for source, expected in DECLARED_TOKEN_READINGS:
        strings: list = []
        code, _ = nt.check_fidelity.read_lean(source, strings)
        read = [(source[:offset].count("\n") + 1, word, text)
                for offset, word, text in nt.check_fidelity.declared_tokens(code, strings)]
        if read != expected:
            nt.failures.append(f"declared_tokens({source!r}) read {read!r}, not {expected!r}")
