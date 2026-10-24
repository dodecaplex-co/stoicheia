"""Without a build, in a scratch copy of I.1's file in a temporary tree, read by the
source scan alone: `set_option«debug».skipKernelTC true in`, which Lean reads with no
space before the guillemet, and the other spellings of `set_option debug.…` and
`doc.…` with none, guillemets around one part or each, in a command and in a tactic
block, and after a space, a tab or a line break: each refused by its file, line and
spelling, and the unplanted copy passes (#197). With them, `set_option«debug».…` and
`axiom` closed up to the postfix `⁻¹`, which Lean reads as `⁻¹` and the word after it
(`1⁻¹set_option`, `1⁻¹axiom`); `set_option«debug».…` closed up to a declared
token ending in `℃`, which Lean lets a name hold and `\\w` does not take
(`2 +℃1set_option`), refused as a declared token too: each refused by its line (#234).
"""

import negative_tests as nt

BUILDS = False

# The spellings of `set_option debug.…` and `doc.…` with no space before the option, which
# Lean 4.35 reads as the option itself (#197): a guillemet closed up to the command, around
# one part or each, in a command and in a tactic block, and after a comment opened
# `/-/-` or `/--/`; with them, a guillemet after a space, a tab (which Lean refuses on its
# own) and a line break, which the scan caught before; and the command closed up to a
# number or a field before it, decimal, hexadecimal, scientific or with `_`, which Lean ends
# before the command, including numbers after notation ending in `.` and with whitespace or
# a block comment breaking projection adjacency; and the command, and `axiom`, closed up to
# the postfix `⁻¹`, whose `¹` Python's `\w` takes but no Lean name holds, so that Lean reads
# `1⁻¹set_option` as `1`, `⁻¹` and `set_option`; and the command closed up to a token the
# file declares that ends in `℃`, which a Lean name may hold but `\w` does not take, so
# that Lean reads `2 +℃1set_option` as `2`, `+℃`, `1` and `set_option`, which builds on
# `sorryAx`, and which the refusal of such a token catches too (#234). Each
# is planted as (the spelling
# check_fidelity.py names, a line of Lean). SET_OPTION_KEPT holds what the rule does not
# refuse: the command inside a nested comment, `set_optiondebug.skipKernelTC` and
# `set_optiondoc.verso`, with neither a space nor a guillemet, which Lean reads as one name,
# a name with a digit before `set_option`, and fields and numbers in plain use. The explicit
# read_lean cases below preserve ordinary projections after an identifier, `)`, `·`, `⟩`
# and `›`, numbers after a declared notation, and a projection broken by a space or a
# comment, whose digits are then a number; and they blank the `¹` of `⁻¹` and the `ᵥ` and
# `ᗮ` of Mathlib's `-ᵥ` and `ᗮ`, which no name holds, while a name's subscripts stay, end
# a name before `℃`, and keep `ℝ`, `ℕ` and Greek letters in one.
SET_OPTION_SPELLINGS = (
    ("set_option«debug».",
     "set_option«debug».skipKernelTC true in theorem planted_closed : True := trivial"),
    ("set_option«debug».",
     "set_option«debug».«skipKernelTC» true in theorem planted_closed_both : True := trivial"),
    ("set_option«doc».",
     "set_option«doc».verso true in theorem planted_closed_verso : True := trivial"),
    ("set_option«doc».", "set_option«doc».x true in theorem planted_closed_doc : True := trivial"),
    ("set_option«debug».", "theorem planted_closed_tactic : True := by\n"
     "  set_option«debug».byAsSorry true in\n  trivial"),
    ("set_option «debug».",
     "set_option «debug».«skipKernelTC» true in theorem planted_both : True := trivial"),
    ("set_option «debug».",
     "set_option\t«debug».skipKernelTC true in theorem planted_tab : True := trivial"),
    ("set_option «debug».",
     "set_option\n  «debug».skipKernelTC true in theorem planted_break : True := trivial"),
    ("set_option«debug».", "/-/- -/\nset_option«debug».skipKernelTC true in "
     "theorem planted_after_plain_slash : True := trivial"),
    ("set_option«debug».", "/--/ x -/\nset_option«debug».skipKernelTC true in "
     "theorem planted_after_doc_slash : True := trivial"),
    ("set_option«debug».", "def planted_number : Nat := 1set_option«debug».byAsSorry true in "
     "theorem planted_after_number : (0 : Nat) = 1 := by decide"),
    ("set_option«debug».", "def planted_field : Nat := (1, 2).1set_option«debug».byAsSorry "
     "true in theorem planted_after_field : (0 : Nat) = 1 := by decide"),
    ("set_option «debug».", "def planted_hex : Nat := 0xAset_option «debug».skipKernelTC "
     "true in theorem planted_after_hex : True := trivial"),
    ("set_option«debug».", "def planted_scientific : Float := 1.5e5set_option«debug»."
     "byAsSorry true in theorem planted_after_scientific : (0 : Nat) = 1 := by decide"),
    ("set_option«doc».", "def planted_separator : Nat := 1_0set_option«doc».verso true in "
     "theorem planted_after_separator : True := trivial"),
    ("set_option«debug».", 'infixl:65 " +. " => Nat.add\n'
     "def planted_notation_hex : Nat := 2 +.0x1set_option«debug».byAsSorry true in "
     "theorem planted_after_notation_hex : (0 : Nat) = 1 := by decide"),
    ("set_option«debug».", 'infixl:65 " +. " => Nat.add\n'
     "def planted_notation_scientific : Nat := 2 +.1e5set_option«debug».byAsSorry true in "
     "theorem planted_after_notation_scientific : (0 : Nat) = 1 := by decide"),
    ("set_option«debug».", 'infixl:65 " +. " => Nat.add\n'
     "def planted_notation_separator : Nat := 2 +.1_0set_option«debug».byAsSorry true in "
     "theorem planted_after_notation_separator : (0 : Nat) = 1 := by decide"),
    ("set_option«debug».", 'infixl:65 " . " => Nat.add\n'
     "def planted_dot_space_before : Nat := 2 .1e5set_option«debug».byAsSorry true in "
     "theorem planted_after_dot_space_before : (0 : Nat) = 1 := by decide"),
    ("set_option«debug».", 'infixl:65 " . " => Nat.add\n'
     "def planted_dot_space_after_lhs : Nat := 2\n"
     "def planted_dot_space_after : Nat := planted_dot_space_after_lhs. "
     "1_0set_option«debug».byAsSorry true in "
     "theorem planted_after_dot_space_after : (0 : Nat) = 1 := by decide"),
    ("set_option«debug».", 'infixl:65 " . " => Nat.add\n'
     "def planted_dot_comment_before_lhs : Nat := 2\n"
     "def planted_dot_comment_before : Nat := planted_dot_comment_before_lhs/- gap -/."
     "1e5set_option«debug».byAsSorry true in theorem planted_after_dot_comment_before : "
     "(0 : Nat) = 1 := by decide"),
    ("set_option«debug».", 'infixl:65 " . " => Nat.add\n'
     "def planted_dot_comment_after_lhs : Nat := 2\n"
     "def planted_dot_comment_after : Nat := planted_dot_comment_after_lhs./- gap -/"
     "1e5set_option«debug».byAsSorry true in theorem planted_after_dot_comment_after : "
     "(0 : Nat) = 1 := by decide"),
    ("set_option«debug».", 'infixl:65 " . " => Nat.add\n'
     "def planted_adjacent_separator_lhs : Nat := 2\n"
     "def planted_adjacent_separator : Nat := planted_adjacent_separator_lhs."
     "1_0set_option«debug».byAsSorry true in theorem planted_after_adjacent_separator : "
     "(0 : Nat) = 1 := by decide"),
    ("set_option«debug».", 'infixl:65 " . " => Nat.add\n'
     "def planted_adjacent_scientific_lhs : Nat := 2\n"
     "def planted_adjacent_scientific : Nat := planted_adjacent_scientific_lhs."
     "1e5set_option«debug».byAsSorry true in theorem planted_after_adjacent_scientific : "
     "(0 : Nat) = 1 := by decide"),
    ("axiom", 'infixl:65 " . " => Nat.add\n'
     "def planted_adjacent_declaration_lhs : Nat := 2\n"
     "def planted_adjacent_declaration : Nat := planted_adjacent_declaration_lhs.1_0axiom "
     "planted_after_adjacent_axiom : False"),
    ("set_option«debug».", 'infixl:65 " . " => Nat.add\n'
     "def planted_adjacent_hex_lhs : Nat := 2\n"
     "def planted_adjacent_hex : Nat := planted_adjacent_hex_lhs.0x1set_option«debug».byAsSorry "
     "true in theorem planted_after_adjacent_hex : (0 : Nat) = 1 := by decide"),
    ("set_option«debug».", "instance plantedInvNat : Inv Nat := ⟨id⟩\n"
     "def planted_inverse : Nat := 1⁻¹set_option«debug».byAsSorry true in "
     "theorem planted_after_inverse : (0 : Nat) = 1 := by decide"),
    ("axiom", "instance plantedInvNatAxiom : Inv Nat := ⟨id⟩\n"
     "def planted_inverse_declaration : Nat := 1⁻¹axiom planted_after_inverse_axiom : False"),
    ("set_option«debug».", 'infixl:65 " +℃ " => Nat.add\n'
     "def planted_celsius : Nat := 2 +℃1set_option«debug».byAsSorry true in "
     "theorem planted_after_celsius : (0 : Nat) = 1 := by decide"),
)

SET_OPTION_KEPT = (
    "/- /- -/ set_option«debug».skipKernelTC true in "
    "theorem planted_nested : True := trivial -/",
    "theorem set_optiondebug.skipKernelTC : True := trivial",
    "def set_optiondoc.verso : Bool := true",
    "def planted2set_option : Nat := 2",
    "def planted_kept_field : Nat := (1, 2).1.succ + 0x1F + 1_000",
)


def plant() -> None:
    """`set_option«debug».skipKernelTC true in`, and the other SET_OPTION_SPELLINGS, in a
    scratch copy of I.1's file: each refused by its file, line and spelling; nothing of
    SET_OPTION_KEPT is."""
    nt.scratch_plants("set_option«debug».… and its kin, with no space before the option",
                      SET_OPTION_SPELLINGS, SET_OPTION_KEPT)
    for source, expected in (
        ("p.1set_option", "p. set_option"),
        ("p.1.succ", "p.1.succ"),
        ("(·.2.toList)", "(·.2.toList)"),
        ("⟨p, p⟩.1.succ", "⟨p, p⟩.1.succ"),
        ("‹h›.1.succ", "‹h›.1.succ"),
        ("(p).1.succ", "(p).1.succ"),
        ("p .1.succ", "p .  succ"),
        ("p/- c -/.1.succ", "p       .  succ"),
        ("p./- c -/1.succ", "p.         succ"),
        ("2 +.0x1 + 2 +.1e5 + 2 +.1_0", "2 +.0x1 + 2 +.1e5 + 2 +.1_0"),
        ("2 . 0x1 + 2 . 1e5 + 2 . 1_0", "2 . 0x1 + 2 . 1e5 + 2 . 1_0"),
        ("(1, 2).1", "(1, 2).1"),
        ("1⁻¹set_option", "1⁻ set_option"),
        ("x⁻¹.1.succ", "x⁻ .1.succ"),
        ("P -ᵥ A + Kᗮ.1", "P -  A + K .1"),
        ("hᵢ₂ + x₁'", "hᵢ₂ + x₁'"),
        ("2 +℃1set_option", "2 +℃ set_option"),
        ("ℝ₁ + αβ' + ℕ.succ", "ℝ₁ + αβ' + ℕ.succ"),
    ):
        read, unsure = nt.check_fidelity.read_lean(source)
        if read != expected or unsure:
            nt.failures.append(f"read_lean({source!r}) returned {(read, unsure)!r}, not "
                               f"{(expected, [])!r}")
