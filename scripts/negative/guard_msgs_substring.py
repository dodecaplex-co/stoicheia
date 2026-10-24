"""Without a build, in a scratch copy of I.1's file in a temporary tree, read by the source
scan alone, as in set_option_spellings: `#guard_msgs` with `substring`:
`(substring := true)`, closed up and spaced, after a filter or an option, with a remark or a
line break inside, under a docstring that is only part of the error, and
`(substring := false)`: each refused by its file and line, while a `#guard_msgs` with other
options, and the words in a comment or a string, are not (#197).
"""

import negative_tests as nt

BUILDS = False

# `#guard_msgs` with `substring` (#197), in Lean 4.35's forms: closed up and spaced, after a
# filter or an option, with a remark or a line break inside, under a docstring that is only
# part of the error, and set false; each is (the words check_fidelity.py names, a line of
# Lean). GUARD_SUBSTRING_KEPT holds what the rule does not refuse.
GUARD_SUBSTRINGS = (
    ("#guard_msgs (substring := true)",
     "#guard_msgs (substring := true) in theorem planted_sub : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs(substring:=true)",
     "#guard_msgs(substring:=true)in theorem planted_sub_closed : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs ( substring := true )", "#guard_msgs ( substring := true ) "
     "in theorem planted_sub_spaced : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (error, substring := true)", "#guard_msgs (error, substring := true) "
     "in theorem planted_sub_filter : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (whitespace := lax, substring := true)",
     "#guard_msgs (whitespace := lax, substring := true) "
     "in theorem planted_sub_option : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (substring := true)", "#guard_msgs (substring /- a remark -/ := true) "
     "in theorem planted_sub_remark : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (substring := true)", "#guard_msgs\n  (substring\n  := true) "
     "in theorem planted_sub_break : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (substring := true)", "/-- error -/ #guard_msgs (substring := true) "
     "in theorem planted_sub_partial : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (substring := false)",
     "#guard_msgs (substring := false) in #print axioms planted_sub"),
)

GUARD_SUBSTRING_KEPT = (
    "#guard_msgs (whitespace := lax, ordering := sorted) in #print axioms planted_sub",
    "-- #guard_msgs (substring := true) in, in a comment",
    'def plantedKeptSubstring := "#guard_msgs (substring := true) in"',
)


def plant() -> None:
    """`#guard_msgs (substring := true) in` and the other GUARD_SUBSTRINGS in a scratch copy
    of I.1's file: each refused by its file, line and words; nothing of
    GUARD_SUBSTRING_KEPT is."""
    nt.scratch_plants("#guard_msgs with substring, in each of its forms", GUARD_SUBSTRINGS,
                      GUARD_SUBSTRING_KEPT)
