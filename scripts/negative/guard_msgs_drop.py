"""Without a build, in a scratch copy of I.1's file in a temporary tree, read by the source
scan alone, as in set_option_spellings: `#guard_msgs` with `drop`, in each of its forms:
`(drop all)`, closed up and spaced, `(drop error)`, `(drop warning)`, `(drop info)`, `drop`
after another filter or an option, twice, and with a remark or a line break inside: each
refused by its file and line, while a `#guard_msgs` that checks its messages or passes them
on, and the words in a comment or a string, are not (#197).
"""

import negative_tests as nt

BUILDS = False

# `#guard_msgs` with `drop`, in Lean 4.35's forms (#197): each kind of message and `all`,
# the brackets closed up or spaced, `drop` after another filter or an option, twice, and a
# remark or a line break inside; each is (the words check_fidelity.py names, a line of
# Lean). GUARD_KEPT holds what the rule does not refuse: a `#guard_msgs` that checks its
# messages or passes them on, and the words in a comment or a string.
GUARD_DROPS = (
    ("#guard_msgs (drop all)",
     "#guard_msgs (drop all) in theorem planted_drop_all : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs(drop all)",
     "#guard_msgs(drop all)in theorem planted_drop_closed : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (drop error)",
     "#guard_msgs (drop error) in theorem planted_drop_error : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs ( drop error )",
     "#guard_msgs ( drop error ) in theorem planted_drop_spaced : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (drop warning)",
     "#guard_msgs (drop warning) in theorem planted_drop_warning : True := sorry"),
    ("#guard_msgs (drop info)", "#guard_msgs (drop info) in #print axioms planted_drop_all"),
    ("#guard_msgs (warning, drop all)",
     "#guard_msgs (warning, drop all) in theorem planted_drop_after : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (whitespace := lax, drop all)", "#guard_msgs (whitespace := lax, drop all) "
     "in theorem planted_drop_option : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (drop trace, drop error)", "#guard_msgs (drop trace, drop error) "
     "in theorem planted_drop_twice : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (drop all)", "#guard_msgs /- a remark -/ (drop /- a remark -/ all) "
     "in theorem planted_drop_remark : (0 : Nat) = 1 := rfl"),
    ("#guard_msgs (drop all)", "#guard_msgs\n  (drop\n  all) "
     "in theorem planted_drop_break : (0 : Nat) = 1 := rfl"),
)

GUARD_KEPT = (
    "#guard_msgs in #print axioms planted_drop_all",
    "#guard_msgs (error) in #print axioms planted_drop_all",
    "#guard_msgs (pass all) in #print axioms planted_drop_all",
    "/- #guard_msgs (drop all) in -/ theorem planted_kept_remark : True := trivial",
    'def plantedKeptWords := "#guard_msgs (drop all) in"',
)


def plant() -> None:
    """`#guard_msgs (drop all) in` and the other GUARD_DROPS in a scratch copy of I.1's file:
    each refused by its file, line and words; nothing of GUARD_KEPT is."""
    nt.scratch_plants("#guard_msgs with drop, in each of its forms", GUARD_DROPS, GUARD_KEPT)
