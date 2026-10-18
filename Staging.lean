/-!
# Staging: statements awaiting approval

Statements are settled before proofs (docs/WORKFLOW.md, section 2). A new or changed
statement is written here first, in a stage's statement wave, with `sorry` where its proof
is due; it is challenged by readers who did not write it, and approved, before any proof is
assigned (docs/templates/orders.md, kind 2). The staged files import `Elements`, and
nothing imports them, so nothing here changes what `Elements/` proves or what the
certificate reads.

The library is not in the default build. `lake build Staging` checks that each staged
statement is well formed, `sorry` warnings and all: it is a build check, not a check that
anything is proved. When a statement is proved, it leaves Staging for its home in
`Elements/`, and its staged copy is deleted in the same change, so that no name is declared
twice.

No statement is staged yet. This root imports each staged file as it is added.
-/
