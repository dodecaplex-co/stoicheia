- **No numbers in the proofs of I.4 and I.8: a figure's symbols from a list
  ([#312](https://github.com/jackChallis/stoicheia/issues/312)).** FORMALIZATION, section 2,
  says that no numbers, coordinates or real numbers appear in a statement or a proof. The
  proofs of I.4 and I.8 broke that sentence. The restricted rule of superposition numbers
  its symbols (`Fin n` and `Fin m`), and each proof gave its figure's points and straight
  lines a `Symbols` instance that wrote out their count (`card := 6` and `card := 2` in I.4,
  `card := 6` and `card := 1` in I.8) and numbered the points from 0 to 5 in `index`. On 22
  October 2026, told that the counts were bookkeeping of the representation, the owner
  said: "Numbers can be taken out right? They're not used by Euclid and not essential". The
  coordinator's record is the comment on #312. So section 2's sentence is not amended, and
  the numbers come out of the proofs.

  What changed. A new definition, `Symbols.ofList`, gives a vocabulary from a list of its
  symbols' names and a proof that every symbol is in the list, for a type with decidable
  equality: the count is the list's length, a symbol's number is its first place in the
  list, and a number reads back as the symbol in that place. Its one obligation, that a
  symbol's number reads back as that symbol, is proved once for every such list, from
  membership alone, so a list need not be free of repeats. The class `Symbols`,
  `Rule.apply` and the rule `Tacit.superposition` are unchanged, and no axiom changes. Each
  instance in I.4 and I.8 is now one line through `Symbols.ofList`, with the list of
  Euclid's lettered points, or straight lines, and a proof of membership by cases and
  `decide`, which needs the types `Pt` and `Ln` to derive `DecidableEq`. No statement, `--`
  line, citation or other step of either proof changes. Section 3 of FORMALIZATION now says,
  in its row for superposition, that the rule numbers a figure's symbols internally from
  that list, so that a proof names only the points and straight lines.

  This entry approves the new `Symbols.ofList`, with its doc comment, and the sentence
  naming it in the note "Naming the symbols", in
  `Elements/Foundations/Superposition/Soundness.lean`.

  This entry approves I.4's two `Symbols` instances, each now one line through the new
  definition, and `deriving DecidableEq` on its `Pt` and `Ln`, in
  `Elements/BookI/Prop04.lean`.

  This entry approves the same change to I.8's two instances and to its `Pt` and `Ln`, in
  `Elements/BookI/Prop08.lean`.
