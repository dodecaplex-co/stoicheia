- **Generated phrases made true, from the third read-through (tooling,
  [#34](https://github.com/jackChallis/stoicheia/issues/34),
  [#156](https://github.com/jackChallis/stoicheia/issues/156)).** The coordinator's orders
  of 26 October 2026 give this change, a train of its own, the phrases that the third
  read-through of Books I to III and its limitations review found false or misleading in
  what `scripts/render.py` writes. Its readers made the book records of B3 wait on them.

  The line under the enunciation of a proposition Heath prints in brackets, I.40 and
  III.12, said "as Euclid states it", while the same page says that the proposition may be
  a later addition; it now says "as the text states it", as the certificate's Argument
  column already says "the text's". Each book's summary, which heads its index, its
  section of `CERTIFICATE.md` and its row of `README.md`, names the bracketed proposition
  in the same words, and counts its proof apart; and the keys that gloss the scope words,
  *whole*, *restricted* and *in part*, by Euclid's words (each book's index,
  `CERTIFICATE.md` and `book/names.md`) say that for I.40 and III.12 they are said of the
  text's enunciation, which may not be Euclid's. Book III's summary said that 25 proofs
  follow Euclid's argument, counting III.12's, which follows the argument Heath prints,
  and Book I's that every proof does, I.40's among them.

  The folded heading over the Lean before a main theorem counted every declaration as a
  lemma: I.4's "14 lemmas" are two inductive types and twelve abbreviations. The headings
  before and after the theorem now count each declaration by its own keyword, definitions
  apart from what is proved ("14 definitions"; "12 definitions and one lemma"), and a
  `private` declaration is read as any other, where it was left out before (I.13's three
  lemmas beside the proposition, not one; III.2's six, not four). They count the named
  declarations they list; an anonymous instance is in the listing but not in the count,
  as before.

  The line over every commentary echoed the refrain that [STYLE](../STYLE.md), section 3,
  retires ("what Lean made us say out loud") and promised a modern way on pages that have
  none. It now reads "Our commentary: why Euclid's proof, and ours, look as they do.", the
  readers' wording, and `README.md`'s list of what a page holds says the same, with the
  modern way "where it helps". The heading of the tacit rules of magnitude in each page's
  list of rules says "Rules of magnitude", as STYLE section 4 names them, not "Laws".

  The badge "in our measure of circumferences" stood beside III.24 and III.25, whose main
  theorems name no measure: their records carry the tag `angle-measure` for their
  companions. On 19 October 2026 [the decisions record](../briefs/0002-decisions.md) let
  that tag back on III.24 only "if the badge is first kept to statements that use the
  measure". `BADGE_WORDS` in `scripts/render.py` now keeps it so: the badge, on the line
  under the enunciation and as the certificate's dagger, goes only to a statement that
  names `Elements.circumference`, `Elements.standing` or `Elements.Arc.measure`, each a
  whole name of the statement as `statement_names` reads it. III.26 to III.30 keep it; III.24 and
  III.25 do not. The tag's meaning in `review/terms.toml` listed III.24 and III.26 to
  III.29; it now lists the records that carry it, III.26 to III.30, and the companions of
  III.24 and III.25.

  `README.md`'s row for the overlap audit said that each current overlap in the catalogue
  is proved from the rules named; two of the catalogue's four rows, where a rule supplies
  a step, have no audit lemma, and the row now says so, as the limitations review
  proposed.

  The change is to what `render.py` writes and to one meaning's list: no check, test,
  expected value or lock changes, and no record, Lean file, mishnah or figure. P4 of
  `scripts/check_acceptance.py` still asks each page's line under the enunciation to be
  the one `in_lean_line` gives, so the lines it expects of I.40, III.12, III.24 and III.25
  change with the pages, and its requirement does not.

  This entry approves the change to `scripts/render.py`: `in_lean_line`, `book_summary`,
  `bracketed_key` and the three keys that use it, `representation_badge` with
  `BADGE_WORDS` and `statement_names`, `counted`, `certificate_row`, `DECLARATION` and
  `DECLARATION_KEYWORDS`, `use_self_check` with `DECLARATION_CASES`, `LeanParts` with
  `DECLARATION_KIND`, `lean_listing`, `axiom_kind`, the list of kinds in the page's rules
  and `MISHNAH_LEAD`.

  This entry approves the change to `review/terms.toml`: the list in the meaning of
  `angle-measure`, and the comment at its head, which now says that the renderer may keep
  a badge to the statements that use its representation.
