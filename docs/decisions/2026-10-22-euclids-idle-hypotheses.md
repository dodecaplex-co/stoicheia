- **A hypothesis of Euclid's own that his argument leaves idle stays, untagged (#347).** On
  22 October 2026 the coordinator ruled, under the owner's delegation of that day (the
  owner's words, as the coordinator quotes them: "whatever's reasonable and in spirit with
  Euclid"), that a hypothesis Euclid states himself, and that goes unused in his own
  argument, stays in our statement as he states it, with no tag, and that the tag
  `redundant-hypothesis` stays for a redundancy that our representation creates. The
  coordinator's record of the ruling is
  [#347](https://github.com/jackChallis/stoicheia/issues/347).

  Why. Such a hypothesis is Euclid's, not a product of our representation, so the tag
  would say something false of it. Taking it out would change the scope of a published
  statement, which is the owner's decision, and is not asked for.

  The example is III.8, in `Elements/BookIII/Prop08.lean`. Its clause on the concave
  circumference, comparing DE with DF, supposes that F, the more remote, lies on that
  circumference, and its clause on the convex, comparing DK with DL, supposes the same of
  L; neither Euclid's proof nor ours uses either supposition, and both stay in the
  statement.

  The ruling changes no statement, no Lean and no review record.
  [FORMALIZATION](../FORMALIZATION.md), section 5, says so beside `redundant-hypothesis`.
