# Decisions since the plan

*What has changed since [the plan](0001-plan.md), and why. Newest at the bottom.*

## 15 October 2026

- **One voice, and thanks where they are due.** The plan promised an "Also
  formalized in" box on every page, linking the same proposition in other
  formalizations. It was dropped. The pages speak in one voice, and the people
  whose work a page draws on are thanked warmly where it draws on them: in the
  mishnah, in the [gap catalogue](../reports/gaps-book-I.md) and in the README.
- **"Euclid cites" beside "Lean needs".** The certificate line now sets what
  Euclid cites, read from Heath's brackets, beside what the Lean needs, as the plan
  first intended.
- **Captions.** The caption of an "at a glance" figure may be one or two short
  sentences.
- **Porisms and corollaries come after.** A porism, or any other corollary, follows
  its proposition in the same file; the helpers a proof needs come before it.
- **Shared steps that need a proposition.** Book Zero may not cite a proposition, so
  a small step that several proofs share and that does cite one lives in
  [`Elements/BookI/Helpers.lean`](../../Elements/BookI/Helpers.lean).
- **Three statements made stronger.** I.1 takes an optional side for its triangle;
  I.9 says that its bisector lies within the angle; and I.22 builds its triangle at
  a given corner. The first mate's reasons are in
  [first-mate-02.md](../reports/crew/first-mate-02.md).
- **The mishnah has a length.** Each mishnah is held to 200 to 500 words, and
  [docs/STYLE.md](../STYLE.md) is its style guide.
- **System E and LeanEuclid, thanked once a page.** The thanks to Jeremy Avigad,
  Edward Dean and John Mumma for System E, and to Logan Murphy and his colleagues
  for LeanEuclid, is carried once on every page, in its footer.
- **The square logos stay**, for avatars and icons.
- **A wider crew.** From voyage 3 the crew includes OpenAI Codex sailors alongside
  Claude ones, and an enforcer who keeps the voice one voice.
