# Joining in

Thank you for wanting to help carry Euclid into Lean. Everything here is meant to be
picked up by anyone: a proof, a page of commentary, a figure, a correction to the
transcription, or a careful reading of a page. This page says where to begin. The rules
themselves live in a few documents, each the one home of its rules:

| To | Read |
|---|---|
| see the standard at a glance | [AGENTS.md](AGENTS.md): the priorities and the ten rules, written for agents and as useful for people |
| write or change the Lean | [docs/FORMALIZATION.md](docs/FORMALIZATION.md) |
| write anything a reader sees | [docs/STYLE.md](docs/STYLE.md) |
| work alongside others, review, or release | [docs/WORKFLOW.md](docs/WORKFLOW.md) |
| see what good pages look like | [docs/examples.md](docs/examples.md) |
| learn a book's words and decisions | the briefs for [Book I](docs/briefs/book-I.md), [Book II](docs/briefs/book-II.md) and [Book III](docs/briefs/0004-book-III.md) |
| see where the work stands | [docs/PROGRAM.md](docs/PROGRAM.md) |

## What you can do

**Read a page, and tell us where it could be clearer.** Open an issue naming the page and
the sentence. A quotation that does not match Heath, a figure that misleads, a page that
claims more than its theorem proves: each is a real help.

**Check a quotation or the transcription.** `heath/` is Heath's 1908 translation, from the
Internet Archive's scans ([STYLE.md](docs/STYLE.md), section 5, says where each page is).
A correction is made only against the page image, with a comment naming the leaf.

**Improve a proof.** All 99 propositions of Books I–III are proved, and a proof can still
follow Euclid more closely, or a helper say its step more plainly. Keep Heath's `--` lines
word for word and the statement as it is.

**Prove a proposition of a new book.** Book IV, of figures inscribed in and circumscribed
about circles, is next. Each new book starts with its brief, and with its statements
reviewed and approved before anyone proves them; then every proposition is stated in Lean,
with Euclid's sentences as comments and a `sorry`, and marked 🚧 on the book's page. Pick a
🚧 proposition: a proof needs only the statements of what it cites, so it can be proved
before they are.

**Write commentary, or draw a figure.** [STYLE.md](docs/STYLE.md) has the voice, the
mishnah, the further reading and the figures, and [the examples](docs/examples.md) show
them at work.

## A few house rules

1. **Euclid's words go in `--` comments, ours in `/- … -/`.** Keep every `--` line exactly
   as it is: CI checks that, read in order, they spell out Heath's text word for word. Put
   the Lean for each sentence directly under it.
2. **Follow Euclid's route,** and label any departure where it happens. Never add a
   citation only to match Heath's references, or use a hypothesis only to silence a
   warning. Helpers go before the proposition, corollaries after it, and shared steps where
   [FORMALIZATION.md](docs/FORMALIZATION.md) says.
3. **Never add an `axiom`.** All assumptions live in `Elements/Foundations/`. If you believe
   Euclid needs a rule that is not there, open an issue: new rules come from System E, or
   LeanEuclid's corrections of it, with a citation, or are our own, as `exists_centre` is,
   by the owner's decision.
4. **Don't change a statement** without opening an issue first: other propositions are
   written against it.
5. **One warm voice,** generous with credit and never competitive
   ([STYLE.md](docs/STYLE.md), section 1).

## Before you open a pull request

CI runs the commands listed in [WORKFLOW.md](docs/WORKFLOW.md), section 8. Before a pull
request, run at least these:

```sh
python3 scripts/check_paths.py
lake build
lake env lean Certificate/Facts.lean
python3 scripts/check_fidelity.py
python3 scripts/check_style.py
python3 scripts/render.py
```

The first needs no Lean and runs in under a second. It holds the name, type and mode of
every file Git tracks to the standard in [WORKFLOW.md](docs/WORKFLOW.md#file-names),
section 4, "File names"; it reads what you have staged, so `git add` a new file before
you run it.

If you change a Lean file, its review record goes stale, even for a comment, and so does
an edit to the record's own words, its `[review]` table aside: say so in the pull
request, and leave the stamp to a reviewer (WORKFLOW.md, section 6).

If you fix a check, add a test that shows the fault would now be caught. A negative test,
which plants the fault in the real files or a copy of them and requires the check to
refuse it, is one new file in `scripts/negative/`, with no other file of the suite to
edit. Like any file under `scripts/`, it is a protected path, so the pull request that
adds, changes or deletes one names it in a new decision entry and carries the label
`security-review`;
[WORKFLOW.md, section 8](docs/WORKFLOW.md#8-validation-on-the-integrated-revision), says
what the file holds and how to run it alone, and
[section 10](docs/WORKFLOW.md#landing-work-pull-requests), under "Decision entries", how
to write the entry and what else the pull request carries.

Working alone on a pull request, you are its integrator: commit the regenerated `book/`,
`CERTIFICATE.md`, `GRAPH.md`, `facts.json`, README.md's rows between the
`<!-- scope:… -->` markers and PROGRAM.md's status table with your change, and CI checks
that they match. When several people work in parallel, only the integrator commits them
([WORKFLOW.md](docs/WORKFLOW.md), section 4). In the pull request, say what you checked and
what you did not; the handback in [docs/templates/proposition.md](docs/templates/proposition.md)
is a good shape for it.
