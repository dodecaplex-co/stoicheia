# How Stoicheia was made

The [README](../../../README.md#how-it-was-made) says in a few lines how Stoicheia is made. This page gives the whole account, and the logs beside it give each voyage, the first mates' groundwork and the inspections.

## The crew

Stoicheia is built with Claude (Anthropic's AI) working as a crew of agents. A captain plans and merges; from the second voyage on, first mates prepare each stretch, writing or reviewing its statements and testing them; sailors prove each proposition, in parallel; bosuns and first mates merge their work and review it for faithfulness to Euclid; artists drew most of the at-a-glance figures in Byrne's colours and lettered them all; inspectors audited Book I for consistency. Book I's statements and the proofs of I.1–I.3 came with the first commit, before the crew sailed, and three sample figures at a glance, for I.1, I.5 and I.47, came before the artists.

From the third voyage OpenAI's Codex joined the crew: Codex sailors proved I.26, I.28, I.30, I.32, all of I.33–I.48 and all of Books II and III, some of them from scratch proofs Claude's first mates had written to test the statements; they drew Euclid's figure for each and wrote the first draft of its mishnah, and Claude's bosuns, first mates and captains reviewed and edited their work. Later edits, to proofs and records alike, came from both families. Early planning also drew on conversations with ChatGPT.

## Who read what

In October 2026 every review record of Books I and II was read again in full by a reader from the family other than that of the original proof: GPT-6 Astra (Codex) for Claude's proofs, Claude Opus 5.5 for Codex's. This cross-family claim is about the original proofs, not every later edit.

Some of Codex's proofs also keep parts that Claude wrote, such as a first mate's scratch argument or corollary, or a step a bosun rewrote. Where only Claude had read those parts, GPT-6 Astra has since read the whole record: I.28, I.34, I.36, I.38, I.41, I.42 and I.46 in Book I, and II.6, II.7, II.12 and II.13 in Book II.

## What the records say of it

Each record's `reviewer` names the reader of its latest stamp. The first cross-family sign-off (card 220) wrote `run` lines beginning "card 220"; each of those still in place names the original proof's family and its reader. For the eleven records above that GPT-6 Astra has read whole, whose `run` lines begin "card 257" or "card 326", the `run` line also uses only git or record evidence to distinguish later contributions, names their readers, and says when a writer or a cross-family reading remains unrecorded.

## The logs

| Log | What it records |
|---|---|
| [voyage-01.md](voyage-01.md) to [voyage-07.md](voyage-07.md) | Each voyage: its crew, the propositions it proved and its results (voyage 2 in two parts, [02a](voyage-02a.md) and [02b](voyage-02b.md)) |
| [first-mate-02.md](first-mate-02.md), [first-mate-03.md](first-mate-03.md), [first-mate-04.md](first-mate-04.md), [first-mate-II.md](first-mate-II.md), [first-mate-III.md](first-mate-III.md) | The first mates' groundwork for each stretch: its ground and its statements |
| [orders-03.md](orders-03.md), [orders-04.md](orders-04.md), [orders-II.md](orders-II.md), [orders-III.md](orders-III.md) | The sailing orders |
| [inspection-01.md](inspection-01.md), [inspection-02.md](inspection-02.md) | The inspections of Book I |
| [voice-01.md](voice-01.md), [voice-02.md](voice-02.md) | Books I to III brought into one voice |
| [scratch-IV](scratch-IV), [scratch-figures](scratch-figures) | Scratch Lean, committed unbuilt (WORKFLOW, section 2): draft statements and prototypes for Book IV, and two scratch proofs on figures |

Astra's outside review, and [our response](../outside-review-01.md), are in `docs/reports/`.
