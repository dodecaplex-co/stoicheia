<p align="center">
  <img src="assets/stoicheia-social.png" alt="Raphael's Euclid, from The School of Athens, drawing the figure of Proposition I.47 on a laptop" width="760">
</p>

# Stoicheia

*Euclid's Elements, checked line by line in Lean.*

Στοιχεῖα, *Stoicheia*, "Elements", is Euclid's own title for the book that taught geometry for more than two thousand years. Abraham Lincoln, in the short autobiography he wrote in 1860, said of himself: "He studied and nearly mastered the Six-books of Euclid, since he was a member of Congress." This project carries the same book into [Lean](https://lean-lang.org), a programming language that checks mathematical proofs, so that every step Euclid takes is checked by a machine that can't be talked into anything.

For every proposition you get:

- **Euclid's words**, in Sir Thomas Heath's 1908 translation (public domain).
- **Two figures**: one "at a glance", in the bold red, yellow and blue of Oliver Byrne's 1847 Euclid, to show the idea before you read a word; and Euclid's own figure, with Heath's letters, to follow the proof by.
- **The proof in Lean**, written to follow Euclid sentence by sentence. Each of his sentences is a comment, and under it is the Lean that carries it out.
- **A certificate**, computed by Lean itself, of exactly what the proof rests on: which postulates, which common notions, and which of the many things Euclid takes for granted without saying so.
- **A mishnah**: commentary on what Euclid assumed, what Lean made us say out loud, and how the same result looks with modern tools.

There are no coordinates here, no real numbers and no complex numbers. The geometry is the geometry Euclid wrote, the kind Lincoln would recognize. Lengths, angles and areas are *magnitudes*, which can be added and compared and nothing more, just as in the *Elements*.

## Where things stand

| | |
|---|---|
| **Book I** | **Complete: all 48 propositions proved**, every one following Euclid's own proof. The certificate shows the shape of the book: 29 propositions never need the parallel postulate, and the first that does is I.29, just where Euclid puts it. [Read Book I →](book/I/index.md) |
| **Book II** | **Complete: all 14 propositions proved**, every one following Euclid's own proof. "The rectangle contained by AB, BC" and "the square on AB" are areas in Lean, defined rather than assumed, and a rectangle drawn in a figure is proved equal to the rectangle contained by its sides. [Read Book II →](book/II/index.md) |
| Books III–XIII | To come, one book at a time. |

The [certificate](CERTIFICATE.md) and the [graph of who uses whom](GRAPH.md) are regenerated from the proofs on every change.

## Read it

Start with [the definitions, postulates and common notions](book/I/front.md), then [Proposition 1](book/I/01.md). Every page reads the same way: Euclid's statement, his figure, his proof, then the Lean, what it rests on, and the mishnah.

Here is the heart of I.1. Euclid's sentences are the comments:

```lean
  -- With centre A and distance AB let the circle BCD be described; [Post. 3]
  obtain ⟨BCD, hA_BCD, hB_BCD⟩ := Postulate3 A B hAB
  -- again, with centre B and distance BA let the circle ACE be described; [Post. 3]
  obtain ⟨ACE, hB_ACE, hA_ACE⟩ := Postulate3 B A hAB.symm
  -- and from the point C, in which the circles cut one another, …
  have hmeet := circles_meet hB_BCD (centre_inside hA_BCD) (centre_inside hB_ACE) hA_ACE
  /- … C is taken where they cross, on whichever side of AB we need … -/
  -- Now, since the point A is the centre of the circle CDB,
  -- AC is equal to AB. [Def. 15]
  have hAC : ‖A C‖ = ‖A B‖ := Definition15 hA_BCD hC_BCD hB_BCD
```

That `circles_meet` is a step Euclid never justifies. Heath: "It is a commonplace that Euclid has no right to assume, without premising some postulate, that the two circles will meet in a point C." In Lean it has to be a named rule, and so it appears on I.1's certificate.

## What Euclid takes for granted

The foundations are in [`Elements/Foundations/`](Elements/Foundations):

- [**Postulates**](Elements/Foundations/Postulates.lean): Euclid's five, each a Lean `axiom`.
- [**Common Notions**](Elements/Foundations/CommonNotions.lean): all five turn out to be *theorems*, once we state how magnitudes add and compare.
- [**Definitions**](Elements/Foundations/Definitions.lean): the ones that do work in the proofs. Definition 15 (all radii of a circle are equal) is really an axiom, and is treated as one. [Book II's](Elements/Foundations/DefinitionsII.lean) are the rectangle contained by two straight lines and the square on one, defined, not assumed.
- [**Tacit rules**](Elements/Foundations/Tacit): everything Euclid reads off his figures without saying so. That a point lies between two others, that a line through the inside of a circle must cut it, that two triangles which match in every side and angle have the same area. These follow, rule by rule, the System E of Jeremy Avigad, Edward Dean and John Mumma, which was designed to capture exactly how Euclid reasons from a diagram.

Because every assumption is a Lean `axiom`, `#print axioms` lists exactly what a proof rests on, and [`Certificate/Facts.lean`](Certificate/Facts.lean) turns that into the certificate. One famous result can't be faked: whether a proposition needs the parallel postulate. CI fails if anything before I.29 uses it.

Proposition by proposition, the steps Euclid takes without a word, and the rule or lemma that fills each one, are gathered in [a catalogue for Book I](docs/reports/gaps-book-I.md), with the names of those who noticed them first, where we know.

## Run it

1. Install Lean: the easiest route is VS Code with the **Lean 4** extension, or `curl https://elan.lean-lang.org/elan-init.sh -sSf | sh`. The `lean-toolchain` file pins Lean 4.35.0, and there are no other dependencies.
2. Check every proof:
   ```sh
   lake build
   ```
3. Rebuild the certificate and the pages, and check that the Lean still quotes Heath word for word:
   ```sh
   lake env lean Certificate/Facts.lean
   python3 scripts/check_fidelity.py
   python3 scripts/render.py
   ```

**Try breaking it.** In [`Prop01.lean`](Elements/BookI/Prop01.lean), change `Definition15 hA_BCD hC_BCD hB_BCD` to `Definition15 hB_ACE hC_ACE hA_ACE` and run `lake build`. Lean refuses: B is the centre of the other circle, so the radii it gives are the wrong ones.

## How it's built

| Where | What |
|---|---|
| [`heath/`](heath) | Heath's translation, transcribed from the 1908 scans and checked against the page images |
| [`Elements/Foundations/`](Elements/Foundations) | Postulates, common notions, definitions, tacit rules |
| [`Elements/Figure/`](Elements/Figure) | "Book Zero": small facts every figure needs, proved once |
| [`Elements/BookI/`](Elements/BookI), [`Elements/BookII/`](Elements/BookII) | One file per proposition; Book II's shared ground, rectangles and squares from Book I, is in [`Rectangles.lean`](Elements/BookII/Rectangles.lean) |
| [`mishnah/`](mishnah) | The commentary |
| [`figures/`](figures) | The figures: the "at a glance" figures in Byrne's colours, and Euclid's own with Heath's letters |
| [`book/`](book), [`CERTIFICATE.md`](CERTIFICATE.md), [`GRAPH.md`](GRAPH.md) | Generated pages; don't edit by hand |
| [`docs/`](docs) | The [plan](docs/briefs/0001-plan.md) the project started from, the [catalogue of what Euclid takes for granted](docs/reports/gaps-book-I.md), the [crew's logs](docs/reports/crew), and notes on [earlier work](docs/reports/0001-prior-art.md) |

A Lean proof needs only the *statements* of the propositions it cites, not their proofs. So once a book's statements are written, its propositions can be proved in any order, and many at once.

## Join in

Book I is proved, and Book II is under way: pick any 🚧 proposition in [Book II](book/II/index.md) and prove it, write a mishnah or draw a figure. There is plenty to do in [Book I](book/I/index.md) as well: read a page and tell us where it could be clearer, check a quotation against Heath's scans, or improve a figure or a proof. [CONTRIBUTING.md](CONTRIBUTING.md) explains the few house rules.

## How it was made

Stoicheia is Jack Challis's project, built with Claude (Anthropic's AI) working as a crew of agents. From the third voyage OpenAI's Codex joined the crew: Codex sailors proved I.26, I.28, I.30, I.32 and all of I.33–I.48, drew Euclid's figure for each and wrote the first draft of its mishnah, and Claude's bosuns, first mates and captains reviewed and edited their work. A captain plans and merges; first mates prepare each stretch; sailors prove each proposition, in parallel; bosuns and first mates merge their work and review it for faithfulness to Euclid; artists drew the figures; inspectors audit the whole for consistency. Early planning also drew on conversations with ChatGPT. Nothing rests on trust: Lean's kernel checks every proof, CI checks that every proof still quotes Heath word for word, and every quotation in the commentary was checked against the scanned 1908 text. The crew's logs are in [docs/reports/crew](docs/reports/crew).

## Standing on shoulders

This project is a love letter to a long line of people who have read Euclid carefully, and it leans on all of them.

- **The text.** Euclid, of course. J. L. Heiberg, whose Greek text Heath translated. Sir Thomas L. Heath, whose 1908 translation and notes are the backbone of every page here. Proclus, whose commentary on Book I is still the first place to look, and Thomas Taylor, who translated it in 1792. Robert Simson, whose 1756 *Elements* Heath quotes again and again, and whose added sentence in I.24 our mishnah on that proposition builds on. John Casey, whose 1885 *First Six Books* is lovingly kept on Project Gutenberg, and Oliver Byrne, whose 1847 Euclid in colour is one of the most beautiful books ever printed; our "at a glance" figures borrow his palette and his idea that a picture can carry a proof's meaning before any letters do.
- **Readers' editions today.** David E. Joyce's [online *Elements*](https://mathcs.clarku.edu/~djoyce/elements/elements.html) and Richard Fitzpatrick's Greek–English edition, both wonderful companions.
- **The foundations of geometry.** Hilbert and Tarski, who showed how to fill Euclid's gaps, and Robin Hartshorne, whose *Geometry: Euclid and Beyond* explains it all with great clarity. Above all, Jeremy Avigad, Edward Dean and John Mumma, whose System E is the source of our tacit rules.
- **Euclid in proof assistants.** Michael Beeson, Julien Narboux and Freek Wiedijk, whose [*Proof-checking Euclid*](https://arxiv.org/abs/1710.00787) worked through all of Book I in Coq and HOL Light, together with the [GeoCoq](https://github.com/GeoCoq/GeoCoq) team. Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si, whose [LeanEuclid](https://github.com/loganrjmurphy/LeanEuclid) brought System E to Lean. We kept their careful rendering of the rules open beside the paper the whole time, and borrowed their corrections and their form of superposition (see [NOTICE](NOTICE)). André Hernández-Espiet and Alex Kontorovich, whose [synthetic_euclid_4](https://github.com/ah1112/synthetic_euclid_4) proves all of Book I in Lean 4 with every diagram step spelled out. Ariel Kellison, Mark Bickford and Robert Constable, whose [*Implementing Euclid's straightedge and compass constructions in type theory*](https://doi.org/10.1007/s10472-018-9603-0) builds Euclid's constructions in the intuitionistic type theory of the Nuprl proof assistant, and from it proves I.2 in its full generality. Tadd Mao, Tianjun Zhong, Dhruva Arekar, Yuming Feng, One An, Jiani Huang, Xujie Si and Ziyang Li, whose [*Does the Proof Prove It That Way?*](https://arxiv.org/abs/2608.15432) asks exactly the question this project cares about: whether a formal proof follows Euclid's own argument.
- **Lean.** Leonardo de Moura, Sebastian Ullrich, the Lean FRO and the whole Lean community. Patrick Massot's [leanblueprint](https://github.com/PatrickMassot/leanblueprint) and the Lean FRO's [Verso](https://github.com/leanprover/verso), by David Thrane Christiansen, showed us mathematics written out in prose beside its Lean, and inspired the way these pages are laid out.
- **The keepers of the books.** The Internet Archive, Google Books and the Harvard library, whose scan of Heath we read from; HathiTrust; Cornell University Library, whose scans of Casey are the ones Project Gutenberg's edition was made from; Project Gutenberg and its Distributed Proofreaders, among them Joshua Hutchinson and Keith Edkins, who prepared that Casey, and Richard Tonsing, who revised it; the Perseus Digital Library.
- **The logo.** Raphael's *School of Athens* (1509–1511), in Marie-Lan Nguyen's photograph on Wikimedia Commons. Euclid's slate has become a laptop, and he is drawing I.47. See [assets/CREDITS.md](assets/CREDITS.md).

Full references are in [docs/references.bib](docs/references.bib).

## License

The Lean code and scripts are under the [Apache License 2.0](LICENSE). Our own prose (the mishnah, the figures, the docs) is under [CC BY 4.0](LICENSE-PROSE.md). Heath's 1908 translation and Euclid himself are in the public domain. Anyone may use any of it; we'd love to hear if you do.
