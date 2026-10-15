# Earlier work and sources (October 2026)

Notes gathered while planning the project, kept so that later decisions can be
traced. They describe each project by what it does; none of this is a comparison
of merit.

## Euclid in proof assistants

- **LeanEuclid** (Murphy, Yang, Sun, Li, Anandkumar, Si; ICML 2024; MIT;
  [repo](https://github.com/loganrjmurphy/LeanEuclid)). Implements System E in Lean 4
  as `axiom`s over opaque points, lines and circles, and formalizes all 48
  propositions of Book I. Diagrammatic steps are discharged by the tactics
  `euclid_apply` / `euclid_finish`, which call the SMT solvers Z3 and CVC5. The repo
  also holds Euclid's texts and diagrams for Book I. Its rendering of System E was
  our constant companion when writing the tacit rules; see NOTICE.
- **synthetic_euclid_4** (Hernández-Espiet, Kontorovich; Apache-2.0;
  [repo](https://github.com/ah1112/synthetic_euclid_4)). Book I in Lean 4 on a
  System E-style class, with every diagram step proved explicitly (no SMT), using
  Mathlib.
- **Beeson, Narboux and Wiedijk, *Proof-checking Euclid*** (Annals of Mathematics and
  Artificial Intelligence 85, 2019). All of Book I, checked in HOL Light and Coq, on
  a points-only axiom system; about 235 theorems for the 48 propositions. Part of
  [GeoCoq](https://github.com/GeoCoq/GeoCoq).
- **Kellison, Bickford and Constable, *Implementing Euclid's straightedge and compass
  constructions in type theory*** (Annals of Mathematics and Artificial Intelligence
  85(2–4), 2019, pp. 175–192; [doi](https://doi.org/10.1007/s10472-018-9603-0)).
  Euclid's constructions built in the intuitionistic type theory of the Nuprl proof
  assistant, with a predicate for orientation that lets them be stated concisely; one
  result is a proof of I.2 in its full generality. Cornell's Nuprl site also has
  [Nuprl proofs of Book I's propositions](https://nuprl-web.cs.cornell.edu/MathLibrary/TheElements),
  set out as Heath presents them.
- **Pistis** (Mao, Zhong, Arekar, Feng, An, Huang, Si, Li; arXiv 2608.15432, August
  2026). Agentic, oracle-guided proof search producing Lean proofs of Books I–III
  that follow Euclid's natural-language argument, with a definition of
  "faithfulness" and a catalogue of gaps found in Euclid.

## System E

Avigad, Dean and Mumma, *A formal system for Euclid's Elements* (Review of Symbolic
Logic 2(4), 2009, pp. 700–768; arXiv 0810.4315). Construction rules (§3.3),
diagrammatic inferences (§3.4), metric inferences (§3.5), transfer inferences (§3.6)
and superposition (§3.7). Two things we noticed while transcribing the rules:

- Points rule 6 prints "a is on the same side of L as b" where "not on the same side"
  is meant.
- Intersection rule 4 ("a on or inside α") fails for a small circle wholly inside a
  large one; LeanEuclid's form ("a on α") is the one we use.

## The text

- **Heath 1908** (public domain): Internet Archive scans; vol. 1 (Books I–II) is
  `thirteenbookseu02heibgoog`, vol. 2 is `thirteenbookseu00heibgoog`, vol. 3 is
  `thirteenbookseu03heibgoog`. Page-image URLs follow
  `https://archive.org/download/<id>/page/n<LEAF>.jpg`; in vol. 1, leaf = page + 20.
  Book I was transcribed from the OCR and proofread against the page images.
- **Perseus** has Heath's (1926) text under CC BY-SA; used only as a cross-check.
- **Project Gutenberg** has Casey's *First Six Books* (1885, #21076) and Proclus on
  Book I in Taylor's translation (#74253, #79455). The Casey was produced by Joshua
  Hutchinson, Keith Edkins and the Distributed Proofreaders from Cornell University
  Library's scans (its Historical Mathematics Monographs collection), and revised by
  Richard Tonsing.
- **Simson 1756**: Robert Simson's *The Elements of Euclid, viz. the first six books,
  together with the eleventh and twelfth* (Glasgow: Robert and Andrew Foulis). Heath
  quotes him often, and our mishnah on I.24 builds on the sentence he added there,
  which Heath leaves out.
- **Joyce's** online edition and **Fitzpatrick's** Greek–English edition are
  copyrighted; we link to them.

## Mathematics beside Lean

Two projects showed how mathematics written for people can sit beside the Lean that
checks it, and were the inspiration for our pages:

- **leanblueprint** (Patrick Massot;
  [repo](https://github.com/PatrickMassot/leanblueprint)). A plasTeX plugin for
  writing the blueprint of a Lean formalization: the mathematics in prose, each
  statement linked to its Lean.
- **Verso** (David Thrane Christiansen and the Lean FRO;
  [repo](https://github.com/leanprover/verso)). "A tool for writing about Lean":
  documents written in Lean itself, for manuals, tutorials, blogs and papers.
