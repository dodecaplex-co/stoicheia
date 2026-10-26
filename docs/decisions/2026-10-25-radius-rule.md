- **The radius rule: a radius is not nothing, and the lock up to 49 axioms (foundations, #473).**
  On 25 October 2026, at about 22:45 Pacific time, the owner answered "yes to all three."
  to three recommendations the coordinator had put to them. Those words are the owner's.
  The one this entry carries out, recorded by the coordinator on #473 and #477, was to add
  one axiom, as the scoping of those cards found necessary, and then to carry out the
  scoping's plan. This entry records the axiom: one new tacit rule, of our own,
  `Elements.Tacit.radius_ne_zero`, which says `Centre A α → OnCircle B α → ‖A B‖ ≠ 0`,
  with `A`, `B` and `α` implicit. The straight line from a circle's centre to a point on
  the circle has some length; the rule says nothing of how much. The plan's later steps
  come in later changes: Book Zero's proofs are moved onto the rule, so that no proved
  rule of Book Zero rests on `Tacit.circle_eq`, and Circle 1 is retired after III.2, under
  #477. No
  proposition's or porism's statement, no definition and no `--` line changes, in this
  change or in those.

  Why the rule is needed. The scoping of #473 and #477, on 25 October 2026, asked whether
  III.5 and III.6 could stop resting on `Tacit.circle_eq`, and whether Circle 1
  (`Tacit.between_of_inside_chord`) could be retired after III.2. Both propositions reach
  those two rules only through Book Zero, and Book Zero's proof that a radius is not
  nothing, `RuleProofs.Circle.radius_ne_zero` in `Elements/Figure/RuleBase.lean`, uses
  both; every positive length in the edition comes from that lemma. Without Circle 1, or
  without `circle_eq`, the scoping proved neither Metric 1 (`Tacit.eq_of_len_eq_zero`)
  nor the lemma from the rules that remain, and it proved the two equivalent. The one
  structure it found that breaks them, the plane with every length taken as nothing,
  breaks Metric 9 (`Tacit.area_congruent`) as well, and Book Zero has no way to meet
  Metric 9's demand for equal angles at different vertices: a judgement, not a proof that
  the rules are independent. With a radius rule restored, every other step was proved in
  Lean with neither `circle_eq` nor Circle 1. Metric 1 itself cannot be the restored rule
  under its own name, because the certificate's expectations forbid it as an axiom in the
  certificates of III.1, its porism, III.2 and II.14; so the rule recommended, and
  restored, is its equivalent, stated of a circle.

  Why it is ours, and true. Euclid draws every circle with a centre and a distance
  (Postulate 3), and `Elements/Foundations/Words.lean` reads a `Circle`, in the plane
  that models our words, as a circle of positive radius. System E states no such rule,
  since it follows there from Metric 1 with Generalities 3 and 4, that a centre lies
  inside its circle and an inside point is not on it; here the half of Metric 1 it needs
  (`eq_of_len_eq_zero`) and Generalities 3 and 4 are theorems of Book Zero, so the rule
  is our own, as `exists_centre` is. The formal model proves it in
  the plane, at once from the type of circles, whose radius must be positive, and the
  numerical model checks it in the plane and in the hyperbolic plane.

  What moves now. Nothing cites the rule yet, so no certificate changes: `facts.json`
  gains the rule's statement and module in its registry of axioms, and no entry's axioms
  or citations move. The lock goes from 48 axioms to 49, and its tacit rules from 42 to
  43; its vocabulary is unchanged, byte for byte. When Circle 1 is retired after
  III.2 (#477), the lock comes back down to 48. The generated pages move only in their
  counts and in the line numbers of their links into the foundations file, which grew
  above `len_self`. Six sentences that said the foundations have one rule of our own, or
  forty-two tacit rules, or that the overlap screen's ten circle rules are all the circle
  rules, would be false the moment the rule lands, so they change with it: the tacit
  rules' line of `README.md`, the first item of section 7 of `docs/FORMALIZATION.md`, two
  places in `docs/briefs/book-I.md`, the tacit rules' count in Book I's introduction,
  `mishnah/intro/I.md`, and the account of the screen in `docs/reports/overlaps.md`,
  which now says the radius rule is not in the screen's list.

  Approved for the foundations: `Elements/Foundations/Tacit/Metric.lean`, which declares
  the rule under a heading of its own and names it in the module's opening note, and
  changes in nothing else.

  Approved as `--write-lock` wrote it: `Certificate/axioms.lock`, one line longer, for
  `Tacit.radius_ne_zero`, with the count in its axioms header raised to match.

  The formal model's hash, `model/lock.sha256`, is approved with the new lock's digest and
  a dated paragraph saying where the rule's law, translation, check and proof now stand.

  The numerical harness's hash, `tests/model/lock.sha256`, is approved with the same
  digest and a dated paragraph of its own.

  For `tests/model/laws.toml`, one line is approved: the rule's name, mapped to the law
  `radius_ne_zero`, and no other line touched.

  For `tests/model/search.py`, the approval covers one new law, placed after `len_symm`,
  which calls only `is_centre`, `on_circle` and `d2`; every other law keeps its place.

  For `tests/model/hyperbolic.py`, the approval covers one new law after `len_symm`,
  drawn from `gs_circ_pts` and calling only `is_centre`, `on_circle` and `ch2`, the rest
  of the harness as it was.

  The model's page, `tests/model/MODEL.md`, is approved with the rule's row among the
  lengths, a paragraph on why it is ours and what it is assumed for, and the count markers
  that `render.py` moved.

  `model/Model/Audit.lean` is approved with one new pin, that `Euclidean.radius_ne_zero`
  rests on Lean's three axioms alone, and two comments brought up to date, one naming the
  rule, one giving the new number of laws;
  every other pin and guard stays.

  The generated `model/Model/Laws.lean` is approved as the generator wrote it, with the
  rule's law, its field of `Neutral` and the new lock's digest in its header.

  The generated `model/Check/Laws.lean` is approved likewise, gaining the kernel's round
  trip for the rule.

  The generated `model/Model/Assembly.lean` is approved likewise, gathering
  `Euclidean.radius_ne_zero` into `euclidean_laws`, now over 49 laws.

  `model/Model/Laws/circles.lean` is approved with the rule's hand translation among the
  generalities of a centre, and a word in its module text.

  `model/Check/Circles.lean` is approved with an import of the metric foundations file and
  two checks of that translation: by the kernel against the library's declaration, and
  over every signature against the generated law.

  `model/Model/Euclidean/CircleBasics.lean` is approved with the proof in the plane and a
  sentence in its module text.

  `model/README.md` is approved with its tables naming the rule, a paragraph on how it
  joined the model, and the counts that `render.py` moved.

  The numerical model's results are written again by
  `python3 -I tests/model/run.py --full --write`, run at commit `3a2ba2364a3a`, this
  train's merge of main, where every check passed; it also rewrote the counts between
  MODEL.md's own markers.

  Each result file that run rewrites is approved in a sentence of its own. The angle and
  area check's output, `tests/model/results/angle_check.txt`, is approved. The full grid
  enumeration's output, `tests/model/results/exhaustive.txt`, is approved. The second exact
  grid check's output, `tests/model/results/grid_check.txt`, is approved. The hyperbolic
  run's output, `tests/model/results/hyperbolic.txt`, is approved. The weakened statements'
  output, `tests/model/results/mutations.txt`, is approved. The random search's first seed,
  `tests/model/results/search-seed1.txt`, is approved. Its second seed,
  `tests/model/results/search-seed2.txt`, is approved. Its third seed,
  `tests/model/results/search-seed3.txt`, is approved. The structured search's output,
  `tests/model/results/structured.txt`, is approved. The table drawn from them all,
  `tests/model/results/summary.txt`, is approved.
