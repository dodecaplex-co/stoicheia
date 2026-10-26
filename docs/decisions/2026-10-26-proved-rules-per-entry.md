- **Every certificate entry lists the proved rules beneath it (certificate,
  [#168](https://github.com/jackChallis/stoicheia/issues/168)).** On 26 October 2026 the
  coordinator gave card #168, which holds every release while it stays open, to ship ER;
  this is the first of its two trains. The retirement of #119 made eight tacit rules
  theorems: `Tacit.adjacent_eq_of_right`, `Tacit.not_same_side_of_circles_meet`,
  `Tacit.centre_unique`, `Tacit.inside_of_between`, `Tacit.exists_point_outside_circle`,
  `Tacit.line_meets_circle_of_opposite_sides`, `Tacit.triple_incidence3` and
  `Tacit.inside_of_angle_add`. #168 calls for stronger pins excluding the eight retired
  rules beneath III.1, III.1 Por., III.2 and II.14.
  Those pins were written as `excludes` lists on the four entries' `axioms`; a theorem's
  name never appears in an axiom list, so none of them can fail now. So the certificate
  gives every entry a list a pin can read instead, `proved_rules`: each theorem of
  `Elements.Tacit` that the entry's statement or proof reaches, at any depth, through
  what it cites too. Lean's environment gives it, by way of `Certificate/Facts.lean`; it
  is generated, never written by hand. No pin reads the field yet: the second train of
  #168 adds the pins on it, and the planted use that only it can catch.

  When ship TS first built the field, on 21 October, it showed all four entries resting on
  `Tacit.adjacent_eq_of_right`, and the porism on `Tacit.centre_unique` as well. On 21
  October 2026 the owner chose, of the options the coordinator put to them, "Remove the
  uses first"; #168 holds the coordinator's record of that choice. Those uses are gone.
  Generated today, the field shows none of the eight beneath III.1, III.1 Por., III.2 or
  II.14, whose lists hold 24, 23, 24 and 27 proved rules respectively. Elsewhere three of
  the eight are still in use. Of the 144 entries, 37 rest on `Tacit.adjacent_eq_of_right`,
  I.13's corollary, III.3, III.14 and III.25 among them; 8 on `Tacit.centre_unique`, from
  III.26 to III.30, III.36, III.37 and the companion III.30 halves; and 6 on
  `Tacit.triple_incidence3`, all companions of III.16 and III.18. No entry rests on any of
  the other five.

  The new walk, `beneath`, reads each declaration through `mentions`, as the certificate's
  other walks of a proof do, and goes wherever `collectAxioms` goes short of Lean's own
  modules, which cannot reach this project's: into the entries cited and those they cite,
  the Common Notions, the shared steps and the proved rules themselves, so that a rule
  proved from another brings in the pair. It notes each axiom and each proved rule it
  passes. Then, for every entry, the run fails unless the axioms the walk noted are
  exactly the ones `collectAxioms` reports, Lean's own foundations aside; so the rules
  listed come from a walk held to Lean's own answer.
  The listing of the proved rules, `proved_rule_cites` with it, now happens before the
  entries are walked, so that each walk knows which theorems are rules; both top-level
  tables come out as before. Timed the same way on one machine, `time lake env lean
  Certificate/Facts.lean` took from 1:00 to 1:05 on main and from 1:10 to 1:15 with this
  change, about six seconds more of processor time. In `facts.json` each of the 144
  entries gains the field and nothing else changes; `scripts/render.py` then rewrites no
  other generated output.

  Warm thanks go to ship TS, whose design and code this train carries over from its
  branch `tooling/proved-rules-per-entry`, built on 21 October and held for the owner's
  ruling: the structure and the walk, the check against Lean, the field and where it is
  written, the module docstring's additions, the rows that document the field, and four
  tests on a fixture with two stand-in rules, the second proved from the first. Ship TS's
  careful first run of that walk is what found the uses the owner then asked to be
  removed.

  The protected file `Certificate/Facts.lean` is changed here: it gains the structure
  `Beneath` and the walk `beneath`, lists the proved rules ahead of the entries, checks
  each entry's walk against `collectAxioms`, writes the entry field `proved_rules` beside
  `axioms`, and says so in its module docstring.

  The protected file `Certificate/FIELDS.md` is changed here too, with a row for the new
  entry field, dated today, a sentence on the top-level `proved_rules` that points to it,
  and the walk `beneath` set beside the other self-checks.

  A third protected file, `tests/test_certificate.py`, gains ship TS's class of four
  tests on its fixture of two stand-in rules, and one new test, written for this train,
  that an expectation reads an entry's `proved_rules` by its `ref` or over every entry,
  apart from the top-level table of that name, and refuses an entry that lacks the field.
