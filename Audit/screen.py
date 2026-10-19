"""A mechanical screen for docs/reports/overlaps.md.

For every statement in facts.json, Lean's `grind` tries a proof from
  - each axiom alone,
  - each family of axioms together (the module that declares them),
  - each pair of the rules about circles, and
  - each pair of families,
with the phrase definitions (SameSideOf, CirclesMeet, ...) unfolded. A failed attempt
falls back to `sorry`, and only the attempts that close without it are reported.

It is a screen, not a proof search. `grind` instantiates rules among the terms already in
a goal; it does not draw a new circle or lay down a triangle, so a proposition that needs
one (I.23 from superposition) is found by reading, not here. The former I.7 overlap
used Circle 4, now a corollary of I.7 and no longer an axiom in this screen.

The statements are facts.json's entries. At commit d040117 that is the 99 propositions,
399 attempts each, 39,501 in all; with the three porisms as well, 40,698. Either way the
screen closes III.2, III.5 and III.6, and nothing else.

usage (from the repository root, after `lake build`):
    python3 Audit/screen.py OUTDIR [--jobs N]

It writes its Lean files and logs to OUTDIR, which must be outside the repository, and
takes about ten minutes with twelve jobs. Standard library only.
"""

import argparse
import itertools
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Rules that speak of circles: the pairs among these are screened against every statement.
CIRCLE = """Definition15 Postulate3 Tacit.centre_inside Tacit.inside_not_on
Tacit.between_of_inside_chord Tacit.outside_of_between
Tacit.line_meets_circle_of_opposite_sides
Tacit.line_meets_circle_of_inside Tacit.circles_meet_of_on_inside_outside Tacit.circles_meet
Tacit.line_circle_between Tacit.line_circle_beyond Tacit.circles_meet_same_side
Tacit.circles_meet_opposite_side Tacit.exists_point_on_circle Tacit.exists_point_inside_circle
Tacit.exists_point_outside_circle Tacit.circle_eq Tacit.on_circle_of_len_eq
Tacit.inside_of_len_lt Tacit.len_lt_of_inside""".split()

# Phrases unfolded in every attempt.
DEFS = ", ".join("""SameSideOf OppositeSidesOf OppositeSides OutsideCircle CirclesMeet
LineMeetsCircle CirclesTouch TouchesInternally TouchesExternally Touches LinesMeet""".split())

HEAD = "import Elements\nopen Elements Elements.Tacit\nset_option maxErrors 1000000\n\n"


def ident(s: str) -> str:
    return re.sub(r"\W", "_", s)


def attempt(name: str, decl: str, rules: list[str]) -> str:
    plain = ", ".join("Elements." + r for r in rules)
    forward = ", ".join("→ Elements." + r for r in rules)
    return (f"set_option maxHeartbeats 30000 in\n"
            f"theorem {name} : type_of% @Elements.{decl} := by\n"
            f"  intros\n"
            f"  first\n"
            f"  | grind [{plain}, {DEFS}]\n"
            f"  | grind [{forward}, {DEFS}]\n"
            f"  | sorry\n\n")


def attempts(facts: dict) -> list[str]:
    decls = [e["name"] for e in facts["propositions"]]
    axioms = sorted(facts["axiom_modules"])
    missing = [c for c in CIRCLE if c not in facts["axiom_modules"]]
    if missing:
        sys.exit(f"screen: no such axioms in facts.json: {missing}")
    families: dict[str, list[str]] = {}
    for ax, module in facts["axiom_modules"].items():
        families.setdefault(module.split(".")[-1], []).append(ax)
    jobs = []
    for d in decls:
        for ax in axioms:
            jobs.append(attempt(f"single__{ident(d)}__{ident(ax)}", d, [ax]))
        for fam in sorted(families):
            jobs.append(attempt(f"family__{ident(d)}__{fam}", d, sorted(families[fam])))
        for a, b in itertools.combinations(CIRCLE, 2):
            jobs.append(attempt(f"pair__{ident(d)}__{ident(a)}__{ident(b)}", d, [a, b]))
        for f, g in itertools.combinations(sorted(families), 2):
            jobs.append(attempt(f"fampair__{ident(d)}__{f}__{g}", d,
                                sorted(families[f] + families[g])))
    return jobs


def successes(lean: Path, log: str) -> tuple[int, list[str]]:
    lines = lean.read_text().splitlines()
    starts = [(i + 1, m.group(1)) for i, line in enumerate(lines)
              if (m := re.match(r"theorem (\S+) :", line))]
    bad = {int(m.group(1)) for m in re.finditer(
        rf"{re.escape(lean.name)}:(\d+):\d+: (error|warning: declaration uses)", log)}
    found = []
    for k, (start, name) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines) + 1
        if not any(start <= b < end for b in bad):
            found.append(name)
    return len(starts), found


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("outdir", type=Path)
    ap.add_argument("--jobs", type=int, default=12)
    args = ap.parse_args()
    out = args.outdir.resolve()
    if out == ROOT or ROOT in out.parents:
        sys.exit("screen: OUTDIR must be outside the repository")
    out.mkdir(parents=True, exist_ok=True)
    facts = json.loads((ROOT / "facts.json").read_text())
    jobs = attempts(facts)
    files = []
    for k in range(args.jobs):
        path = out / f"Screen{k}.lean"
        path.write_text(HEAD + "".join(jobs[k::args.jobs]))
        files.append(path)
    procs = [(f, subprocess.Popen(["lake", "env", "lean", str(f)], cwd=ROOT,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True))
             for f in files]
    total, found = 0, []
    for f, p in procs:
        log, _ = p.communicate()
        (out / f"{f.stem}.log").write_text(log)
        n, ok = successes(f, log)
        total += n
        found += ok
    print(f"{total} attempts, {len(found)} closed:")
    for name in sorted(found):
        print("  " + name)
    return 0


if __name__ == "__main__":
    sys.exit(main())
