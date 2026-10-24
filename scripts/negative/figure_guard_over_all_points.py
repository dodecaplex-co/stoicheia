"""A guard added to `Rule.Figure` in the restriction, in two runs that differ in the guard
alone. In both, the proof of `Rule.Figure.restrict` (the rule's part about the figure passes
to a part of an interpretation) takes the new guard and passes it from the part to the whole
through the embedding, and `Rule.iff_figure`, which any new hypothesis breaks, is left out.
The control, a guard over the figure's own points and straight line, compiles, and the
theorem rests on no `sorryAx`. The plant, a guard over every point (the straight line
through D and G holds no other point), fails inside the theorem's proof and nowhere else.
Read, not built. Its constants and helpers, the guards and plant_figure_guard among them,
are in scripts/negative_tests.py, where tests/test_negative_tests.py reads them.
"""

import re

import negative_tests as nt

BUILDS = False


def plant() -> None:
    """A guard of `Rule.Figure` that ranges over every point, against a control (#150,
    question 2). Both runs add a guard to `Rule.Figure` after the others, and change the
    proof of `Rule.Figure.restrict` alike: it introduces the guard as `hX` and passes it
    from J to I through the embedding, by `simpa` with the embedding's laws. Both leave out
    `Rule.iff_figure`, which any new hypothesis breaks, since `Rule.Figure` is then no
    longer the statement of the locked rule; nothing else in the file uses it. So the runs
    differ in the guard alone.

    The control, a guard over the figure's own points and straight line (if D is between
    A and G, then B and H are on one side of the straight line through D and G), must
    compile: no error anywhere, and `sorryAx` not among `Rule.Figure.restrict`'s printed
    axioms. The plant, a guard that the straight line through D and G holds no other point
    of the interpretation, must fail, every error inside `Rule.Figure.restrict`'s own
    lines, and the theorem then rests on `sorryAx`. So the proof passes a guard over the
    figure from a part of an interpretation to the whole, and refuses, in the same proof,
    one over every point. It does not show that no other proof could pass the second.
    Read, not built: the file is compiled against the built modules it imports, and no
    build output changes."""
    path = nt.ROOT / nt.RESTRICTION
    saved = path.read_bytes()
    name = "a guard over every point added to Rule.Figure"
    axioms_line = re.compile(
        rf"'{re.escape(nt.RESTRICT_NAME)}' depends on axioms: \[([^\]]*)\]")
    try:
        caught = None
        for guard in (nt.OVER_THE_FIGURE, nt.OVER_ALL_POINTS):
            control = guard == nt.OVER_THE_FIGURE
            text = nt.plant_figure_guard(saved.decode(), guard)
            restrict = nt.declaration_lines(text, nt.RESTRICT)
            path.write_text(text)
            result = nt.run("lake", "env", "lean", nt.RESTRICTION)
            out = result.stdout + result.stderr
            errors = [int(n) for n in
                      re.findall(rf"{re.escape(nt.RESTRICTION)}:(\d+):\d+: error", out)]
            within = [n for n in errors if n in restrict]
            printed = axioms_line.search(out)
            sorry = printed is not None and "sorryAx" in printed.group(1)
            where = (f"errors at lines {errors or 'none'}; the theorem is at "
                     f"{nt.RESTRICTION}:{restrict.start}-{restrict.stop - 1}")
            if control:
                if result.returncode != 0 or errors or printed is None or sorry:
                    nt.failures.append(
                        f"{name}: the control, a guard over the figure alone, does not "
                        f"compile through Rule.Figure.restrict (exit {result.returncode}, "
                        f"{where}; its axioms "
                        f"{'not printed' if printed is None else printed.group(1)}), so "
                        "the plant could not tell the guards apart")
                    print(out[-3000:])
                    return
            elif (result.returncode == 0 or not within or len(within) < len(errors)
                  or not sorry):
                nt.failures.append(
                    f"{name}: not caught by Rule.Figure.restrict alone ({where})")
                print(out[-3000:])
                return
            else:
                caught = within[0]
        nt.refused(f"{name}: caught by Rule.Figure.restrict at {nt.RESTRICTION}:{caught}, "
                   "while a guard over the figure alone compiles through it")
    finally:
        path.write_bytes(saved)
