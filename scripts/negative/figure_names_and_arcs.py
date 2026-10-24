"""Without a build, names and arcs in real figures (#172), each refused by
`check_style.py --no-lean`: `*e*.*g*.` in II.7's modern way, with an italic e planted in
its figure, fails S25 for the emphasis and for e, no name of the modern way; an italic p
planted there fails S25 too, though Heath's "p. 389" stands in the paragraph; and an arc
whose ends are one point and one with a radius of 0, planted in I.1's figure, fail S26 with
what SVG draws for each.
"""

import sys

import negative_tests as nt

BUILDS = False


def plant() -> None:
    label = ('<text font-family="Georgia, serif" font-size="17" x="30" y="30" '
             'font-style="italic" fill="#3b2f2f">{}</text></svg>')
    modern = "figures/II/07-modern.svg"
    arcs = ('<path d="M 20 20 A 5 5 0 0 1 20 20" fill="none" stroke="#3b2f2f" '
            'stroke-width="1.6"/><path d="M 30 20 A 0 5 0 0 1 40 20" fill="none" '
            'stroke="#3b2f2f" stroke-width="1.6"/></svg>')
    plants = (
        ("*e*.*g*. in II.7's modern way, and e in its figure",
         (("mishnah/II/07.md", "beside II.4's square on a sum.",
           "beside II.4's square on a sum, *e*.*g*. a planted one."),
          (modern, "</svg>", label.format("e"))),
         (f"S25 {modern}: mishnah/II/07.md: unsupported intraword emphasis",
          f"S25 {modern}: <text>e</text>: e is no name of the page's modern way")),
        ("p in II.7's modern figure, beside Heath's page, p. 389",
         ((modern, "</svg>", label.format("p")),),
         (f"S25 {modern}: <text>p</text>: p is no name of the page's modern way",)),
        ("an arc whose ends are one point, and one of radius 0, in I.1's figure",
         (("figures/I/01.svg", "</svg>", arcs),),
         ("S26 figures/I/01.svg: <path> d 'M 20 20 A 5 5 0 0 1 20 20': SVG draws nothing",
          "S26 figures/I/01.svg: <path> d 'M 30 20 A 0 5 0 0 1 40 20': SVG draws a "
          "straight line")),
    )
    for name, changes, wanted in plants:
        saved = {}
        try:
            for rel, old, new in changes:
                saved[rel] = nt.replace_once(rel, old, new)
            nt.expect_failure(name, nt.run(sys.executable, "scripts/check_style.py", "--no-lean"),
                              *wanted)
        finally:
            for rel, text in saved.items():
                (nt.ROOT / rel).write_text(text)
