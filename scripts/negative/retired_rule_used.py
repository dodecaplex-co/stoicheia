"""One build with a retired rule used in III.2's proof (#168): `Tacit.centre_unique`, one of
the eight tacit rules that the retirement of #119 made theorems, which the pins on the
`proved_rules` of III.1, III.1 Por., III.2 and II.14 keep from beneath them. Every axiom
beneath it is already beneath III.2, and it cites no entry, so III.2's `axioms` and `cites`
stay exactly as they were and no pin on them can see the use; the plant fails if either
changes. The certificate recomputed, `check_fidelity.py` must refuse it by the pin on
III.2's `proved_rules`, naming that expectation, and by no pin on III.2's `axioms`. The
source and `facts.json` are put back byte for byte, and a restoration build attempted,
with the build files as fallback.
"""

import json

import negative_tests as nt

BUILDS = True

RULE = "Tacit.centre_unique"
SOURCE = "Elements/BookIII/Prop02.lean"
# The line that opens III.2's proof, and the use planted after it.
HEAD = "    ∀ E : Point, Between A E B → InsideCircle E ABC := by\n"
USE = f"  have _retired := @Elements.{RULE}\n"


def plant() -> None:
    """`Tacit.centre_unique` used in III.2's proof, adding no axiom and no citation: of the
    pins, only the one on III.2's `proved_rules` can refuse it."""
    name = f"{RULE} in III.2's proof, its axioms unchanged"
    pins = json.loads((nt.ROOT / "tests/certificate_expectations.json").read_text())
    numbers = [i for i, x in enumerate(pins["expectations"], 1)
               if x.get("ref") == "III.2" and x.get("field") == "proved_rules"
               and RULE in x.get("excludes", [])]
    if len(numbers) != 1:
        nt.failures.append(f"{name}: expected one pin keeping {RULE} from III.2's "
                           f"proved_rules, found {len(numbers)}; update this test")
        return
    pin = (f"III.2: its proved_rules should not include {RULE} "
           f"(tests/certificate_expectations.json, expectation {numbers[0]}:")
    saved = {rel: (nt.ROOT / rel).read_bytes() for rel in (SOURCE, "facts.json")}
    text = saved[SOURCE].decode()
    assert text.count(HEAD) == 1, f"{SOURCE}: expected one {HEAD!r}; update this test"
    before = nt.entry(json.loads(saved["facts.json"]), "III.2")
    outputs = nt.BuildOutputs()
    try:
        (nt.ROOT / SOURCE).write_text(text.replace(HEAD, HEAD + USE))
        if not nt.expect_success("III.2 built with a retired rule in its proof",
                                 nt.run("lake", "build")):
            return
        if not nt.expect_success("the certificate with a retired rule in III.2",
                                 nt.run("lake", "env", "lean", "Certificate/Facts.lean")):
            return
        after = nt.entry(json.loads((nt.ROOT / "facts.json").read_text()), "III.2")
        for field in ("axioms", "cites"):
            if after[field] != before[field]:
                nt.failures.append(f"{name}: {RULE} changed III.2's {field}, so the plant no "
                                   "longer shows what only proved_rules can; update this test")
        nt.expect_failure(name, nt.fidelity(), pin, unwanted=("III.2: its axioms ",))
    finally:
        for rel, data in saved.items():
            (nt.ROOT / rel).write_bytes(data)
        nt.rebuild_restored("the restored III.2 builds", outputs)
