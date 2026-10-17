"""Check that the Lean follows Euclid, and that the house rules hold.

1. Fidelity. For every proposition, the docstring of `theorem PropN` must be
   Heath's enunciation, and the full-line `--` comments inside its proof, read in
   order, must be exactly Heath's proof (whitespace aside). Euclid's words go in
   `--` comments; our own remarks go in `/- … -/` blocks.
2. Every `axiom` lives in `Elements/Foundations/`: a first look in the source here,
   and the real check from Lean's own environment in 5.
3. Book Zero (`Elements/Figure/`) never imports a proposition.
4. Nothing that gets round the kernel or adds an axiom without the word: no
   `native_decide` or `decide +native` (each adds an axiom Lean's kernel doesn't
   check), no `set_option debug.…`, and no `run_cmd`, `run_elab`, `elab`, `macro`,
   `implemented_by`, `extern` or `unsafe` under `Elements/`.
5. With `facts.json` present (run `lake env lean Certificate/Facts.lean` first):
   - every axiom a proposition rests on, other than Lean's own `propext`,
     `Classical.choice` and `Quot.sound`, is declared under `Elements.Foundations`,
     and so is every axiom declared anywhere in `Elements`, as Lean itself reports;
   - there are 87 of them, and the 17 primitive words of `Words.lean` and
     `Magnitudes.lean` are still `opaque`. Changing either is a decision, recorded in
     `docs/briefs/0002-decisions.md` with the new number here;
   - only I.4 and I.8 may use superposition directly;
   - no proposition before I.29 rests on Postulate 5 or any Euclidean-only rule.
     Every proposition of a later book comes after I.29, and may rest on it;
   - every proposition of a completed book is proved, with both figures and a mishnah;
   - the certificate covers exactly the books in `heath.BOOKS` (`Certificate/Facts.lean`
     keeps its own list), and no proposition cites one that does not come before it.

Exits non-zero on any failure. Standard library only.
"""

import json
import re
import sys

import heath

ROOT = heath.ROOT
BOOKS = heath.BOOKS
# Books whose every proposition is proved: they must stay that way.
COMPLETE = {"I", "II", "III"}
SUPERPOSITION_ALLOWED = {"I.4", "I.8"}
EUCLIDEAN_ONLY = re.compile(r"^(Postulate5|Tacit\.Euclidean\..*)$")
# The first proposition of each book allowed to rest on Postulate 5. Euclid holds it
# back until I.29; Books II and III come after the whole of Book I, so they may use the
# postulate from their first proposition on, as II.10 does by name. A book missing here
# may use it throughout.
FIRST_EUCLIDEAN = {"I": 29, "II": 1, "III": 1}
# Euclid's assumptions: 5 postulates, Definition 15 and 81 tacit rules. A change is a
# decision (docs/briefs/0002-decisions.md), and this number changes with it.
AXIOM_COUNT = 87
# The words Euclid leaves undefined, and the magnitudes. Each must stay `opaque`: Lean
# then knows only what the axioms say of them, and the axioms stay true in the plane.
PRIMITIVES = {
    "Point", "Line", "Circle", "OnLine", "SameSide", "Between", "OnCircle", "InsideCircle",
    "Centre",                                                  # Words.lean
    "MagnitudeImpl", "Magnitude.zero", "Magnitude.add", "Magnitude.lt", "len", "ang", "area",
    "rightAngle",                                              # Magnitudes.lean
}
# Lean's own logical foundations, which every proof may use.
LEAN_FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}
# Commands that could get round the kernel, or bring in an axiom without the keyword.
# Matched as whole words, in the Lean with its comments taken out.
FORBIDDEN = re.compile(
    r"\bnative_decide\b|\bdecide\s*\+\s*native\b|\bset_option\s+debug\.|"
    r"\b(run_cmd|run_elab|run_meta|elab|elab_rules|macro|macro_rules|implemented_by|"
    r"extern|unsafe)\b")

errors: list[str] = []


def fail(msg: str) -> None:
    errors.append(msg)


def theorem_block(src: str, n: int):
    """Return (docstring, proof_comment_text) for `theorem PropN`."""
    m = re.search(r"/--((?:(?!-/).)*?)-/\s*theorem Prop%d\s" % n, src, re.S)
    if not m:
        return None, None
    doc = m.group(1)
    start = m.end()
    # The proof runs until the next top-level declaration or the namespace end.
    rest = src[start:]
    stop = re.search(r"^(end |theorem |lemma |def |structure |/--|/-!|@\[)", rest, re.M)
    body = rest[: stop.start()] if stop else rest
    # Drop block comments (our remarks), keep full-line `--` comments (Euclid's words).
    body = re.sub(r"/-.*?-/", "", body, flags=re.S)
    words = [m.group(1) for m in re.finditer(r"^\s*--\s?(.*)$", body, re.M)]
    return doc, " ".join(words)


def first_difference(a: str, b: str) -> str:
    i = next((k for k in range(min(len(a), len(b))) if a[k] != b[k]), min(len(a), len(b)))
    return f"…{a[max(0, i - 40):i + 40]!r}\n      expected …{b[max(0, i - 40):i + 40]!r}"


def check_fidelity() -> None:
    for book, count in BOOKS.items():
        for n in range(1, count + 1):
            path = ROOT / "Elements" / f"Book{book}" / f"Prop{n:02d}.lean"
            if not path.exists():
                fail(f"{book}.{n}: missing {path.relative_to(ROOT)}")
                continue
            doc, words = theorem_block(path.read_text(), n)
            if doc is None:
                fail(f"{book}.{n}: no documented `theorem Prop{n}` found")
                continue
            _, enunciation, proof = heath.read(book, n)
            if heath.normalize(doc) != heath.normalize(enunciation):
                fail(f"{book}.{n}: docstring is not Heath's enunciation:\n      "
                     + first_difference(heath.normalize(doc), heath.normalize(enunciation)))
            expected = heath.normalize(" ".join(proof))
            got = heath.normalize(words)
            if got != expected:
                fail(f"{book}.{n}: the `--` comments don't match Heath's proof:\n      "
                     + first_difference(got, expected))


def without_comments(src: str) -> str:
    """The Lean with its comments taken out: `/- … -/` blocks (docstrings among them,
    nested ones too) and `--` to the end of the line."""
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and src.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            out.append(" " if src[i] != "\n" else "\n")
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def check_rules() -> None:
    for path in sorted((ROOT / "Elements").rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        src = path.read_text()
        code = without_comments(src)
        if re.search(r"^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable|unsafe|partial)\s+)*axiom\s",
                     code, re.M) and not rel.startswith("Elements/Foundations/"):
            fail(f"{rel}: declares an axiom outside Elements/Foundations/")
        if "native_decide" in src:
            fail(f"{rel}: uses native_decide")
        for m in FORBIDDEN.finditer(code):
            if m.group(0) != "native_decide":
                line = code[: m.start()].count("\n") + 1
                fail(f"{rel}:{line}: uses `{' '.join(m.group(0).split())}`, which could get "
                     "round Lean's kernel or bring in an axiom unseen")
        if rel.startswith("Elements/Figure/") and re.search(r"^import Elements\.Book", src, re.M):
            fail(f"{rel}: Book Zero must not import a proposition")


def check_axioms(facts) -> None:
    """Where the axioms live, read from Lean's environment by Certificate/Facts.lean."""
    modules = facts.get("axiom_modules")
    if modules is None or "opaque" not in facts:
        fail("facts.json has no axiom_modules or opaque: rerun `lake env lean Certificate/Facts.lean`")
        return
    def foundations(module: str) -> bool:
        return module.startswith("Elements.Foundations.")
    for name, module in sorted(modules.items()):
        if module.startswith("Elements") and not foundations(module):
            fail(f"{name}: an axiom declared in {module}, outside Elements/Foundations/")
    for p in facts["propositions"]:
        for a in p["axioms"]:
            if a in LEAN_FOUNDATIONS:
                continue
            if not foundations(modules.get(a, "")):
                fail(f"{p['ref']}: rests on {a}, which is not one of Euclid's assumptions in "
                     f"Elements/Foundations/ (declared in {modules.get(a) or 'an unknown module'})")
    count = sum(1 for m in modules.values() if foundations(m))
    if count != AXIOM_COUNT:
        fail(f"Elements/Foundations/ declares {count} axioms, not {AXIOM_COUNT}: a new or "
             "removed assumption is a decision for docs/briefs/0002-decisions.md, and then "
             "AXIOM_COUNT here")
    for name in sorted(PRIMITIVES - set(facts["opaque"])):
        fail(f"{name}: no longer an opaque primitive; Lean must know only what the axioms say of it")


def check_facts() -> None:
    path = ROOT / "facts.json"
    if not path.exists():
        print("note: facts.json not found; skipping certificate checks")
        return
    facts = json.loads(path.read_text())
    check_axioms(facts)
    have = {p["ref"] for p in facts["propositions"]}
    want = {f"{book}.{n}" for book, count in BOOKS.items() for n in range(1, count + 1)}
    for ref in sorted(want - have, key=heath.prop_key):
        fail(f"{ref}: missing from facts.json (does Certificate/Facts.lean list Book {ref.split('.')[0]}?)")
    for ref in sorted(have - want, key=heath.prop_key):
        fail(f"{ref}: in facts.json but not in heath.BOOKS")
    for p in facts["propositions"]:
        ref = p["ref"]
        book, num = ref.split(".")
        # Euclid cites only what comes before: nothing after II.N, and Book I nothing of Book II.
        for c in p.get("cites", []):
            if heath.prop_key(c) >= heath.prop_key(ref):
                fail(f"{ref}: cites {c}, which does not come before it")
        if "Tacit.superposition" in p.get("direct_axioms", []) and ref not in SUPERPOSITION_ALLOWED:
            fail(f"{ref}: uses superposition directly (only I.4 and I.8 may)")
        first = FIRST_EUCLIDEAN.get(book, 1)
        if int(num) < first:
            bad = [a for a in p["axioms"] if EUCLIDEAN_ONLY.match(a)]
            if bad:
                fail(f"{ref}: rests on {', '.join(bad)} before {book}.{first}")
    by_ref = {p["ref"]: p for p in facts["propositions"]}
    for book in COMPLETE:
        for n in range(1, BOOKS[book] + 1):
            ref = f"{book}.{n}"
            if by_ref.get(ref, {}).get("status") != "proved":
                fail(f"{ref}: Book {book} is complete, but {ref} is not proved")
            for f in (f"figures/{book}/{n:02d}.svg", f"figures/{book}/{n:02d}-idea.svg",
                      f"mishnah/{book}/{n:02d}.md"):
                if not (ROOT / f).exists():
                    fail(f"{ref}: {f} is missing")


def main() -> int:
    check_fidelity()
    check_rules()
    check_facts()
    if errors:
        print(f"{len(errors)} problem(s):")
        for e in errors:
            print("  ✗ " + e)
        return 1
    total = sum(BOOKS.values())
    print(f"✓ fidelity: all {total} propositions quote Heath exactly; house rules hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
