"""Check that the Lean follows Euclid, and that the house rules hold.

1. Fidelity. For every proposition, the docstring of `theorem PropN` must be
   Heath's enunciation, and the full-line `--` comments inside its proof, read in
   order, must be exactly Heath's proof (whitespace aside). Euclid's words go in
   `--` comments; our own remarks go in `/- … -/` blocks.
2. Every `axiom` lives in `Elements/Foundations/`.
3. Book Zero (`Elements/Figure/`) never imports a proposition.
4. No `native_decide` (it would add an axiom Lean's kernel doesn't check).
5. With `facts.json` present (run `lake env lean Certificate/Facts.lean` first):
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
COMPLETE = {"I"}
SUPERPOSITION_ALLOWED = {"I.4", "I.8"}
EUCLIDEAN_ONLY = re.compile(r"^(Postulate5|Tacit\.Euclidean\..*)$")
# The first proposition of each book allowed to rest on Postulate 5. Euclid holds it
# back until I.29; Book II comes after the whole of Book I, so it may use the
# postulate from II.1 on, as II.10 does by name. A book missing here may use it
# throughout.
FIRST_EUCLIDEAN = {"I": 29, "II": 1}

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


def check_rules() -> None:
    for path in sorted((ROOT / "Elements").rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        src = path.read_text()
        if re.search(r"^\s*(private\s+|protected\s+)?axiom\s", src, re.M) and \
                not rel.startswith("Elements/Foundations/"):
            fail(f"{rel}: declares an axiom outside Elements/Foundations/")
        if "native_decide" in src:
            fail(f"{rel}: uses native_decide")
        if rel.startswith("Elements/Figure/") and re.search(r"^import Elements\.Book", src, re.M):
            fail(f"{rel}: Book Zero must not import a proposition")


def check_facts() -> None:
    path = ROOT / "facts.json"
    if not path.exists():
        print("note: facts.json not found; skipping certificate checks")
        return
    facts = json.loads(path.read_text())
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
