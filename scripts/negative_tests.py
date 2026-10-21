"""Break the project on purpose, and check that it notices.

Each test makes one small change that must be caught, runs the check that should
catch it, and puts everything back. Run from the repo root after `lake build` and
`lake env lean Certificate/Facts.lean`, with `Certificate/axioms.lock` and the review
records current; CI runs it on every push.

1. An edited Heath word: `check_fidelity.py` fails on I.1.
2. The README's "Try breaking it": I.1 takes its radii from the wrong circle, and
   Lean refuses the proof.
3. Without a build, on a copy of `facts.json`: Postulate 1 weakened in the printed
   statements no longer matches the axiom lock; `Touches`, a word only Book III's
   statements use, given another meaning no longer matches it either; a changed
   statement of III.1's porism makes III.1's review record stale; `Centre`, no
   longer among the opaque primitives (as if it had been made a `def`), is caught;
   the name of Circle 2, now a theorem, is deliberately added to III.3's axioms, and
   Circle 3 to I.15's porism or II.1's general companion; all three are refused by the
   entry's name. Circle 3 renamed in the axiom lock (restored after) and in the copy
   alike is caught as missing from the lock; Circle 2 proved without a forbidden axiom
   beneath it is refused by name, while Circle 2 proved from Circle 3 still in the lock
   passes; and placement among III.26's shared steps is caught, while III.24, given it
   too, is not blamed.
4. A changed Lean file makes its review record stale (I.1).
5. III.16's review record without the passage that declares its angle clauses, of
   whatever kind, leaves a run of `--` lines with no Lean beneath it undeclared.
6. A remark planted in I.5 between two sentences that share one step of Lean leaves the
   first with no Lean of its own: a remark ends a run and carries nothing. A second
   remark, between the next sentence and its Lean, does not stop that Lean carrying it.
7. A `native_decide` in a proposition's file (I.16), read from the source, is caught.
8. Every command docs/FORMALIZATION.md, section 7, forbids, an attribute for each ending
   and prefix by which the scan knows one, and an axiom declared twice, once after
   another command on the same line, planted in a new file of each folder the
   scan reads, `Elements/`, `Staging/` (in a folder of its own), `Audit/`, `model/Model/`
   and `model/Check/`, with
   `#exit` at the end of each root file, `Elements.lean`, `Staging.lean` and
   `Audit.lean`, `model/Model.lean` and `model/Check.lean`, and a new Book Zero file that
   imports a proposition: each is caught on
   its own line. Some of the commands stand after a string, a raw string or a character
   literal holding `/-`, `-/`, `]` or `"`, and one in an interpolated string's hole, so
   the scan must read Lean's literals as Lean does; a string whose braces Lean could
   read as code is caught too. Generator calls, plain and parenthesised, are caught
   outside the model's Check files; there they are allowed only first on their line,
   with other commands still caught on that line and in their arguments. The files are
   read, not built; no tree is copied, so model/.lake is never copied either.
   Symbolic links to a directory in model/Model/ and a file in model/Check/ are refused
   by their own paths, without following them. An axiom in a `.lake` folder of
   model/Model/ and of model/Check/ is caught, and one in model/.lake is not read. A
   link named `.lake`, to a directory, a file or nothing, is refused in model/,
   model/Model/ and model/Check/, each in a small tree of its own.
9. A lemma of the `Placement` namespace named in Book III's shared steps
   (`Squares.lean`), outside placement's own files, III.24's and `Arcs.lean`, read from
   the source, is caught; the word in a comment there is not.
10. One build with planted assumptions, the certificate recomputed:
   - in I.16, Postulate 5, a planted Euclidean-only rule (`Tacit.Euclidean.planted`)
     and an axiom declared in I.16's own file after a docstring on the same line:
     each is caught, so are the count of Euclid's assumptions and the two planted
     axioms missing from `Certificate/axioms.lock`;
   - in I.15's porism, which I.15 does not use: Postulate 5, superposition and the
     later I.22, each caught as the porism's, "I.15 Por.: …", and I.15 not blamed;
   - a helper of I.16 that mentions I.22 only in its statement: the certificate's
     walk reads types as well as proofs, so I.16 is caught citing a later proposition;
   - a `sorry` in I.16's proof: Book I is complete, so I.16 not proved is caught.
11. An em dash in I.1's mishnah: `check_style.py` fails with S1 and the file's name.
12. A relative link to a missing file in README.md: `check_links.py` names the link
    and its source file.
13. I.1's generated page left stale beside a changed mishnah: after `render.py`, the
    section 8 `git status --porcelain` command names the changed page. Editing just
    the page would be repaired back to HEAD and leave that status clean.
14. An axiom dropped from an audit lemma's expected list: `lake build Audit` fails
    with the file's name and a `#guard_msgs` mismatch; the restored audit must build.
15. A corrupt header in I.1's compiled `.olean`, for leanchecker's loading of compiled
    files: leanchecker, invoked as in `check_kernel.py`, fails naming the file and its
    invalid header. The original bytes are restored, a rebuild is required, and on
    success the whole environment is replayed.
16. Without a build, in a temporary copy of the tracked files without Git: opening,
    base and closing merge markers, a middle between outer markers, and a lone middle
    in a non-Markdown file, comment, fence or after a completed heading, indented code
    or link reference definition (on one line or two) each fail S23 with their
    file, line and kind.
    Setext headings, including several lines and one after a comment containing a
    fence, leave the unplanted copy's result unchanged. Symlinks are not copied.
    This runs before the plants that build, and preserves any existing findings.
17. Without a build, in a disposable source copy: a stale inline vocabulary count
    and an unknown count name are refused by check_fidelity.py, and a correct count
    passes. Missing or mismatched Git work trees and a Markdown symlink are refused
    with diagnostics. Run just these plants and the file-only regressions with --counts-only.
18. Counting congruence constructors instead of `Coincidence.step` in the certificate:
    `tests/test_certificate.py` fails on transformers with no step. The restored
    certificate must pass the same regression, including its real-step cases.
19. Without a build, names and arcs in real figures (#172): `*e*.*g*.` in II.7's modern
    way, with an italic e planted in its figure, fails S25 for the emphasis and for e,
    no name of the modern way; an italic p planted there fails S25 too, though Heath's
    "p. 389" stands in the paragraph; and an arc whose ends are one point and one with a
    radius of 0, planted in I.1's figure, fail S26 with what SVG draws for each.
20. I.1's figure, idea figure and mishnah, each removed in turn: Book I is complete, so
    `check_fidelity.py` fails naming the missing file, and not the other two. Each is
    restored byte for byte.
21. An ill-typed proof in I.1's compiled module, for leanchecker's kernel replay:
    `True.intro` as a proof of `False`, added past the kernel by
    `set_option debug.skipKernelTC true` and a `run_cmd` that calls `addDecl`, the way
    docs/reports/read-through-01.md names. The source scan refuses both, so I.1 is
    compiled with them by `lake env lean -o`, over its own `.olean`, from a copy outside
    the tree. leanchecker, invoked as in `check_kernel.py`, rejects the proof, naming the
    declaration and the kernel's type mismatch, not a file it cannot read. The build is
    restored as in item 15, and on success the whole environment is replayed.
22. Without a build, the six probes an independent reviewer planted for #207, each a
    forbidden command or an axiom hidden behind a carriage-return comment
    (`-- a remark\\r"`), in one scratch copy of I.1's file in a temporary tree, read by the
    source scan alone (`rules_in`): Lean ends a `--` comment only at a line feed, so a
    scan that read the file with Python's universal newlines would end the comment at the
    `\\r` and let a string open behind it that hides the command up to a later `"`. Read as
    Lean reads the bytes, the lone `\\r` of each is refused by its file and line, and the
    `set_option debug.…` pair and the `axiom`, no longer hidden, are named too; the other
    three (`#guard_msgs (drop all)`, a pinned error and `#guard_panic`) are named by
    command once #197's rules land, and here the lone `\\r` refuses all six. The unplanted
    copy passes, and so does a copy of it with CRLF line endings, which Lean allows; the
    check before #207, reading with universal newlines, missed all six.

The copies of items 16 and 17, and item 13's list of generated outputs, read Git's
tracked files. One absent from the work tree is named on stdout and passed over: as a
note under the check inputs, since the pre-flight's pass with origin/main's checks takes
out the files a commit adds there while Git's index still lists them (scripts/safe_push.py,
step 4); as a failure anywhere else. The rule is generated_counts.absent_tracked's, which
check_fidelity.py and render.py follow for the tracked Markdown they read.

These faults exercise the style and link checks, page freshness, an audit pin, a
complete book's figures and mishnah, and leanchecker's loading of compiled files and its
kernel replay, as well as the earlier checks. `check_kernel.py`'s own `--self-test`
withholds Postulate 5 from nanoda alone.

Every new plant restores its inputs in `finally`; the freshness plant also restores
all renderer outputs.
Tests 10, 14, 15 and 21 attempt a restoration build; if it fails or is interrupted, every
file in `.lake/build` returns to its saved contents and presence or absence before
the plant, including dependent modules, hashes and traces. Test 10 always restores or
removes `Planted.*` outputs in a nested `finally`. Tests 11 to 15, the proved Circle 2
plant and tests 18 and 21 report elapsed time, restoration included. An outer
`finally` compares Git status with the entry status, including on interruption, without
replacing an exception already in flight.
Temporary-directory regressions run first, without Lean. Exits non-zero if a fault
goes unnoticed or a restoration check fails. Restoration needs writable files and
an opportunity for `finally` to finish; a forced process kill cannot provide it.
Standard library only; Python 3.11 or later, for the review records.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path
from time import perf_counter

import check_fidelity
import check_kernel
import generated_counts
import heath

ROOT = heath.ROOT
PLANTED = ROOT / "Elements" / "Foundations" / "Tacit" / "Planted.lean"
failures: list[str] = []
GENERATED = ("facts.json", "book", "CERTIFICATE.md", "GRAPH.md", "README.md",
             "docs/PROGRAM.md")


def run(*cmd: str) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def tracked_names() -> tuple[subprocess.CompletedProcess, list[str]]:
    """List tracked names without text mode changing control characters in them."""
    result = subprocess.run(("git", "ls-files", "-z"), cwd=ROOT, capture_output=True)
    names = [name.decode() for name in result.stdout.split(b"\0") if name]
    return result, names


def fidelity(*args: str) -> subprocess.CompletedProcess:
    return run(sys.executable, "scripts/check_fidelity.py", *args)


def replace_once(rel: str, old: str, new: str) -> str:
    """Change `old` to `new` in the file, and return the text to put back."""
    path = ROOT / rel
    text = path.read_text()
    assert text.count(old) == 1, f"{rel}: expected one {old!r}"
    path.write_text(text.replace(old, new))
    return text


def expect_failure(name: str, result: subprocess.CompletedProcess, *wanted: str,
                   unwanted: tuple = ()) -> None:
    """The check must fail, saying each of `wanted` and none of `unwanted`."""
    out = result.stdout + result.stderr
    missing = [w for w in wanted if w not in out]
    present = [u for u in unwanted if u in out]
    if result.returncode == 0 or missing or present:
        detail = []
        if missing:
            detail.append(f"missing {', '.join(repr(m) for m in missing)}")
        if present:
            detail.append(f"wrongly says {', '.join(repr(p) for p in present)}")
        failures.append(f"{name}: not caught" + (f" ({'; '.join(detail)})" if detail else ""))
        print(out[-3000:])
    else:
        print(f"✓ {name}: caught")


def expect_success(name: str, result: subprocess.CompletedProcess) -> bool:
    if result.returncode != 0:
        message = f"{name}: exit {result.returncode}"
        failures.append(message)
        print(f"✗ {message}")
        output = (result.stdout + result.stderr)[-3000:]
        if output:
            print(output, end="" if output.endswith("\n") else "\n")
        return False
    return True


class BuildOutputs:
    """Save build files without a suffix list, including outputs of dependents.

    A pattern can select just a temporary module for cleanup after a successful
    build too. Rescanning on restore removes files absent when the snapshot was made.
    """

    def __init__(self, pattern: str = "**/*"):
        self.root = ROOT / ".lake/build"
        self.pattern = pattern
        self.saved = {p: p.read_bytes() for p in self.files()}

    def files(self) -> set[Path]:
        return {p for p in self.root.glob(self.pattern) if p.is_file()}

    def restore(self) -> None:
        for path in self.files() - self.saved.keys():
            path.unlink()
        for path, data in self.saved.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)


def rebuild_restored(name: str, outputs: BuildOutputs, *targets: str,
                     force: Path | None = None) -> bool:
    """Keep the restoration build, with saved files as fallback on failure or interrupt."""
    rebuilt = False
    try:
        if force is not None:
            # Lake removes companion outputs too when rebuilding this module.
            force.unlink()
        rebuilt = expect_success(name, run("lake", "build", *targets))
        return rebuilt
    finally:
        if not rebuilt:
            outputs.restore()


def style_error() -> None:
    rel = "mishnah/I/01.md"
    path = ROOT / rel
    saved = path.read_bytes()
    try:
        path.write_bytes(saved + ("\nA planted punctuation fault " + chr(0x2014)
                                  + " here.\n").encode())
        expect_failure("an em dash in I.1's mishnah",
                       run(sys.executable, "scripts/check_style.py"),
                       f"S1 {rel}:", "S1 an em dash")
    finally:
        path.write_bytes(saved)


def figure_names_and_arcs() -> None:
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
                saved[rel] = replace_once(rel, old, new)
            expect_failure(name, run(sys.executable, "scripts/check_style.py", "--no-lean"),
                           *wanted)
        finally:
            for rel, text in saved.items():
                (ROOT / rel).write_text(text)


def absent_tracked(rels: list[str | Path]) -> list[str | Path]:
    """The tracked paths of `rels` absent from the work tree, each named on stdout.

    The rule is generated_counts.absent_tracked's, which the count checks follow too: one
    under the check inputs is noted, and the caller goes on with what is present, since the
    pre-flight's pass with origin/main's checks (scripts/safe_push.py, step 4) takes out
    the files a commit adds there while Git's index still lists them. One absent outside
    the check inputs is a failure too, so none goes unseen. Any other error from the work
    tree, as for a path in a directory of mode 000, is raised.
    """
    missing, faults = generated_counts.absent_tracked(ROOT, rels)
    for message in faults:
        if message not in failures:
            failures.append(message)
        print(f"✗ {message}")
    return missing


def copy_marker_files(root: Path, names: list[str]) -> None:
    """Copy the tracked files for item 16, skipping symlinks without reading targets,
    and naming those absent from the work tree (absent_tracked)."""
    absent_tracked([name for name in names if name])
    for name in names:
        source = ROOT / name
        if name and not source.is_symlink() and source.is_file():
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)


def merge_conflict_markers() -> None:
    """Plant raw marker lines in copies of tracked text, with no Git or Lean needed
    by the check. Compare the harmless heading with the baseline, so an existing
    marker elsewhere cannot masquerade as a refusal of the planted heading.
    """
    listing, names = tracked_names()
    if listing.returncode != 0:
        decoded = subprocess.CompletedProcess(
            listing.args, listing.returncode,
            listing.stdout.decode(errors="replace"), listing.stderr.decode(errors="replace"))
        expect_success("tracked files for marker plants", decoded)
        return
    with tempfile.TemporaryDirectory(prefix="stoicheia-markers-") as tmp:
        root = Path(tmp)
        copy_marker_files(root, names)

        def check() -> subprocess.CompletedProcess:
            return subprocess.run([sys.executable, "scripts/check_style.py", "--no-lean"],
                                  cwd=root, capture_output=True, text=True)

        baseline = check()
        markdown = "CONTRIBUTING.md"
        non_markdown = "NOTICE"
        cases = [
            ("opening", markdown, ["<" * 7 + " ours"], [(0, "opening")]),
            ("base", markdown, ["|" * 7 + " base"], [(0, "base")]),
            ("middle between markers", markdown,
             ["<" * 7 + " ours", "A paragraph.", "=" * 7, ">" * 7 + " theirs"],
             [(0, "opening"), (2, "middle"), (3, "closing")]),
            ("lone middle", non_markdown, ["=" * 7], [(0, "middle")]),
            ("closing", markdown, [">" * 7 + " theirs"], [(0, "closing")]),
            ("middle in a comment", markdown,
             ["<!--", "Comment text", "=" * 7, "-->"], [(2, "middle")]),
            ("middle after a completed heading", markdown,
             ["Heading", "=" * 3, "=" * 7], [(2, "middle")]),
            ("middle after a hyphen heading", markdown,
             ["Heading", "-" * 3, "=" * 7], [(2, "middle")]),
            ("middle after indented code", markdown,
             ["", "    code", "=" * 7], [(2, "middle")]),
            ("middle after a reference definition", markdown,
             ["", "[label]: destination", "=" * 7], [(2, "middle")]),
            ("middle after a two-line reference definition", markdown,
             ["", "[label]:", " /url", "=" * 7], [(3, "middle")]),
            ("middle in a fence", markdown,
             ["```", "Code text", "=" * 7, "```"], [(2, "middle")]),
            ("middle after a fence inside a comment", markdown,
             ["<!--", "```", "Comment text", "=" * 7, "-->"], [(3, "middle")]),
        ]
        for name, rel, lines, expected in cases:
            path = root / rel
            saved = path.read_bytes()
            prefix = saved + b"\n"
            first = prefix.count(b"\n") + 1
            try:
                path.write_bytes(prefix + ("\n".join(lines) + "\n").encode())
                wanted = [f"S23 {rel}:{first + offset}: {kind} merge-conflict marker"
                          for offset, kind in expected]
                expect_failure(f"{name} merge marker", check(), *wanted)
            finally:
                path.write_bytes(saved)
        path = root / markdown
        saved = path.read_bytes()
        for heading in ("A planted setext heading", "A planted heading\ncontinued",
                        "<!--\n```\n-->\nA planted heading",
                        "A planted heading\n    continued"):
            try:
                path.write_bytes(saved + ("\n" + heading + "\n" + "=" * 7 + "\n").encode())
                result = check()
                if (result.returncode, result.stdout, result.stderr) != (
                        baseline.returncode, baseline.stdout, baseline.stderr):
                    failures.append(f"a setext heading changed the style check's result: {heading!r}")
                    print(result.stdout + result.stderr)
                else:
                    print(f"✓ a seven-equals setext heading ({heading!r}): no new refusal")
            finally:
                path.write_bytes(saved)


def broken_link() -> None:
    path = ROOT / "README.md"
    target = "book/I/planted-missing-page.md"
    assert not (ROOT / target).exists(), f"{target} exists; update this test"
    saved = path.read_bytes()
    line = saved.count(b"\n") + 2
    try:
        path.write_bytes(saved + f"\n[Planted missing page]({target})\n".encode())
        expect_failure("a relative link to a missing page",
                       run(sys.executable, "scripts/check_links.py"),
                       f"README.md:{line}: {target}: no such file: {target}")
    finally:
        path.write_bytes(saved)


def generated_files() -> set[Path]:
    paths = set()
    for rel in GENERATED:
        path = ROOT / rel
        if path.is_dir():
            paths.update(p for p in path.rglob("*") if p.is_file())
        elif path.exists():
            paths.add(path)
    tracked = generated_counts.tracked_markdown(ROOT)
    missing = set(absent_tracked(tracked))
    for rel in tracked:
        path = ROOT / rel
        if (rel not in missing and not generated_counts.whole_output(rel)
                and not generated_counts.historical(rel)
                and generated_counts.START.search(path.read_text())):
            paths.add(path)
    return paths


def stale_page() -> None:
    """A stale page after a source change, tested by the actual freshness command.

    Rendering a hand edit alone restores HEAD, so it cannot test the post-render
    Git status. Change the source too, then require both its rendered text and the
    page's own status line. Save every output, including pre-existing local edits.
    """
    source = ROOT / "mishnah/I/01.md"
    page = ROOT / "book/I/01.md"
    saved_source = source.read_bytes()
    saved = {p: p.read_bytes() for p in generated_files()}
    command = ("git", "status", "--porcelain", "--", *GENERATED)
    before = run(*command)
    if not expect_success("freshness entry status", before):
        return
    page_status = run("git", "status", "--porcelain", "--", "book/I/01.md")
    if not expect_success("I.1 page entry status", page_status):
        return
    if page_status.stdout:
        failures.append("freshness: book/I/01.md must be clean before the plant")
        return
    current = b"A source sentence planted for the freshness check."
    obsolete = b"An obsolete sentence planted in the generated page."
    assert current not in saved_source and obsolete not in saved[page]
    try:
        source.write_bytes(saved_source + b"\n" + current + b"\n")
        page.write_bytes(saved[page] + b"\n" + obsolete + b"\n")
        if not expect_success("rendering the stale page",
                              run(sys.executable, "scripts/render.py")):
            return
        status = run(*command)
        if not expect_success("freshness status", status):
            return
        rendered = page.read_bytes()
        if (current not in rendered or obsolete in rendered
                or status.stdout.splitlines() != sorted(
                    [*before.stdout.splitlines(), " M book/I/01.md"], key=lambda s: s[3:])):
            failures.append("freshness: expected the rendered source and ' M book/I/01.md'")
            print(status.stdout)
        else:
            print("✓ a stale generated page: caught by git status:  M book/I/01.md")
    finally:
        source.write_bytes(saved_source)
        for path in generated_files() - saved.keys():
            path.unlink()
        for path, data in saved.items():
            path.write_bytes(data)
        after = run(*command)
        if expect_success("restored freshness status", after):
            if after.stdout != before.stdout:
                failures.append("freshness: generated paths did not return to their entry status")
            else:
                print("✓ freshness: generated paths restored to their entry status")


def changed_audit_pin() -> None:
    rel = "Audit/Overlaps.lean"
    path = ROOT / rel
    saved = path.read_bytes()
    pins = list(re.finditer(rb"'Audit\.III_2' depends on axioms: \[([^\]]*)\]", saved))
    assert len(pins) == 1, "expected exactly one Audit.III_2 axiom pin"
    pin = pins[0]
    axioms = [a.strip() for a in pin[1].split(b",") if a.strip()]
    dropped = next((a for a in axioms if a.startswith(b"Elements.")), None)
    assert dropped is not None, "Audit.III_2's pin has no project axiom to drop"
    remaining = axioms.copy()
    remaining.remove(dropped)
    changed = saved[:pin.start(1)] + b", ".join(remaining) + saved[pin.end(1):]
    outputs = BuildOutputs()
    try:
        path.write_bytes(changed)
        expect_failure("an axiom dropped from Audit.III_2's pin", run("lake", "build", "Audit"),
                       f"{rel}:", "Docstring on `#guard_msgs` does not match generated message",
                       "Audit.III_2", dropped.decode())
    finally:
        path.write_bytes(saved)
        rebuild_restored("the restored audit build", outputs, "Audit")


def corrupt_olean() -> None:
    """Exercise leanchecker's loader, without pretending to plant an invalid proof."""
    bin_ = check_kernel.toolchain_bin()
    command = ("lake", "env", str(bin_ / "leanchecker"), "--fresh", "Elements")
    path = ROOT / ".lake/build/lib/lean/Elements/BookI/Prop01.olean"
    saved = path.read_bytes()
    assert saved.startswith(b"olean"), "I.1's compiled header has changed; update this test"
    outputs = BuildOutputs()
    try:
        path.write_bytes(b"broken" + saved[6:])
        expect_failure("a corrupt compiled header read by leanchecker", run(*command),
                       "failed to read file", "Elements/BookI/Prop01.olean", "invalid header")
    finally:
        path.write_bytes(saved)
        if rebuild_restored("the restored Elements build", outputs, force=path):
            expect_success("leanchecker's replay after restoration", run(*command))


# `True.intro` given as a proof of `False`, added past the kernel as the read-through found
# possible (docs/reports/read-through-01.md). The source scan refuses both commands, so they
# are compiled from a copy of I.1 it never reads. `Lean.Elab.Command` defines the monad
# `run_cmd` runs in, so it is the least of Lean's library the plant can import, and it
# brings `addDecl` with it.
ILL_TYPED = "Elements.BookI.planted_ill_typed"
ILL_TYPED_LEAN = ("\nopen Lean in\nset_option debug.skipKernelTC true in\n"
                  "run_cmd Elab.Command.liftCoreM <| addDecl <| .thmDecl {\n"
                  f"  name := `{ILL_TYPED}, levelParams := [],\n"
                  "  type := mkConst ``False, value := mkConst ``True.intro }\n")


def ill_typed_proof() -> None:
    """Exercise leanchecker's kernel replay with an ill-typed proof in I.1's compiled module,
    rejected by name, not as a file it cannot read; the build is restored as in item 15."""
    bin_ = check_kernel.toolchain_bin()
    command = ("lake", "env", str(bin_ / "leanchecker"), "--fresh", "Elements")
    rel = "Elements/BookI/Prop01.lean"
    path = ROOT / ".lake/build/lib/lean/Elements/BookI/Prop01.olean"
    saved = path.read_bytes()
    outputs = BuildOutputs()
    try:
        with tempfile.TemporaryDirectory(prefix="stoicheia-kernel-") as tmp:
            root = Path(tmp).resolve()
            source = root / rel
            source.parent.mkdir(parents=True)
            source.write_text("import Lean.Elab.Command\n" + (ROOT / rel).read_text()
                              + ILL_TYPED_LEAN)
            if not expect_success("I.1 compiled with an ill-typed proof",
                                  run("lake", "env", "lean", "-R", str(root), "-o", str(path),
                                      str(source))):
                return
        expect_failure("an ill-typed proof in I.1's compiled module, replayed by leanchecker",
                       run(*command), f"while replaying declaration '{ILL_TYPED}'",
                       f"(kernel) declaration type mismatch, '{ILL_TYPED}'",
                       unwanted=("failed to read file", "invalid header", "does not exist"))
    finally:
        path.write_bytes(saved)
        if rebuild_restored("the Elements build restored after the ill-typed proof", outputs,
                            force=path):
            expect_success("leanchecker's replay after the ill-typed proof", run(*command))


def heath_word() -> None:
    rel = "heath/I/01.md"
    saved = replace_once(rel, "With centre A and distance AB", "With centre A and radius AB")
    try:
        expect_failure("an edited Heath word", fidelity(),
                       "I.1: the `--` comments don't match Heath's proof")
    finally:
        (ROOT / rel).write_text(saved)


def wrong_radii() -> None:
    rel = "Elements/BookI/Prop01.lean"
    saved = replace_once(rel, "Definition15 hA_BCD hC_BCD hB_BCD", "Definition15 hB_ACE hC_ACE hA_ACE")
    try:
        expect_failure("the README's wrong radii in I.1", run("lake", "env", "lean", rel), "error")
    finally:
        (ROOT / rel).write_text(saved)


def entry(facts: dict, ref: str) -> dict:
    return next(p for p in facts["propositions"] if p["ref"] == ref)


def with_facts(change) -> subprocess.CompletedProcess:
    """Run check_fidelity.py on a copy of facts.json changed by `change`; the real
    facts.json is not touched."""
    facts = json.loads((ROOT / "facts.json").read_text())
    change(facts)
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "facts.json"
        copy.write_text(json.dumps(facts, ensure_ascii=False))
        return fidelity("--facts", str(copy))


def weakened_postulate() -> None:
    def weaken(facts):
        # "Ne A B → …" becomes "Ne A B → False → …": a Postulate 1 that says nothing.
        types = facts["axiom_types"]
        s = types["Postulate1"]
        types["Postulate1"] = s.replace("Ne A B →", "Ne A B → False →", 1) if "Ne A B →" in s \
            else "False → " + s
    expect_failure("Postulate 1 weakened in facts.json", with_facts(weaken),
                   "Postulate1: its statement is not the one in Certificate/axioms.lock")


def changed_word() -> None:
    def change(facts):
        # A straight line "touches" a circle without the clause that A and B differ. The
        # statements name the word without its meaning, so no printed statement and no
        # review fingerprint moves: only the lock can see it.
        words = facts["vocabulary"]
        words["Touches"] = words["Touches"].replace("And (Ne A B) ", "", 1) + " "
    expect_failure("Touches given another meaning in facts.json", with_facts(change),
                   "Touches: its definition is not the one in Certificate/axioms.lock")


def stale_statement() -> None:
    def change(facts):
        e = entry(facts, "III.1 Por.")
        e["statement"] = e["statement"] + " → True"
    expect_failure("a changed statement of III.1's porism", with_facts(change),
                   "III.1: its statement has changed since it was reviewed")


def primitive_not_opaque() -> None:
    def change(facts):
        facts["opaque"] = [w for w in facts["opaque"] if w != "Centre"]
    expect_failure("a primitive word no longer opaque", with_facts(change),
                   "Centre: no longer an opaque primitive")


def circle_dependencies() -> None:
    for ref, axiom, rule in (
        ("III.3", "Tacit.inside_of_between", "Circle 2"),
        ("I.15 Por.", "Tacit.outside_of_between", "Circle 3"),
        ("II.1 general", "Tacit.outside_of_between", "Circle 3"),
    ):
        def change(facts):
            entry(facts, ref)["axioms"].append(axiom)
        expect_failure(f"{rule} in {ref}'s axioms", with_facts(change),
                       f"{ref}: rests on {axiom} ({rule}), forbidden for every entry",
                       unwanted=(f"{ref.split()[0]}: rests on {axiom}",) if " " in ref else ())


def circle_renamed() -> None:
    """Circle 3 renamed in the lock and in a copy of facts.json alike: the two still agree,
    so the missing name is what must show that the check no longer refuses it. (III.2's
    [overlap] names the rule and is refused as well; the plant does not rely on that.)"""
    old, new = "Tacit.outside_of_between", "Tacit.Circle.outside_of_between"
    rel = "Certificate/axioms.lock"
    saved = replace_once(rel, f'"{old}" =', f'"{new}" =')

    def change(facts):
        for table in ("axiom_types", "axiom_modules"):
            facts[table][new] = facts[table].pop(old)
    try:
        expect_failure("Circle 3 renamed in the lock and facts.json", with_facts(change),
                       f"{old} (Circle 3): not an axiom in {rel}",
                       unwanted=("an assumption not in", "no longer an axiom"))
    finally:
        (ROOT / rel).write_text(saved)


def circle_proved() -> None:
    """A proved Circle 2 must still bring in Circle 3 as a locked axiom."""
    inside, outside = "Tacit.inside_of_between", "Tacit.outside_of_between"
    path = ROOT / "Certificate/axioms.lock"
    saved = path.read_bytes()
    saved_errors = list(check_fidelity.errors)
    axioms, vocabulary = check_fidelity.read_lock(path)
    axioms.pop(inside, None)
    try:
        path.write_text(check_fidelity.render_lock(axioms, vocabulary))
        for dependencies in ([], [outside]):
            facts = json.loads((ROOT / "facts.json").read_text())
            for table in ("axiom_types", "axiom_modules"):
                facts[table].pop(inside, None)
            facts.setdefault("proved_rules", {})[inside] = dependencies
            check_fidelity.errors.clear()
            check_fidelity.check_lock(facts, path)
            found = list(check_fidelity.errors)
            result = subprocess.CompletedProcess([], int(bool(found)), "\n".join(found), "")
            if not dependencies:
                expect_failure("Circle 2 proved without a forbidden axiom", result,
                               f"{inside} (Circle 2): proved without another forbidden circle rule")
            elif expect_success("Circle 2 proved from locked Circle 3", result):
                print("✓ Circle 2 proved from locked Circle 3: allowed")
    finally:
        path.write_bytes(saved)
        check_fidelity.errors[:] = saved_errors


def placement_called() -> None:
    """Placement among the shared steps of III.26, on a copy of facts.json, is caught; III.24,
    the one entry that may call on it, is given the same step and is not blamed."""
    step = {"name": "BookIII.placement", "brings_in": ["I.7"],
            "file": "Elements/BookIII/Placement.lean", "line": 1}

    def change(facts):
        for ref in ("III.24", "III.26"):
            steps = entry(facts, ref)["shared_steps"]
            if not any(s.get("name") == step["name"] for s in steps):
                steps.append(dict(step))
    expect_failure("placement among III.26's shared steps in facts.json", with_facts(change),
                   "III.26: calls on BookIII.placement",
                   unwanted=("III.24: calls on",))


def native_decide() -> None:
    rel = "Elements/BookI/Prop16.lean"
    saved = replace_once(rel, "\nend Elements.BookI", "\n/-- Planted by scripts/negative_tests.py. "
                         "-/\ntheorem planted_native : 2 + 2 = 4 := by native_decide\n\n"
                         "end Elements.BookI")
    try:
        text = (ROOT / rel).read_text()
        line = text[:text.index("by native_decide")].count("\n") + 1
        expect_failure("a native_decide in I.16's file", fidelity(),
                       f"{rel}:{line}: uses native_decide")
    finally:
        (ROOT / rel).write_text(saved)


# Each command docs/FORMALIZATION.md, section 7, forbids, as check_fidelity.py names it,
# with a line of Lean that uses it, some behind a literal that a scan blind to Lean's
# literals would misread, and a string whose braces Lean could read as code ("string");
# `#exit` comes last, as it would in a file.
PLANTED_COMMANDS = (
    ("decide +native", "theorem planted_decide : 2 + 2 = 4 := by decide +native"),
    ("native := true",
     "theorem planted_config : 2 + 2 = 4 := by decide (config := { native := true })"),
    ("native", "theorem planted_item : 10 * 10 = 100 := by decide +zetaReduce +native"),
    ("native", "theorem planted_value : 11 * 11 = 121 := by decide (native := Bool.true)"),
    ("(config :=", "theorem planted_whole : 12 * 12 = 144 := "
     "by decide (config := ⟨false, true, true, false⟩)"),
    ("(«config» :=", "theorem planted_escaped_config : 13 * 13 = 169 := "
     "by decide («config» := ⟨false, true, true, false⟩)"),
    ("bv_decide", "theorem planted_bv (x y : BitVec 8) : x * y = y * x := by bv_decide"),
    ("bv_check", 'theorem planted_lrat (x : BitVec 8) : x = x := by bv_check "planted.lrat"'),
    ("set_option debug.",
     "set_option debug.skipKernelTC true in theorem planted_skip : True := trivial"),
    ("set_option «debug».",
     "set_option «debug».skipKernelTC true in theorem planted_escaped : True := trivial"),
    ("set_option doc.", "set_option doc.verso true"),
    ("set_option «doc».",
     "set_option «doc».«verso» true in theorem planted_verso : True := trivial"),
    ("#eval", '#eval IO.println "planted"'),
    ("run_cmd", "run_cmd pure ()"),
    ("run_cmd", 'run_cmd Lean.logInfo "x"'),
    ("run_cmd", "example : True := trivial run_cmd Check.Generator.checkFiles"),
    ("run_cmd", "run_cmd Check.GeneratorOther.checkFiles"),
    ("run_cmd", "run_cmd Check.Generator.checkFiles.other"),
    ("run_elab", "run_elab pure ()"),
    ("run_meta", "run_meta pure ()"),
    ("run_tac", "theorem planted_tac : True := by run_tac pure ()"),
    ("by_elab", "def plantedByElab : Nat := by_elab pure (Lean.mkNatLit 4)"),
    ("elab", 'elab "planted_elab" : term => pure (Lean.mkNatLit 4)'),
    ("elab_rules", "elab_rules : term | `(planted_elab) => pure (Lean.mkNatLit 4)"),
    ("macro", 'macro "planted_macro" : term => `(4)'),
    ("macro_rules", "macro_rules | `(planted_macro) => `(4)"),
    ("simproc", "simproc ↓ plantedSimproc (Nat.succ _) := fun _ => return .continue"),
    ("dsimproc", "dsimproc plantedDSimproc (Nat.succ _) := fun _ => return .continue"),
    ("simproc_decl",
     "simproc_decl plantedSimprocDecl (Nat.succ _) := fun _ => return .continue"),
    ("dsimproc_decl",
     "dsimproc_decl plantedDSimprocDecl (Nat.succ _) := fun _ => return .continue"),
    ("simproc_pattern", "simproc_pattern% Nat.succ _ => plantedSimprocDecl"),
    ("cbv_simproc", "cbv_simproc plantedCbv (Nat.succ _) := fun _ => return .continue"),
    ("sym_simproc", "sym_simproc plantedSym (Nat.succ _) := fun _ => return .continue"),
    ("builtin_simproc",
     "builtin_simproc plantedBuiltinSimproc (Nat.succ _) := fun _ => return .continue"),
    ("set_library_suggestions", "set_library_suggestions plantedSelector"),
    ("command_elab", "def plantedCommandAttr : Lean.Name := `command_elab"),
    ("term_elab", "def plantedTermAttr : Lean.Name := `term_elab"),
    ("@[command_elab]", "@[command_elab plantedStx] def plantedCommand : "
     "Lean.Elab.Command.CommandElab := fun _ => pure ()"),
    ("@[term_elab]", "@[term_elab plantedStx] def plantedTerm : Lean.Elab.Term.TermElab := "
     "fun _ _ => pure (Lean.mkNatLit 4)"),
    ("@[doElem_elab]", "@[doElem_elab plantedStx] def plantedDoElem : "
     "Lean.Elab.Do.DoElab := fun _ _ => failure"),
    ("@[inductive_elab]", "@[inductive_elab plantedStx] def plantedInductive : "
     "Lean.Elab.Command.InductiveElabDescr := default"),
    ("@[tactic]", "@[tactic plantedStx] def plantedTactic : Lean.Elab.Tactic.Tactic := "
     "fun _ => pure ()"),
    ("@[tactic]", "attribute [tactic plantedStx] plantedTactic"),
    ("@[grind_tactic]", "@[grind_tactic plantedStx] def plantedGrind : "
     "Lean.Elab.Tactic.Grind.GrindTactic := fun _ => pure ()"),
    ("@[try_tactic]", "@[try_tactic plantedStx] def plantedTry : "
     "Lean.Elab.Tactic.Try.TryTactic := fun _ => failure"),
    ("@[simproc]", "@[simproc] def plantedSimprocAttr : Lean.Meta.Simp.Simproc := "
     "fun _ => return .continue"),
    ("@[sevalproc]", "attribute [sevalproc] plantedSimprocAttr"),
    ("@[delab]", "@[delab app.plantedK] def plantedDelab : "
     "Lean.PrettyPrinter.Delaborator.Delab := failure"),
    ("@[app_unexpander]", "@[app_unexpander plantedK] def plantedUnexpander : "
     "Lean.PrettyPrinter.Unexpander := fun _ => throw ()"),
    ("@[quot_precheck]", "@[quot_precheck plantedStx] def plantedPrecheck : "
     "Lean.Elab.Term.Quotation.Precheck := fun _ => pure ()"),
    ("@[sym_discharger]", "@[sym_discharger plantedStx] def plantedDischarger := ()"),
    ("@[formatter]", "@[formatter plantedK] def plantedFormatter : "
     "Lean.PrettyPrinter.Formatter := pure ()"),
    ("@[parenthesizer]", "@[parenthesizer plantedK] def plantedParenthesizer : "
     "Lean.PrettyPrinter.Parenthesizer := pure ()"),
    ("@[doElem_control_info]", "@[doElem_control_info plantedStx] def plantedControl : "
     "Lean.Elab.Do.ControlInfoHandler := fun _ => pure {}"),
    ("@[command_code_action]", "@[command_code_action plantedStx] def plantedAction := ()"),
    ("@[server_rpc_method]", "@[server_rpc_method] def plantedRpc (_ : Nat) := ()"),
    ("@[builtin_env_linter]", "@[builtin_env_linter] def plantedLinter := ()"),
    ("@[term_parser]", "@[term_parser] def plantedParser : Lean.Parser.Parser := "
     "Lean.Parser.skip"),
    ("@[cpass]", "@[cpass] def plantedPass : Lean.Compiler.LCNF.PassInstaller := "
     "{ phase := .base, install := pure }"),
    ("@[doc_role]", "@[doc_role] def plantedRole := ()"),
    ("@[deferred_doc_check]", "@[deferred_doc_check] def plantedDocCheck := ()"),
    ("@[try_suggestion]", "@[try_suggestion] def plantedSuggestion := ()"),
    ("@[library_suggestions]", "@[library_suggestions] def plantedSelector : "
     "Lean.LibrarySuggestions.Selector := fun _ _ => pure #[]"),
    ("@[package_code_quality_check]", "@[package_code_quality_check] def plantedQuality := ()"),
    ("@[missing_docs_handler]", "@[missing_docs_handler plantedStx] def plantedHandler : "
     "Lean.Linter.MissingDocs.Handler := fun _ _ => pure ()"),
    ("@[code_action_provider]", "@[code_action_provider] def plantedProvider : "
     "Lean.Server.CodeActionProvider := fun _ _ => pure #[]"),
    ("@[unused_variables_ignore_fn]", "@[unused_variables_ignore_fn] def plantedIgnore : "
     "Lean.Linter.IgnoreFunction := fun _ _ _ => false"),
    ("@[widget_module]", "@[widget_module] def plantedWidget : Lean.Widget.Module := "
     '{ javascript := "" }'),
    ("@[run_parser_attribute_hooks]", "@[run_parser_attribute_hooks] def plantedHooks : "
     "Lean.Parser.Parser := Lean.Parser.skip"),
    ("@[builtin_macro]", "@[builtin_macro plantedStx] def plantedBuiltinMacro : Lean.Macro := "
     "fun _ => Lean.Macro.throwUnsupported"),
    ("@[builtin_doc]", "@[builtin_doc] def plantedBuiltinDoc := ()"),
    ("@[simprocAttr]", "attribute [simprocAttr] plantedSimprocDecl"),
    ("initialize", "initialize plantedRef : IO.Ref Nat ← IO.mkRef 0"),
    ("builtin_initialize", "builtin_initialize plantedBuiltin : IO.Ref Nat ← IO.mkRef 0"),
    ("@[init]", "@[init plantedInit] opaque plantedInitRef : IO.Ref Nat"),
    ("implemented_by", "@[implemented_by plantedSpec] def plantedImpl : Nat := 4"),
    ("extern", '@[extern "planted"] opaque plantedExtern : Nat'),
    ("unsafe", "unsafe def plantedUnsafe : Nat := 4"),
    ("@[tactic]", '@[deprecated "]" (since := "2026-01-01"), tactic plantedStx] '
     "def plantedHidden : Lean.Elab.Tactic.Tactic := fun _ => pure ()"),
    ("@[tactic]", 'attribute [deprecated "]", tactic plantedStx] plantedHidden'),
    ("#eval", 'def plantedOpen := "/-" #eval IO.println "planted"'),
    ("#eval", '#eval IO.println "-/"'),
    ("#eval", 'def plantedRaw := r#"]"/-"# #eval IO.println r"-/"'),
    ("#eval", "def plantedChar := '\"' #eval IO.println \"planted\""),
    ("by_elab",
     'def plantedHole : String := s!"{(by_elab pure (Lean.mkStrLit "x") : String)}"'),
    ("string", 'def plantedBraces := "{" ++ "}"'),
    ("#exit", "#exit"),
)
# A new file in each folder the scan reads, paired with its root module; Staging's in a
# folder of its own, which shows that the scan reads every folder beneath.
PLANTED_FILES = (("Elements", "Elements/Planted.lean"),
                 ("Staging", "Staging/Planted/Commands.lean"),
                 ("Audit", "Audit/Planted.lean"),
                 ("model/Model", "model/Model/Planted.lean"),
                 ("model/Check", "model/Check/Planted.lean"))
# A new file of Book Zero, and the line of it that imports a proposition.
BOOK_ZERO = ("Elements/Figure/Planted.lean", 2, "-- Planted by scripts/negative_tests.py: "
             "the import below must be caught.\nimport Elements.BookI.Prop01\n")


def forbidden_commands() -> None:
    """Every forbidden command, and an axiom declared twice, once after another command
    on the same line, in a new file of each folder `check_fidelity.py` scans, `#exit` at
    the end of each root file, and a Book Zero file importing a proposition. Each must be
    caught, by its file and line."""
    header = ["/-! Planted by scripts/negative_tests.py: forbidden commands must be caught. -/",
              ""]
    body = [("axiom", "example : True := trivial axiom planted_inline : True"),
            ("axiom", "axiom planted_axiom : True"),
            ("native_decide", "theorem planted_native : 2 + 2 = 4 := by native_decide"),
            *PLANTED_COMMANDS]
    generator = ["run_cmd Check.Generator.checkFiles",
                 "  run_cmd (Check.Generator.checkFiles)"]
    text = "\n".join(header + [line for _, line in body] + generator) + "\n"

    def caught(rel: str, line: int, word: str) -> str:
        if word == "axiom":
            return f"{rel}:{line}: declares an axiom outside Elements/Foundations/"
        if word == "native_decide":
            return f"{rel}:{line}: uses native_decide"
        if word == "string":
            return f"{rel}:{line}: a string the scan cannot read for certain"
        return f"{rel}:{line}: uses `{word}`"

    wanted: dict[str, list[str]] = {}
    allowed: list[str] = []
    planted: list[Path] = []          # files, then the folders made for them
    roots: dict[Path, str] = {}
    try:
        for tree, rel in PLANTED_FILES:
            path = ROOT / rel
            assert not path.exists(), f"{rel} exists; update this test"
            if not path.parent.exists():
                path.parent.mkdir()
                planted.append(path.parent)
            path.write_text(text)
            planted.insert(0, path)
            wanted[tree] = [caught(rel, len(header) + i, word)
                            for i, (word, _) in enumerate(body, 1)]
            calls = [caught(rel, len(header) + len(body) + i, "run_cmd")
                     for i in range(1, len(generator) + 1)]
            if tree == "model/Check":
                allowed += calls
                # The allowance covers only run_cmd, not another command or its arguments.
                extra = ['run_cmd Check.Generator.checkFiles run_cmd Lean.logInfo "x"',
                         'run_cmd (Check.Generator.checkFiles (by_elab pure (.str "x")))']
                path.write_text(text + "\n".join(extra) + "\n")
                first = len(header) + len(body) + len(generator) + 1
                wanted[tree] += [caught(rel, first, "run_cmd"), caught(rel, first + 1, "by_elab")]
                allowed.append(caught(rel, first + 1, "run_cmd"))
            else:
                wanted[tree] += calls
        for tree in wanted:
            root = ROOT / f"{tree}.lean"
            roots[root] = root.read_text()
            changed = roots[root] + "\n" + "\n".join(generator) + "\n#exit\n"
            root.write_text(changed)
            line = changed[:changed.rindex("#exit")].count("\n") + 1
            wanted[tree].append(caught(f"{tree}.lean", line, "#exit"))
            calls = [caught(f"{tree}.lean", line - len(generator) + i, "run_cmd")
                     for i in range(len(generator))]
            if tree == "model/Check":
                allowed += calls
            else:
                wanted[tree] += calls
        figure, line, text = BOOK_ZERO
        assert not (ROOT / figure).exists(), f"{figure} exists; update this test"
        (ROOT / figure).write_text(text)
        planted.insert(0, ROOT / figure)
        result = fidelity()
        for tree, messages in wanted.items():
            expect_failure(f"every forbidden command and an axiom in {tree}/ and {tree}.lean",
                           result, *messages, unwanted=tuple(allowed))
        expect_failure("a proposition imported by Book Zero", result,
                       f"{figure}:{line}: Book Zero must not import a proposition")
    finally:
        for root, saved in roots.items():
            root.write_text(saved)
        for path in planted:
            if path.is_dir():
                path.rmdir()
            else:
                path.unlink(missing_ok=True)


def symbolic_links() -> None:
    """Refuse a directory link and a file link by their own paths."""
    links = (("model/Model/PlantedLink", ROOT / "model/Check"),
             ("model/Check/PlantedLink.lean", ROOT / "Elements.lean"))
    planted: list[Path] = []
    try:
        for rel, target in links:
            path = ROOT / rel
            assert not path.exists() and not path.is_symlink(), f"{rel} exists; update this test"
            assert target.exists(), f"{target.relative_to(ROOT)} is missing; update this test"
            path.symlink_to(target, target_is_directory=target.is_dir())
            planted.append(path)
        result = fidelity()
        for rel, _ in links:
            expect_failure(f"a symbolic link at {rel}", result,
                           f"{rel}: a symbolic link, which the source scan does not follow;",
                           unwanted=("model/Model/PlantedLink/",))
    finally:
        for path in planted:
            path.unlink(missing_ok=True)


def model_lake() -> None:
    """An axiom in a `.lake` folder of model/Model/ and of model/Check/ is caught, and one
    in the package's own model/.lake is not read."""
    plants = ("model/Model/.lake/Planted.lean", "model/Check/.lake/Planted.lean",
              "model/.lake/Planted.lean")
    planted: list[Path] = []          # files, then the folders made for them
    try:
        for rel in plants:
            path = ROOT / rel
            assert not path.exists() and not path.is_symlink(), f"{rel} exists; update this test"
            if not path.parent.exists():
                path.parent.mkdir()
                planted.append(path.parent)
            path.write_text("axiom planted_axiom : True\n")
            planted.insert(0, path)
        result = fidelity()
        for rel in plants[:2]:
            expect_failure(f"an axiom in {rel}", result,
                           f"{rel}:1: declares an axiom outside Elements/Foundations/",
                           unwanted=("model/.lake/",))
    finally:
        for path in planted:
            if path.is_dir():
                path.rmdir()
            else:
                path.unlink(missing_ok=True)


def rules_in(root: Path) -> subprocess.CompletedProcess:
    """check_fidelity's source scan, run on the tree at `root` instead of the edition's."""
    saved_root, saved_errors = check_fidelity.ROOT, list(check_fidelity.errors)
    check_fidelity.ROOT = root
    check_fidelity.errors.clear()
    try:
        check_fidelity.check_rules()
        found = list(check_fidelity.errors)
    finally:
        check_fidelity.ROOT = saved_root
        check_fidelity.errors[:] = saved_errors
    return subprocess.CompletedProcess([], 1 if found else 0, "\n".join(found) + "\n", "")


def lake_links() -> None:
    """A symbolic link named `.lake`, to a directory, to a file or to nothing, is refused
    by its own path in model/, model/Model/ and model/Check/, never followed; a real
    model/.lake directory holding an axiom and a link is not entered. Each case is a
    small tree of its own, so the edition's model/.lake is never moved, copied or read."""
    axiom = "axiom planted_axiom : True\n"
    for folder in ("model", "model/Model", "model/Check"):
        for kind in ("directory", "file", "dangling"):
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp).resolve()
                (root / "model/Model").mkdir(parents=True)
                (root / "model/Check").mkdir()
                target = root / "Target"
                if kind == "directory":
                    target.mkdir()
                    (target / "Planted.lean").write_text(axiom)
                elif kind == "file":
                    target.write_text(axiom)
                rel = f"{folder}/.lake"
                (root / rel).symlink_to(target, target_is_directory=kind == "directory")
                expect_failure(f"a {kind} link at {rel}", rules_in(root),
                               f"{rel}: a symbolic link, which the source scan does not follow;",
                               unwanted=(f"{rel}/", f"{rel}:1:"))
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "model/.lake").mkdir(parents=True)
        (root / "model/.lake/Planted.lean").write_text(axiom)
        (root / "model/.lake/Link.lean").symlink_to(root / "model/.lake/Planted.lean")
        result = rules_in(root)
        if result.returncode != 0:
            failures.append("a real model/.lake was read: " + result.stdout.strip())
            print(result.stdout[-3000:])
        else:
            print("✓ a real model/.lake holding an axiom and a link: not read")


# The six probes an independent reviewer planted for #207 (its issue lists them), each a
# forbidden command or an axiom hidden behind a carriage-return comment: Lean ends a `--`
# comment only at a line feed, so `-- a remark\r"` is one comment to Lean, the quote among
# it, while a scan that reads the file with Python's universal newlines sees the comment
# end at the `\r` and a string open on the next line, which swallows the command up to the
# `"` of the closing `-- "`. Each is (a short name, the probe's exact bytes). Read as Lean
# reads the bytes (`check_fidelity.lean_text`), the comment hides nothing: the lone `\r`
# of each is refused, and the scan names the command of three of them (the
# `set_option debug.…` pair and the `axiom`) once the comment no longer hides it.
CARRIAGE_RETURN_PROBES = (
    ("#guard_msgs (drop all)", '-- a remark\r"\n#guard_msgs (drop all) in\n'
     'theorem bad : (0 : Nat) = 1 := rfl\n-- "\n#print axioms bad\n'),
    ("set_option debug.byAsSorry", '-- a remark\r"\nset_option debug.byAsSorry true in\n'
     'theorem bad : (0 : Nat) = 1 := by decide\n-- "\n#print axioms bad\n'),
    ("a pinned error", '-- a remark\r"\n/-- error: boom\n⊢ 0 = 1 -/\n#guard_msgs in\n'
     'theorem bad : (0 : Nat) = 1 := by fail "boom"\n-- "\n#print axioms bad\n'),
    ("#guard_panic", '-- a remark\r"\n#guard_panic in\n'
     'theorem bad : (0 : Nat) = 1 := by fail "PANIC"\n-- "\n#print axioms bad\n'),
    ("set_option debug.skipKernelTC", '-- a remark\r"\nset_option debug.skipKernelTC true in\n'
     'theorem ok : True := trivial\n-- "\n'),
    ("axiom", '-- a remark\r"\naxiom planted : (0 : Nat) = 1\n-- "\n#print axioms planted\n'),
)
# The three probes whose command check_fidelity.py already names once the carriage-return
# comment no longer hides it: {probe index: (the words it names, the token that begins
# them in the probe)}. The FORBIDDEN regex matches `set_option debug.` up to its dot; the
# axiom has its own message. The other three the lone `\r` alone refuses here.
CR_COMMANDS = {
    1: ("uses `set_option debug.`", "set_option"),
    4: ("uses `set_option debug.`", "set_option"),
    5: ("declares an axiom outside Elements/Foundations/", "axiom"),
}


def carriage_return_comment() -> None:
    """The six CARRIAGE_RETURN_PROBES of #207, in one scratch copy of I.1's file in a
    temporary tree, run through the source scan (`rules_in`): read as Lean reads the bytes,
    the lone `\\r` of each is refused by its file and line, and the `set_option debug.…`
    pair and the `axiom`, no longer hidden, are named too. The unplanted copy passes, and
    so does a copy of it with CRLF line endings, which Lean allows."""
    rel = "Elements/BookI/Prop01.lean"
    marker = "\nend Elements.BookI\n"
    source = (ROOT / rel).read_text()
    assert source.count(marker) == 1, f"{rel}: expected one {marker!r}; update this test"
    header = "\n/-! Planted by scripts/negative_tests.py (#207). -/\n"
    block = header + "".join(body for _, body in CARRIAGE_RETURN_PROBES)
    planted = source.replace(marker, block + marker)
    cr_message = ("an isolated carriage return (a `\\r` not followed by `\\n`), which Lean "
                  "accepts inside a comment or a literal and a `--` comment does not "
                  "end at")

    def line(offset: int) -> int:
        return planted[:offset].count("\n") + 1

    wanted, at = [], planted.index(block) + len(header)
    for i, (_, body) in enumerate(CARRIAGE_RETURN_PROBES):
        wanted.append(f"{rel}:{line(at + body.index(chr(13)))}: {cr_message}")
        if i in CR_COMMANDS:
            msg, token = CR_COMMANDS[i]
            wanted.append(f"{rel}:{line(at + body.index(token))}: {msg}")
        at += len(body)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        path = root / rel
        path.parent.mkdir(parents=True)
        path.write_text(source)
        if not expect_success("the unplanted scratch copy of I.1 for #207's probes",
                              rules_in(root)):
            return
        path.write_bytes(source.replace("\n", "\r\n").encode("utf-8"))
        expect_success("the unplanted scratch copy of I.1 for #207's probes, with CRLF "
                       "line endings", rules_in(root))
        path.write_bytes(planted.encode("utf-8"))
        expect_failure("the six #207 probes behind a carriage-return comment",
                       rules_in(root), *wanted)


def placement_named() -> None:
    """A lemma of the `Placement` namespace named in Squares.lean, Book III's shared steps,
    read from the source: caught on its line. The word in a comment on the line before
    cites nothing, and is not caught."""
    rel = "Elements/BookIII/Squares.lean"
    marker = "\nend Elements\n"
    saved = replace_once(rel, marker,
                         "\n-- The word placement, in a comment, cites nothing.\n"
                         "/-- Planted by scripts/negative_tests.py. -/\n"
                         "theorem planted_placement : True := (fun _ => trivial) @Placement.dist\n"
                         + marker)
    before = saved[:saved.index(marker)].count("\n") + 1
    try:
        expect_failure("a lemma of placement named in Squares.lean", fidelity(),
                       f"{rel}:{before + 3}: names `Placement`",
                       unwanted=(f"{rel}:{before + 1}:",))
    finally:
        (ROOT / rel).write_text(saved)


def stale_lean() -> None:
    path = ROOT / "Elements" / "BookI" / "Prop01.lean"
    saved = path.read_text()
    path.write_text(saved + "\n-- A line planted by scripts/negative_tests.py.\n")
    try:
        expect_failure("a changed Lean file under a review record", fidelity(),
                       "I.1: its Lean file has changed since it was reviewed")
    finally:
        path.write_text(saved)


def missing_files() -> None:
    """I.1's figure, idea figure and mishnah, each taken away in turn: Book I is complete,
    so `check_fidelity.py` names the one missing, and not the other two."""
    rels = ("figures/I/01.svg", "figures/I/01-idea.svg", "mishnah/I/01.md")
    for rel in rels:
        path = ROOT / rel
        saved = path.read_bytes()
        try:
            path.unlink()
            expect_failure(f"I.1's {rel} missing from a complete book", fidelity(),
                           f"I.1: {rel} is missing",
                           unwanted=tuple(f"I.1: {other} is missing" for other in rels
                                          if other != rel))
        finally:
            path.write_bytes(saved)


def toml_blocks(text: str) -> list[str]:
    """A TOML file cut before each table header, so that whole tables can be dropped."""
    blocks, current = [], []
    for line in text.splitlines(keepends=True):
        if line.lstrip().startswith("[") and current:
            blocks.append("".join(current))
            current = []
        current.append(line)
    blocks.append("".join(current))
    return blocks


def undeclared_run() -> None:
    """Drop the [[passage]] tables that begin within III.16's runs of `--` lines with no
    Lean beneath them, and the run of the angle clauses must be caught: the message names
    it by its first words, since the runs before it are caught too. The passage that
    declares that run may be of any kind (left in Euclid's words, or argued another way
    by a companion); what is tested is that a run no passage declares is caught."""
    import tomllib
    record = heath.review_path("III", 16)
    src = heath.lean_path("III", 16).read_text()
    runs = check_fidelity.uncarried_runs(src, 16)
    starts = check_fidelity.sentence_starts(check_fidelity.proof_lines(src, 16))
    saved = record.read_text()
    kept, dropped = [], []
    for block in toml_blocks(saved):
        table = tomllib.loads(block).get("passage", [{}])[0] if block.lstrip().startswith("[[passage]]") else {}
        at = check_fidelity._plain(table.get("at", "")) if table else None
        if at and any(ln in run.lines and words.startswith(at) for run in runs for ln, words in starts):
            dropped.append(at)
        else:
            kept.append(block)
    angles = check_fidelity._plain("I say further that the angle of the")
    if not any(at.startswith(angles) for at in dropped):
        failures.append("III.16's angle clauses: review/III/16.toml declares no passage in "
                        "the run of `--` lines with no Lean beneath it that begins 'I say "
                        "further that the angle of the'; update this test")
        return
    record.write_text("".join(kept))
    try:
        expect_failure("III.16's record without the passage on its angle clauses", fidelity(),
                       "III.16: the `--` lines from 'I say further that the angle of the'")
    finally:
        record.write_text(saved)


def remark_ends_run() -> None:
    """A remark between two sentences of I.5 that share one step of Lean. The first
    sentence then has no Lean before the next run of `--` lines, and must be caught; the
    second keeps its Lean, beneath a remark of its own, and must not be."""
    rel = "Elements/BookI/Prop05.lean"
    first = "and in these AB is equal to AC,"
    second = "the remainder BF is equal to the remainder CG."
    saved = replace_once(rel, f"  -- {first}\n  -- {second}\n",
                         f"  -- {first}\n"
                         "  /- Planted by scripts/negative_tests.py: these words have no Lean. -/\n"
                         f"  -- {second}\n"
                         "  /- Planted too: a remark between a sentence and its Lean. -/\n")
    line = saved[:saved.index(f"-- {first}")].count("\n") + 1
    try:
        expect_failure("a sentence with no Lean before a remark in I.5", fidelity(),
                       f"I.5: the `--` lines from {first!r} ({rel}:{line}) have no Lean",
                       unwanted=("I.5: the `--` lines from 'the remainder BF",))
    finally:
        (ROOT / rel).write_text(saved)


def planted_assumptions() -> None:
    # The count of Euclid's assumptions is the lock's, read before anything is planted:
    # the planted rule makes one more, whatever the foundations hold.
    lock = check_fidelity.read_lock()
    assert lock is not None, "Certificate/axioms.lock is missing"
    locked = len(lock[0])

    facts = (ROOT / "facts.json").read_text()
    outputs = BuildOutputs()
    planted_outputs = BuildOutputs("**/Elements/Foundations/Tacit/Planted.*")

    # I.16: Postulate 5, the planted rule, a hidden axiom, and a helper whose statement
    # alone mentions the later I.22.
    rel16 = "Elements/BookI/Prop16.lean"
    saved16 = (ROOT / rel16).read_text()
    text = "import Elements.Foundations.Tacit.Planted\nimport Elements.BookI.Prop22\n" + saved16
    text = text.replace(
        "namespace Elements.BookI\n",
        "namespace Elements.BookI\n\n/-- Planted. -/ axiom sneaky : True\n\n"
        "/-- Planted: only the statement mentions I.22, and the proof is `trivial`. -/\n"
        "theorem Prop16.typeOnly : (fun _ => True) @Elements.BookI.Prop22 := trivial\n", 1)
    head = ("theorem Prop16 {A B C D : Point} (hABC : Triangle A B C) (hBCD : Between B C D) :\n"
            "    ∠ C B A < ∠ A C D ∧ ∠ B A C < ∠ A C D := by\n")
    assert text.count(head) == 1, "Prop16's statement has changed; update this test"
    text = text.replace(head, head + "  have _p5 := @Postulate5\n"
                        "  have _planted := @Elements.Tacit.Euclidean.planted\n"
                        "  have _sneaky := @Elements.BookI.sneaky\n"
                        "  have _typeOnly : True := Prop16.typeOnly\n"
                        "  have _unproved : True := sorry\n")

    # I.15's porism: Postulate 5, superposition and the later I.22 (which does not
    # import I.15), none of them used by I.15 itself.
    rel15 = "Elements/BookI/Prop15.lean"
    saved15 = (ROOT / rel15).read_text()
    porism = saved15.find("theorem Prop15.porism")
    proof = saved15.find(":= by\n", porism)
    assert porism >= 0 and proof >= 0, "Prop15.porism has changed; update this test"
    proof += len(":= by\n")
    text15 = ("import Elements.BookI.Prop22\n" + saved15[:proof]
              + "  have _p5 := @Postulate5\n"
              "  have _sup := @Tacit.superposition\n"
              "  have _later := @Elements.BookI.Prop22\n" + saved15[proof:])

    try:
        PLANTED.write_text(
            "import Elements.Foundations.Words\n\n"
            "namespace Elements.Tacit.Euclidean\n\n"
            "/-- A rule planted by scripts/negative_tests.py. -/\n"
            "axiom planted : True\n\n"
            "end Elements.Tacit.Euclidean\n")
        (ROOT / rel16).write_text(text)
        (ROOT / rel15).write_text(text15)
        build = run("lake", "build")
        if build.returncode != 0:
            failures.append("the planted assumptions: the changed I.15 and I.16 did not build")
            print((build.stdout + build.stderr)[-3000:])
            return
        run("lake", "env", "lean", "Certificate/Facts.lean")
        result = fidelity()
        expect_failure("Postulate 5, a Euclidean-only rule and a hidden axiom in I.16",
                       result,
                       "I.16: rests on Postulate5, Tacit.Euclidean.planted before I.29",
                       "BookI.sneaky: an axiom declared in Elements.BookI.Prop16, outside",
                       "I.16: rests on BookI.sneaky",
                       f"declares {locked + 1} axioms, not {locked}")
        expect_failure("the planted axioms missing from the lock", result,
                       "Tacit.Euclidean.planted: an assumption not in Certificate/axioms.lock",
                       "BookI.sneaky: an assumption not in Certificate/axioms.lock")
        expect_failure("Postulate 5, superposition and a later citation in I.15's porism only",
                       result,
                       "I.15 Por.: rests on Postulate5 before I.29",
                       "I.15 Por.: uses superposition directly (only I.4 and I.8 may)",
                       "I.15 Por.: cites I.22, which does not come before it",
                       unwanted=("✗ I.15: rests on", "✗ I.15: uses superposition",
                                 "✗ I.15: cites"))
        expect_failure("a later proposition named only in a helper's statement", result,
                       "I.16: cites I.22, which does not come before it")
        expect_failure("a sorry in I.16, in a complete book", result,
                       "I.16: Book I is complete, but I.16 is not proved")
    finally:
        (ROOT / rel16).write_text(saved16)
        (ROOT / rel15).write_text(saved15)
        PLANTED.unlink(missing_ok=True)
        (ROOT / "facts.json").write_text(facts)
        try:
            rebuild_restored("the restored files build", outputs)
        finally:
            planted_outputs.restore()


def certificate_constructor_counting() -> None:
    """Rebuilding constructors must not invent a coincidence step."""
    rel = "Certificate/Facts.lean"
    path = ROOT / rel
    saved = path.read_bytes()
    try:
        replace_once(
            rel, "used.contains coincidenceStep",
            "([`Elements.Superposition.Derives.len_congr,\n"
            "           `Elements.Superposition.Derives.angle_congr,\n"
            "           `Elements.Superposition.Derives.area_congr]).any used.contains",
        )
        expect_failure(
            "constructor counting reports a step in a transformer",
            run(sys.executable, "-I", "tests/test_certificate.py"),
            "FAIL: test_transformers_without_step_do_not_count",
            "AssertionError: Lists differ: ['C.N. 4'] != []",
        )
    finally:
        path.write_bytes(saved)
    expect_success("the restored certificate regression",
                   run(sys.executable, "-I", "tests/test_certificate.py"))


@contextmanager
def count_source_copy():
    """Copy tracked sources plus current Python tools under /tmp, with no build or .git.

    Git reads the original index through GIT_DIR; GIT_WORK_TREE points only at the
    copy. No Git command writes. Include new Python sources before they are committed.
    A tracked file absent from the work tree is named (absent_tracked), not copied.
    """
    tracked, names = tracked_names()
    tracked.check_returncode()
    git_dir = run("git", "rev-parse", "--absolute-git-dir")
    git_dir.check_returncode()
    paths = {Path(p) for p in names}
    paths.difference_update(absent_tracked(sorted(paths)))
    paths.update(p.relative_to(ROOT) for p in (ROOT / "scripts").glob("*.py"))
    with tempfile.TemporaryDirectory(prefix="stoicheia-counts-", dir="/tmp") as tmp:
        copy = Path(tmp)
        for rel in paths:
            target = copy / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / rel, target)
        yield copy, {**os.environ, "GIT_DIR": git_dir.stdout.strip(),
                     "GIT_WORK_TREE": str(copy)}


def count_markers() -> None:
    """Plant count faults and unsafe discovery paths in a copy, without Lean."""
    with count_source_copy() as (copy, env):
        path = copy / "docs/PROGRAM.md"
        original = path.read_text()
        line = original.count("\n") + 2
        computed = generated_counts.vocabulary(copy)
        for name, stated in (("vocabulary", str(computed + 1)),
                             ("unknown-count", "0"), ("vocabulary", str(computed))):
            path.write_text(original + f"\nVocabulary: <!-- count:{name} -->"
                            f"{stated}<!-- /count -->.\n")
            result = subprocess.run([sys.executable, "scripts/check_fidelity.py"],
                                    cwd=copy, env=env, capture_output=True, text=True)
            where = f"docs/PROGRAM.md:{line}:"
            if name == "unknown-count":
                expect_failure("an unknown count name", result, where,
                               "unknown count name 'unknown-count'")
            elif stated != str(computed):
                expect_failure("a stale inline count", result, where, "count 'vocabulary'",
                               f"stated '{stated}'", f"computed '{computed}'",
                               "run python3 scripts/render.py")
            elif expect_success("a correct inline count", result):
                print("✓ a correct inline count: passed (without Lean)")
        path.write_text(original)
        for name, git_env, diagnostic in (
                ("missing Git metadata",
                 {k: v for k, v in env.items() if not k.startswith("GIT_")},
                 "cannot resolve Git work tree"),
                ("a mismatched Git work tree", {**env, "GIT_WORK_TREE": str(ROOT)},
                 "does not match repository root")):
            result = subprocess.run([sys.executable, "scripts/check_fidelity.py"],
                                    cwd=copy, env=git_env, capture_output=True, text=True)
            expect_failure(name, result, diagnostic, unwanted=("Traceback",))
        with tempfile.TemporaryDirectory(prefix="stoicheia-count-target-", dir="/tmp") as tmp:
            target = Path(tmp) / "notes.md"
            text = "<!-- count:vocabulary -->0<!-- /count -->\n"
            target.write_text(text)
            path.unlink()
            path.symlink_to(target)
            try:
                for script in ("check_fidelity.py", "render.py"):
                    result = subprocess.run([sys.executable, f"scripts/{script}"],
                                            cwd=copy, env=env, capture_output=True, text=True)
                    expect_failure(f"a Markdown symlink in {script}", result,
                                   "docs/PROGRAM.md: symlink is forbidden", unwanted=("Traceback",))
                    if target.read_text() != text:
                        failures.append(f"{script} wrote through a Markdown symlink")
            finally:
                path.unlink()
                path.write_text(original)


def main(argv=()) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--counts-only", action="store_true",
                        help="only the count plants and file-only regressions; no build needed")
    args = parser.parse_args(argv)
    if not expect_success("restoration regressions",
                          run(sys.executable, "-I", "tests/test_negative_tests.py")):
        return 1
    print("✓ restoration regressions passed (without Lean)")
    if not expect_success("count regressions",
                          run(sys.executable, "-I", "tests/test_generated_counts.py")):
        return 1
    print("✓ count regressions passed (without Lean)")
    if not expect_success("decision entry regressions",
                          run(sys.executable, "-I", "tests/test_decision_entries.py")):
        return 1
    print("✓ decision entry regressions passed (without Lean)")
    if args.counts_only:
        count_markers()
        if failures:
            print("\n".join(failures))
            return 1
        print("✓ count plants passed; other plants were not run (--counts-only)")
        return 0
    before = run("git", "status", "--porcelain")
    if not expect_success("entry Git status", before):
        return 1
    try:
        heath_word()
        merge_conflict_markers()
        count_markers()
        wrong_radii()
        weakened_postulate()
        changed_word()
        stale_statement()
        primitive_not_opaque()
        circle_dependencies()
        circle_renamed()
        placement_called()
        stale_lean()
        undeclared_run()
        remark_ends_run()
        native_decide()
        forbidden_commands()
        symbolic_links()
        model_lake()
        lake_links()
        carriage_return_comment()
        placement_named()
        figure_names_and_arcs()
        missing_files()
        planted_assumptions()
        for test in (circle_proved, style_error, broken_link, stale_page,
                     changed_audit_pin, corrupt_olean, certificate_constructor_counting,
                     ill_typed_proof):
            started = perf_counter()
            try:
                test()
            finally:
                print(f"  {test.__name__}: {perf_counter() - started:.2f}s (including restoration)")
        restored = fidelity()
        if restored.returncode != 0:
            failures.append("the unplanted tree failed check_fidelity.py")
            print((restored.stdout + restored.stderr)[-3000:])
        else:
            print("✓ the unplanted tree passes check_fidelity.py")
    finally:
        original = sys.exception()
        try:
            after = run("git", "status", "--porcelain")
            if expect_success("final Git status", after):
                if after.stdout != before.stdout:
                    message = "the working tree did not return to its entry Git status"
                    failures.append(message)
                    print(f"✗ {message}:")
                    output = after.stdout + after.stderr
                    if output:
                        print(output, end="" if output.endswith("\n") else "\n")
                else:
                    print("✓ working tree restored to its entry Git status")
        except BaseException as error:
            if original is None:
                raise
            print(f"Final Git status also failed: {type(error).__name__}: {error}")
    if failures:
        print(f"{len(failures)} negative-test failure(s):")
        for f in failures:
            print("  ✗ " + f)
        return 1
    print("✓ every planted change was caught")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
