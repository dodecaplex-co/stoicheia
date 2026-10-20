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
   longer among the opaque primitives (as if it had been made a `def`), is caught; and
   placement among III.26's shared steps is caught, while III.24, given it too, is not
   blamed.
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
   scan reads, `Elements/`, `Staging/` (in a folder of its own) and `Audit/`, with
   `#exit` at the end of each root file, `Elements.lean`, `Staging.lean` and
   `Audit.lean`, and a new Book Zero file that imports a proposition: each is caught on
   its own line. Some of the commands stand after a string, a raw string or a character
   literal holding `/-`, `-/`, `]` or `"`, and one in an interpolated string's hole, so
   the scan must read Lean's literals as Lean does; a string whose braces Lean could
   read as code is caught too. The files are read, not built.
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
15. A corrupt header in I.1's compiled `.olean`: leanchecker, invoked as in
    `check_kernel.py`, fails naming the file and its invalid header. The original
    bytes are restored, a rebuild is required, and on success the whole environment
    is replayed.

These faults exercise the style and link checks, page freshness, an audit pin and
leanchecker's loading of compiled files as well as the earlier checks. They do not
plant an invalid proof term for leanchecker's kernel replay. `check_kernel.py`'s own
`--self-test` withholds Postulate 5 from nanoda alone. The update to README.md's
"What the checks show" table is deferred to a later pull request after this check change.

Every new plant restores its inputs in `finally`; the freshness plant also restores
all renderer outputs.
Tests 10, 14 and 15 attempt a restoration build; if it fails or is interrupted, every
file in `.lake/build` returns to its saved contents and presence or absence before
the plant, including dependent modules, hashes and traces. Test 10 always restores or
removes `Planted.*` outputs in a nested `finally`. Tests 11 to 15 report elapsed time,
restoration included. An outer `finally` compares Git status with the entry status,
including on interruption, without replacing an exception already in flight.
Temporary-directory regressions run first, without Lean. Exits non-zero if a fault
goes unnoticed or a restoration check fails. Restoration needs writable files and
an opportunity for `finally` to finish; a forced process kill cannot provide it.
Standard library only; Python 3.11 or later, for the review records.
"""

import json
import subprocess
import sys
import tempfile
from pathlib import Path
from time import perf_counter

import check_fidelity
import check_kernel
import heath

ROOT = heath.ROOT
PLANTED = ROOT / "Elements" / "Foundations" / "Tacit" / "Planted.lean"
failures: list[str] = []
GENERATED = ("facts.json", "book", "CERTIFICATE.md", "GRAPH.md", "README.md",
             "docs/PROGRAM.md")


def run(*cmd: str) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


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
    pin = b"'Audit.III_2' depends on axioms: [Elements.Tacit.inside_of_between]"
    assert saved.count(pin) == 1, "Audit.III_2's pin has changed; update this test"
    outputs = BuildOutputs()
    try:
        path.write_bytes(saved.replace(pin, b"'Audit.III_2' depends on axioms: []"))
        expect_failure("an axiom dropped from Audit.III_2's pin", run("lake", "build", "Audit"),
                       f"{rel}:", "Docstring on `#guard_msgs` does not match generated message",
                       "Audit.III_2", "Elements.Tacit.inside_of_between")
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
# A new file in each folder the scan reads; Staging's in a folder of its own, which
# shows that the scan reads every folder beneath.
PLANTED_FILES = ("Elements/Planted.lean", "Staging/Planted/Commands.lean", "Audit/Planted.lean")
# A new file of Book Zero, and the line of it that imports a proposition.
BOOK_ZERO = ("Elements/Figure/Planted.lean", 2, "-- Planted by scripts/negative_tests.py: "
             "the import below must be caught.\nimport Elements.BookI.Prop01\n")


def forbidden_commands() -> None:
    """Every forbidden command, and an axiom declared twice, once after another command
    on the same line, in a new file of each folder `check_fidelity.py` scans, `#exit` at
    the end of each root file, and a Book Zero file importing a proposition. Each must be
    caught, by its file and line."""
    header = ["/-! Planted by scripts/negative_tests.py: every line below must be caught. -/",
              ""]
    body = [("axiom", "example : True := trivial axiom planted_inline : True"),
            ("axiom", "axiom planted_axiom : True"),
            ("native_decide", "theorem planted_native : 2 + 2 = 4 := by native_decide"),
            *PLANTED_COMMANDS]
    text = "\n".join(header + [line for _, line in body]) + "\n"

    def caught(rel: str, line: int, word: str) -> str:
        if word == "axiom":
            return f"{rel}:{line}: declares an axiom outside Elements/Foundations/"
        if word == "native_decide":
            return f"{rel}:{line}: uses native_decide"
        if word == "string":
            return f"{rel}:{line}: a string the scan cannot read for certain"
        return f"{rel}:{line}: uses `{word}`"

    wanted: dict[str, list[str]] = {}
    planted: list[Path] = []          # files, then the folders made for them
    roots: dict[Path, str] = {}
    try:
        for rel in PLANTED_FILES:
            path = ROOT / rel
            assert not path.exists(), f"{rel} exists; update this test"
            if not path.parent.exists():
                path.parent.mkdir()
                planted.append(path.parent)
            path.write_text(text)
            planted.insert(0, path)
            wanted[rel.split("/")[0]] = [caught(rel, len(header) + i, word)
                                         for i, (word, _) in enumerate(body, 1)]
        for tree in wanted:
            root = ROOT / f"{tree}.lean"
            roots[root] = root.read_text()
            changed = roots[root] + "\n#exit\n"
            root.write_text(changed)
            line = changed[:changed.rindex("#exit")].count("\n") + 1
            wanted[tree].append(caught(f"{tree}.lean", line, "#exit"))
        figure, line, text = BOOK_ZERO
        assert not (ROOT / figure).exists(), f"{figure} exists; update this test"
        (ROOT / figure).write_text(text)
        planted.insert(0, ROOT / figure)
        result = fidelity()
        for tree, messages in wanted.items():
            expect_failure(f"every forbidden command and an axiom in {tree}/ and {tree}.lean",
                           result, *messages)
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


def main() -> int:
    if not expect_success("restoration regressions",
                          run(sys.executable, "-I", "tests/test_negative_tests.py")):
        return 1
    print("✓ restoration regressions passed (without Lean)")
    before = run("git", "status", "--porcelain")
    if not expect_success("entry Git status", before):
        return 1
    try:
        heath_word()
        wrong_radii()
        weakened_postulate()
        changed_word()
        stale_statement()
        primitive_not_opaque()
        placement_called()
        stale_lean()
        undeclared_run()
        remark_ends_run()
        native_decide()
        forbidden_commands()
        placement_named()
        planted_assumptions()
        for test in (style_error, broken_link, stale_page, changed_audit_pin, corrupt_olean):
            started = perf_counter()
            try:
                test()
            finally:
                print(f"  {test.__name__}: {perf_counter() - started:.2f}s (including restoration)")
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
    sys.exit(main())
