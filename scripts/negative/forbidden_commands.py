"""Every command docs/FORMALIZATION.md, section 7, forbids, an attribute for each ending and
prefix by which the scan knows one, and an axiom declared twice, once after another command
on the same line, planted in a new file of each folder the scan reads, `Elements/`,
`Staging/` (in a folder of its own), `Audit/`, `model/Model/` and `model/Check/`, with
`#exit` at the end of each root file, `Elements.lean`, `Staging.lean` and `Audit.lean`,
`model/Model.lean` and `model/Check.lean`, a new Book Zero file that imports a
proposition, and a `native_decide` in a theorem added to a proposition's own file, I.16's
(`Elements/BookI/Prop16.lean`), inside its namespace: `check_fidelity.py` must catch each
on its own line, naming its file and line.
Some of the commands stand after a string, a raw string or a character literal holding
`/-`, `-/`, `]` or `"`, and one in an interpolated string's hole, so the scan must read
Lean's literals as Lean does; a string whose braces Lean could read as code is caught too.
Generator calls, plain and parenthesised, are caught outside the model's Check files; there
they are allowed only first on their line, with other commands still caught on that line
and in their arguments. The files are read, not built; no tree is copied, so model/.lake is
never copied either.
"""

from pathlib import Path

import negative_tests as nt

BUILDS = False

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
    ("#guard_panic",
     '#guard_panic in theorem planted_panic : (0 : Nat) = 1 := by fail "PANIC"'),
    ("#time", "#time def plantedTime : Nat := 1"),
    ("#with_exporting", "#with_exporting def plantedExporting : Nat := 1"),
    ("#guard", "#guard true"),
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

# A proposition's own file, the end of its namespace, and the theorem planted before it.
PROPOSITION = ("Elements/BookI/Prop16.lean", "\nend Elements.BookI",
               "\n/-- Planted by scripts/negative_tests.py. -/\n"
               "theorem planted_native : 2 + 2 = 4 := by native_decide\n")


def plant() -> None:
    """Every forbidden command, and an axiom declared twice, once after another command
    on the same line, in a new file of each folder `check_fidelity.py` scans, `#exit` at
    the end of each root file, a Book Zero file importing a proposition, and a
    `native_decide` in I.16's file. Each must be caught, by its file and line."""
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
    proposition, end, theorem = PROPOSITION
    kept: str | None = None           # the proposition's file as it was
    try:
        for tree, rel in PLANTED_FILES:
            path = nt.ROOT / rel
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
            root = nt.ROOT / f"{tree}.lean"
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
        assert not (nt.ROOT / figure).exists(), f"{figure} exists; update this test"
        (nt.ROOT / figure).write_text(text)
        planted.insert(0, nt.ROOT / figure)
        kept = nt.replace_once(proposition, end, theorem + end)
        changed = (nt.ROOT / proposition).read_text()
        native = changed[:changed.index("by native_decide")].count("\n") + 1
        result = nt.fidelity()
        for tree, messages in wanted.items():
            nt.expect_failure(f"every forbidden command and an axiom in {tree}/ and {tree}.lean",
                              result, *messages, unwanted=tuple(allowed))
        nt.expect_failure("a proposition imported by Book Zero", result,
                          f"{figure}:{line}: Book Zero must not import a proposition")
        nt.expect_failure("a native_decide in I.16's file", result,
                          caught(proposition, native, "native_decide"))
    finally:
        if kept is not None:
            (nt.ROOT / proposition).write_text(kept)
        for root, saved in roots.items():
            root.write_text(saved)
        for path in planted:
            if path.is_dir():
                path.rmdir()
            else:
                path.unlink(missing_ok=True)
