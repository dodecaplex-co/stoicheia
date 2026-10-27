#!/usr/bin/env python3
"""scripts/risk.py, the risk class of a change: its table's first-match order, R5 for a
path no rule names, a change's highest class, `--diff` on a repository of the test's own,
paths printed so that none can start a line of CI's log, `--audit` over this repository's
tracked files, and the formal model's inputs: the Lean headers and imports it reads, and
those it cannot read or resolve, each of which then checks the model for every change; the
files a model imports, followed through, on a repository of the test's own and on this
one, whose every header and import it reads.

    python3 -I tests/test_risk.py

Standard library and Git only; no Lean or network. Each `--diff` case runs in a Git
repository of its own, read with no configuration but its own. scripts/negative_tests.py
runs it beside the decision entry regressions, so CI's `negative` job runs it on every push
to main, and on a pull request of class R3 and above (a change to
scripts/risk.py is R5); the cadence runs it on main every six hours.
"""

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RISK = ROOT / "scripts" / "risk.py"
sys.path.insert(0, str(ROOT / "scripts"))
import risk  # noqa: E402


def git_environment(home):
    """The environment, for Git, of a repository of a test's own: none named by GIT_DIR or
    the like, no configuration but the repository's, and an author for its commits."""
    env = {name: value for name, value in os.environ.items() if not name.startswith("GIT_")}
    env.pop("GITHUB_OUTPUT", None)
    return {**env, "HOME": str(home), "XDG_CONFIG_HOME": str(home / ".config"),
            "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_CEILING_DIRECTORIES": str(home.parent),
            "GIT_AUTHOR_NAME": "Risk test", "GIT_AUTHOR_EMAIL": "risk-test@example.invalid",
            "GIT_COMMITTER_NAME": "Risk test",
            "GIT_COMMITTER_EMAIL": "risk-test@example.invalid"}


class Table(unittest.TestCase):
    def assertClass(self, path, expected, ruled=True):
        self.assertEqual(risk.classify(path), (expected, ruled), path)

    def test_first_match_wins(self):
        # A specific rule above a broader, lighter one: each of these paths also matches a
        # later rule of a lower class.
        cases = (
            ("scripts/safe_push.py", "R5"),          # though scripts/* is R3
            ("scripts/test_safe_push.py", "R5"),
            ("scripts/risk.py", "R5"),               # it decides which checks run
            ("scripts/registry.py", "R5"),           # main's copy: the pre-flight's checks
            ("scripts/run_checks.py", "R5"),         # CI's `check` job
            ("scripts/shadow_policy.py", "R5"),      # CI's shadow of the pre-flight
            ("scripts/hooks/pre-push", "R5"),
            ("tests/test_safe_push.py", "R5"),       # though tests/* is R3
            (".github/workflows/ci.yml", "R5"),
            ("Certificate/axioms.lock", "R4"),       # though Certificate/* is R3
            ("tests/model/run.py", "R4"),            # though tests/* is R3
            ("scripts/check_model_kernel.py", "R4"), # though scripts/* is R3
            ("lakefile.lean", "R4"),                 # though *.lean is R2
            ("Elements/Foundations/Plane.lean", "R4"),  # though Elements/* is R2
            ("Elements/Companions.lean", "R4"),
            ("Certificate/Facts.lean", "R3"),        # though *.lean is R2
            ("docs/WORKFLOW.md", "R3"),              # though docs/* is R0
            (".gitignore", "R3"),                    # can hide a file from the clean check
            ("docs/.gitignore", "R3"),               # though docs/* is R0
            (".gitattributes", "R3"),
            ("Audit/screen.py", "R3"),               # though Audit/* is R2
            ("review/SCHEMA.md", "R3"),              # though review/* is R1
            ("review/terms.toml", "R3"),
            ("scripts/check_style.py", "R3"),
            ("scripts/audit/jev.py", "R3"),          # `*` crosses `/`
            ("checks/01-lake-build.toml", "R3"),     # the registry of checks (#229)
            ("checks/README.md", "R3"),              # though README.md is R0
            ("checks/99-a-new-check.toml", "R3"),
            ("docs/ACCEPTANCE.md", "R3"),            # a check input (#249), not R1
            ("docs/ACCEPTANCE.md.orig", "R0"),
            ("Elements/BookI/Prop01.lean", "R2"),
            ("Audit/Overlaps.lean", "R2"),
            ("Overlap.lean", "R2"),                  # any .lean outside Elements
            ("Staging/BookIII/Prop31.lean", "R2"),
            ("docs/STYLE.md", "R1"),                 # though docs/* is R0
            ("docs/decisions/2026-10-22-risk-lanes.md", "R1"),
            ("review/I/01.toml", "R1"),
            ("heath/I/01.md", "R1"),
            ("facts.json", "R1"),
            ("README.md", "R0"),
            ("docs/examples.md", "R0"),
            ("LICENSE-PROSE.md", "R0"),
        )
        for path, expected in cases:
            with self.subTest(path=path):
                self.assertClass(path, expected)

    def test_the_formal_model_jobs_own_files_are_R4_or_above(self):
        # The check the formal-model job runs, and the workflow that runs it; the model's
        # own files and the lock are tested over this repository's tracked files below.
        for path in ("model/lock.sha256", "Certificate/axioms.lock",
                     "scripts/check_model_kernel.py", ".github/workflows/ci.yml"):
            with self.subTest(path=path):
                self.assertIn(risk.classify(path)[0], ("R4", "R5"))

    def test_rules_run_from_the_highest_class_down(self):
        order = [cls for cls, _ in risk.RULES]
        self.assertEqual(order, sorted(risk.CLASSES, reverse=True))
        # And no rule is caught by a lighter one before it: a path standing for each
        # pattern takes the pattern's class or a higher one.
        for cls, patterns in risk.RULES:
            for pattern in patterns:
                with self.subTest(pattern=pattern):
                    self.assertGreaterEqual(risk.classify(pattern.replace("*", "x"))[0], cls)

    def test_a_path_no_rule_names_is_R5(self):
        for path in ("Makefile", "src/main.py", "NEWS", "docs", "scripts", ".github",
                     "elements/BookI/Prop01.lean.bak", "Docs/notes.md", "readme.md"):
            with self.subTest(path=path):
                self.assertClass(path, "R5", ruled=False)

    def test_a_change_takes_its_highest_class(self):
        self.assertEqual(risk.change_class([])[0], "R0")
        self.assertEqual(risk.change_class(["README.md", "docs/examples.md"])[0], "R0")
        records = ["review/I/01.toml", "heath/I/01.md", "README.md"]
        self.assertEqual(risk.change_class(records)[0], "R1")
        proof = records + ["Elements/BookI/Prop01.lean"]
        self.assertEqual(risk.change_class(proof)[0], "R2")
        self.assertEqual(risk.change_class(proof + ["scripts/check_style.py"])[0], "R3")
        self.assertEqual(risk.change_class(proof + ["Makefile"])[0], "R5")
        top, per = risk.change_class(proof + ["Certificate/axioms.lock"])
        self.assertEqual(top, "R4")
        self.assertEqual(per["heath/I/01.md"], ("R1", True))

    def test_a_check_added_to_the_registry_is_R3(self):
        # Adding a check is one file in checks/, section 8's regenerated block and the
        # decision entry naming the file (#229): R3, with neither safe_push.py nor a
        # workflow, which would make it R5.
        added = ["checks/19-a-new-check.toml", "docs/WORKFLOW.md",
                 "docs/decisions/2026-10-22-a-new-check.md"]
        top, per = risk.change_class(added)
        self.assertEqual(top, "R3")
        self.assertEqual(per["checks/19-a-new-check.toml"], ("R3", True))
        self.assertEqual(risk.change_class(added + ["scripts/safe_push.py"])[0], "R5")
        self.assertEqual(risk.change_class(added + [".github/workflows/ci.yml"])[0], "R5")
        # The registry's reader and runner are the landing tool and CI: a change to either,
        # with a check or without, is R5.
        for path in ("scripts/registry.py", "scripts/run_checks.py"):
            with self.subTest(path=path):
                self.assertEqual(risk.change_class(added + [path])[0], "R5")
                self.assertEqual(risk.change_class([path]), ("R5", {path: ("R5", True)}))


class Header(unittest.TestCase):
    """The imports of a Lean file's header, read by a narrow grammar that fails closed."""

    def test_the_forms_of_an_import(self):
        cases = (
            ("import A.B\n", ["A.B"]),
            ("public import A\n", ["A"]),
            ("meta import A\npublic meta import B\n", ["A", "B"]),
            ("import all A\n", ["A"]),
            # Lean refuses `private import`; read as an import, it can only widen the set.
            ("private import A\n", ["A"]),
            ("module\n\npublic import A\n", ["A"]),
            ("prelude\nimport A\n", ["A"]),
            # Several modules on one line, each with its own `import`.
            ("import A import B.C\n", ["A", "B.C"]),
            ("public import A public import B -- and a remark\n", ["A", "B"]),
            ("import A /- a remark -/ import B\n", ["A", "B"]),
            # Comments anywhere, nested blocks and doc comments among them.
            ("-- A remark.\n/- A block\n/- nested, with\nimport X -/\n-/\n/-! A module's doc.\n"
             "import Y -/\nimport A\n", ["A"]),
            ("import A--a remark\nimport B/-a remark-/import C\n", ["A", "B", "C"]),
            ("import\nA\r\nimport -- a remark\nB\r\n", ["A", "B"]),
            # A quoted part of plain characters, as the model's own headers use.
            ("import Model.Laws.«areas-p5»\n", ["Model.Laws.«areas-p5»"]),
            ("public import «areas-p5».B\n", ["«areas-p5».B"]),
            # Any character in a comment, as Lean reads it.
            ("import A -- «.», ℀ and λ\nimport B /- «..» -/\n", ["A", "B"]),
            # The header ends at the first command: an `import` after it is none.
            ("import A\nnamespace N\nimport B\n", ["A"]),
            ('import A\ndef s := "\npublic import B"\n', ["A"]),
            ("import A\npublic section\nimport B\n", ["A"]),
            ("import A\n#check 1\nimport B\n", ["A"]),
            ("import A\n«x» := 1\nimport B\n", ["A"]),
            # Lean takes one module to an `import`, and refuses B here as a command.
            ("import A B\n", ["A"]),
            ("theorem t : True := trivial\n", []),
            ("", []),
        )
        for text, expected in cases:
            with self.subTest(text=text):
                self.assertEqual(risk.imported_modules(text), expected)

    def test_comments_are_read_as_lean_reads_them(self):
        # #349: a block's body begins past its third character, so `/-/- -/` is a whole
        # comment and the `-/` of `/--/` closes nothing, as Lean's tokenizer ends them.
        # Read the old way, the first hid the import after it (a narrower set of the
        # model's inputs), and the second read one inside a doc comment and missed the one
        # after it. (Lean refuses a doc comment before an import; reading the import after
        # it all the same is the reader's widening, as above.)
        cases = (
            ("/-/- -/\nimport A\n", ["A"]),
            ("/--/\nimport X -/\nimport A\n", ["A"]),
            ("/-/- -/ import A /-/- /- nested -/ -/ import B\n", ["A", "B"]),
            ("/- unclosed\nimport A\n", []),
        )
        for text, expected in cases:
            with self.subTest(text=text):
                self.assertEqual(risk.imported_modules(text), expected)

    def test_the_comment_reader_is_heath_s_word_for_word(self):
        # risk.py runs alone, so it keeps a copy of the scripts' one comment reader,
        # heath.comment_end (#206, #349): the same function, by its syntax tree (its code
        # and its docstring; a comment inside it is not compared), and, in the test after
        # this, reading the same on a corpus of comments, strings, character literals and
        # «…» names.
        import ast
        import inspect
        import heath
        def body(function):
            tree = ast.parse(inspect.getsource(function))
            return ast.dump(tree)
        self.assertEqual(body(risk.comment_end), body(heath.comment_end))

    def test_the_comment_reader_reads_as_heath_s(self):
        # Apart from its source, so that a drift in either copy fails this on its own.
        import heath
        corpus = (
            "/-/- -/ import A", "/--/ x -/ y", "/-- doc -/ theorem t", "/-! module -/",
            "/- a /- nested /- deeper -/ -/ -/ after", "/- unclosed /- -/", "-- line\nnext",
            "-- last line", "def s := \"/- not a comment -/\" -- but this is",
            "def c := '\"' /- after a character -/", "def c := '(' -- a bracket's character",
            "def «x /- y» := 1 /- -/", "/-/--/-/", "--/-\n/--\n-/", "/---/ -/", "",
        )
        for text in corpus:
            for i in range(len(text)):
                if text.startswith(("--", "/-"), i):
                    with self.subTest(text=text, at=i):
                        self.assertEqual(risk.comment_end(text, i), heath.comment_end(text, i))

    def test_a_header_the_reader_cannot_read_cleanly_is_unread(self):
        # Lean 4.35 reads a file for each of the first five (named on the right) that a
        # reader matching Lean less closely would leave out of the set; this one fails
        # closed on them, as on the rest.
        cases = (
            "import Elements.BookI.«.».Hidden\n",           # Lean reads Elements/BookI/Hidden
            "import Q.«».A\nimport Q.B\n",                  # Q/A
            "import Q.«..».R.B\n",                          # R/B
            "import Q.X℀\nimport Q.B\n",                    # a letter-like symbol, then Q/B
            "import Q.A\nimport",                           # an import with no module
            "import Q.A\nimport all\n",
            "import -- a remark\n",
            "import all import Q.A\n",
            "import public\nimport Q.B\n",
            "import Q.℀\nimport Q.B\n",
            "import Q.X₁\n",                                # a subscript
            "import Q.α\n",
            "import «Q.A»\n",
            "import Q.«a/b»\n",
            "import Q.«A»B\n",
            "import Q.A.\n",
            "﻿import Q.A\n",                           # a byte order mark
            "import Q.A import Q.B\n",
            "import Q.A\x0cimport Q.B\n",
            "public℀ import Q.A\n",
            "import Q.A\n℀\nimport Q.B\n",
        )
        for text in cases:
            with self.subTest(text=text):
                with self.assertRaises(risk.Unread):
                    risk.imported_modules(text)

    def test_a_module_is_found_at_its_path(self):
        for module, path in (("Elements.BookI.Prop07", "Elements/BookI/Prop07.lean"),
                             ("Model.Laws.«areas-p5»", "Model/Laws/areas-p5.lean"),
                             ("Elements", "Elements.lean"),
                             ("Q.«a/./b».C", "Q/a/b/C.lean")):
            with self.subTest(module=module):
                self.assertEqual(risk.module_path(module), path)

    def test_a_module_with_a_part_empty_dot_or_dot_dot_or_outside_the_tree_is_unread(self):
        for module in ("Elements.BookI.«.».Hidden", "Q.«».A", "Q.«..».R.B", "«..»",
                       "Q.«../..».B", "«/etc».B", "A..B", ""):
            with self.subTest(module=module):
                with self.assertRaises(risk.Unread):
                    risk.module_path(module)


class Repo(unittest.TestCase):
    """A Git repository of the test's own, its first commit holding FILES."""

    FILES: dict = {}

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.temp = Path(temp.name).resolve()
        self.root = self.temp / "repository"
        self.root.mkdir()
        home = self.temp / "home"
        home.mkdir()
        self.env = git_environment(home)
        self.git("init", "-q")
        # Rename detection on, as in an ordinary clone: risk.py must turn it off.
        self.git("config", "diff.renames", "true")
        self.base = self.commit(self.FILES)

    def git(self, *args, data=None):
        done = subprocess.run(["git", *args], cwd=self.root, env=self.env, input=data,
                              capture_output=True, text=data is None)
        self.assertEqual(done.returncode, 0, done.stderr)
        return done.stdout

    def commit(self, files, removed=()):
        for name, text in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        for name in removed:
            self.git("rm", "-q", "--", name)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", "A change")
        return self.git("rev-parse", "HEAD").strip()

    def commit_in_index(self, files):
        """Commit files through Git's index alone, at paths a file system might refuse."""
        records = b""
        for name, text in files.items():
            blob = self.git("hash-object", "-w", "--stdin", data=text.encode()).strip()
            records += b"100644 " + blob + b"\t" + name.encode() + b"\0"
        self.git("update-index", "-z", "--index-info", data=records)
        self.git("commit", "-q", "-m", "A change at odd paths")
        return self.git("rev-parse", "HEAD").strip()

    def risk(self, *args, env=None):
        return subprocess.run([sys.executable, "-I", str(RISK), *args], cwd=self.root,
                              env=env or self.env, capture_output=True, text=True)

    def diff_class(self, head, base=None):
        done = self.risk("--diff", base or self.base, head)
        self.assertEqual(done.returncode, 0, done.stderr)
        return done.stdout.splitlines()[0].split()[0], done.stdout

    def lane(self, head):
        """The class and formal_model `--diff --github-output` writes, and what it prints."""
        output = self.temp / "github-output"
        output.write_text("", encoding="utf-8")
        done = self.risk("--diff", self.base, head, "--github-output",
                         env=dict(self.env, GITHUB_OUTPUT=str(output)))
        self.assertEqual(done.returncode, 0, done.stderr)
        values = dict(line.split("=", 1)
                      for line in output.read_text(encoding="utf-8").splitlines())
        self.assertEqual(sorted(values), ["class", "formal_model"])
        return values["class"], values["formal_model"], done.stdout


class Command(Repo):
    """The script itself, on a repository of the test's own."""

    FILES = {"README.md": "A reader's edition.\n", ".github/workflows/ci.yml": "name: CI\n",
             "docs/a b/notes.md": "Notes.\n"}

    def test_an_empty_diff_is_R0(self):
        self.assertEqual(self.diff_class(self.base)[0], "R0")
        head = self.commit({})
        cls, out = self.diff_class(head)
        self.assertEqual(cls, "R0")
        self.assertIn("(no file changed)", out)
        self.assertEqual(self.lane(head)[:2], ("R0", "false"))

    def test_a_workflow_change_is_R5(self):
        head = self.commit({"README.md": "Changed.\n",
                            ".github/workflows/ci.yml": "name: CI\non: push\n"})
        cls, out = self.diff_class(head)
        self.assertEqual(cls, "R5")
        self.assertIn("  R5 .github/workflows/ci.yml", out.splitlines())
        self.assertIn("  R0 README.md", out.splitlines())
        self.assertIn("formal model: in full, since the class is R5", out.splitlines())

    def test_a_path_with_a_space_is_one_path(self):
        # Split on white space, the path would give `b/notes.md`, which no rule names: R5.
        head = self.commit({"docs/a b/notes.md": "Notes, changed.\n"})
        cls, out = self.diff_class(head)
        self.assertEqual(cls, "R0", out)
        self.assertIn("  R0 docs/a b/notes.md", out.splitlines())

    def test_no_path_can_start_a_line_of_the_log(self):
        # GitHub takes a line of a step's log that starts `::`, after any spaces, for a
        # workflow command. A path with a line break is still one path, printed on one
        # line with the break escaped; one that starts `::` follows the class, as all do.
        odd = {"docs/x\n::error::planted.md": "x\n", "docs/y\r::add-mask::R0.md": "y\n",
               "::warning::z.md": "z\n"}
        head = self.commit_in_index(odd)
        cls, out = self.diff_class(head)
        self.assertEqual(cls, "R5", out)        # `::warning::z.md` matches no rule
        lines = out.splitlines()
        self.assertIn("  R0 docs/x\\n::error::planted.md", lines)
        self.assertIn("  R0 docs/y\\r::add-mask::R0.md", lines)
        self.assertIn("  R5 ::warning::z.md  (no rule)", lines)
        done = self.risk("--audit", str(self.root))
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("  unruled (R5 by default): ::warning::z.md", done.stdout.splitlines())
        paths = self.risk("--paths", *odd)
        self.assertEqual(paths.returncode, 0, paths.stderr)
        self.assertIn("R0 docs/x\\n::error::planted.md", paths.stdout.splitlines())
        # Read as text, an unescaped carriage return would also end a line here.
        for printed in (out, done.stdout, paths.stdout):
            for line in printed.splitlines():
                with self.subTest(line=line):
                    self.assertFalse(line.lstrip().startswith("::"), line)

    def test_a_submodule_change_counts_whatever_gitmodules_says(self):
        # `ignore = all` in .gitmodules would hide the change from `git diff`.
        self.commit({".gitmodules": ('[submodule "sub"]\n\tpath = scripts/sub\n'
                                     "\turl = ./sub\n\tignore = all\n")})
        self.git("update-index", "--add", "--cacheinfo", f"160000,{'1' * 40},scripts/sub")
        self.git("commit", "-q", "-m", "A submodule")
        self.base = self.git("rev-parse", "HEAD").strip()
        self.git("update-index", "--cacheinfo", f"160000,{'2' * 40},scripts/sub")
        self.git("commit", "-q", "-m", "The submodule moved")
        cls, out = self.diff_class(self.git("rev-parse", "HEAD").strip())
        self.assertEqual(cls, "R3", out)
        self.assertIn("  R3 scripts/sub", out.splitlines())

    def test_a_file_moved_counts_where_it_was(self):
        # With rename detection, Git would name only docs/ci.md, which is R0.
        self.git("mv", ".github/workflows/ci.yml", "docs/ci.md")
        self.git("commit", "-q", "-m", "Move the workflow")
        cls, out = self.diff_class(self.git("rev-parse", "HEAD").strip())
        self.assertEqual(cls, "R5", out)
        self.assertIn("  R5 .github/workflows/ci.yml", out.splitlines())
        self.assertIn("  R0 docs/ci.md", out.splitlines())

    def test_the_diff_is_the_change_since_the_branch_left_base(self):
        # BASE...HEAD: what base gained after the branch left it is not the branch's.
        branch_point = self.git("rev-parse", "HEAD").strip()
        self.git("checkout", "-q", "-b", "side")
        head = self.commit({"README.md": "The branch's line.\n"})
        self.git("checkout", "-q", "-")
        main = self.commit({".github/workflows/ci.yml": "name: CI, on main\n"})
        self.assertNotEqual(main, branch_point)
        self.assertEqual(self.diff_class(head, base=main)[0], "R0")

    def test_github_output_takes_the_class(self):
        head = self.commit({".github/workflows/ci.yml": "name: CI\non: push\n"})
        output = self.temp / "github-output"
        output.write_text("earlier=1\n", encoding="utf-8")
        done = self.risk("--diff", self.base, head, "--github-output",
                         env=dict(self.env, GITHUB_OUTPUT=str(output)))
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(output.read_text(encoding="utf-8"),
                         "earlier=1\nclass=R5\nformal_model=true\n")
        self.assertTrue(done.stdout.startswith("R5 "), done.stdout)
        # Asked for, GITHUB_OUTPUT must be set: no class otherwise.
        done = self.risk("--diff", self.base, head, "--github-output")
        self.assertEqual((done.returncode, done.stdout), (2, ""), done.stderr)
        self.assertIn("GITHUB_OUTPUT is not set", done.stderr)

    def test_a_git_failure_prints_no_class(self):
        output = self.temp / "github-output"
        output.write_text("", encoding="utf-8")
        env = dict(self.env, GITHUB_OUTPUT=str(output))
        for args in (("--diff", "no-such-revision", "HEAD"),
                     ("--diff", self.base, "0" * 40),
                     ("--diff", "--output=written", "HEAD"),
                     ("--diff", self.base, "HEAD", "--github-output", "--github-output"),
                     ("--diff", self.base)):
            with self.subTest(args=args):
                done = self.risk(*args, "--github-output", env=env)
                self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
                self.assertEqual(done.stdout, "")
                self.assertEqual(output.read_text(encoding="utf-8"), "")
        self.assertFalse((self.root / "written...HEAD").exists())
        for args in (("--model-inputs", "no-such-revision"), ("--model-inputs", "--all"),
                     ("--model-inputs",)):
            with self.subTest(args=args):
                done = self.risk(*args)
                self.assertEqual((done.returncode, done.stdout), (2, ""), done.stderr)
        # Outside any repository, too.
        outside = self.temp / "outside"
        outside.mkdir()
        done = subprocess.run([sys.executable, "-I", str(RISK), "--diff", "HEAD~1", "HEAD"],
                              cwd=outside, env=self.env, capture_output=True, text=True)
        self.assertEqual((done.returncode, done.stdout), (2, ""), done.stderr)

    def test_the_worktree_form_reads_the_given_base(self):
        head = self.commit({".github/workflows/ci.yml": "name: CI\non: push\n"})
        done = subprocess.run([sys.executable, "-I", str(RISK), str(self.root), self.base],
                              cwd=self.temp, env=self.env, capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertTrue(done.stdout.startswith("R5 Landing tool and CI\n"), done.stdout)
        self.assertNotEqual(head, self.base)

    def test_audit_names_a_file_no_rule_covers(self):
        done = self.risk("--audit", str(self.root))
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.commit({"Makefile": "all:\n"})
        done = self.risk("--audit", str(self.root))
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("  unruled (R5 by default): Makefile", done.stdout.splitlines())
        # A folder Git cannot read is a failure, never a clean audit.
        outside = self.temp / "outside"
        outside.mkdir()
        done = self.risk("--audit", str(outside))
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)


class FormalModel(Repo):
    """formal_model: a change of any class to a file the model imports runs the model."""

    FILES = {
        "model/Check.lean": "import Check.Circles\nimport Check.Angles\n",
        # Prop07 directly, and Prop05 through it; Mathlib's and the model's own modules
        # have no file in the main package; Prop09 only in a string, after the header.
        "model/Check/Circles.lean": (
            "-- The model's check of circles.\n/- A block /- nested -/ remark. -/\n"
            "import Elements.BookI.Prop07 import Mathlib.Data.Real.Basic\n"
            "import Check.Hand\n\nnamespace Check\n"
            'def text := "\nimport Elements.BookI.Prop09"\nend Check\n'),
        "model/Check/Angles.lean": ("module\n\npublic import Elements.BookI.Prop13\n"
                                    "meta import Model.Laws.«areas-p5»\n"),
        "model/Check/Hand.lean": "import Elements.Foundations.Postulates\n",
        "model/Model/Laws/areas-p5.lean": "theorem a : True := trivial\n",
        "Elements/BookI/Prop07.lean": ("import Elements.BookI.Prop05\n\n"
                                       "theorem p7 : True := trivial\n"),
        "Elements/BookI/Prop05.lean": "theorem p5 : True := trivial\n",
        "Elements/BookI/Prop09.lean": "theorem p9 : True := trivial\n",
        "Elements/BookI/Prop13.lean": "theorem p13 : True := trivial\n",
        "Elements/Foundations/Postulates.lean": "theorem p : True := trivial\n",
        "Certificate/axioms.lock": "Postulates\n",
        "README.md": "A reader's edition.\n",
    }

    def test_the_model_inputs_follow_the_imports(self):
        done = self.risk("--model-inputs", self.base)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout.splitlines(),
                         ["Elements/BookI/Prop05.lean", "Elements/BookI/Prop07.lean",
                          "Elements/BookI/Prop13.lean",
                          "Elements/Foundations/Postulates.lean"])

    def test_a_file_the_model_imports_runs_it(self):
        head = self.commit({"Elements/BookI/Prop07.lean": "theorem p7 : True := trivial\n"})
        cls, model, out = self.lane(head)
        self.assertEqual((cls, model), ("R2", "true"), out)
        self.assertIn("formal model: in full, since the formal model imports "
                      "Elements/BookI/Prop07.lean", out.splitlines())

    def test_a_file_imported_through_another_runs_it(self):
        head = self.commit({"Elements/BookI/Prop05.lean": "theorem p5' : True := trivial\n"})
        self.assertEqual(self.lane(head)[:2], ("R2", "true"))

    def test_an_unresolved_direct_import_runs_it_for_every_change(self):
        start = self.commit({"model/Check/Hand.lean": "import Elements.Missing\n"})
        self.base = start
        head = self.commit({"README.md": "Changed.\n"})
        cls, model, out = self.lane(head)
        self.assertEqual((cls, model), ("R0", "true"), out)
        self.assertIn("model/Check/Hand.lean, in the formal model's imports", out)
        self.assertIn("Elements.Missing has no Elements/Missing.lean in the tree", out)

    def test_an_unresolved_transitive_import_retains_resolved_inputs(self):
        start = self.commit({
            "Elements/BookI/Prop07.lean": (
                "import Elements.BookI.Prop05\nimport Elements.BookI.Missing\n\n"
                "theorem p7 : True := trivial\n")})
        self.base = start
        head = self.commit({"Elements/BookI/Prop09.lean": "theorem p9' : True := trivial\n"})
        cls, model, out = self.lane(head)
        self.assertEqual((cls, model), ("R2", "true"), out)
        self.assertIn("Elements/BookI/Prop07.lean, in the formal model's imports", out)
        done = self.risk("--model-inputs", head)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("Elements/BookI/Prop05.lean", done.stdout.splitlines())
        self.assertIn(
            "unread: Elements/BookI/Prop07.lean: Elements.BookI.Missing has no "
            "Elements/BookI/Missing.lean in the tree; while it is, every change checks "
            "the formal model", done.stdout.splitlines())

    def test_an_R2_edit_after_a_src_dir_change_runs_the_model(self):
        start = self.commit({
            "lakefile.toml": ('name = "fixture"\n\n[[lean_lib]]\nname = "Library"\n'
                              'srcDir = "src"\n'),
            "model/Check/SourceDir.lean": "import Library.Theorem\n",
            "src/Library/Theorem.lean": "theorem fromSource : True := trivial\n",
        })
        self.base = start
        head = self.commit({
            "src/Library/Theorem.lean": "theorem fromSource' : True := trivial\n"})
        cls, model, out = self.lane(head)
        self.assertEqual((cls, model), ("R2", "true"), out)
        self.assertIn("model/Check/SourceDir.lean, in the formal model's imports", out)
        self.assertIn("Library.Theorem has no Library/Theorem.lean in the tree", out)

    def test_known_external_roots_are_not_unread(self):
        roots = ("Check", "Model", "Mathlib", "Lean", "Init", "Std")
        imports = "".join(f"import {root}.Absent\n" for root in roots)
        start = self.commit({"model/Check/Hand.lean": imports})
        self.base = start
        head = self.commit({"README.md": "Changed.\n"})
        cls, model, out = self.lane(head)
        self.assertEqual((cls, model), ("R0", "false"), out)
        done = self.risk("--model-inputs", head)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertFalse(any(line.startswith("unread: ") for line in done.stdout.splitlines()),
                         done.stdout)

    def test_a_public_import_runs_it(self):
        head = self.commit({"Elements/BookI/Prop13.lean": "theorem p13' : True := trivial\n"})
        self.assertEqual(self.lane(head)[:2], ("R2", "true"))

    def test_a_file_outside_the_imports_does_not(self):
        head = self.commit({"Elements/BookI/Prop09.lean": "theorem p9' : True := trivial\n",
                            "README.md": "Changed.\n"})
        cls, model, out = self.lane(head)
        self.assertEqual((cls, model), ("R2", "false"), out)
        self.assertIn("formal model: passes at once, since the change touches nothing under "
                      "model/, nor the axiom lock, nor a file the formal model imports",
                      out.splitlines())

    def test_a_file_the_change_deletes_still_counts(self):
        # At the diff's end the file is gone, so only the diff's start shows that the model
        # imported it, directly (Prop13) or through another (Prop05), which nothing changed.
        for name in ("Elements/BookI/Prop13.lean", "Elements/BookI/Prop05.lean"):
            with self.subTest(name=name):
                self.git("checkout", "-q", "--detach", self.base)
                head = self.commit({}, removed=(name,))
                cls, model, out = self.lane(head)
                self.assertEqual((cls, model), ("R2", "true"), out)
                self.assertEqual(out.splitlines()[1:-1], [f"  R2 {name}"])

    def test_a_new_import_counts_at_the_diffs_end(self):
        # A proof change that also gives the model a new input is R4, by model/; the file
        # it now imports counts from then on.
        head = self.commit({"model/Check/Hand.lean": ("import Elements.Foundations.Postulates\n"
                                                      "import Elements.BookI.Prop09\n")})
        self.assertEqual(self.lane(head)[:2], ("R4", "true"))
        self.base = head
        head = self.commit({"Elements/BookI/Prop09.lean": "theorem p9' : True := trivial\n"})
        self.assertEqual(self.lane(head)[:2], ("R2", "true"))

    def test_the_lock_runs_it(self):
        head = self.commit({"Certificate/axioms.lock": "Postulates, changed\n"})
        self.assertEqual(self.lane(head)[:2], ("R4", "true"))

    def test_a_header_the_reader_cannot_read_runs_it_for_every_change(self):
        # Prop07, which the model imports, is given each header; a later change to Prop09,
        # which the model does not import, then checks the model, naming Prop07.
        proof = "\ntheorem p7 : True := trivial\n"
        cases = (
            ("«.»", "import Elements.BookI.«.».Prop05\n" + proof),
            ("«»", "import Elements.BookI.«».Prop05\n" + proof),
            ("«..»", "import Elements.«..».Elements.BookI.Prop05\n" + proof),
            ("a letter-like symbol",
             "import Elements.Note℀\nimport Elements.BookI.Prop05\n" + proof),
            ("an import with no module", "import Elements.BookI.Prop05\nimport\n"),
        )
        for form, text in cases:
            with self.subTest(form=form):
                self.git("checkout", "-q", "--detach", self.base)
                start = self.commit({"Elements/BookI/Prop07.lean": text})
                head = self.commit({"Elements/BookI/Prop09.lean":
                                    "theorem p9' : True := trivial\n"})
                done = self.risk("--diff", start, head)
                self.assertEqual(done.returncode, 0, done.stderr)
                lines = done.stdout.splitlines()
                self.assertEqual(lines[:2], ["R2 Proofs", "  R2 Elements/BookI/Prop09.lean"])
                self.assertTrue(lines[-1].startswith(
                    "formal model: in full, since Elements/BookI/Prop07.lean, in the formal "
                    "model's imports, has a header the classifier cannot read ("), lines[-1])
                self.assertTrue(lines[-1].endswith("), so every change checks the model"),
                                lines[-1])

    def test_a_file_hidden_behind_a_header_the_reader_cannot_read_still_runs_it(self):
        # Two R2 changes: the first gives Prop07, which the model imports, an import of
        # Hidden that Lean reads (Elements/BookI/Hidden.lean) and the reader cannot; the
        # second changes Hidden alone. Both check the model.
        head = self.commit({
            "Elements/BookI/Prop07.lean": ("import Elements.BookI.«.».Hidden\n\n"
                                           "theorem p7 : True := trivial\n"),
            "Elements/BookI/Hidden.lean": "def hidden := 1\n"})
        self.assertEqual(self.lane(head)[:2], ("R2", "true"))
        self.base = head
        head = self.commit({"Elements/BookI/Hidden.lean": "def hidden := 2\n"})
        cls, model, out = self.lane(head)
        self.assertEqual((cls, model), ("R2", "true"), out)
        self.assertIn("formal model: in full, since Elements/BookI/Prop07.lean, in the formal "
                      "model's imports, has a header the classifier cannot read "
                      "(Elements/BookI/Prop07.lean: Elements.BookI runs into '.'), so every "
                      "change checks the model", out.splitlines())
        done = self.risk("--model-inputs", head)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout.splitlines()[-1],
                         "unread: Elements/BookI/Prop07.lean: Elements.BookI runs into '.'; "
                         "while it is, every change checks the formal model")

    def test_a_gitattributes_anywhere_runs_it_for_every_change(self):
        # An encoding there makes the checkout Lean reads differ from the blob the reader
        # reads: under UTF-7 a blob's `℀/` checks out as `+IQA-/`, ending a comment the blob
        # leaves open, so an import only Lean sees would follow. Any .gitattributes, root or
        # nested, makes every change check the formal model.
        for where in (".gitattributes", "Elements/BookI/.gitattributes"):
            with self.subTest(where=where):
                start = self.commit({where: "*.txt working-tree-encoding=UTF-7\n"})
                self.base = start
                head = self.commit({"README.md": f"Changed for {where}.\n"})
                cls, model, out = self.lane(head)
                self.assertEqual((cls, model), ("R0", "true"), out)
                self.assertIn(f"{where}, in the formal model's imports", out)
                self.base = self.commit({}, removed=[where])

    def test_a_model_file_the_reader_cannot_read_runs_it_for_every_change(self):
        start = self.commit({"model/Check/Hand.lean":
                             "import Elements.«.».Foundations.Postulates\n"})
        self.assertEqual(self.lane(start)[:2], ("R4", "true"))
        self.base = start
        head = self.commit({"README.md": "Changed.\n"})
        cls, model, out = self.lane(head)
        self.assertEqual((cls, model), ("R0", "true"), out)
        self.assertIn("model/Check/Hand.lean, in the formal model's imports", out)


class Repository(unittest.TestCase):
    def test_every_tracked_file_has_a_rule(self):
        done = subprocess.run([sys.executable, "-I", str(RISK), "--audit", str(ROOT)],
                              capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)

    def test_every_file_of_the_model_and_the_lock_is_R4_or_above(self):
        # CI's formal-model job runs for R4 and R5 whatever else it reads, so a table edit
        # must never take a file of the model, or the lock its hash ties, below R4.
        done = subprocess.run(["git", "ls-files", "-z", "--", "model", "Certificate/axioms.lock"],
                              cwd=ROOT, capture_output=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        paths = [os.fsdecode(path) for path in done.stdout.split(b"\0") if path]
        self.assertIn("model/lock.sha256", paths)
        self.assertIn("Certificate/axioms.lock", paths)
        for path in paths:
            with self.subTest(path=path):
                self.assertIn(risk.classify(path)[0], ("R4", "R5"))

    def test_the_model_imports_these_files(self):
        done = subprocess.run([sys.executable, "-I", str(RISK), "--model-inputs", "HEAD"],
                              cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        inputs = set(done.stdout.splitlines())
        self.assertEqual([line for line in inputs if line.startswith("unread: ")], [])
        for path in ("Elements/BookI/Prop07.lean", "Elements/BookI/Prop13.lean",
                     "Elements/Figure/Circles.lean"):
            with self.subTest(path=path):
                self.assertIn(path, inputs)
        for path in inputs:
            with self.subTest(path=path):
                self.assertTrue(path.endswith(".lean") and not path.startswith("model/"), path)
                self.assertTrue((ROOT / path).is_file(), path)

    def test_every_header_the_model_reaches_is_read_so_a_proof_outside_it_passes_at_once(self):
        # The model's own headers, «areas-p5» among them, and those of every file they
        # reach, read cleanly; so a change of R2 to a proof outside the set leaves the
        # formal model to the cadence.
        inputs, unread = risk.model_inputs("HEAD", str(ROOT))
        self.assertEqual(unread, {})
        done = subprocess.run(["git", "ls-files", "-z", "--", "Elements/BookI"], cwd=ROOT,
                              capture_output=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        proofs = sorted(set(os.fsdecode(path) for path in done.stdout.split(b"\0") if path)
                        - inputs)
        self.assertTrue(proofs)
        outside = proofs[0]
        self.assertEqual(risk.classify(outside), ("R2", True))
        full, why = risk.formal_model("R2", [outside], "HEAD", "HEAD", str(ROOT))
        self.assertEqual((full, why), (False, "the change touches nothing under model/, nor "
                                              "the axiom lock, nor a file the formal model "
                                              "imports"))


if __name__ == "__main__":
    unittest.main()
