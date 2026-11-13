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

import ast
import fnmatch
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

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
        self.assertEqual(sorted(values), ["class", "formal_model", "gate"])
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
                         "earlier=1\nclass=R5\nformal_model=true\ngate=true\n")
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
                self.assertEqual(out.splitlines()[1:-2], [f"  R2 {name}"])
                self.assertTrue(out.splitlines()[-1].startswith("gate tests: "), out)

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
                # The last line is the gate's (L3.2); the formal model's comes before it.
                self.assertTrue(lines.pop().startswith("gate tests: "), done.stdout)
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


# The landing tool's inputs (CI-SCOPE-1a, L3.1): the reads of its two files that the check
# below resolves, `HERE /` and `SOURCE /` paths with their loops, constants and globs, and the
# programs they run by subprocess; and the trace of the code under test, which shows what it
# opens at runtime.
GATE_FILES = ("scripts/safe_push.py", "scripts/test_safe_push.py")
# What `HERE` and `SOURCE` name in the two files: scripts/ and the tree's root.
BASES = {"HERE": "scripts", "SOURCE": ""}
# The rows of GATE_READ_EXCLUDED as built, each with the decisions entry that names its path
# and this test (G-ADD): a row beyond them is refused, so that the list only shrinks unless a
# protected pull request of its own adds a row here, beside risk.py's.
EXCLUDED_AS_BUILT = {("scripts/test_safe_push.py", "assets/*.png"):
                     "docs/decisions/2026-11-12-ci-scope-1a.md"}
# A line of a decisions entry that records a run of the whole landing tool's suite on main,
# sharded: the compensating run that GATE_READ_EXCLUDED_LIVE needs (G-FLIP).
SUITE_RUN = re.compile(r"^- Whole-suite run on main: ([0-9a-f]{40}), (\d{4}-\d\d-\d\dT\d\d:\d\d:"
                       r"\d\dZ), (\d+) of \3 shards green\.$", re.M)


def constants(tree: ast.Module) -> dict:
    """A module's constants, read by `ast` alone: each name bound once at the top level to a
    string, an f-string of other such names, or a tuple or list of strings, in which a
    starred generator of an f-string `<folder>/{...}` stands for `<folder>/*`."""
    found: dict = {}

    def value(node):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return node.value
        if isinstance(node, ast.JoinedStr):
            parts = [value(part.value) if isinstance(part, ast.FormattedValue)
                     else part.value for part in node.values]
            return "".join(parts) if all(isinstance(p, str) for p in parts) else None
        if isinstance(node, ast.Name):
            return found.get(node.id)
        if isinstance(node, (ast.Tuple, ast.List)):
            items = []
            for element in node.elts:
                if isinstance(element, ast.Starred):
                    inner = element.value
                    if isinstance(inner, ast.Call) and inner.args:
                        inner = inner.args[0]
                    template = getattr(inner, "elt", None)
                    if not isinstance(template, ast.JoinedStr) or not template.values \
                            or not isinstance(template.values[0], ast.Constant) \
                            or not str(template.values[0].value).endswith("/"):
                        return None
                    items.append(template.values[0].value + "*")
                else:
                    item = value(element)
                    if not isinstance(item, str):
                        return None
                    items.append(item)
            return tuple(items)
        return None

    for statement in tree.body:
        if isinstance(statement, ast.Assign) and len(statement.targets) == 1 \
                and isinstance(statement.targets[0], ast.Name):
            got = value(statement.value)
            if got is not None:
                found[statement.targets[0].id] = got
    return found


def gate_reads(texts: dict[str, str]) -> list[tuple[str, int, frozenset | None, str]]:
    """Every read of the two files' text (by path in `texts`): (file, line, the paths it
    takes, or None when the check cannot resolve it, and its text). A read is a `HERE /` or
    `SOURCE /` path (HERE.parent is SOURCE) whose operands are strings, safe_push's module
    constants, names bound in its function to one of them, or the target of a `for` over a
    tuple of strings or such a constant; on which `.glob(pattern)` is `<path>/<pattern>`
    and shutil.copytree `<path>/*`. And each string under scripts/ or tests/ in a list or
    tuple given first to a subprocess call, a program the file runs."""
    own = {path: ast.parse(text, filename=path) for path, text in texts.items()}
    safe_push = constants(own["scripts/safe_push.py"]) if "scripts/safe_push.py" in own else {}
    reads = []
    for path, tree in own.items():
        module = constants(tree)
        parents = {child: node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}

        def bindings(node) -> dict:
            """The names bound in the function holding `node`: by assignment, and as a loop's
            target, each to the values it may take (a tuple)."""
            scope = node
            while scope in parents and not isinstance(scope, (ast.FunctionDef,
                                                               ast.AsyncFunctionDef)):
                scope = parents[scope]
            bound: dict = {}
            for inner in ast.walk(scope):
                if isinstance(inner, ast.For) and isinstance(inner.target, ast.Name):
                    got = operand(inner.iter, {})
                    if got is not None:
                        bound[inner.target.id] = got
                elif isinstance(inner, ast.Assign) and len(inner.targets) == 1 \
                        and isinstance(inner.targets[0], ast.Name):
                    got = operand(inner.value, {})
                    if got is not None:
                        bound.setdefault(inner.targets[0].id, got)
            return bound

        def operand(node, bound) -> tuple | None:
            """The strings an operand may be, or None."""
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                return (node.value,)
            if isinstance(node, (ast.Tuple, ast.List)) and all(
                    isinstance(e, ast.Constant) and isinstance(e.value, str) for e in node.elts):
                return tuple(e.value for e in node.elts)
            if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) \
                    and node.value.id == "safe_push" and node.attr in safe_push:
                got = safe_push[node.attr]
                return got if isinstance(got, tuple) else (got,)
            if isinstance(node, ast.Name):
                if node.id in bound:
                    return bound[node.id]
                if node.id in module and node.id not in BASES:
                    got = module[node.id]
                    return got if isinstance(got, tuple) else (got,)
            return None

        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) \
                    and isinstance(node.func.value, ast.Name) \
                    and node.func.value.id == "subprocess" and node.args \
                    and isinstance(node.args[0], (ast.List, ast.Tuple)):
                for element in node.args[0].elts:
                    if isinstance(element, ast.Constant) and isinstance(element.value, str) \
                            and element.value.startswith(("scripts/", "tests/")):
                        reads.append((path, node.lineno, frozenset([element.value]),
                                      element.value))
            if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div)) or (
                    isinstance(parents.get(node), ast.BinOp)
                    and isinstance(parents[node].op, ast.Div) and parents[node].left is node):
                continue
            chain, left = [], node
            while isinstance(left, ast.BinOp) and isinstance(left.op, ast.Div):
                chain.insert(0, left.right)
                left = left.left
            if isinstance(left, ast.Attribute) and left.attr == "parent" \
                    and isinstance(left.value, ast.Name) and left.value.id == "HERE":
                base = ""
            elif isinstance(left, ast.Name) and left.id in BASES:
                base = BASES[left.id]
            else:
                continue
            bound = bindings(node)
            options = [operand(part, bound) for part in chain]
            text = ast.unparse(node)
            if any(option is None for option in options):
                reads.append((path, node.lineno, None, text))
                continue
            paths = {base}
            for option in options:
                paths = {"/".join(p for p in (prefix, item) if p)
                         for prefix in paths for item in option}
            above = parents.get(node)
            if isinstance(above, ast.Attribute) and above.attr == "glob" \
                    and isinstance(parents.get(above), ast.Call) and parents[above].args:
                pattern = operand(parents[above].args[0], bound)
                if pattern is None:
                    reads.append((path, node.lineno, None, text))
                    continue
                paths = {f"{p}/{g}" for p in paths for g in pattern}
            elif isinstance(above, ast.Call) and ast.unparse(above.func) == "shutil.copytree" \
                    and above.args and above.args[0] is node:
                paths = {f"{p}/*" for p in paths}
            reads.append((path, node.lineno, frozenset(paths), text))
    return reads


def covered(path: str, inputs: set[str]) -> bool:
    """Whether a read's path is among the inputs: a file, or a folder whose files are."""
    return risk.reaches(path, inputs) or risk.reaches(path + "/x", inputs)


def gate_read_problems(reads, inputs: set[str], rows) -> list[str]:
    """What the reads and GATE_READ_EXCLUDED's rows break: a read the check cannot resolve
    that no row names; a path read that is neither among the inputs nor a row's path on its
    lines; and a row with no reason, a row whose lines hold no read, and a row whose lines no
    longer read its path (F-N4, F-EXCL, G-STALE)."""
    problems = []
    for file, line, paths, text in reads:
        named = [row for row in rows if row[0] == file and row[1] <= line <= row[2]]
        if paths is None:
            if not named:
                problems.append(f"{file}:{line} reads {text}, which the check cannot resolve: "
                                "name it in gate_inputs, or its line in GATE_READ_EXCLUDED")
            continue
        for path in sorted(paths):
            if not covered(path, inputs) and not any(
                    fnmatch.fnmatchcase(path, row[3]) for row in named):
                problems.append(f"gate_inputs lacks {path}, which {file}:{line} executes "
                                "or loads")
    for row in rows:
        file, first, last, path, reason = row
        if not isinstance(reason, str) or not reason.strip():
            problems.append(f"GATE_READ_EXCLUDED's row {path} gives no reason")
        held = [read for read in reads if read[0] == file and first <= read[1] <= last]
        if not held:
            problems.append(f"GATE_READ_EXCLUDED's row {path} names {file} {first} to {last}, "
                            "which holds no HERE / or SOURCE / read")
        elif not any(read[2] and path in read[2] for read in held):
            problems.append(f"GATE_READ_EXCLUDED's row {path} is stale: {file} {first} to "
                            f"{last} no longer reads it")
    return problems


TRACER = r'''
import atexit, os, runpy, sys
out, root, script = sys.argv[1], os.path.realpath(sys.argv[2]), sys.argv[3]
seen = set()
def hook(event, args):
    if event == "open" and isinstance(args[0], (str, bytes, os.PathLike)):
        p = os.path.realpath(os.path.join(os.getcwd(), os.fsdecode(args[0])))
        if p.startswith(root + os.sep):
            seen.add(os.path.relpath(p, root))
    elif event == "subprocess.Popen" and isinstance(args[1], (list, tuple)):
        argv = [os.fsdecode(a) for a in args[1]]
        if argv and os.path.basename(argv[0]) == "git" and ({"cat-file", "show"} & set(argv)):
            seen.update(a.split(":", 1)[1] for a in argv[1:] if ":" in a and a[:1] != "-")
def write():
    with open(out, "w", encoding="utf-8") as f:
        f.write("".join(p + "\n" for p in sorted(seen)))
sys.addaudithook(hook)
atexit.register(write)
sys.argv = [script]
sys.path.insert(0, os.path.dirname(os.path.abspath(script)))
runpy.run_path(script, run_name="__main__")
'''
# The guards safe_push.py runs on every commit it checks, the tests' good commits among them,
# with --_test-skip-checks too (guard_fidelity and guard_generated): the code under test that
# reads the tree at runtime (docs/reports/what-the-checks-read.md measured the checks so).
GUARDS = ("scripts/check_fidelity.py", "scripts/render.py")
TRACED: dict = {}


def traced(root: Path = ROOT) -> dict[str, set[str]]:
    """The tree's paths each guard opens at runtime, or names to `git cat-file` or `git
    show`, run once each under an audit hook in a clone of `root` at HEAD (sharing its
    objects, writing nothing to it), each required to pass."""
    if root not in TRACED:
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp).resolve()
            env = git_environment(temp)
            head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, env=env,
                                  capture_output=True, text=True, check=True).stdout.strip()
            clone = temp / "clone"
            for args in (["clone", "-q", "--shared", "--no-checkout", str(root), str(clone)],
                         ["-C", str(clone), "checkout", "-q", "--detach", head]):
                subprocess.run(["git", *args], env=env, capture_output=True, check=True)
            (temp / "tracer.py").write_text(TRACER, encoding="utf-8")
            found = {}
            for guard in GUARDS:
                out = temp / (Path(guard).stem + ".txt")
                done = subprocess.run([sys.executable, "-I", str(temp / "tracer.py"), str(out),
                                       str(clone), guard], cwd=clone, env=env,
                                      capture_output=True, text=True)
                if done.returncode != 0:
                    raise AssertionError(f"the trace could not run {guard} (exit "
                                         f"{done.returncode}): {done.stdout[-400:]}"
                                         f"{done.stderr[-400:]}")
                found[guard] = set(out.read_text(encoding="utf-8").split("\n")) - {""}
            TRACED[root] = found
    return TRACED[root]


def opened_problems(rows, opened: dict[str, set[str]]) -> list[str]:
    """Each row whose path the trace shows the code under test opening (G-OPENED)."""
    problems = []
    for row in rows:
        for guard, paths in sorted(opened.items()):
            hit = sorted(p for p in paths if fnmatch.fnmatchcase(p, row[3]))
            if hit:
                problems.append(f"GATE_READ_EXCLUDED's row {row[3]}: the code under test opens "
                                f"{hit[0]} at runtime ({guard}, as safe_push.py runs it): it is "
                                "no fixture data, and stays in the gate's reach")
                break
    return problems


def added_problems(rows, root: Path = ROOT) -> list[str]:
    """Each row beyond EXCLUDED_AS_BUILT, or whose decisions entry does not name its path and
    this test (G-ADD)."""
    problems = []
    for row in rows:
        entry = EXCLUDED_AS_BUILT.get((row[0], row[3]))
        text = (root / entry).read_text(encoding="utf-8") if entry and (root / entry).is_file() \
            else ""
        if entry is None or row[3] not in text or "tests/test_risk.py" not in text:
            problems.append(f"GATE_READ_EXCLUDED gains {row[3]}: a row is added only by its own "
                            "protected pull request, which names it in tests/test_risk.py's "
                            "EXCLUDED_AS_BUILT with a decisions entry citing this test")
    return problems


def live_problems(live, grounds, root: Path = ROOT) -> list[str]:
    """GATE_READ_EXCLUDED_LIVE: False, or True with grounds, a decisions entry recording two
    or more runs of the whole suite on main, sharded, each green, at most six hours apart
    (G-FLIP)."""
    if live is False:
        return []
    if live is not True:
        return [f"GATE_READ_EXCLUDED_LIVE is {live!r}, neither True nor False"]
    path = root / grounds if isinstance(grounds, str) and grounds.startswith(
        "docs/decisions/") else None
    runs = SUITE_RUN.findall(path.read_text(encoding="utf-8")) if path and path.is_file() else []
    import datetime
    stamps = sorted(datetime.datetime.strptime(stamp, "%Y-%m-%dT%H:%M:%SZ")
                    for _, stamp, _ in runs)
    if len(stamps) < 2 or any((b - a).total_seconds() > 6 * 3600
                              for a, b in zip(stamps, stamps[1:])):
        return ["GATE_READ_EXCLUDED_LIVE is True, but its grounds cite no recorded runs of the "
                "whole suite on main, every six hours at most (GATE_READ_EXCLUDED_GROUNDS)"]
    return []


def head_texts(root: Path = ROOT) -> dict[str, str]:
    return {path: (root / path).read_text(encoding="utf-8") for path in GATE_FILES}


class GateCommand(Repo):
    """`--diff`'s gate on a repository of the test's own, shaped as the landing tool is: its
    two files, what they import, and what they run or read (L3)."""

    FILES = {
        "scripts/safe_push.py": "import sys\nimport heath\n",
        "scripts/test_safe_push.py": ("import sys\nfrom pathlib import Path\n"
                                      "HERE = Path(__file__).resolve().parent\n"
                                      "sys.path.insert(0, str(HERE))\n"
                                      "import safe_push\nimport render\n"),
        "scripts/render.py": "import check_style\n",
        "scripts/check_style.py": "import re\n",
        "scripts/heath.py": "import os\n",
        "scripts/check_paths.py": "import os\n",
        "scripts/check_links.py": "import os\n",
        "scripts/install_hooks.sh": "#!/bin/sh\n",
        "scripts/check_release_gate.py": "import json\n",
        "tests/test_release_gate.py": ("import sys\nfrom pathlib import Path\n"
                                       "ROOT = Path(__file__).resolve().parents[1]\n"
                                       "sys.path.insert(0, str(ROOT / 'scripts'))\n"
                                       "import check_release_gate\n"),
        "tests/model/run.py": "import search\n",
        "tests/model/search.py": "import math\n",
        "tests/model/derived.py": "import math\n",
        "README.md": "A reader's edition.\n",
        "facts.json": "{}\n",
        "AGENTS.md": "For agents.\n",
        "docs/STYLE.md": "The style.\n",
        "assets/logo.png": "an image\n",
        ".github/workflows/ci.yml": "name: CI\n",
    }

    def gate(self, head, base=None):
        """The gate `--diff --github-output` writes, and the line it prints."""
        output = self.temp / "gate-output"
        output.write_text("", encoding="utf-8")
        done = self.risk("--diff", base or self.base, head, "--github-output",
                         env=dict(self.env, GITHUB_OUTPUT=str(output)))
        self.assertEqual(done.returncode, 0, done.stderr)
        values = dict(line.split("=", 1)
                      for line in output.read_text(encoding="utf-8").splitlines())
        line = [text for text in done.stdout.splitlines() if text.startswith("gate tests: ")]
        self.assertEqual(len(line), 1, done.stdout)
        print(f"  {self.id().split('.')[-1]}: gate={values['gate']}; {line[0]}")
        return values["gate"], line[0]

    def assertReached(self, head, path, base=None):
        self.assertEqual(self.gate(head, base), (
            "true", f"gate tests: in full, since {path} is among the landing tool's inputs"))

    def assertNotReached(self, head, base=None):
        self.assertEqual(self.gate(head, base), (
            "false", "gate tests: pass at once, since the change touches none of the landing "
                     "tool's inputs"))

    def test_L3_g1_the_landing_tool_reaches_it(self):
        self.assertReached(self.commit({"scripts/safe_push.py": "import sys\nimport heath\n#\n"}),
                           "scripts/safe_push.py")

    def test_L3_g2_a_document_outside_the_inputs_does_not(self):
        # Round 2 named README.md; R3.F's F-README puts it in the reach (test_F_README), so
        # the case is run on a document the tests never read.
        self.assertNotReached(self.commit({"docs/STYLE.md": "The style, changed.\n"}))

    def test_L3_g3_an_import_of_the_landing_tool_reaches_it(self):
        self.assertReached(self.commit({"scripts/heath.py": "import os\n#\n"}), "scripts/heath.py")

    def test_L3_g5_the_model_s_harness_reaches_it(self):
        self.assertReached(self.commit({"tests/model/run.py": "import search\n#\n"}),
                           "tests/model/run.py")

    def test_L3_g6_install_hooks_reaches_it(self):
        self.assertReached(self.commit({"scripts/install_hooks.sh": "#!/bin/sh\n#\n"}),
                           "scripts/install_hooks.sh")

    def test_L3_g7_check_paths_reaches_it(self):
        self.assertReached(self.commit({"scripts/check_paths.py": "import os\n#\n"}),
                           "scripts/check_paths.py")

    def test_L3_g8_a_deletion_reaches_it_by_the_base_s_inputs(self):
        self.assertReached(self.commit({}, removed=["scripts/install_hooks.sh"]),
                           "scripts/install_hooks.sh")
        # And a file only the base's import scan reaches: at the head nothing imports it.
        base = self.commit({"scripts/safe_push.py": "import sys\nimport heath\nimport extra\n",
                            "scripts/extra.py": "import os\n"})
        self.git("rm", "-q", "--", "scripts/extra.py")
        (self.root / "scripts/safe_push.py").write_text("import sys\nimport heath\n")
        head = self.commit({})
        self.assertNotIn("scripts/extra.py", risk.gate_inputs(head, str(self.root))[0])
        self.assertReached(head, "scripts/extra.py", base=base)

    def test_L3_g9_a_rename_reaches_it_at_both_ends(self):
        self.git("mv", "scripts/check_paths.py", "scripts/check_paths2.py")
        head = self.commit({})
        self.assertReached(head, "scripts/check_paths.py")
        # The new name alone is outside the inputs: the old one reaches them.
        self.assertFalse(risk.reaches("scripts/check_paths2.py",
                                      risk.gate_inputs(head, str(self.root))[0]))

    def test_L3_g10_check_links_does_not(self):
        self.assertNotReached(self.commit({"scripts/check_links.py": "import os\n#\n"}))

    def test_L3_g11_any_file_of_the_model_s_harness_reaches_it(self):
        self.assertReached(self.commit({"tests/model/derived.py": "import math\n#\n"}),
                           "tests/model/derived.py")

    def test_L3_b7_a_new_import_of_safe_push_is_among_the_inputs_at_the_head(self):
        self.commit({"scripts/foo.py": "import os\n"})
        before = self.git("rev-parse", "HEAD").strip()
        head = self.commit({"scripts/safe_push.py": "import sys\nimport heath\nimport foo\n"})
        self.assertNotIn("scripts/foo.py", risk.gate_inputs(before, str(self.root))[0])
        self.assertIn("scripts/foo.py", risk.gate_inputs(head, str(self.root))[0])
        later = self.commit({"scripts/foo.py": "import os\n#\n"})
        self.assertReached(later, "scripts/foo.py", base=head)

    def test_L3_b8_an_unparsed_test_file_reaches_it_for_every_change(self):
        broken = self.commit({"scripts/test_safe_push.py": "def (:\n"})
        head = self.commit({"docs/STYLE.md": "The style, changed.\n"})
        gate, line = self.gate(head, base=broken)
        self.assertEqual(gate, "true")
        self.assertTrue(line.startswith("gate tests: in full, since scripts/test_safe_push.py, "
                                        "which the landing tool's tests read, cannot be read "
                                        "(it does not parse"), line)

    def test_F_N3_UNREAD_an_unresolved_sys_path_folder_reaches_it_for_every_change(self):
        unread = self.commit({"scripts/heath.py": "import sys\nsys.path.insert(0, sys.argv[1])\n"})
        head = self.commit({"docs/STYLE.md": "The style, changed.\n"})
        gate, line = self.gate(head, base=unread)
        self.assertEqual(gate, "true")
        self.assertIn("scripts/heath.py, which the landing tool's tests read, cannot be read "
                      "(line 2 names a folder for sys.path that the reader cannot resolve", line)

    def test_F_N3_RG_the_release_gate_is_found_through_its_insertion(self):
        # The fixture's GATE_EXECUTED without the release gate: the import scan finds it, in
        # scripts/, by tests/test_release_gate.py's own sys.path.insert; without that line,
        # the import resolves in tests/ alone, where no such file is.
        rows = tuple(row for row in risk.GATE_EXECUTED if row[0] != "scripts/check_release_gate.py")
        with mock.patch.object(risk, "GATE_EXECUTED", rows):
            self.assertIn("scripts/check_release_gate.py",
                          risk.gate_inputs(self.base, str(self.root))[0])
            plain = self.commit({"tests/test_release_gate.py": "import check_release_gate\n"})
            self.assertNotIn("scripts/check_release_gate.py",
                             risk.gate_inputs(plain, str(self.root))[0])
        imported, why = risk.imports_of("tests/test_release_gate.py",
                                        (ROOT / "tests/test_release_gate.py").read_text(),
                                        {"", "scripts", "tests"})
        self.assertIsNone(why)
        self.assertIn("scripts/check_release_gate.py", imported)
        self.assertIn("scripts/safe_push.py", imported)
        print("  F-N3-RG: tests/test_release_gate.py's sys.path.insert of scripts/ puts "
              "scripts/check_release_gate.py among the gate's inputs; without it, it is not")

    def test_F_README_F_FACTS_F_ASSETS(self):
        for label, files, path in (("F-README", {"README.md": "Changed.\n"}, "README.md"),
                                   ("F-FACTS", {"facts.json": "{\"a\": 1}\n"}, "facts.json"),
                                   ("F-ASSETS", {"assets/new.png": "a new image\n"},
                                    "assets/new.png")):
            with self.subTest(label):
                before = self.git("rev-parse", "HEAD").strip()
                self.assertReached(self.commit(files), path, base=before)

    def test_G_LIVE_an_excluded_path_stays_in_reach_while_the_switch_is_off(self):
        head = self.commit({"assets/new.png": "a new image\n"})
        self.assertReached(head, "assets/new.png")
        self.assertFalse(risk.GATE_READ_EXCLUDED_LIVE)
        # Planted: the switch on, and the excluded path alone leaves the reach.
        with mock.patch.object(risk, "GATE_READ_EXCLUDED_LIVE", True):
            reached, _, _ = risk.gate(self.base, head, cwd=str(self.root))
        self.assertFalse(reached)
        print("  G-LIVE: with GATE_READ_EXCLUDED_LIVE False, a new assets/*.png reaches the "
              "gate; planted True, it does not")


class GroupLaneSwitch(unittest.TestCase):
    """`--group-lane` (L1.0): off as built; on only for a condition it names."""

    def run_with(self, value):
        """risk.py with GROUP_LANE set to `value` (a Python expression), run --group-lane."""
        text = RISK.read_text(encoding="utf-8")
        self.assertEqual(text.count("\nGROUP_LANE = None\n"), 1)
        with tempfile.TemporaryDirectory() as temp:
            copy = Path(temp) / "risk.py"
            copy.write_text(text.replace("\nGROUP_LANE = None\n", f"\nGROUP_LANE = {value}\n"))
            return subprocess.run([sys.executable, "-I", str(copy), "--group-lane"],
                                  capture_output=True, text=True)

    def test_off_as_built(self):
        done = subprocess.run([sys.executable, "-I", str(RISK), "--group-lane"],
                              capture_output=True, text=True)
        self.assertEqual((done.returncode, done.stdout), (0, "group-lane: off\n"))
        self.assertIsNone(risk.GROUP_LANE)

    def test_on_for_a_named_condition(self):
        for value in ("L6", "GROUP-VERIFY"):
            with self.subTest(value):
                done = self.run_with(repr(value))
                self.assertEqual((done.returncode, done.stdout),
                                 (0, f"group-lane: on, because {value}\n"))

    def test_L1_s4_any_other_value_exits_2(self):
        for value in ('"L2"', '"L4"', "True", '""'):
            with self.subTest(value):
                done = self.run_with(value)
                self.assertEqual((done.returncode, done.stdout), (2, ""))
                self.assertIn(f"risk.py: GROUP_LANE is {value.replace(chr(34), chr(39))}, "
                              "neither None, L6 nor GROUP-VERIFY", done.stderr)
        print("  L1.s4: GROUP_LANE 'L2': --group-lane exits 2: "
              + self.run_with('"L2"').stderr.strip())


class GateReads(unittest.TestCase):
    """The audited reads of the landing tool's two files (F-N4), and GATE_READ_EXCLUDED's
    rows held by the same check and by the trace of the code under test (R3.G, R3.H)."""

    @classmethod
    def setUpClass(cls):
        cls.texts = head_texts()
        cls.reads = gate_reads(cls.texts)
        cls.inputs, cls.unread = risk.gate_inputs("HEAD", str(ROOT))

    def problems(self, texts=None, rows=None):
        return gate_read_problems(gate_reads(texts) if texts else self.reads, self.inputs,
                                  risk.GATE_READ_EXCLUDED if rows is None else rows)

    def planted(self, file, before, after, count=1):
        texts = dict(self.texts)
        self.assertEqual(texts[file].count(before), count, before)
        texts[file] = texts[file].replace(before, after, 1)
        return texts

    def line_of(self, texts, file, needle):
        return next(n for n, line in enumerate(texts[file].splitlines(), 1) if needle in line)

    def test_F_AST_BASE_every_read_of_the_head_resolves_into_the_inputs(self):
        self.assertEqual(self.unread, {})
        self.assertEqual(self.problems(), [])
        resolved = sum(1 for read in self.reads if read[2] is not None)
        print(f"  F-AST-BASE: {resolved} of {len(self.reads)} reads of the two files resolved, "
              f"each among gate_inputs or a GATE_READ_EXCLUDED row")

    def test_F_AST_BASE_at_the_base_commit(self):
        # The two files as public main held them before this change (b34df227's, the same
        # at 640b0d2f), against the head's inputs.
        texts = {}
        for path in GATE_FILES:
            done = subprocess.run(["git", "show", f"640b0d2f7a2c3c9d86f0a95e1e4a9348f53fd13c:{path}"],
                                  cwd=ROOT, capture_output=True, text=True)
            if done.returncode != 0:
                self.skipTest("the base commit is not in this repository")
            texts[path] = done.stdout
        self.assertEqual(gate_read_problems(gate_reads(texts), self.inputs, ()), [])

    def test_F_AST_NEW_a_new_read_outside_the_inputs_fails_naming_it(self):
        texts = self.planted("scripts/test_safe_push.py", "\nTIMES = HERE /",
                             '\nSTYLE = (SOURCE / "docs" / "STYLE.md").read_text()\nTIMES = HERE /')
        line = self.line_of(texts, "scripts/test_safe_push.py", 'STYLE = (SOURCE')
        self.assertEqual(self.problems(texts), [
            f"gate_inputs lacks docs/STYLE.md, which scripts/test_safe_push.py:{line} executes "
            "or loads"])
        print(f"  F-AST-NEW: {self.problems(texts)[0]}")

    def test_F_AST_UNRESOLVED_a_read_it_cannot_resolve_fails_naming_its_line(self):
        texts = self.planted("scripts/test_safe_push.py", "\nTIMES = HERE /",
                             "\nODD = SOURCE / os.environ['ODD']\nTIMES = HERE /")
        line = self.line_of(texts, "scripts/test_safe_push.py", "ODD = SOURCE")
        print(f"  F-AST-UNRESOLVED: {self.problems(texts)[0]}")
        self.assertEqual(self.problems(texts), [
            f"scripts/test_safe_push.py:{line} reads SOURCE / os.environ['ODD'], which the "
            "check cannot resolve: name it in gate_inputs, or its line in GATE_READ_EXCLUDED"])
        # Named by a row, the line passes.
        row = ("scripts/test_safe_push.py", line, line, "anything", "a reason")
        self.assertEqual([p for p in self.problems(texts, (*risk.GATE_READ_EXCLUDED, row))
                          if "cannot resolve" in p], [])

    def test_L3_b9_a_program_run_outside_the_inputs_fails_naming_it(self):
        texts = self.planted("scripts/test_safe_push.py", "\nTIMES = HERE /",
                             '\nNEW = subprocess.run([sys.executable, "scripts/new_tool.py"])'
                             "\nTIMES = HERE /")
        line = self.line_of(texts, "scripts/test_safe_push.py", "scripts/new_tool.py")
        problems = self.problems(texts)
        self.assertEqual(problems, [f"gate_inputs lacks scripts/new_tool.py, which "
                                    f"scripts/test_safe_push.py:{line} executes or loads"])
        print(f"  L3.b9: {problems[0]}")

    def test_F_EXCL_a_row_with_no_reason_or_no_read_on_its_lines_fails(self):
        (file, first, last, path, _), = risk.GATE_READ_EXCLUDED
        self.assertEqual(self.problems(rows=((file, first, last, path, ""),)),
                         [f"GATE_READ_EXCLUDED's row {path} gives no reason"])
        self.assertEqual(self.problems(rows=((file, 1, 1, path, "a reason"),)), [
            f"GATE_READ_EXCLUDED's row {path} names {file} 1 to 1, which holds no HERE / or "
            "SOURCE / read"])
        print("  F-EXCL: refused: a row with no reason, and a row on a line with no read")

    def test_G_STALE_a_row_whose_line_no_longer_reads_its_path_fails(self):
        (file, first, last, path, reason), = risk.GATE_READ_EXCLUDED
        texts = self.planted(file, '(SOURCE / "assets").glob("*.png")',
                             '(SOURCE / "assets").glob("*.jpg")')
        self.assertEqual(self.problems(texts), [
            "gate_inputs lacks assets/*.jpg, which scripts/test_safe_push.py:"
            f"{first} executes or loads",
            f"GATE_READ_EXCLUDED's row {path} is stale: {file} {first} to {last} no longer "
            "reads it"])
        print(f"  G-STALE: {self.problems(texts)[1]}")

    def test_G2_the_rows_as_built(self):
        self.assertEqual([(row[0], row[3]) for row in risk.GATE_READ_EXCLUDED],
                         [("scripts/test_safe_push.py", "assets/*.png")])
        self.assertEqual(added_problems(risk.GATE_READ_EXCLUDED), [])
        self.assertEqual(live_problems(risk.GATE_READ_EXCLUDED_LIVE,
                                       risk.GATE_READ_EXCLUDED_GROUNDS), [])
        self.assertIs(risk.GATE_READ_EXCLUDED_LIVE, False)
        # Every row's path stays in the gate's reach while the switch is off (G-LIVE).
        for row in risk.GATE_READ_EXCLUDED:
            self.assertTrue(covered(row[3], self.inputs), row)

    def test_G_ADD_a_row_added_without_its_own_grounds_is_refused(self):
        row = ("scripts/test_safe_push.py", 1, 1, "AGENTS.md", "a reason")
        self.assertEqual(added_problems((*risk.GATE_READ_EXCLUDED, row)), [
            "GATE_READ_EXCLUDED gains AGENTS.md: a row is added only by its own protected pull "
            "request, which names it in tests/test_risk.py's EXCLUDED_AS_BUILT with a decisions "
            "entry citing this test"])
        print(f"  G-ADD: {added_problems((*risk.GATE_READ_EXCLUDED, row))[0]}")

    def test_G_FLIP_the_switch_on_needs_recorded_runs_of_the_whole_suite(self):
        refused = ["GATE_READ_EXCLUDED_LIVE is True, but its grounds cite no recorded runs of the "
                   "whole suite on main, every six hours at most (GATE_READ_EXCLUDED_GROUNDS)"]
        self.assertEqual(live_problems(True, None), refused)
        self.assertEqual(live_problems("yes", None),
                         ["GATE_READ_EXCLUDED_LIVE is 'yes', neither True nor False"])
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "docs/decisions").mkdir(parents=True)
            entry = root / "docs/decisions/grounds.md"
            run = "- Whole-suite run on main: {}, {}, 12 of 12 shards green.\n"
            for text, expected in (
                    ("No runs.\n", refused),
                    (run.format("a" * 40, "2026-12-01T00:00:00Z"), refused),
                    (run.format("a" * 40, "2026-12-01T00:00:00Z")
                     + run.format("b" * 40, "2026-12-01T09:00:00Z"), refused),
                    (run.format("a" * 40, "2026-12-01T00:00:00Z")
                     + run.format("b" * 40, "2026-12-01T06:00:00Z"), [])):
                with self.subTest(text=text):
                    entry.write_text(text)
                    self.assertEqual(live_problems(True, "docs/decisions/grounds.md", root),
                                     expected)
        print(f"  G-FLIP: {refused[0]}")


class GateTrace(unittest.TestCase):
    """The trace of the code under test (R3.G G1, R3.H): check_fidelity.py and render.py,
    as safe_push.py runs them on every commit it checks, under an audit hook. A row of
    GATE_READ_EXCLUDED whose path they open is refused by name."""

    @classmethod
    def setUpClass(cls):
        cls.opened = traced()

    def row(self, path, line=None):
        return ("scripts/test_safe_push.py", line or 1, line or 1, path, "a planted row")

    def test_G2_assets_png_is_never_opened(self):
        self.assertEqual(opened_problems(risk.GATE_READ_EXCLUDED, self.opened), [])
        self.assertTrue(any(p.startswith("assets/") for ps in self.opened.values() for p in ps),
                        "the trace sees the assets folder's other files")
        print("  G2: assets/*.png: never opened by "
              + " or ".join(sorted(self.opened)) + "; the row stands")

    def test_G_AGENTS_R3_H_a_planted_AGENTS_md_row_is_refused(self):
        problems = opened_problems([self.row("AGENTS.md")], self.opened)
        self.assertEqual(len(problems), 1)
        self.assertTrue(problems[0].startswith("GATE_READ_EXCLUDED's row AGENTS.md: the code "
                                               "under test opens AGENTS.md at runtime"), problems)
        for guard in GUARDS:
            self.assertIn("AGENTS.md", self.opened[guard], guard)
        print(f"  G-AGENTS (R3.H): {problems[0]}")

    def test_G_OPENED_a_planted_row_for_review_III_16_toml_is_refused(self):
        for path in ("review/III/16.toml", "Elements/BookIII/Prop01.lean"):
            with self.subTest(path):
                problems = opened_problems([self.row(path)], self.opened)
                self.assertEqual(len(problems), 1)
                self.assertTrue(problems[0].startswith(
                    f"GATE_READ_EXCLUDED's row {path}: the code under test opens {path} at "
                    "runtime"), problems)
                print(f"  G-OPENED: {problems[0]}")

    def test_G_FIG_the_idea_figure_stays_in_reach(self):
        problems = opened_problems([self.row("figures/I/01-idea.svg")], self.opened)
        self.assertEqual(len(problems), 1)
        self.assertIn("scripts/render.py", problems[0])
        print(f"  G-FIG: {problems[0]}")

    def test_G1_the_nine_paths(self):
        # G1's table, as the trace reads it at this head: every path but assets/*.png opened.
        verdicts = {path: bool(opened_problems([self.row(path)], self.opened))
                    for path in ("README.md", "facts.json", "docs/FORMALIZATION.md",
                                 "docs/PROGRAM.md", "figures/I/01-idea.svg",
                                 "Elements/BookIII/Prop01.lean", "review/III/16.toml",
                                 "AGENTS.md", "assets/*.png")}
        self.assertEqual([path for path, opened in verdicts.items() if not opened],
                         ["assets/*.png"])


if __name__ == "__main__":
    unittest.main()
