#!/usr/bin/env python3
"""scripts/risk.py, the risk class of a change: its table's first-match order, R5 for a
path no rule names, a change's highest class, `--diff` on a repository of the test's own,
and `--audit` over this repository's tracked files.

    python3 -I tests/test_risk.py

Standard library and Git only; no Lean or network. Each `--diff` case runs in a Git
repository of its own, read with no configuration but its own. scripts/negative_tests.py
runs it beside the decision entry regressions, so CI's `negative` job runs it on every
pull request of class R3 and above (a change to scripts/risk.py is R5), on every push, and
on the cadence.
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

    def test_formal_model_inputs_are_R4_or_above(self):
        # CI's formal-model job reads the class alone, and runs for R4 and R5: every file of
        # the model, the lock its hash ties, and the check the job runs must reach it.
        for path in ("model/lock.sha256", "model/Model.lean", "model/Check/Generated.lean",
                     "model/lakefile.toml", "model/lake-manifest.json",
                     "Certificate/axioms.lock", "scripts/check_model_kernel.py",
                     ".github/workflows/ci.yml"):
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


class Command(unittest.TestCase):
    """The script itself, on a repository of the test's own."""

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
        self.base = self.commit({"README.md": "A reader's edition.\n",
                                 ".github/workflows/ci.yml": "name: CI\n",
                                 "docs/a b/notes.md": "Notes.\n"})

    def git(self, *args):
        done = subprocess.run(["git", *args], cwd=self.root, env=self.env,
                              capture_output=True, text=True)
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

    def risk(self, *args, env=None):
        return subprocess.run([sys.executable, "-I", str(RISK), *args], cwd=self.root,
                              env=env or self.env, capture_output=True, text=True)

    def diff_class(self, head, base=None):
        done = self.risk("--diff", base or self.base, head)
        self.assertEqual(done.returncode, 0, done.stderr)
        return done.stdout.splitlines()[0].split()[0], done.stdout

    def test_an_empty_diff_is_R0(self):
        self.assertEqual(self.diff_class(self.base)[0], "R0")
        head = self.commit({})
        cls, out = self.diff_class(head)
        self.assertEqual(cls, "R0")
        self.assertIn("(no file changed)", out)

    def test_a_workflow_change_is_R5(self):
        head = self.commit({"README.md": "Changed.\n",
                            ".github/workflows/ci.yml": "name: CI\non: push\n"})
        cls, out = self.diff_class(head)
        self.assertEqual(cls, "R5")
        self.assertIn("  R5 .github/workflows/ci.yml", out.splitlines())
        self.assertIn("  R0 README.md", out.splitlines())

    def test_a_path_with_a_space_is_one_path(self):
        # Split on white space, the path would give `b/notes.md`, which no rule names: R5.
        head = self.commit({"docs/a b/notes.md": "Notes, changed.\n"})
        cls, out = self.diff_class(head)
        self.assertEqual(cls, "R0", out)
        self.assertIn("  R0 docs/a b/notes.md", out.splitlines())

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
        self.assertEqual(output.read_text(encoding="utf-8"), "earlier=1\nclass=R5\n")
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


class Repository(unittest.TestCase):
    def test_every_tracked_file_has_a_rule(self):
        done = subprocess.run([sys.executable, "-I", str(RISK), "--audit", str(ROOT)],
                              capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)


if __name__ == "__main__":
    unittest.main()
