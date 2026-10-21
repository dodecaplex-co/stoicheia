#!/usr/bin/env python3
"""The cases of scripts/check_paths.py: the standard for file names, types and modes.

    python3 -I tests/test_check_paths.py        # no Lean, no network

Each rule, P1 to P6, is put to paths it must accept and paths it must refuse, through
`findings`, the script's pure function over (mode, path) entries, the model's nine laws
and their lower-case names among them; and every finding, even for a path holding a
newline, is one line of printable ASCII. Then the script itself
is run on throwaway Git repositories, whose faults are planted straight into the index
with `git update-index --add --cacheinfo`, as a case-insensitive disk cannot hold two
files of one name: a case twin of a file and of a folder, an NFC/NFD twin, a space, an
upper-case extension, a symbolic link, a submodule, an executable bit on a seventh file
and one missing from the six, an svg under book/, a misnamed review record, Prop1.lean,
a law of the model named in capitals, lakefile.lean at the root and in model/, a
.gitattributes, a Python keyword, a ".." segment (which Git refuses itself), and a file
renamed with `git mv` to a bad name; an untracked file is not judged, `--rev` judges a
commit's tree and not the index, a tree made with `git mktree` that lists one path twice
is refused, a module planted beside the script (scripts/unicodedata.py and others) never
stands in for the standard library's, explicit Git locations must identify both the
script's worktree and its worktree-specific Git directory, and the repository passes.
CI runs this file first, before the script's own `--self-test`.
"""

import os
import sys

# As in scripts/check_paths.py: a module planted beside this file must not stand in for the
# standard library's, so its folder is taken off sys.path (where -I has not kept it off)
# before any other import, and there is no `from __future__` import, which would read one
# first. The script is loaded from its file, never by putting scripts/ on sys.path, so a
# planted scripts/unicodedata.py cannot stand in either.
sys.path[:] = [p for p in sys.path if os.path.realpath(p or os.curdir)
               != os.path.dirname(os.path.realpath(__file__))]

import importlib.util  # noqa: E402
import shutil  # noqa: E402
import subprocess  # noqa: E402
import tempfile  # noqa: E402
import unittest  # noqa: E402
from pathlib import Path  # noqa: E402
from unittest.mock import patch  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
SCRIPT = REPO / "scripts" / "check_paths.py"
SPEC = importlib.util.spec_from_file_location("check_paths", SCRIPT)
paths = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = paths
SPEC.loader.exec_module(paths)

PLAIN, EXECUTABLE = paths.PLAIN, paths.EXECUTABLE


def entries(*names: str, mode: str = PLAIN) -> list[tuple[str, str]]:
    return [(mode, name) for name in names]


class Rules(unittest.TestCase):
    """Each rule's accepting and refusing cases, through `findings`."""

    def refused(self, rule: int, entries_: list[tuple[str, str]], name: str) -> list[str]:
        found = paths.findings(entries_)
        prefix = f"P{rule} {paths.shown(name)}: "
        self.assertTrue(any(f.startswith(prefix) for f in found),
                        f"{prefix!r} not among {found}")
        return found

    def accepted(self, *entries_: tuple[str, str]) -> None:
        self.assertEqual(paths.findings(list(entries_)), [])

    def test_p1_characters(self):
        for name in ("book/I/Planted page.md", "docs/café.md", "docs/tab\there.md",
                     "docs/new\nline.md", "docs/a+b.md", "docs/a:b.md", "docs/a\\b.md",
                     "docs/a\udcffb.md"):
            with self.subTest(name=name):
                self.refused(1, entries(name), name)
        self.accepted((PLAIN, "docs/reports/acceptance/jev/audit-books-I-II_1.0.md"))

    def test_p1_segments(self):
        for name in ("docs//a.md", "/docs/a.md", "docs/a.md/", "docs/../a.md", "docs/./a.md",
                     "docs/-a.md", "docs/a-/b.md", "docs/a./b.md", "docs/.a.md", ".hidden/a.md",
                     "docs/.github/a.md", "docs/.gitignore/a.md"):
            with self.subTest(name=name):
                self.refused(1, entries(name), name)
        self.accepted((PLAIN, ".github/workflows/ci.yml"), (PLAIN, ".gitignore"),
                      (PLAIN, "model/.gitignore"), (PLAIN, "Staging/.gitkeep"))

    def test_p1_lengths(self):
        segment = "docs/" + "a" * 98 + ".md"            # a segment of 101
        self.refused(1, entries(segment), segment)
        self.accepted((PLAIN, "docs/" + "a" * 97 + ".md"))  # a segment of 100
        long = "docs/" + "/".join(["abcdefghij"] * 14) + "/a.md"   # 163 in all
        self.assertGreater(len(long), paths.MAX_PATH)
        self.refused(1, entries(long), long)
        fits = "docs/" + "/".join(["abcdefghij"] * 13) + "/abcdefghi.md"
        self.assertEqual(len(fits), paths.MAX_PATH)
        self.accepted((PLAIN, fits))

    def test_p1_windows_devices(self):
        for name in ("docs/CON.md", "docs/con.md", "docs/Aux.tar.md", "docs/nul/a.md",
                     "docs/COM1.md", "docs/lpt9.md", "docs/PRN.md", "docs/COM0.md",
                     "docs/lpt0.md", "docs/Com0.tar.md", "docs/LPT0/a.md"):
            with self.subTest(name=name):
                self.refused(1, entries(name), name)
        self.assertEqual(len(paths.DEVICES), 24)    # CON, PRN, AUX, NUL; COM0-9; LPT0-9
        self.accepted((PLAIN, "docs/console.md"), (PLAIN, "docs/COM10.md"),
                      (PLAIN, "docs/LPT10.md"), (PLAIN, "docs/auxiliary.md"),
                      (PLAIN, "docs/com.md"))

    def test_p2_twins(self):
        found = self.refused(2, entries("README.md", "readme.md"), "readme.md")
        self.assertIn("P2 README.md: a case twin of readme.md", "\n".join(found))
        found = self.refused(2, entries("scripts/a.py", "Scripts/json.py"), "Scripts/")
        self.assertIn("(the folder of Scripts/json.py)", "\n".join(found))
        self.refused(2, entries("scripts/a.py", "Scripts/json.py"), "scripts/")
        # An accented e, composed (NFC) and decomposed (NFD): escapes, so no editor merges them.
        self.refused(2, entries("docs/caf\u00e9.md", "docs/cafe\u0301.md"), "docs/cafe\u0301.md")
        self.refused(2, entries("docs/Notes", "docs/notes/a.md"), "docs/notes/")
        self.refused(2, entries("docs/STRASSE.md", "docs/straße.md"), "docs/STRASSE.md")
        self.refused(2, entries("Elements/BookI/Prop01.lean", "Elements/booki/Prop02.lean"),
                     "Elements/booki/")
        self.accepted((PLAIN, "docs/a.md"), (PLAIN, "docs/b.md"), (PLAIN, "docs/a/b.md"))

    def test_p2_a_path_listed_twice(self):
        # A tree made by hand can list one name twice (Git's fsck: duplicateEntries); the
        # entries are judged as listed, so the repeat is seen, whatever the modes.
        found = self.refused(2, entries("README.md", "README.md"), "README.md")
        self.assertIn("P2 README.md: listed 2 times; a tree names a path once", "\n".join(found))
        found = self.refused(2, [(PLAIN, "docs/a.md"), (EXECUTABLE, "docs/a.md"),
                                 (PLAIN, "docs/a.md")], "docs/a.md")
        self.assertIn("P2 docs/a.md: listed 3 times", "\n".join(found))
        self.assertTrue([f for f in found if f.startswith("P6 docs/a.md: ")], found)

    def test_p3_extensions(self):
        for name in ("docs/notes.MD", "docs/notes.Md", "docs/notes.markdown",
                     ".github/workflows/ci.yaml", "assets/page.htm", "docs/notes.txt.bak",
                     "docs/Makefile", "scripts/run", "README.MD", "x.Md", "docs/x.Md",
                     "docs/notes.md.MD", "Elements/BookI/Prop01.Lean", "license",
                     "Lean-toolchain", "docs/LICENSE"):
            with self.subTest(name=name):
                self.refused(3, entries(name), name)
        found = self.refused(3, entries("README.MD"), "README.MD")
        self.assertIn("P3 README.MD: the extension .MD is not in lower case", found)
        # Only the last dot counts, and only an ASCII extension is "not in lower case".
        self.accepted(*entries("docs/notes.MD.md", "docs/v1.2.md", "README.md"))
        found = self.refused(3, entries("docs/a.locK"), "docs/a.locK")
        self.assertFalse([f for f in found if "lower case" in f], found)
        for name in sorted(paths.EXTENSIONLESS):
            with self.subTest(name=name):
                self.assertFalse([f for f in paths.findings(entries(name)) if f.startswith("P3")])

    def test_p4_folders_and_types(self):
        for name in ("book/I/01.svg", "notes/a.md", "notes.txt", "Readme.md", "readme.md",
                     ".gitattributes", ".gitmodules", "docs/.gitignore", "Staging/Sub/.gitkeep",
                     ".gitkeep", "figures/I/01.png", "lakefile.lean", "Elements/a.py",
                     "review/I/01.md", "scripts/notes.md", "Audit/other.py",
                     "Certificate/other.lock", "docs/run.sh", "TRAILING-.md",
                     "DOUBLE--HYPHEN.md", "LOWER-case.md", "A-.md", "README_2.md"):
            with self.subTest(name=name):
                self.refused(4, entries(name), name)
        self.accepted(*entries("README.md", "SECURITY.md", "LICENSE-PROSE.md", "CITATION.cff",
                               "CODE-OF-CONDUCT.md", "A1-B2.md", "Audit/screen.py",
                               "Certificate/axioms.lock", "review/SCHEMA.md"),
                      (EXECUTABLE, "scripts/hooks/pre-push"))

    def test_p5_book_names(self):
        for name in ("review/I/1.toml", "review/I/001.toml", "book/XIV/01.md", "book/I/1.md",
                     "heath/I/index.md", "mishnah/I/front.md", "mishnah/intro/i.md",
                     "reading/I/front.md", "figures/I/01-sketch.svg", "figures/I/01_idea.svg",
                     "mishnah/I/00.md", "reading/I/1000.md", "book/IIII/01.md",
                     "review/I/extra/01.toml", "docs/briefs/13-book-V.md",
                     "docs/briefs/0013_book.md", "docs/briefs/0013-.md",
                     "docs/briefs/book-XIV.md", "docs/briefs/sub/0001-a.md"):
            with self.subTest(name=name):
                self.refused(5, entries(name), name)

    def test_p5_lean_and_python_names(self):
        for name in ("Elements/BookI/Prop1.lean", "Elements/BookI/Prop001.lean",
                     "Elements/Book1/Prop01.lean", "Elements/BookIIII/Prop01.lean",
                     "Elements/BookI/prop01.lean", "Elements/BookI/Prop_01.lean",
                     "Staging/stage5/A.lean", "Audit/overlaps.lean", "Elements/angles.lean",
                     "model/lakefile.lean", "docs/lakefile.lean", "tests/Lakefile.lean",
                     "scripts/check-paths.py", "scripts/Check.py", "tests/model/2d.py",
                     "scripts/class.py"):
            with self.subTest(name=name):
                self.refused(5, entries(name), name)
        # Outside the edition's Lean libraries, a Lean file is named as its folder wants.
        self.accepted(*entries("docs/reports/crew/scratch-IV/PrototypeIV1.lean",
                               "tests/fixtures/CertificateCN4.lean",
                               "Staging/Stage3/Prop23Point.lean", "model/Model.lean",
                               "Elements/Figure/OnCircles.lean", "scripts/a.py",
                               "scripts/match.py", "tests/case.py"))

    def test_p5_the_model_laws(self):
        # The nine laws keep the model's own lower-case names, and a new law would fit; the
        # exception holds only for files directly in model/Model/Laws/, and nowhere else.
        self.assertEqual(paths.LAW_FOLDER, "model/Model/Laws")
        laws = ("angles", "areas-p5", "circles", "incidence", "intersections", "lengths",
                "order", "sides", "superposition", "ratios")
        self.accepted(*entries(*(f"model/Model/Laws/{law}.lean" for law in laws),
                               "model/Model/Laws.lean", "model/Model/Euclidean/Angles.lean"))
        for name in ("model/Model/Laws/Angles.lean", "model/Model/Laws/areas_p5.lean",
                     "model/Model/Laws/Areas-P5.lean", "model/Model/Laws/areas--p5.lean",
                     "model/Model/laws.lean", "model/Model/Laws/sub/x.lean",
                     "model/Model/Laws/Sub/x.lean", "model/Model/Euclidean/angles.lean",
                     "model/Check/angles.lean", "model/model/laws/angles.lean",
                     "Elements/angles.lean", "Elements/Model/Laws/angles.lean",
                     "Staging/angles.lean", "model/Model/Laws/lakefile.lean",
                     "model/Model/Laws/Lakefile.lean"):
            with self.subTest(name=name):
                self.refused(5, entries(name), name)
        found = self.refused(5, entries("model/Model/Laws/Angles.lean"),
                             "model/Model/Laws/Angles.lean")
        self.assertIn("'Angles' is not a law's name in model/Model/Laws/", "\n".join(found))

    def test_p5_a_new_book_fits(self):
        self.accepted(*entries(
            "book/IV/01.md", "book/IV/front.md", "book/IV/index.md", "heath/IV/16.md",
            "heath/IV/front.md", "mishnah/IV/16.md", "mishnah/intro/IV.md", "reading/IV/16.md",
            "review/IV/16.toml", "figures/IV/01.svg", "figures/IV/01-idea.svg",
            "figures/IV/01-modern.svg", "Elements/BookIV/Prop16.lean", "docs/briefs/book-IV.md",
            "docs/briefs/0012-book-IV.md", "book/X/115.md", "heath/X/115.md",
            "mishnah/X/115.md", "reading/X/100.md", "review/X/115.toml", "figures/X/115.svg",
            "Elements/BookX/Prop115.lean", "Elements/BookXIII/Prop18.lean",
            "mishnah/intro/XIII.md"))

    def test_p6_modes(self):
        self.refused(6, [("120000", "docs/link.md")], "docs/link.md")
        self.refused(6, [("160000", "docs/sub")], "docs/sub")
        self.refused(6, [("100664", "docs/a.md")], "docs/a.md")
        self.refused(6, [(EXECUTABLE, "scripts/heath.py")], "scripts/heath.py")
        for name in sorted(paths.EXECUTABLES):
            with self.subTest(name=name):
                self.refused(6, [(PLAIN, name)], name)
        self.accepted(*((EXECUTABLE, name) for name in sorted(paths.EXECUTABLES)))
        self.assertEqual(len(paths.EXECUTABLES), 6)

    def test_findings_are_sorted_lines_naming_rule_and_path(self):
        found = paths.findings([(PLAIN, "notes.txt"), ("120000", "docs/link.md"),
                                (PLAIN, "docs/a b.md")])
        self.assertEqual(found, sorted(found, key=lambda f: (int(f[1]), f)))
        self.assertTrue(found[0].startswith('P1 "docs/a b.md": holds a space'))
        self.assertTrue(all(f.split(" ", 1)[0] in {f"P{n}" for n in range(1, 7)} for f in found))

    def test_each_finding_is_one_printable_line(self):
        # A name inside a reason is escaped as the path is, so no finding breaks a line.
        hostile = ("docs/a.m\nd", "docs/a.md\r", "docs/x\x85y.md", "docs/a b.md",
                   "Elements/Book\nX/Prop01.lean", "Elements/BookI/Prop1\n.lean",
                   "Elements/café.lean", "model/Model/Laws/an\ngles.lean",
                   "model/Model/Laws/é.lean", "docs/a.locK", "docs/a\udcffb.md",
                   "Dé/a.md", "docs/con\n.md", "docs/-\n")
        found = paths.findings(entries(*hostile) + [("100\n644", "docs/mode.md")])
        self.assertTrue(found)
        for f in found:
            with self.subTest(finding=f):
                self.assertEqual(f.splitlines(), [f])
                self.assertTrue(f.isascii() and f.isprintable(), repr(f))
                self.assertRegex(f, r"^P[1-6] ")
        for name in hostile:
            with self.subTest(name=name):
                self.assertTrue(any(f.startswith(f"P1 {paths.shown(name)}: ") for f in found))
        twins = paths.findings(entries("docs/Tw\nin.md", "docs/tw\nin.md"))
        self.assertTrue([f for f in twins if f.startswith("P2 ")], twins)
        self.assertTrue(all(f.splitlines() == [f] and f.isascii() for f in twins), twins)

    def test_shown_quotes_as_git_does(self):
        self.assertEqual(paths.shown("docs/a.md"), "docs/a.md")
        self.assertEqual(paths.shown("docs/a b.md"), '"docs/a b.md"')
        self.assertEqual(paths.shown("docs/café.md"), '"docs/caf\\303\\251.md"')
        self.assertEqual(paths.shown("docs/a\nb\"c"), '"docs/a\\nb\\"c"')
        self.assertEqual(paths.shown("docs/a\udcffb"), '"docs/a\\377b"')

    def test_self_test_passes_and_catches_a_rule_turned_off(self):
        self.assertEqual(paths.self_test(), [])
        for rule, entries_, name in paths.PLANTED:
            self.assertTrue(paths.findings(list(entries_)), name)
        self.assertEqual({rule for rule, _, _ in paths.PLANTED}, set(range(1, 7)))
        with patch.object(paths, "mode", return_value=[]):
            problems = paths.self_test()
        self.assertTrue(problems)
        self.assertTrue(all("by P6" in p for p in problems), problems)


def git_env(**extra: str) -> dict[str, str]:
    """An environment for a throwaway repository: none of the caller's GIT_ variables, and
    no global or system configuration."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_AUTHOR_NAME="Planted", GIT_AUTHOR_EMAIL="planted@example.invalid",
               GIT_COMMITTER_NAME="Planted", GIT_COMMITTER_EMAIL="planted@example.invalid",
               **extra)
    return env


# A small tree that keeps the standard, with the six executables.
BASE = (*((PLAIN, name) for name in ("README.md", "LICENSE", "docs/a.md", "book/I/01.md",
                                      "review/I/01.toml", "Elements/BookI/Prop01.lean",
                                      "model/Model.lean", "model/Model/Laws/areas-p5.lean",
                                      "scripts/a.py", "scripts/match.py")),
        *((EXECUTABLE, name) for name in sorted(paths.EXECUTABLES)))


class Index(unittest.TestCase):
    """The script run on a throwaway repository, its faults planted in the index."""

    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.git("init", "-q", "-b", "main", ".")
        self.blob = self.git("hash-object", "-w", "--stdin", input=b"planted\n").strip()
        for mode, name in BASE:
            self.plant(mode, name)
        self.git("commit", "-q", "-m", "A tree that keeps the standard")
        self.git("read-tree", "HEAD")
        (self.root / "scripts").mkdir()
        shutil.copyfile(SCRIPT, self.root / "scripts" / "check_paths.py")

    def git(self, *args: str, input: bytes | None = None, check: bool = True) -> str:
        done = subprocess.run(["git", *args], cwd=self.root, env=git_env(), input=input,
                              capture_output=True)
        if check and done.returncode != 0:
            self.fail(f"git {' '.join(args)}: {done.stderr.decode(errors='replace')}")
        return done.stdout.decode()

    def mktree(self, records: list[tuple[str, str, str, str]]) -> str:
        listing = "".join(f"{mode} {kind} {oid}\t{name}\n"
                          for mode, kind, oid, name in records)
        done = subprocess.run(["git", "mktree"], cwd=self.root, env=git_env(),
                              input=listing.encode(), capture_output=True)
        if done.returncode != 0:
            self.fail("git mktree: " + done.stderr.decode(errors="replace"))
        return done.stdout.decode().strip()

    def tree_commit(self, records: list[tuple[str, str, str, str]], message: str) -> str:
        tree = self.mktree(records)
        return self.git("commit-tree", tree, "-p", "HEAD", "-m", message).strip()

    def plant(self, mode: str, name: str, check: bool = True) -> subprocess.CompletedProcess:
        """Put an entry straight into the index, with Git told not to fold case or Unicode,
        so that twins stay two entries on any disk."""
        done = subprocess.run(["git", "-c", "core.ignorecase=false",
                               "-c", "core.precomposeunicode=false", "update-index", "--add",
                               "--cacheinfo", f"{mode},{self.blob},{name}"],
                              cwd=self.root, env=git_env(), capture_output=True)
        if check and done.returncode != 0:
            self.fail(f"planting {name!r}: {done.stderr.decode(errors='replace')}")
        return done

    def check(self, *args: str, env: dict[str, str] | None = None,
              isolated: bool = True) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, *(["-I"] if isolated else []),
                               str(self.root / "scripts/check_paths.py"), *args],
                              cwd=self.root, env=git_env() if env is None else env,
                              capture_output=True, text=True)

    def caught(self, rule: int, names: str | tuple[str, ...], *args: str) -> None:
        result = self.check(*args)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        for name in (names,) if isinstance(names, str) else names:
            self.assertIn(f"✗ P{rule} {paths.shown(name)}: ", result.stdout)

    def test_the_base_tree_passes(self):
        result = self.check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"✓ paths: all {len(BASE)} tracked paths of the index follow", result.stdout)

    def test_planted_faults_are_caught(self):
        cases = (
            ("a case twin of a file", [(PLAIN, "readme.md")], 2, ("README.md", "readme.md")),
            ("a twin of a folder", [(PLAIN, "Scripts/json.py")], 2, ("Scripts/", "scripts/")),
            ("an NFC/NFD twin", [(PLAIN, "docs/caf\u00e9.md"), (PLAIN, "docs/cafe\u0301.md")],
             2, ("docs/caf\u00e9.md", "docs/cafe\u0301.md")),
            ("a space", [(PLAIN, "docs/two words.md")], 1, "docs/two words.md"),
            ("an upper-case extension", [(PLAIN, "docs/notes.MD")], 3, "docs/notes.MD"),
            ("a symbolic link", [("120000", "docs/link.md")], 6, "docs/link.md"),
            ("a submodule", [("160000", "docs/sub")], 6, "docs/sub"),
            ("an executable bit on a seventh file", [(EXECUTABLE, "scripts/a.py")], 6,
             "scripts/a.py"),
            ("the executable bit missing from one of the six", [(PLAIN, "scripts/safe_push.py")],
             6, "scripts/safe_push.py"),
            ("an svg under book/", [(PLAIN, "book/I/01.svg")], 4, "book/I/01.svg"),
            ("a misnamed review record", [(PLAIN, "review/I/1.toml")], 5, "review/I/1.toml"),
            ("Prop1.lean", [(PLAIN, "Elements/BookI/Prop1.lean")], 5,
             "Elements/BookI/Prop1.lean"),
            ("a law of the model named in capitals", [(PLAIN, "model/Model/Laws/Angles.lean")],
             5, "model/Model/Laws/Angles.lean"),
            ("lakefile.lean at the root", [(PLAIN, "lakefile.lean")], 4, "lakefile.lean"),
            ("lakefile.lean in model/", [(PLAIN, "model/lakefile.lean")], 5,
             "model/lakefile.lean"),
            ("a Python keyword", [(PLAIN, "scripts/class.py")], 5, "scripts/class.py"),
            ("a .gitattributes", [(PLAIN, ".gitattributes")], 4, ".gitattributes"),
        )
        for label, planted, rule, names in cases:
            with self.subTest(label):
                self.git("read-tree", "HEAD")
                for mode, path in planted:
                    self.plant(mode, path)
                self.caught(rule, names)

    def test_a_dot_dot_segment(self):
        planted = self.plant(PLAIN, "docs/../escape.md", check=False)
        if planted.returncode != 0:
            self.skipTest("Git refuses a '..' segment itself: "
                          + planted.stderr.decode(errors="replace").strip().splitlines()[0])
        self.caught(1, "docs/../escape.md")

    def test_a_rename_to_a_bad_name(self):
        (self.root / "docs").mkdir()
        (self.root / "docs/notes.md").write_text("notes\n")
        self.git("add", "docs/notes.md")
        self.assertEqual(self.check().returncode, 0)
        self.git("mv", "docs/notes.md", "docs/Notes draft.MD")
        self.caught(1, "docs/Notes draft.MD")
        self.caught(3, "docs/Notes draft.MD")

    def test_an_untracked_file_is_not_judged(self):
        (self.root / "Untracked Notes.MD").write_text("not tracked\n")
        (self.root / "book/I").mkdir(parents=True)
        (self.root / "book/I/01.svg").write_text("<svg/>\n")
        result = self.check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Untracked", result.stdout)

    def test_the_index_file_named_by_git_index_file(self):
        copy = Path(self.enterContext(tempfile.TemporaryDirectory())) / "index"
        shutil.copyfile(self.root / ".git/index", copy)
        subprocess.run(["git", "update-index", "--add", "--cacheinfo",
                        f"120000,{self.blob},docs/link.md"], cwd=self.root,
                       env=git_env(GIT_INDEX_FILE=str(copy)), check=True)
        result = subprocess.run(
            [sys.executable, "-I", str(self.root / "scripts/check_paths.py")], cwd=self.root,
            env=git_env(GIT_INDEX_FILE=str(copy)), capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("✗ P6 docs/link.md: ", result.stdout)
        self.assertEqual(self.check().returncode, 0)    # the real index is untouched

    def test_rev_judges_the_commit_and_not_the_index(self):
        self.plant("120000", "docs/link.md")
        self.caught(6, "docs/link.md")
        result = self.check("--rev", "HEAD")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f"all {len(BASE)} paths of HEAD", result.stdout)
        self.git("commit", "-q", "-m", "A link")
        self.caught(6, "docs/link.md", "--rev", "HEAD")
        result = self.check("--rev", "HEAD~1")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        result = self.check("--rev=--not-a-commit")
        self.assertEqual(result.returncode, 1)
        self.assertIn("✗ paths: git rev-parse", result.stderr)

    def test_rev_refuses_a_tree_listing_a_path_twice(self):
        # No index holds one path twice, but `git mktree` writes a tree that names README.md
        # twice (Git's fsck: duplicateEntries); --rev reads the tree as listed.
        listing = self.git("ls-tree", "HEAD")
        readme = next(line for line in listing.splitlines() if line.endswith("\tREADME.md"))
        made = subprocess.run(["git", "mktree"], cwd=self.root, env=git_env(),
                              input=f"{listing}{readme}\n".encode(), capture_output=True)
        if made.returncode != 0:
            self.skipTest("git mktree refuses a tree that names one path twice: "
                          + made.stderr.decode(errors="replace").strip())
        commit = self.git("commit-tree", made.stdout.decode().strip(), "-p", "HEAD",
                          "-m", "README.md twice").strip()
        self.caught(2, "README.md", "--rev", commit)
        self.assertIn("✗ P2 README.md: listed 2 times", self.check("--rev", commit).stdout)

    def test_rev_refuses_an_invalid_empty_directory(self):
        empty = self.mktree([])
        commit = self.tree_commit(
            [("040000", "tree", empty, "bad directory")], "An invalid empty directory")
        self.caught(1, "bad directory/", "--rev", commit)

    def test_rev_refuses_duplicate_directories_with_disjoint_children(self):
        left = self.mktree([(PLAIN, "blob", self.blob, "a.md")])
        right = self.mktree([(PLAIN, "blob", self.blob, "b.md")])
        commit = self.tree_commit([
            ("040000", "tree", left, "docs"),
            ("040000", "tree", right, "docs"),
        ], "The docs directory twice")
        self.caught(2, "docs/", "--rev", commit)
        self.assertIn("✗ P2 docs/: listed 2 times", self.check("--rev", commit).stdout)

    def test_rev_refuses_directory_twins_and_a_file_directory_collision(self):
        leaf = self.mktree([(PLAIN, "blob", self.blob, "a.md")])
        twins = self.tree_commit([
            ("040000", "tree", leaf, "Docs"),
            ("040000", "tree", leaf, "docs"),
        ], "Twin directories")
        self.caught(2, ("Docs/", "docs/"), "--rev", twins)
        collision_tree = self.mktree([
            (PLAIN, "blob", self.blob, "same"),
            ("040000", "tree", leaf, "same"),
        ])
        collision = self.tree_commit(
            [("040000", "tree", collision_tree, "docs")], "A file and directory collide")
        self.caught(2, ("docs/same", "docs/same/"), "--rev", collision)

    def test_rev_accepts_valid_nested_and_empty_directories(self):
        empty = self.mktree([])
        nested = self.mktree([(PLAIN, "blob", self.blob, "a.md")])
        docs = self.mktree([
            ("040000", "tree", empty, "empty"),
            ("040000", "tree", nested, "nested"),
        ])
        commit = self.tree_commit(
            [("040000", "tree", docs, "docs")], "Valid explicit directories")
        result = self.check("--rev", commit)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("all 1 paths", result.stdout)

    def test_a_module_planted_beside_the_script_never_stands_in(self):
        # A module planted in scripts/ that would pass any tree: run as CI runs it, without
        # -I, the script still refuses a bad path, and the plant never runs. A probe in the
        # same folder that imports the module shows the plant is live for a script that
        # keeps its folder on sys.path; a module this Python loads before any script runs
        # cannot be planted, and its case is skipped.
        self.plant(PLAIN, "docs/two words.md")
        env = {k: v for k, v in git_env().items() if not k.startswith("PYTHON")}
        for name in ("unicodedata", "argparse", "keyword", "subprocess", "pathlib",
                     "__future__"):
            with self.subTest(name):
                marker = self.root / f"{name}.ran"
                plant = self.root / "scripts" / f"{name}.py"
                probe = self.root / "scripts" / "probe.py"
                plant.write_text(f"open({str(marker)!r}, 'w').close()\n"
                                 "print('paths: all tracked paths of the index pass')\n"
                                 "raise SystemExit(0)\n")
                probe.write_text("from __future__ import annotations\n" if name == "__future__"
                                 else f"import {name}\n")
                try:
                    subprocess.run([sys.executable, str(probe)], cwd=self.root, env=env,
                                   capture_output=True)
                    if not marker.exists():
                        self.skipTest(f"this Python loads {name} before a script runs")
                    marker.unlink()
                    for args in ((), ("--self-test",)):
                        result = self.check(*args, env=env, isolated=False)
                        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                        self.assertIn('✗ P1 "docs/two words.md": ', result.stdout)
                        self.assertFalse(marker.exists(), f"the planted {name}.py ran")
                finally:
                    plant.unlink()
                    probe.unlink()

    def test_an_inherited_git_dir_is_refused_saying_what_to_do(self):
        # A Git alias run from a linked worktree sets GIT_DIR, and Git then takes the folder
        # it runs in for the work tree; a GIT_WORK_TREE may name another. Either is refused.
        elsewhere = str(Path(self.enterContext(tempfile.TemporaryDirectory())).resolve())
        gitdir = str(self.root / ".git")
        for extra in ({"GIT_DIR": gitdir}, {"GIT_WORK_TREE": elsewhere},
                      {"GIT_DIR": gitdir, "GIT_WORK_TREE": elsewhere}):
            with self.subTest(**extra):
                result = self.check(env=git_env(**extra))
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(f"{' and '.join(extra)} {'is' if len(extra) == 1 else 'are'} set",
                              result.stderr)
                self.assertIn("run the check with neither (env -u GIT_DIR -u GIT_WORK_TREE "
                              "python3 scripts/check_paths.py)", result.stderr)
                self.assertNotIn("✓", result.stdout)
        # Both naming this repository, as negative_tests.py's copies name theirs, judge it.
        result = self.check(env=git_env(GIT_DIR=gitdir, GIT_WORK_TREE=str(self.root)))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_a_foreign_git_dir_cannot_supply_the_index(self):
        self.plant("120000", "docs/link.md")
        foreign = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.git("-C", str(foreign), "init", "-q", "-b", "main", ".")
        self.git("-C", str(foreign), "commit", "-q", "--allow-empty", "-m", "Clean")
        result = self.check(env=git_env(GIT_DIR=str(foreign / ".git"),
                                        GIT_WORK_TREE=str(self.root)))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("not the script's repository Git directory", result.stderr)
        self.assertNotIn("✓", result.stdout)

    def test_self_test_runs_before_the_index(self):
        self.plant(PLAIN, "readme.md")
        result = self.check("--self-test")
        self.assertEqual(result.returncode, 1)
        self.assertIn("  self-test: ", result.stdout)
        self.assertLess(result.stdout.index("self-test"), result.stdout.index("✗ P2"))


class Repository(unittest.TestCase):
    def test_the_repository_passes(self):
        result = subprocess.run([sys.executable, "-I", str(SCRIPT)], cwd=REPO,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r"✓ paths: all \d+ tracked paths of the index follow")


if __name__ == "__main__":
    unittest.main()
