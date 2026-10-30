#!/usr/bin/env python3
"""The cases of scripts/check_released_names.py, without Lean.

    python3 -I tests/test_check_released_names.py

The rule, on lists and main's names made in memory. A released name that main lacks fails,
naming the name, its tag and FORMALIZATION's section; the same name with a deprecated alias
on main passes, and so does one main still declares plainly; a name deprecated on main with
nothing to replace it passes; beside a name with its alias, a name aliased nowhere fails
alone; a namespace renamed fails once for each name in it, in the list's order; a name the
tag marked deprecated passes, on main or not; and a name new on main passes. The summary
counts the names released, those present on main, those of them deprecated there and those
missing, and those gone after the release that deprecated them. The list's tag: the
repository's tag at another commit is a finding, naming the tag line; the tag absent, or
git unable to say where it points, is a note of one line and no finding; the same commit
is neither; and a later tag is a note naming it, beside a finding or alone, never a finding.

The list's reader refuses, naming the line: no tag line (a row before it, or no line at
all but comments), two tag lines, a tag line of the wrong shape, a commit that is short, in
capitals or not hex, a tag's name that is not one, an unknown marker, a row with no name or
two words, a name listed twice (with one marker or with two), rows out of order, a list
with no rows, a blank line and a comment after the tag line; and an empty file. A list made
by `render_list` reads back as it was made, sorted, with the deprecated rows first and its
header naming the command that makes it. The probe's reader refuses a Lean message, a
line such as `#check` prints, a name printed twice and an empty output, and reads rows of
both markers.

The self-test's judging is exercised with explicit rows: it finds no surprise for the
expected plants, and finds one when a plant is read otherwise (the private `hidden`
present, under its own name or its private one, the parser of the notation or of the infix
present, a name of the structure that a filter leaves out present, an internal detail of
the planted namespace present, one of Lean's own names present, the alias `renamed` plain,
`New.a` or the instance absent, the real `Elements.BookI.Prop1` absent or deprecated),
naming it. The planted lists are the seven the script holds, and each judged as stated;
every plant that must give no row is used by an `example` in the plants, so that a plant
removed stops Lean rather than reading as absent. What Lean prints for the plants is not
run here: the registered `scripts/check_released_names.py --self-test` runs it.

The refusal of a stale build, with `lake` stood in for. The script runs exactly `lake build
--no-build Elements` from the repository's root; when it exits 0 the probe runs after it,
and when it fails the probe never runs, and the refusal says the build of Elements is not
current, with the last lines Lake printed, the earlier ones left out. Each mode that runs
the probe (the check, `--self-test`, `--list`) refuses so (exit 2), printing nothing on
its standard output; on a current build the check and `--list` go on to the probe.

The modes, with the probe and git stood in for. The check exits 1 with each finding and the
summary when a name is missing, 1 when the tag is the repository's at another commit, 0
when nothing is missing, with a note when the tag is absent, and 2 when the probe's output
or the list cannot be read; the self-test exits 1 on a surprise without running the check,
and leaves the planted namespace out of the check it runs. `--list` refuses (exit 2) a
tag's name that is not one, a tag the repository does not hold, a HEAD at another commit
and a file that differs from the tag's commit, and otherwise prints a list that reads back.

With git itself, on repositories made for the test: what bars `--list` is any tracked file
except the list marked `assume-unchanged` or `skip-worktree`, even while its contents match
HEAD; a tracked file modified; or an ordinary or ignored untracked Lean file,
`lakefile.lean`, `lakefile.toml`, `lake-manifest.json` or `lean-toolchain`, including inside
an ignored directory and with characters Git quotes. The list itself, emptied as the
recipe's redirection empties it, an untracked script and ignored build artifacts do not bar
it; each refusal happens before the probe. Rename records are read as one change, including
a rename to the excepted list path. The later tags are those whose history holds the list's
commit, the list's own left out, and none when the repository lacks the commit. The
environment of git's commands holds none of the variables that point git elsewhere.
`run_lean` gives Lean's output as printed, which `run_probe` reads.

And the real tests/released_names.txt reads, names `book-III` with a full commit, holds 498
names, none of them the parser of one of the four notations, and holds
`Elements.Triangle.of_onCircle`, `Elements.exists_onCircle_oppositeSidesOf` and
`Elements.exists_onCircle_sameSideOf` as plain released names; it is byte for byte what
`render_list` makes of its own rows.
"""

import io
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))
import check_released_names as released  # noqa: E402

COMMIT = "792082f0cc791c1fca61123a6f8f45fef80c1648"
OTHER = "0123456789abcdef0123456789abcdef01234567"
THREE = ("Elements.Triangle.of_onCircle", "Elements.exists_onCircle_oppositeSidesOf",
         "Elements.exists_onCircle_sameSideOf")
# The parsers of the four notations of Elements/Foundations/Magnitudes.lean.
PARSERS = ("Elements.«term‖__‖»", "Elements.«term∟»", "Elements.«term∠___»",
           "Elements.«term△___»")
STALE = ("the build of Elements is not current (lake build --no-build failed): run "
         "`lake build` first")
P = "Elements.ReleasedNamesPlant"
REAL = "Elements.BookI.Prop1"
BUILD_COMMAND = ["lake", "build", "--no-build", "Elements"]
LEAN_COMMAND = ["lake", "env", "lean"]


def listed(names: dict[str, str], tag: str = "book-III") -> released.Listed:
    return released.Listed(tag, COMMIT, 9, names)


def text(*rows: str, head: str = f"# a comment\ntag book-III {COMMIT}\n") -> str:
    return head + "".join(f"{row}\n" for row in rows)


def planted_output() -> dict[str, str]:
    """The explicit rows expected from the executable self-test's plants."""
    return {
        f"{P}.kept": "name",
        f"{P}.New.a": "name",
        f"{P}.New.b": "name",
        f"{P}.Old.b2": "name",
        f"{P}.instPlant": "name",
        f"{P}.renamed": "deprecated",
        f"{P}.retired": "deprecated",
        f"{P}.Old.a": "deprecated",
        f"{P}.Shape": "name",
        f"{P}.Shape.mk": "name",
        f"{P}.Shape.side": "name",
        REAL: "name",
        "Elements.BookI.Prop2": "name",
    }


class TheRule(unittest.TestCase):
    def test_a_released_name_removed_fails_naming_it(self):
        self.assertEqual(released.missing(listed({"Elements.gone": "name"}), {}),
                         ["Elements.gone: released in book-III, missing on main with no "
                          "deprecated alias (FORMALIZATION.md, section 2)"])

    def test_a_renamed_name_with_its_deprecated_alias_passes(self):
        main = {"Elements.new": "name", "Elements.old": "deprecated"}
        self.assertEqual(released.missing(listed({"Elements.old": "name"}), main), [])

    def test_a_name_main_still_declares_plainly_passes(self):
        self.assertEqual(released.missing(listed({"Elements.kept": "name"}),
                                          {"Elements.kept": "name"}), [])

    def test_a_name_deprecated_with_nothing_to_replace_it_passes(self):
        self.assertEqual(released.missing(listed({"Elements.retired": "name"}),
                                          {"Elements.retired": "deprecated"}), [])

    def test_beside_a_name_with_its_alias_one_aliased_nowhere_fails_alone(self):
        main = {"Elements.New.a": "name", "Elements.Old.a": "deprecated"}
        found = released.missing(listed({"Elements.Old.a": "name", "Elements.Old.c": "name"}),
                                 main)
        self.assertEqual(found, [released.finding("Elements.Old.c", "book-III")])

    def test_a_namespace_renamed_fails_once_for_each_name_in_it(self):
        main = {"Elements.New.x": "name", "Elements.New.y": "name"}
        found = released.missing(listed({"Elements.Old.x": "name", "Elements.Old.y": "name"}),
                                 main)
        self.assertEqual(found, [released.finding("Elements.Old.x", "book-III"),
                                 released.finding("Elements.Old.y", "book-III")])

    def test_a_name_the_tag_deprecated_passes_on_main_or_not(self):
        names = {"Elements.gone": "deprecated"}
        self.assertEqual(released.missing(listed(names), {}), [])
        self.assertEqual(released.missing(listed(names), {"Elements.gone": "deprecated"}), [])
        self.assertEqual(released.missing(listed(names), {"Elements.gone": "name"}), [])

    def test_a_name_new_on_main_passes(self):
        main = {"Elements.kept": "name", "Elements.New.a": "name", "Elements.New.b": "name"}
        self.assertEqual(released.missing(listed({"Elements.kept": "name"}), main), [])

    def test_the_summary_counts(self):
        names = {"Elements.a": "name", "Elements.b": "name", "Elements.c": "name",
                 "Elements.d": "deprecated", "Elements.e": "deprecated"}
        main = {"Elements.a": "name", "Elements.b": "deprecated", "Elements.e": "deprecated"}
        lines, code = released.report(listed(names), main, COMMIT)
        self.assertEqual(code, 1)
        self.assertEqual(lines, [
            released.finding("Elements.c", "book-III"),
            "✗ tests/released_names.txt: 5 names released in book-III: 3 present on main, 2 of "
            "them deprecated there; 1 missing with no deprecated alias; 1 gone after the "
            "release that deprecated them"])
        lines, code = released.report(listed({"Elements.a": "name"}), main, COMMIT)
        self.assertEqual((lines, code), ([
            "✓ tests/released_names.txt: 1 names released in book-III: 1 present on main, 0 "
            "of them deprecated there; 0 missing with no deprecated alias"], 0))


class TheTag(unittest.TestCase):
    def test_the_tag_at_another_commit_is_a_finding_naming_the_tag_line(self):
        found, notes = released.tag_lines(listed({"Elements.a": "name"}), OTHER)
        self.assertEqual(notes, [])
        self.assertEqual(found, [f"tests/released_names.txt:9: the list gives book-III as "
                                 f"{COMMIT}, but the tag in this repository points to {OTHER}, "
                                 "so the list is not the tag's; make it with --list book-III"])
        lines, code = released.report(listed({"Elements.a": "name"}), {"Elements.a": "name"},
                                      OTHER)
        self.assertEqual(code, 1)
        self.assertTrue(lines[-1].endswith("; and the list is not the tag's"), lines)

    def test_the_tag_absent_or_unknown_is_a_note_and_no_finding(self):
        for local, error, says in ((None, None, "holds no tag book-III"),
                                   (None, "git cannot be run", "cannot be read here")):
            with self.subTest(says):
                found, notes = released.tag_lines(listed({"Elements.a": "name"}), local, error)
                self.assertEqual(found, [])
                self.assertEqual(len(notes), 1)
                self.assertIn(says, notes[0])
                self.assertIn("is not compared", notes[0])
                lines, code = released.report(listed({"Elements.a": "name"}),
                                              {"Elements.a": "name"}, local, error)
                self.assertEqual(code, 0)
                self.assertEqual(lines[0], notes[0])

    def test_the_same_commit_gives_nothing(self):
        self.assertEqual(released.tag_lines(listed({"Elements.a": "name"}), COMMIT), ([], []))

    def test_a_later_tag_is_a_note_never_a_finding(self):
        names = {"Elements.a": "name"}
        found, notes = released.tag_lines(listed(names), COMMIT, None, ["book-IV"])
        self.assertEqual(found, [])
        self.assertEqual(notes, ["tests/released_names.txt:9: tag book-IV came after book-III, "
                                 "so the list may be out of date; once a release is tagged, "
                                 "make the list with --list <its tag> and commit it"])
        lines, code = released.report(listed(names), names, COMMIT, None, ["book-IV"])
        self.assertEqual((lines[0], code), (notes[0], 0))
        found, notes = released.tag_lines(listed(names), OTHER, None, ["book-IV"])
        self.assertEqual(len(found), 1)
        self.assertEqual(len(notes), 1)
        self.assertIn("book-IV came after", notes[0])


class TheList(unittest.TestCase):
    def refused(self, source: str, line: int | None, says: str):
        with self.assertRaises(released.Unreadable) as raised:
            released.parse_list(source, "L")
        where = f"L:{line}: " if line else "L: "
        self.assertTrue(str(raised.exception).startswith(where), str(raised.exception))
        self.assertIn(says, str(raised.exception))

    def test_a_good_list_reads_in_order(self):
        got = released.parse_list(text("deprecated Elements.z", "name Elements.a",
                                       "name Elements.«term∠___»"))
        self.assertEqual((got.tag, got.commit, got.tag_line), ("book-III", COMMIT, 2))
        self.assertEqual(list(got.names.items()), [
            ("Elements.z", "deprecated"), ("Elements.a", "name"),
            ("Elements.«term∠___»", "name")])

    def test_no_tag_line_is_refused(self):
        self.refused(text("name Elements.a", head="# a comment\n"), 2, "a row before the tag")
        self.refused("# only a comment\n", None, "no tag line")

    def test_two_tag_lines_are_refused(self):
        self.refused(text("name Elements.a", head=f"tag book-III {COMMIT}\ntag book-II "
                                                  f"{COMMIT}\n"), 2,
                     "a second tag line (the first is line 1)")

    def test_a_tag_line_of_the_wrong_shape_is_refused(self):
        for line in ("tag book-III", f"tag book-III {COMMIT} extra", f"tag  book-III {COMMIT}"):
            with self.subTest(line):
                self.refused(text("name Elements.a", head=f"{line}\n"), 1, "is not a tag line")

    def test_a_bad_commit_is_refused(self):
        for commit in (COMMIT[:12], COMMIT.upper(), "g" * 40, COMMIT + "0"):
            with self.subTest(commit):
                self.refused(text("name Elements.a", head=f"tag book-III {commit}\n"), 1,
                             "is not a full commit, 40 lower-case hex digits")

    def test_a_bad_tag_name_is_refused(self):
        self.refused(text("name Elements.a", head=f"tag -book {COMMIT}\n"), 1,
                     "is not a tag's name")

    def test_an_unknown_marker_is_refused(self):
        for row in ("removed Elements.a", "Elements.a", "Name Elements.a"):
            with self.subTest(row):
                self.refused(text(row), 3, "is an unknown marker")

    def test_a_row_with_no_name_or_two_words_is_refused(self):
        for row in ("name", "name ", "name Elements.a b", "deprecated  Elements.a",
                    "name Elements.a\r"):
            with self.subTest(repr(row)):
                self.refused(text(row), 3, "is not a row")

    def test_a_name_listed_twice_is_refused(self):
        self.refused(text("name Elements.a", "name Elements.a"), 4,
                     "`Elements.a` is listed twice (first at line 3)")
        self.refused(text("deprecated Elements.a", "name Elements.a"), 4,
                     "`Elements.a` is listed twice (first at line 3)")

    def test_rows_out_of_order_are_refused(self):
        self.refused(text("name Elements.b", "name Elements.a"), 4, "is out of order")
        self.refused(text("name Elements.a", "deprecated Elements.b"), 4, "is out of order")

    def test_a_list_with_no_rows_is_refused(self):
        self.refused(text(), 2, "no row follows the tag line")

    def test_a_blank_line_and_a_late_comment_are_refused(self):
        self.refused(text("name Elements.a", "", "name Elements.b"), 4, "a blank line")
        self.refused(text("name Elements.a", "# late", "name Elements.b"), 4,
                     "a comment after the tag line")

    def test_an_empty_file_is_refused(self):
        self.refused("", None, "no tag line")
        self.refused("\n", 1, "a blank line")

    def test_a_list_made_by_render_list_reads_back(self):
        rows = {"Elements.b": "name", "Elements.a": "deprecated", "Elements.«term∟»": "name",
                "Elements.Triangle.ne₁₂": "name"}
        made = released.render_list("book-IV", OTHER, rows)
        self.assertIn("--list book-IV > tests/released_names.txt", made)
        got = released.parse_list(made)
        self.assertEqual((got.tag, got.commit), ("book-IV", OTHER))
        self.assertEqual(got.names, rows)
        self.assertEqual(list(got.names), ["Elements.a", "Elements.Triangle.ne₁₂",
                                           "Elements.b", "Elements.«term∟»"])


class TheProbe(unittest.TestCase):
    def refused(self, out: str, says: str):
        with self.assertRaises(released.Unreadable) as raised:
            released.read_probe(out)
        self.assertIn(says, str(raised.exception))

    def test_rows_of_both_markers_are_read(self):
        self.assertEqual(released.read_probe("deprecated Elements.b\nname Elements.a\n"),
                         {"Elements.b": "deprecated", "Elements.a": "name"})

    def test_a_lean_message_is_refused(self):
        warning = ("/tmp/released-names-x/Probe.lean:10:2: warning: `[deprecated]` attribute "
                   "should specify either a new name or a deprecation message")
        self.refused(f"name Elements.a\n{warning}\n", "the probe's line 2 is not a row")
        self.refused("Elements.Angle : Type\n", "the probe's line 1 is not a row")
        self.refused("Elements.Angle\n", "the probe's line 1 is not a row")

    def test_a_name_printed_twice_is_refused(self):
        self.refused("name Elements.a\ndeprecated Elements.a\n",
                     "printed `Elements.a` twice, at line 2")

    def test_an_empty_output_is_refused(self):
        for out in ("", "\n"):
            with self.subTest(repr(out)):
                with self.assertRaises(released.Unreadable):
                    released.read_probe(out)
        self.refused("", "the probe printed no names")

class TheSelfTest(unittest.TestCase):
    def test_the_expected_executable_rows_give_no_surprise(self):
        self.assertEqual(released.self_test(planted_output()), [])

    def test_a_plant_read_otherwise_is_a_surprise(self):
        cases = {
            "hidden present": ({f"{P}.hidden": "name"}, (), f"`{P}.hidden` as plain, where it "
                                                            "must be absent"),
            "the notation's parser present": ({f"{P}.«term⟪_⟫»": "name"}, (),
                                              f"`{P}.«term⟪_⟫»` as plain, where it must be "
                                              "absent"),
            "the infix's parser present": ({f"{P}.«term_⊞_»": "name"}, (),
                                           f"`{P}.«term_⊞_»` as plain, where it must be "
                                           "absent"),
            "renamed plain": ({f"{P}.renamed": "name"}, (), f"`{P}.renamed` as plain, where it "
                                                            "must be deprecated"),
            "New.a absent": ({}, (f"{P}.New.a",), f"`{P}.New.a` as absent, where it must be "
                                                  "plain"),
            "the instance absent": ({}, (f"{P}.instPlant",), f"`{P}.instPlant` as absent, "
                                                             "where it must be plain"),
            "the recursor present": ({f"{P}.Shape.rec": "name"}, (),
                                     f"`{P}.Shape.rec` as plain, where it must be absent"),
            "a name without a range present": ({f"{P}.Shape.mk.injEq": "name"}, (),
                                               f"`{P}.Shape.mk.injEq` as plain, where it "
                                               "must be absent"),
            "an internal detail present": ({f"{P}._aux_Probe___unexpand_id_1": "name"}, (),
                                           f"`{P}._aux_Probe___unexpand_id_1` as plain, "
                                           "where it must be absent"),
            "the private plant under its private name": (
                {f"_private.Probe.0.{P}.hidden": "name"}, (),
                f"1 name outside `Elements`: `_private.Probe.0.{P}.hidden`"),
            "one of Lean's own names": ({"Nat.add": "name", "Lean.Name": "name"}, (),
                                        "2 names outside `Elements`: `Lean.Name`, `Nat.add`"),
            "Prop1 absent": ({}, (REAL,), f"`{REAL}` as absent"),
            "Prop1 deprecated": ({REAL: "deprecated"}, (), f"`{REAL}` as deprecated"),
        }
        for label, (changed, dropped, says) in cases.items():
            with self.subTest(label):
                rows = planted_output() | changed
                for name in dropped:
                    rows.pop(name)
                problems = released.self_test(rows)
                self.assertTrue(any(says in problem for problem in problems), problems)

    def test_the_planted_rule_cases_are_judged_as_expected(self):
        cases = (
            ("a released name removed fails", {"gone": "name"}, ["gone"]),
            ("a renamed name with its deprecated alias passes", {"renamed": "name"}, []),
            ("a name deprecated with nothing to replace it passes",
             {"retired": "name"}, []),
            ("beside a name with its alias, a name aliased nowhere fails alone",
             {"Old.a": "name", "Old.c": "name"}, ["Old.c"]),
            ("a namespace renamed fails once for each name in it",
             {"Old.x": "name", "Old.y": "name"}, ["Old.x", "Old.y"]),
            ("a removed name the tag marked deprecated passes",
             {"gone": "deprecated"}, []),
            ("a list that names nothing new on main passes",
             {"kept": "name", REAL: "name"}, []),
        )
        self.assertEqual(released.PLANT_CASES, cases)
        rows = planted_output()
        self.assertEqual(released.self_test(rows), [])
        for what, names, failing in cases:
            with self.subTest(what):
                full = {name if name.startswith("Elements.") else f"{P}.{name}": marker
                        for name, marker in names.items()}
                got = released.missing(released.Listed("plant", "0" * 40, 1, full), rows)
                expected = [f"{P}.{name}: released in plant, missing on main with no "
                            "deprecated alias (FORMALIZATION.md, section 2)"
                            for name in failing]
                self.assertEqual(got, expected)


    def test_every_plant_that_gives_no_row_is_rejected_when_present(self):
        absent = {name for name, marker in released.PLANTED.items() if marker is None}
        self.assertEqual(len(absent), 12)
        self.assertEqual(released.self_test(planted_output()), [])
        for name in absent:
            with self.subTest(name):
                full = released.full_name(name)
                rows = planted_output() | {full: "name"}
                self.assertEqual(
                    released.self_test(rows),
                    [f"the probe read `{full}` as plain, where it must be absent"],
                )


def lake(test: unittest.TestCase, build: int, said: bytes = b"",
         rows: str = "name Elements.a\n"):
    """A stand-in for subprocess.run, patched in: `lake build --no-build Elements` exits
    `build`, printing `said`, and `lake env lean` prints `rows`; any other command, or one
    run elsewhere than the repository's root, fails the test. `test.ran` keeps each
    command run."""
    test.ran = []

    def run(args, **kwargs):
        test.ran.append(list(args))
        test.assertEqual(kwargs.get("cwd"), released.ROOT)
        if list(args) == BUILD_COMMAND:
            return subprocess.CompletedProcess(args, build, stdout=said)
        if list(args[:3]) == LEAN_COMMAND:
            return subprocess.CompletedProcess(args, 0, stdout=rows.encode(), stderr=b"")
        raise AssertionError(f"an unexpected command: {args}")

    test.enterContext(mock.patch.object(released.shutil, "which", return_value="/bin/lake"))
    test.enterContext(mock.patch.object(released.subprocess, "run", side_effect=run))


# A stale build's output in the form Lake 4.35 prints it: the module lines made up, the last
# three in Lake's words.
STALE_SAID = "".join(f"✖ [{k}/60] Building Elements.Module{k}\n" for k in range(1, 21)) + (
    "error: target is out-of-date and needs to be rebuilt\n"
    "Some required targets logged failures:\n- Elements\n")


class TheBuild(unittest.TestCase):
    def test_a_current_build_passes(self):
        lake(self, 0, b"Build completed successfully (60 jobs).\n")
        self.assertIsNone(released.require_current_build())
        self.assertEqual(self.ran, [BUILD_COMMAND])

    def test_a_stale_build_is_refused_with_its_last_lines(self):
        lake(self, 3, STALE_SAID.encode())
        with self.assertRaises(released.Unreadable) as raised:
            released.require_current_build()
        lines = str(raised.exception).splitlines()
        self.assertEqual(lines[0], STALE)
        self.assertEqual(lines[1:], STALE_SAID.splitlines()[-released.BUILD_LINES:])
        self.assertNotIn(STALE_SAID.splitlines()[0], str(raised.exception))
        self.assertEqual(lines[-1], "- Elements")

    def test_a_failure_with_nothing_printed_is_refused(self):
        lake(self, 1)
        with self.assertRaises(released.Unreadable) as raised:
            released.require_current_build()
        self.assertEqual(str(raised.exception), STALE)

    def test_the_probe_runs_only_after_the_guard_passes(self):
        lake(self, 3, STALE_SAID.encode())
        with self.assertRaises(released.Unreadable):
            released.run_probe(released.probe())
        self.assertEqual(self.ran, [BUILD_COMMAND])
        lake(self, 0)
        self.assertEqual(released.run_probe(released.probe()), {"Elements.a": "name"})
        self.assertEqual(len(self.ran), 2)
        self.assertEqual(self.ran[0], BUILD_COMMAND)
        self.assertEqual(self.ran[1][:3], LEAN_COMMAND)

    def test_run_lean_gives_what_lean_printed(self):
        lake(self, 0, rows="name Elements.a\nname Elements.b\n")
        self.assertEqual(released.run_lean("-- any file\n"), "name Elements.a\nname Elements.b\n")
        self.assertEqual(self.ran[0], BUILD_COMMAND)
        self.assertEqual(self.ran[1][:3], LEAN_COMMAND)


class WithGit(unittest.TestCase):
    """The script's git reads on repositories made here, with its ROOT pointed at them."""

    def setUp(self):
        self.repo = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.enterContext(mock.patch.object(released, "ROOT", self.repo))
        # The runner's own git configuration (signing, hooks, renames) stays out.
        self.enterContext(mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": os.devnull,
                                                       "GIT_CONFIG_NOSYSTEM": "1"}))
        self.git("init", "-q")

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args],
                              cwd=self.repo, env=released.git_env(), check=True,
                              capture_output=True, text=True).stdout.strip()

    def commit(self, files: dict[str, str]) -> str:
        for path, body in files.items():
            (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / path).write_text(body, encoding="utf-8")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "c")
        return self.git("rev-parse", "HEAD")

    def tag(self, files: dict[str, str]) -> str:
        commit = self.commit(files)
        self.git("tag", "book-III")
        return commit

    def assert_list_refused_before_probe(self, path: str):
        probe = mock.Mock(return_value={"Elements.a": "name"})
        with mock.patch.object(released, "run_probe", probe):
            with self.assertRaises(released.Unreadable) as raised:
                released.make_list("book-III")
        self.assertIn(path, str(raised.exception))
        probe.assert_not_called()

    def write_bytes_path(self, path: bytes):
        raw = os.fsencode(self.repo) + b"/" + path
        try:
            descriptor = os.open(raw, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        except OSError as error:
            self.skipTest(f"the filesystem does not support this bytes path: {error}")
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(b"x\n")

    def test_what_bars_list_and_what_does_not(self):
        self.commit({"Elements/A.lean": "x\n", str(released.LIST): "old\n",
                     "lakefile.toml": "x\n"})
        (self.repo / released.LIST).write_text("", encoding="utf-8")
        (self.repo / "scripts").mkdir()
        (self.repo / "scripts/check_released_names.py").write_text("", encoding="utf-8")
        (self.repo / "notes.txt").write_text("", encoding="utf-8")
        self.assertEqual(released.modified(), [])
        planted = ["Elements/B.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain",
                   "sub/lakefile.lean"]
        for path in planted:
            (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / path).write_text("x\n", encoding="utf-8")
        (self.repo / "Elements/A.lean").write_text("y\n", encoding="utf-8")
        self.assertEqual(sorted(released.modified()), sorted(planted + ["Elements/A.lean"]))

    def test_an_ignored_root_lakefile_refuses_list_before_the_probe(self):
        self.tag({".gitignore": "/lakefile.lean\n", "Elements/A.lean": "x\n"})
        (self.repo / "lakefile.lean").write_text("x\n", encoding="utf-8")
        self.assert_list_refused_before_probe("lakefile.lean")

    def test_a_lakefile_in_other_letters_refuses_list_before_the_probe(self):
        self.tag({"Elements/A.lean": "x\n"})
        (self.repo / "lakefile.LEAN").write_text("x\n", encoding="utf-8")
        self.assertEqual(released.modified(), ["lakefile.LEAN"])
        self.assert_list_refused_before_probe("lakefile.LEAN")

    def test_an_ignored_lakefile_in_other_letters_refuses_list(self):
        self.tag({".gitignore": "/LAKEFILE.TOML\n", "Elements/A.lean": "x\n"})
        (self.repo / "LAKEFILE.TOML").write_text("x\n", encoding="utf-8")
        self.assertEqual(released.modified(), ["LAKEFILE.TOML"])

    def test_build_inputs_inside_an_ignored_directory_refuse_list_before_the_probe(self):
        self.tag({".gitignore": "ignored/\n", "Elements/A.lean": "x\n"})
        (self.repo / "ignored").mkdir()
        (self.repo / "ignored/Source.lean").write_text("x\n", encoding="utf-8")
        (self.repo / "ignored/lakefile.toml").write_text("x\n", encoding="utf-8")
        self.assertEqual(released.modified(),
                         ["ignored/Source.lean", "ignored/lakefile.toml"])
        self.assert_list_refused_before_probe("ignored/Source.lean")

    def test_a_quoted_untracked_lean_path_refuses_list_before_the_probe(self):
        self.tag({"Elements/A.lean": "x\n"})
        path = 'Elements/quoted\t"line\nname.lean'
        (self.repo / path).write_text("x\n", encoding="utf-8")
        self.assertEqual(released.modified(), [path])
        self.assert_list_refused_before_probe(path)

    def test_ignored_build_artifacts_do_not_prevent_listing_a_clean_tag(self):
        commit = self.tag({".gitignore": ".lake/\n", "Elements/A.lean": "x\n"})
        artifact = self.repo / ".lake/build/lib/lean/Elements/A.olean"
        artifact.parent.mkdir(parents=True)
        artifact.write_text("built\n", encoding="utf-8")
        (artifact.parent / "A.trace").write_text("trace\n", encoding="utf-8")
        (self.repo / ".lake/lakefile.olean").write_text("config build\n", encoding="utf-8")
        probe = mock.Mock(return_value={"Elements.a": "name"})
        with mock.patch.object(released, "run_probe", probe):
            made = released.make_list("book-III")
        self.assertEqual(released.parse_list(made).commit, commit)
        probe.assert_called_once()

    def test_a_rename_to_the_excepted_list_path_is_still_one_change(self):
        self.commit({"notes.txt": "x\n"})
        (self.repo / released.LIST).parent.mkdir(parents=True)
        self.git("mv", "notes.txt", str(released.LIST))
        self.assertEqual(released.modified(),
                         [f"notes.txt -> {released.LIST.as_posix()}"])

    def test_an_assume_unchanged_source_refuses_list_without_changing_the_flag(self):
        self.tag({"Elements/A.lean": "x\n"})
        self.git("update-index", "--assume-unchanged", "Elements/A.lean")
        (self.repo / "Elements/A.lean").write_text("changed\n", encoding="utf-8")
        self.assert_list_refused_before_probe("assume-unchanged: Elements/A.lean")
        self.assertEqual(self.git("ls-files", "-v", "Elements/A.lean"),
                         "h Elements/A.lean")

    def test_a_skip_worktree_source_refuses_list_without_changing_the_flag(self):
        self.tag({"Elements/A.lean": "x\n"})
        self.git("update-index", "--skip-worktree", "Elements/A.lean")
        (self.repo / "Elements/A.lean").write_text("changed\n", encoding="utf-8")
        self.assert_list_refused_before_probe("skip-worktree: Elements/A.lean")
        self.assertEqual(self.git("ls-files", "-t", "Elements/A.lean"),
                         "S Elements/A.lean")

    def test_index_flags_preserve_the_released_list_exception(self):
        self.commit({str(released.LIST): "old\n", "Elements/A.lean": "x\n"})
        self.git("update-index", "--assume-unchanged", str(released.LIST))
        self.git("update-index", "--skip-worktree", str(released.LIST))
        (self.repo / released.LIST).write_text("", encoding="utf-8")
        self.assertEqual(released.modified(), [])
        self.assertEqual(self.git("ls-files", "-v", str(released.LIST)),
                         f"s {released.LIST.as_posix()}")
        self.assertEqual(self.git("ls-files", "-t", str(released.LIST)),
                         f"S {released.LIST.as_posix()}")

    def test_an_unrelated_non_utf8_untracked_path_remains_allowed(self):
        commit = self.tag({"Elements/A.lean": "x\n"})
        self.write_bytes_path(b"unrelated-\xff.txt")
        self.assertEqual(released.modified(), [])
        probe = mock.Mock(return_value={"Elements.a": "name"})
        with mock.patch.object(released, "run_probe", probe):
            made = released.make_list("book-III")
        self.assertEqual(released.parse_list(made).commit, commit)
        probe.assert_called_once()

    def test_a_non_utf8_untracked_lean_path_exits_2_before_the_probe(self):
        self.tag({"Elements/A.lean": "x\n"})
        self.write_bytes_path(b"Elements/untracked-\xff.lean")
        probe = mock.Mock(return_value={"Elements.a": "name"})
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(released, "run_probe", probe), \
                redirect_stdout(out), redirect_stderr(err):
            code = released.main(["--list", "book-III"])
        self.assertEqual(code, 2)
        self.assertEqual(out.getvalue(), "")
        self.assertIn(r"Elements/untracked-\xff.lean", err.getvalue())
        self.assertNotIn("Traceback", err.getvalue())
        probe.assert_not_called()

    def test_the_later_tags_hold_the_lists_commit(self):
        first = self.commit({"a": "1\n"})
        self.git("tag", "book-III")
        self.commit({"a": "2\n"})
        self.git("tag", "book-IV")
        self.git("tag", "book-V")
        self.git("checkout", "-q", first)
        self.commit({"a": "3\n"})
        self.git("tag", "elsewhere")
        self.assertEqual(released.later_tags(released.Listed("book-III", first, 9, {})),
                         ["book-IV", "book-V", "elsewhere"])
        self.assertEqual(released.later_tags(released.Listed("book-III", OTHER, 9, {})), [])

    def test_gits_environment_points_nowhere_else(self):
        planted = {name: "x" for name in released.GIT_VARIABLES}
        with mock.patch.dict(released.os.environ, planted):
            env = released.git_env()
        self.assertEqual(env["GIT_NO_REPLACE_OBJECTS"], "1")
        self.assertFalse(set(env) & (released.GIT_VARIABLES - {"GIT_NO_REPLACE_OBJECTS"}))
        for name in ("GIT_DIR", "GIT_CONFIG_PARAMETERS", "GIT_CONFIG_COUNT",
                     "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES"):
            self.assertIn(name, released.GIT_VARIABLES)


class TheModes(unittest.TestCase):
    def setUp(self):
        self.folder = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.list = self.folder / "released_names.txt"
        self.enterContext(mock.patch.object(released, "LIST_FILE", self.list))

    def run_lake(self, argv, build: int):
        """The script's exit code, standard output and standard error, with git stood in
        for as at the tag and `lake` by `lake`, its build check exiting `build`."""
        lake(self, build, STALE_SAID.encode() if build else b"")
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(released, "tag_commit", return_value=COMMIT), \
                mock.patch.object(released, "head_commit", return_value=COMMIT), \
                mock.patch.object(released, "modified", return_value=[]), \
                mock.patch.object(released, "later_tags", return_value=[]), \
                redirect_stdout(out), redirect_stderr(err):
            code = released.main(argv)
        return code, out.getvalue(), err.getvalue()

    def run_main(self, argv, rows=None, tag=COMMIT, head=COMMIT, changed=()):
        """The script's exit code, standard output and standard error, with the probe giving
        `rows` (or refusing, when `rows` is an exception) and git giving the rest."""
        probe = mock.Mock(side_effect=rows) if isinstance(rows, Exception) \
            else mock.Mock(return_value=rows)
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(released, "run_probe", probe), \
                mock.patch.object(released, "tag_commit", return_value=tag), \
                mock.patch.object(released, "head_commit", return_value=head), \
                mock.patch.object(released, "modified", return_value=list(changed)), \
                mock.patch.object(released, "later_tags", return_value=[]), \
                redirect_stdout(out), redirect_stderr(err):
            code = released.main(argv)
        return code, out.getvalue(), err.getvalue(), probe

    def write(self, *rows: str):
        self.list.write_text(text(*rows), encoding="utf-8")

    def test_the_check_exits_1_with_each_finding_and_the_summary(self):
        self.write("name Elements.a", "name Elements.b")
        code, out, _, _ = self.run_main([], {"Elements.a": "name"})
        self.assertEqual(code, 1, out)
        self.assertEqual(out.splitlines(), [
            released.finding("Elements.b", "book-III"),
            "✗ tests/released_names.txt: 2 names released in book-III: 1 present on main, 0 "
            "of them deprecated there; 1 missing with no deprecated alias"])

    def test_the_check_exits_1_when_the_tag_is_at_another_commit(self):
        self.write("name Elements.a")
        code, out, _, _ = self.run_main([], {"Elements.a": "name"}, tag=OTHER)
        self.assertEqual(code, 1, out)
        self.assertIn("so the list is not the tag's", out)

    def test_the_check_exits_0_and_notes_an_absent_tag(self):
        self.write("name Elements.a", "name Elements.b")
        code, out, _, _ = self.run_main([], {"Elements.a": "name", "Elements.b": "deprecated"},
                                        tag=None)
        self.assertEqual(code, 0, out)
        self.assertEqual(len(out.splitlines()), 2)
        self.assertIn("holds no tag book-III", out)
        self.assertIn("✓ tests/released_names.txt: 2 names released", out)

    def test_the_check_exits_2_when_it_cannot_read(self):
        self.write("name Elements.a")
        code, _, err, _ = self.run_main([], released.Unreadable("the probe's line 1 is not a "
                                                                "row"))
        self.assertEqual(code, 2)
        self.assertIn("check_released_names: the probe's line 1 is not a row", err)
        self.list.write_text(text("name Elements.b", "name Elements.a"), encoding="utf-8")
        code, _, err, probe = self.run_main([], {"Elements.a": "name"})
        self.assertEqual(code, 2)
        self.assertIn("is out of order", err)
        probe.assert_not_called()

    def test_the_self_test_stops_on_a_surprise_and_leaves_the_plants_out(self):
        self.write("name Elements.BookI.Prop1")
        rows = planted_output()
        code, out, _, probe = self.run_main(["--self-test"], rows | {f"{P}.hidden": "name"})
        self.assertEqual(code, 1, out)
        self.assertIn("✗ self-test: 1 surprise; the check is not run", out)
        self.assertNotIn("names released", out)
        self.assertEqual(probe.call_args.args, (released.probe(released.PLANTS),))
        code, out, _, _ = self.run_main(["--self-test"], rows)
        self.assertEqual(code, 0, out)
        self.assertIn("✓ self-test:", out)
        self.assertIn("1 names released in book-III: 1 present on main", out)

    def test_list_refuses_unless_at_the_tag_unmodified(self):
        cases = {
            "not a tag's name": (["--list=-x"], {}, "is not a tag's name"),
            "no such tag": (["--list", "book-IV"], {"tag": None}, "holds no tag book-IV"),
            "HEAD elsewhere": (["--list", "book-III"], {"head": OTHER},
                               f"HEAD is {OTHER}, not the tag's commit {COMMIT}"),
            "modified": (["--list", "book-III"], {"changed": ["Elements/Angle.lean"]},
                         "1 files differ from the tag's commit (Elements/Angle.lean)"),
        }
        for label, (argv, given, says) in cases.items():
            with self.subTest(label):
                code, out, err, probe = self.run_main(argv, {"Elements.a": "name"}, **given)
                self.assertEqual(code, 2, err)
                self.assertEqual(out, "")
                self.assertIn(says, err)
                probe.assert_not_called()

    def test_each_mode_refuses_a_stale_build_before_the_probe(self):
        self.write("name Elements.a")
        for argv in ([], ["--self-test"], ["--list", "book-III"]):
            with self.subTest(argv):
                code, out, err = self.run_lake(argv, 3)
                self.assertEqual(code, 2, err)
                self.assertEqual(out, "")
                self.assertTrue(err.startswith(f"check_released_names: {STALE}\n"), err)
                self.assertIn("error: target is out-of-date and needs to be rebuilt", err)
                self.assertEqual(self.ran, [BUILD_COMMAND])

    def test_on_a_current_build_the_modes_go_on_to_the_probe(self):
        self.write("name Elements.a")
        code, out, err = self.run_lake([], 0)
        self.assertEqual(code, 0, err)
        self.assertIn("✓ tests/released_names.txt: 1 names released in book-III", out)
        self.assertEqual(len(self.ran), 2)
        self.assertEqual(self.ran[0], BUILD_COMMAND)
        self.assertEqual(self.ran[1][:3], LEAN_COMMAND)
        code, out, err = self.run_lake(["--list", "book-III"], 0)
        self.assertEqual(code, 0, err)
        self.assertEqual(out, released.render_list("book-III", COMMIT, {"Elements.a": "name"}))

    def test_list_prints_a_list_that_reads_back(self):
        rows = {"Elements.a": "name", "Elements.b": "deprecated"}
        code, out, err, probe = self.run_main(["--list", "book-III"], rows)
        self.assertEqual(code, 0, err)
        self.assertEqual(out, released.render_list("book-III", COMMIT, rows))
        self.assertEqual(released.parse_list(out).names, rows)
        self.assertEqual(probe.call_args.args, (released.probe(),))


class TheRealList(unittest.TestCase):
    def test_the_real_list_reads_and_holds_the_three_names(self):
        source = (REPO / released.LIST).read_text(encoding="utf-8")
        got = released.parse_list(source)
        self.assertEqual(got.tag, "book-III")
        self.assertRegex(got.commit, r"^[0-9a-f]{40}$")
        self.assertEqual(len(got.names), 498)
        for name in THREE:
            with self.subTest(name):
                self.assertEqual(got.names.get(name), "name")
        for name in PARSERS:
            with self.subTest(name):
                self.assertNotIn(name, got.names)
        self.assertEqual(source, released.render_list(got.tag, got.commit, got.names))


if __name__ == "__main__":
    unittest.main()
