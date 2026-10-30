#!/usr/bin/env python3
"""The unfinished work and release gates, without Lean, gh or a network.

Run with python3 -I tests/test_release_gate.py. The command's fixture mode is exercised
as a subprocess; GitHub's replies and HTTP pages are data supplied by the tests. Its
--results-current mode runs git for real, in a repository the tests build for it.
"""

import io
import http.client
import json
import os
import subprocess
import sys
import tempfile
import unittest
import urllib.error
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_release_gate as gate
import safe_push

REPOSITORY_URL = "https://api.github.com/repos/example/edition"


def issue(**changes):
    return dict({"number": 38, "title": "Finish the prototype", "state": "open",
                 "labels": [{"name": "blocks-release"}],
                 "repository_url": REPOSITORY_URL,
                 "html_url": "https://github.com/example/edition/issues/38"}, **changes)


class Fixtures(unittest.TestCase):
    def run_fixture(self, data=None, *, raw=None):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "issues.json"
            path.write_text(json.dumps(data) if raw is None else raw, encoding="utf-8")
            return subprocess.run(
                [sys.executable, str(ROOT / "scripts/check_release_gate.py"),
                 "--issues-json", str(path)], capture_output=True, text=True)

    def test_empty_passes(self):
        result = self.run_fixture([])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "no open blocks-release issue")

    def test_open_labelled_issue_holds_release_and_is_named(self):
        for labels in (["blocks-release"], [{"name": "blocks-release"}]):
            with self.subTest(labels=labels):
                result = self.run_fixture([issue(labels=labels, state="OPEN")])
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("#38: Finish the prototype", result.stdout)
                self.assertIn(issue()["html_url"], result.stdout)

    def test_closed_or_unlabelled_issue_passes(self):
        for data in ([issue(state="closed")], [issue(state="CLOSED")],
                     [issue(labels=[])], [issue(labels=["text"])]):
            with self.subTest(data=data):
                result = self.run_fixture(data)
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_gh_issue_list_form_and_pull_requests_count(self):
        data = issue(labels=["blocks-release"], state="OPEN", pull_request={})
        data["url"] = data.pop("html_url")
        result = self.run_fixture([data])
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(data["url"], result.stdout)

    def test_bad_json_and_missing_fields_fail_closed(self):
        for raw in ("", "{", "null", "{}", "[null]", '[{"number": 38}]',
                    json.dumps([issue(state="unknown")]),
                    json.dumps([issue(labels=[{}])]),
                    json.dumps([issue(title="")]), json.dumps([issue(html_url="")])):
            with self.subTest(raw=raw):
                result = self.run_fixture(raw=raw)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertNotIn("no open", result.stdout)

    def test_empty_fixture_path_never_falls_back_to_github(self):
        with mock.patch.object(gate, "read_live", return_value=[]) as read, \
                mock.patch.object(gate, "repo_slug", return_value="example/edition"), \
                redirect_stderr(io.StringIO()):
            self.assertEqual(gate.main(["--issues-json", ""]), 2)
        read.assert_not_called()


COMMITTED = "harness files as committed"
OLDER = "1" * 40   # a commit the fixture's repository lacks
DIGEST = "0" * 64


def results_files(commit, state=COMMITTED):
    """The model's results, their headers as run.py writes them, naming commit."""
    line = f"# commit: {commit} ({state})\n"
    files = {f"tests/model/results/{key}.txt":
             f"# {key}: a run\n# command: python3 {key}.py\n# seeds: none (deterministic)\n"
             f"{line}# harness sha256: {DIGEST}\n# date: 2026-10-30\n\n{key}: done\n"
             for key in ("exhaustive", "mutations")}
    files["tests/model/results/summary.txt"] = f"{line}# harness: {DIGEST}\n\nno counterexample\n"
    return files


def model_page(commit, prose="The model checks each axiom on configurations of points."):
    return (f"# The model\n\n{prose}\n\n<!-- counts:begin -->\n"
            f"Counts from `run.py --full --write` at commit `{commit[:12]}`, 2026-10-30.\n"
            "<!-- counts:end -->\n\nWhat the counts say.\n")


def screen_source(record="none yet", code="RULES = 1\n"):
    return f'"""The overlap screen.\n\nIts last run: {record}.\n"""\nimport sys\n\n{code}'


class ResultsCurrent(unittest.TestCase):
    """--results-current on a git repository of its own, built as results_check's self-test
    builds one, its git run for real with its environment cleared. Its commits: O, the
    library, the model's page and results naming an older commit, the screen, the reports
    and the README; C, a change to the library; R, the results and counts naming C; S, the
    screen's record, catalogue and docstring; E, the release's decisions entry; P, the
    acceptance report. No Lean, network or gh."""

    @classmethod
    def setUpClass(cls):
        folder = tempfile.TemporaryDirectory()
        cls.addClassCleanup(folder.cleanup)
        cls.root = Path(folder.name) / "edition"
        cls.root.mkdir()
        # The script keeps HOME, so its git reads no configuration of the person running.
        home = Path(folder.name) / "home"
        home.mkdir()
        cls.home = {"HOME": str(home), "XDG_CONFIG_HOME": str(home)}
        cls.env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        cls.env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1", **cls.home)
        cls.git("init", "-q")
        cls.O = cls.commit(None, {
            "Elements/A.lean": "theorem a : True := trivial\n",
            "tests/model/MODEL.md": model_page(OLDER), **results_files(OLDER),
            "Audit/screen.py": screen_source(),
            "docs/reports/overlaps.md": "# Overlaps\n\nNone screened yet.\n",
            "docs/reports/acceptance-books-I-III.md": "Revision: none\n",
            "README.md": "# Edition\n\n<!-- scope:books -->\nBooks I and II\n"
                         "<!-- /scope:books -->\n",
            "docs/decisions/README.md": "The entries, in name order.\n",
            "docs/decisions/2026-10-21-entry-files.md": "- **Entry files.** One each.\n"})
        cls.C = cls.commit(cls.O, {"Elements/A.lean": "theorem a : True := by trivial\n"})
        cls.R = cls.commit(cls.C, {**results_files(cls.C),
                                   "tests/model/MODEL.md": model_page(cls.C)})
        cls.S = cls.commit(cls.R, {
            "Audit/screen-run.toml": f'commit = "{cls.C}"\n',
            "docs/reports/overlaps.md": "# Overlaps\n\nScreened: none closed.\n",
            "Audit/screen.py": screen_source(record=cls.C[:12])})
        cls.E = cls.commit(cls.S, {
            "docs/decisions/2026-10-30-release-books-i-iii.md": "- **The release.** Its runs.\n"})
        cls.P = cls.commit(cls.E, {"docs/reports/acceptance-books-I-III.md":
                                   f"Revision: {cls.E}\n"})

    @classmethod
    def git(cls, *args):
        return subprocess.run(["git", "-c", "user.name=release-gate test",
                               "-c", "user.email=release-gate@example.invalid", *args],
                              cwd=cls.root, env=cls.env, check=True, capture_output=True,
                              text=True).stdout.strip()

    @classmethod
    def commit(cls, base, changes):
        """A commit on base with these files changed: text, None to delete, or a function
        given the path."""
        if base:
            cls.git("checkout", "-q", "-f", "--detach", base)
            cls.git("clean", "-q", "-f", "-d", "-x")
        for name, change in changes.items():
            path = cls.root / name
            if change is None or callable(change):
                path.unlink()
            if callable(change):
                change(path)
            elif change is not None:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(change, encoding="utf-8")
        cls.git("add", "-A")
        cls.git("commit", "-q", "--allow-empty", "-m", "a commit")
        return cls.git("rev-parse", "HEAD")

    def judge(self, rev, **environ):
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.dict(os.environ, {**self.home, **environ}), \
                redirect_stdout(out), redirect_stderr(err):
            code = gate.main(["--results-current", "--repo-dir", str(self.root), f"--rev={rev}"])
        return code, out.getvalue(), err.getvalue()

    def refused(self, rev, paths, *said):
        """Exit 1, naming exactly these paths, each reason with its words."""
        code, out, err = self.judge(rev)
        self.assertEqual(code, 1, out + err)
        named = {line[2:].split(": ", 1)[0] for line in out.splitlines()
                 if line.startswith("  ")}
        self.assertEqual(named, set(paths), out)
        for words in said:
            self.assertIn(words, out)
        return out

    def test_the_heads_own_fresh_run_passes(self):
        for rev in (self.R, self.S, self.E, self.P):
            with self.subTest(rev=rev):
                code, out, err = self.judge(rev)
                self.assertEqual((code, err), (0, ""), out)
                self.assertIn(f"they name {self.C[:12]}", out)
        # Run where it is, as the coordinator runs it: HEAD, with no option but the mode.
        self.git("checkout", "-q", "-f", "--detach", self.P)
        with mock.patch.dict(os.environ, self.home), redirect_stdout(io.StringIO()):
            cwd = os.getcwd()
            try:
                os.chdir(self.root)
                self.assertEqual(gate.main(["--results-current"]), 0)
            finally:
                os.chdir(cwd)

    def test_results_from_an_older_commit_fail_naming_the_library(self):
        stale = self.commit(self.P, {**results_files(self.O),
                                     "tests/model/MODEL.md": model_page(self.O)})
        self.refused(stale, ["Elements/A.lean"],
                     f"Elements/A.lean: modified since {self.O[:12]}, the results' commit")
        # So does a change to the library made after the run, edited or added.
        changed = self.commit(self.P, {"Elements/A.lean": "theorem a : 1 = 1 := rfl\n",
                                       "Elements/B.lean": "theorem b : True := trivial\n"})
        self.refused(changed, ["Elements/A.lean", "Elements/B.lean"], "modified since",
                     "Elements/B.lean: added since")

    def test_each_change_outside_the_release_steps_outputs_is_refused(self):
        entry = "docs/decisions/2026-10-30-release-books-i-iii.md"
        old_entry = "docs/decisions/2026-10-21-entry-files.md"
        cases = [
            ({"tests/model/MODEL.md": model_page(self.C, prose="Other prose.")},
             ["tests/model/MODEL.md"], "changed outside its one counts block"),
            ({"tests/model/MODEL.md": model_page(self.C).replace("<!-- counts:end -->\n",
                                                                 "")},
             ["tests/model/MODEL.md"], "has no one counts block"),
            ({"tests/model/MODEL.md": None}, ["tests/model/MODEL.md"], "deleted since"),
            ({"Audit/screen.py": screen_source(self.C[:12], code="RULES = 2\n")},
             ["Audit/screen.py"], "changed in the code the screen hashes"),
            # Code on the docstring's last line keeps the whole text, so the change is refused.
            ({"Audit/screen.py": '"""The screen, run."""; import sys\n'},
             ["Audit/screen.py"], "changed in the code"),
            ({"Audit/screen.py": screen_source(self.C[:12], code="RULES = (\n")},
             ["Audit/screen.py"], "changed in the code"),
            ({"Audit/screen.py": None}, ["Audit/screen.py"], "deleted since"),
            ({"README.md": "# Edition\n\n<!-- scope:books -->\nBooks I to III\n"
                           "<!-- /scope:books -->\n"}, ["README.md"], "modified since"),
            ({old_entry: "- **Entry files.** Two each.\n"}, [old_entry], "modified since"),
            ({old_entry: None}, [old_entry], "deleted since"),
            ({"docs/decisions/README.md": "Changed.\n"}, ["docs/decisions/README.md"],
             "modified since"),
            ({"docs/decisions/2026-10-30-second.md": "- **Another.** Its runs.\n"},
             [entry, "docs/decisions/2026-10-30-second.md"],
             "one of 2 decisions entries added, where a release adds one"),
            ({"docs/decisions/2026-10-30-Release.md": "- **Misnamed.**\n"},
             ["docs/decisions/2026-10-30-Release.md"], "added since"),
            ({"tests/model/results/mutations.txt": None},
             ["tests/model/results/mutations.txt"], "deleted since"),
            ({"tests/model/results/notes.md": "A note.\n"},
             ["tests/model/results/notes.md"], "added since"),
            ({"tests/model/results/mutations.txt": lambda p: p.symlink_to("summary.txt")},
             ["tests/model/results/mutations.txt"], "not a regular file", "changed in type"),
            ({"docs/reports/overlaps.md": None}, ["docs/reports/overlaps.md"], "deleted"),
            ({"docs/reports/acceptance-books-I-III.md": None},
             ["docs/reports/acceptance-books-I-III.md"], "deleted"),
            ({"facts.json": "{}\n"}, ["facts.json"], "added since"),
        ]
        for changes, paths, *said in cases:
            with self.subTest(changes=list(changes), said=said):
                self.refused(self.commit(self.P, changes), paths, *said)

    def test_results_that_name_another_commit_or_state_are_refused(self):
        two = self.commit(self.P, results_files(self.O) | {
            k: v for k, v in results_files(self.C).items() if k.endswith("summary.txt")})
        out = self.refused(two, ["the results name 2 commits"])
        self.assertIn(f"{self.C[:12]} in tests/model/results/summary.txt", out)
        state = self.commit(self.P, {k: v for k, v in results_files(
            self.C, "harness files differ from this commit").items()
            if k.endswith("mutations.txt")})
        self.refused(state, ["tests/model/results/mutations.txt"],
                     '"(harness files differ from this commit)", not '
                     '"(harness files as committed)"')
        named = self.commit(self.P, {"tests/model/MODEL.md": model_page(self.O)})
        self.refused(named, ["tests/model/MODEL.md"],
                     f"its counts name {self.O[:12]}, not {self.C[:12]}")
        # Results run on a side branch: their commit is not in the head's history.
        side = self.commit(self.O, {"Elements/A.lean": "theorem a : 2 = 2 := rfl\n"})
        moved = self.commit(self.P, {**results_files(side),
                                     "tests/model/MODEL.md": model_page(side)})
        self.refused(moved, [f"{side[:12]}, the results' commit, is not an ancestor of "
                             f"{moved[:12]}"])

    def test_paths_are_printed_escaped(self):
        out = self.refused(self.commit(self.P, {"Elements/\x1b[2J.lean": "x\n"}),
                           ["Elements/\\x1b[2J.lean"])
        self.assertNotIn("\x1b", out)

    def test_what_cannot_be_read_is_exit_two(self):
        summary = "tests/model/results/summary.txt"
        line = f"# commit: {self.C} ({COMMITTED})\n"
        cases = [
            (self.commit(self.P, {**results_files(OLDER),
                                  "tests/model/MODEL.md": model_page(OLDER)}), "lacks"),
            (self.O, "lacks"),
            (self.commit(self.P, {k: None for k in results_files(self.C)}),
             "holds no tests/model/results"),
            (self.commit(self.P, {**{k: None for k in results_files(self.C)},
                                  "tests/model/results/README": "Notes.\n"}),
             "holds no results in tests/model/results"),
            (self.commit(self.P, {"tests/model/results/mutations.txt":
                                  "# mutations: a run\n# command: c\n# seeds: none\n"
                                  "# commit: unknown (state unknown)\n\n"}),
             "mutations.txt: its header names no commit, once, on line 4"),
            (self.commit(self.P, {summary: f"# harness: {DIGEST}\n{line}\n"}),
             "summary.txt: its header names no commit, once, on line 1"),
            (self.commit(self.P, {summary: f"{line}{line}\n"}),
             "summary.txt: its header names no commit, once"),
            (self.commit(self.P, {summary: f"{line.rstrip()} \n\n"}), "on line 1"),
            ("no-such-branch", "names no commit"),
            ("--output=/dev/null", "names no commit"),
        ]
        for rev, said in cases:
            with self.subTest(rev=rev, said=said):
                code, out, err = self.judge(rev)
                self.assertEqual(code, 2, out + err)
                self.assertEqual(out, "")
                self.assertIn(said, err)
        with tempfile.TemporaryDirectory() as empty, redirect_stderr(io.StringIO()), \
                mock.patch.dict(os.environ, self.home):
            self.assertEqual(gate.main(["--results-current", "--repo-dir", empty]), 2)

    def test_git_is_not_redirected_by_the_environment_or_replacements(self):
        stale = self.commit(self.P, {"Elements/A.lean": "theorem a : 3 = 3 := rfl\n"})
        other = Path(self.root.parent) / "other"
        subprocess.run(["git", "init", "-q", str(other)], env=self.env, check=True,
                       capture_output=True)
        redirect = {"GIT_DIR": str(other / ".git"), "GIT_WORK_TREE": str(other),
                    "GIT_OBJECT_DIRECTORY": str(other / ".git/objects"),
                    "GIT_INDEX_FILE": str(other / ".git/index"),
                    "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "diff.external",
                    "GIT_CONFIG_VALUE_0": "false"}
        self.assertEqual(self.judge(self.P, **redirect)[0], 0)
        self.assertEqual(self.judge(stale, **redirect)[0], 1)
        # A replacement cannot make a stale head read as the fresh one.
        self.git("replace", stale, self.P)
        try:
            self.assertEqual(self.git("rev-parse", f"{stale}^{{tree}}"),
                             self.git("rev-parse", f"{self.P}^{{tree}}"))
            self.refused(stale, ["Elements/A.lean"])
        finally:
            self.git("replace", "-d", stale)

    def test_the_command_line(self):
        script = str(ROOT / "scripts/check_release_gate.py")
        env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        env.update(self.home)
        stale = self.commit(self.P, {"Elements/A.lean": "theorem a : 4 = 4 := rfl\n"})
        for rev, code, stream, words in (
                (self.P, 0, "stdout", "the model's results are current"),
                (stale, 1, "stdout", "Elements/A.lean: modified since"),
                (self.O, 2, "stderr", "release gate: the results name")):
            with self.subTest(code=code):
                result = subprocess.run([sys.executable, script, "--results-current",
                                         "--repo-dir", str(self.root), "--rev", rev],
                                        capture_output=True, text=True, env=env)
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn(words, getattr(result, stream))
        for args, words in ((["--results-current", "--issues-json", os.devnull],
                             "--results-current reads no issue"),
                            (["--results-current", "--repo", "example/edition"],
                             "--results-current reads no issue"),
                            (["--repo-dir", str(self.root)], "go with --results-current"),
                            (["--issues-json", os.devnull, "--rev", self.P],
                             "go with --results-current")):
            with self.subTest(args=args):
                result = subprocess.run([sys.executable, script, *args], capture_output=True,
                                        text=True, env=env)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertEqual(result.stdout, "")
                self.assertIn("usage:", result.stderr)
                self.assertIn(words, result.stderr)

    def test_the_patterns_are_run_pys(self):
        # tests/model/run.py is imported as results_check imports it, but in a process of
        # its own, so that the harness modules its import brings stay out of this one; its
        # header() is given a stand-in run, and its paths are taken from its root.
        program = (
            "import json, os, sys, types\n"
            "sys.path.insert(0, os.path.join(sys.argv[1], 'tests', 'model'))\n"
            "import run\n"
            "r = types.SimpleNamespace(key='k', what='w', command='c', seeds=None, seconds=0.0)\n"
            "prov = {'commit': 'a' * 40 + ' (' + run.COMMITTED + ')', 'harness': 'h',\n"
            "        'python': 'p', 'date': 'd'}\n"
            "print(json.dumps({'committed': run.COMMITTED, 'counts_from': run.COUNTS_FROM,\n"
            "    'counts': [run.COUNTS.pattern, run.COUNTS.flags], 'summary': run.SUMMARY,\n"
            "    'results': os.path.relpath(run.RESULTS, run.ROOT),\n"
            "    'model_md': os.path.relpath(run.MODEL_MD, run.ROOT),\n"
            "    'header': run.header(r, prov), 'short': run.short_commit(prov['commit'])}))\n")
        result = subprocess.run([sys.executable, "-I", "-c", program, str(ROOT)],
                                capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(result.returncode, 0, result.stderr)
        run = json.loads(result.stdout)
        self.assertEqual(gate.COMMITTED, run["committed"])
        self.assertEqual(gate.COUNTS_FROM, run["counts_from"])
        self.assertEqual([gate.COUNTS.pattern, gate.COUNTS.flags], run["counts"])
        self.assertEqual((gate.SUMMARY, gate.RESULTS, gate.MODEL_MD),
                         (run["summary"], run["results"], run["model_md"]))
        self.assertEqual(run["short"], "a" * 12)
        match = gate.COMMIT_LINE.fullmatch(run["header"].splitlines()[3])
        self.assertEqual(match.groups(), ("a" * 40, COMMITTED))
        # And each of this repository's own results names its commit where the gate reads.
        for path in sorted((ROOT / gate.RESULTS).glob("*.txt")):
            with self.subTest(path=path.name):
                lines = path.read_text(encoding="utf-8").splitlines()
                at = 0 if path.name == gate.SUMMARY else 3
                self.assertTrue(gate.COMMIT_LINE.fullmatch(lines[at]), lines[at])


class UnfinishedWork(unittest.TestCase):
    def refs(self, text):
        return safe_push.unfinished_refs(text)

    TEMPLATE = ("## What and why\n\n## Unfinished work\n\n<!-- Name each piece. -->\n\n"
                "## Review records\n\n## Checklist\n")

    def section(self, text, before="", after=""):
        """A body from the small template above, its section holding text."""
        body = self.TEMPLATE.replace("<!-- Name each piece. -->\n",
                                     "<!-- Name each piece. -->\n" + text + "\n")
        return before + body + after

    def gate(self, body, template=None):
        ctx = safe_push.Context(ROOT, "", "", 0, "", "example/edition", {})
        with mock.patch.object(safe_push, "read_issues") as read:
            verdict, detail = safe_push.unfinished_gate(ctx, body, template or self.TEMPLATE)
            read.assert_not_called()
        return verdict, detail

    def test_the_one_heading_exactly(self):
        self.assertEqual(self.gate(self.section("None")), ("ok", "None"))
        for heading in ("# Unfinished work", "### Unfinished work", "## Unfinished work ##",
                        "  ## Unfinished work", "## unfinished work", "##\tUnfinished work",
                        "Unfinished work\n===", "Unfinished work\n---"):
            with self.subTest(heading=heading):
                body = self.section("None").replace("## Unfinished work", heading)
                verdict, detail = self.gate(body)
                self.assertEqual(verdict, "FAIL")
                self.assertIn("exactly one ## Unfinished work heading", detail)

    def test_a_second_heading_or_look_alike_anywhere_is_refused(self):
        for alike in ("## Unfinished work", "## Unfinished work ##", "### Unfinished work",
                      "<h2>Unfinished work</h2>", "> ## Unfinished work", "- ## Unfinished work",
                      "## Unfinished&#32;work", "## *Unfinished work*",
                      "## Unfinished work (continued)", "## Unfinished\u200bwork",
                      "## \uff35nfinished work", "Unfinished\nwork\n---",
                      "unfinished work\n==="):
            for wrapper in ("{}", "<!--\n{}\n-->", "```\n{}\n```"):
                with self.subTest(alike=alike, wrapper=wrapper):
                    body = self.section("None", after="\n" + wrapper.format(alike)
                                        + "\n- Deferred page to come\n")
                    verdict, detail = self.gate(body)
                    self.assertEqual(verdict, "FAIL")
                    self.assertIn("exactly one ## Unfinished work heading", detail)

    def test_a_heading_github_does_not_show_is_refused(self):
        for before, after in (("<!--", "-->"), ("```", "```"), ("~~~", "~~~"),
                              ("<div>", "</div>"), ("<details>", "</details>"),
                              ("<!-- safe_push:custom begin -->",
                               "<!-- safe_push:custom end -->")):
            with self.subTest(before=before):
                body = self.section("None").replace(
                    "## Unfinished work\n", f"{before}\n## Unfinished work\nNone\n"
                    f"## Review records\n{after}\n\n", 1)
                verdict, detail = self.gate(body)
                self.assertEqual(verdict, "FAIL")
                self.assertIn("must be one GitHub shows", detail)
        # A part safe_push writes is read in place, as GitHub shows it: a fence opened in
        # it hides the heading after it, run to the end or closed by a longer fence.
        for closer in ("", "````\n"):
            with self.subTest(closer=closer):
                body = self.TEMPLATE.replace(
                    "## Unfinished work\n\n<!-- Name each piece. -->\n\n", "") + (
                    "<!-- safe_push:custom begin -->\n```\n<!-- safe_push:custom end -->\n"
                    "## Unfinished work\nNone\n## Review records\n" + closer)
                verdict, detail = self.gate(body)
                self.assertEqual(verdict, "FAIL")
                self.assertIn("must be one GitHub shows", detail)
        # Each closed before the heading, it is shown, and the section is read.
        shown_body = self.section("None", before="<!--\nA note.\n-->\n```\ncode\n```\n"
                                  "<div>\nA note.\n</div>\n\n<!-- safe_push:custom begin -->\n"
                                  "- A commit\n<!-- safe_push:custom end -->\n\n")
        self.assertEqual(self.gate(shown_body), ("ok", "None"))

    def test_section_ends_only_at_the_templates_next_heading(self):
        for line in ("##", "## #", "# Next", "## Next", "### Next", "---", "===",
                     "## &nbsp;", "  ## Next"):
            with self.subTest(line=line):
                verdict, _ = self.gate(self.section("None\n\n" + line
                                                    + "\n\n- Deferred page to come"))
                self.assertEqual(verdict, "FAIL")
        # No following heading of the template: refused, never read to the end.
        body = "## Unfinished work\n\nNone\n"
        self.assertIn("next heading", self.gate(body)[1])
        # With no template, the section runs to the end of the body.
        self.assertEqual(safe_push.unfinished_section(body), ("\nNone\n", []))

    def test_breaks_github_and_the_gate_read_differently_are_refused(self):
        for sep in ("\u2028", "\u2029", "\x0b", "\x0c", "\x85", "\r", "\x1c"):
            with self.subTest(sep=repr(sep)):
                body = self.section("None." + sep + "##\n\n- Prototype with no issue")
                verdict, detail = self.gate(body)
                self.assertEqual(verdict, "FAIL")
                self.assertIn("break", detail)
        # A body edited on GitHub's page has CRLF line ends: those are fine.
        crlf = self.section("- Prototype #38").replace("\n", "\r\n")
        text, problems = safe_push.unfinished_section(crlf, self.TEMPLATE)
        self.assertEqual(problems, [])
        self.assertEqual(safe_push.unfinished_refs(text, "<!-- Name each piece. -->"),
                         ([38], []))

    def test_comments_other_than_the_templates_are_refused(self):
        for text in ("None <!--\n\n- Deferred page to come\n\n-->",
                     "None\n<!-->\n- Prototype with no issue\n<!-- -->",
                     "- Prototype #38 <!--\n- Deferred page to come\n-->",
                     "<!-- safe_push:custom begin -->\n- Prototype with no issue\n"
                     "<!-- safe_push:custom end -->",
                     "<!-- safe_push:commits begin -->\n- Prototype #38\n"
                     "<!-- safe_push:commits end -->",
                     "None\n\n<div><ul><li>Deferred page</li></ul></div>",
                     "None\n\n```\n- Deferred page to come\n```",
                     "None\n\n~~~\n- Deferred page to come\n~~~"):
            with self.subTest(text=text):
                self.assertEqual(self.gate(self.section(text))[0], "FAIL")
        # The template's own comment may stay, or go.
        self.assertEqual(self.gate(self.section("None")), ("ok", "None"))
        self.assertEqual(self.gate(self.section("None").replace(
            "<!-- Name each piece. -->\n", "")), ("ok", "None"))

    def test_non_ascii_and_other_issue_forms_are_refused(self):
        for text in ("- Prototype #38, deferred page GH-39", "- Prototype #38, page *GH-39*",
                     '- Prototype #38, page "GH-39"', "- Prototype #\u00ad38",
                     "- Prototype #\uff13\uff18", "- Prototype \u00e9 #38",
                     "- Prototype & #38", "- Prototype&nbsp;#38"):
            with self.subTest(text=text):
                refs, problems = self.refs(text)
                self.assertTrue(problems)

    def test_text_after_the_template_comment_on_its_line_is_refused(self):
        comment = "<!-- Name each piece. -->"
        refs, problems = safe_push.unfinished_refs(
            "- Prototype #38\n" + comment + "  Deferred page with no issue", comment)
        self.assertIn("comment other than the template's own", "\n".join(problems))
        self.assertEqual(safe_push.unfinished_refs("- Prototype #38\n" + comment, comment),
                         ([38], []))

    def test_the_ascii_refusal_names_the_character_and_its_line(self):
        refs, problems = self.refs("- Prototype #38\n- III.18\u2013III.22 awaiting, #39")
        self.assertIn("U+2013 on line 2", "\n".join(problems))

    def test_addresses_and_emphasis_are_refused(self):
        for text in ("- Prototype #38; see github.com/example/edition/issues/39",
                     "- Prototype #38, example/edition/issues/39",
                     "- Prototype #38, example/edition/pull/40",
                     "- Prototype #38 example.org/ticket/39",
                     "- Prototype #38 192.0.2.1/ticket/39",
                     "- Prototype #38 localhost:8080/ticket/39",
                     "- **Prototype** #38", "- Prototype *later* #38",
                     "- _Prototype_ #38"):
            with self.subTest(text=text):
                self.assertTrue(self.refs(text)[1])
        # The list marker "* " stays allowed.
        self.assertEqual(self.refs("* Prototype #38"), ([38], []))

    def test_a_stale_template_comment_is_named_as_such(self):
        refs, problems = self.refs("<!-- An older wording. -->\nNone")
        self.assertIn("comment other than the template's own", "\n".join(problems))

    def test_issue_titles_are_printed_escaped(self):
        self.assertEqual(safe_push.printable_text("a\x1b[2Jb\u202e"), "a\\x1b[2Jb\\u202e")
        ctx = safe_push.Context(ROOT, "", "", 0, "", "example/edition", {}, gh=("stand-in",))
        with mock.patch.object(safe_push, "read_issues",
                               return_value=[issue(title="Finish\x1b]0;x\x07 it")]):
            verdict, detail = safe_push.release_gate(ctx, {"release"})
        self.assertEqual(verdict, "FAIL")
        self.assertNotIn("\x1b", detail)
        self.assertIn("\\x1b", detail)

    def test_template_and_required_box(self):
        template = (ROOT / safe_push.TEMPLATE).read_text()
        headings = list(safe_push.sections(template))
        self.assertLess(headings.index("Statements changed"), headings.index("Unfinished work"))
        self.assertLess(headings.index("Unfinished work"), headings.index("Review records"))
        self.assertTrue(any(kind == "Required" and '"Unfinished work"' in text
                            and "blocks-release" in text
                            for _, kind, text in safe_push.boxes(template)))
        comment, ends = safe_push.template_section(template)
        self.assertTrue(comment.startswith("<!--") and comment.endswith("-->"))
        self.assertIn("## Review records", ends)
        # The template as it stands: its section unwritten, so refused; written, it passes.
        text, problems = safe_push.unfinished_section(template, template)
        self.assertEqual(problems, [])
        self.assertTrue(safe_push.unfinished_refs(text, comment)[1])
        written = template.replace(comment + "\n", comment + "\n\nNone\n", 1)
        text, problems = safe_push.unfinished_section(written, template)
        self.assertEqual(safe_push.unfinished_refs(text, comment), ([], []))

    def test_empty_section_refused(self):
        refs, problems = self.refs("")
        self.assertEqual(refs, [])
        self.assertTrue(problems)

    def test_none_passes(self):
        for text in ("None", "None.", "  nOnE. \n"):
            with self.subTest(text=text):
                self.assertEqual(self.refs(text), ([], []))
        for text in ("None yet", "- None", "`None`", "None.."):
            with self.subTest(text=text):
                self.assertTrue(self.refs(text)[1])

    def test_local_references_collected_once(self):
        self.assertEqual(self.refs(
            "- Prototype #38\n- Page #39\n* Test (#38), #39"), ([38, 39], []))
        self.assertEqual(self.refs("- Prototype awaiting a proof (#38)"), ([38], []))
        self.assertEqual(self.refs("* Two pieces #38, #39"), ([38, 39], []))
        # An item may begin with its issue: "#38" followed by a word is no heading.
        self.assertEqual(self.refs("- #38, the prototype"), ([38], []))
        self.assertEqual(self.refs("- #38: a deferred page"), ([38], []))

    def test_wrapped_item_can_name_its_issue_on_the_continuation(self):
        self.assertEqual(self.refs("- Prototype awaiting a proof,\n  tracked by #38."),
                         ([38], []))
        self.assertEqual(self.refs("- Prototype awaiting a proof\n  #38"), ([38], []))

    def test_anchor_and_url_fragment_do_not_name_issues(self):
        for text in ("[section](#38)", "https://example.invalid/page?x=#38", "page#38"):
            with self.subTest(text=text):
                refs, problems = self.refs("- Prototype " + text)
                self.assertEqual(refs, [])
                self.assertTrue(problems)

    def test_code_html_and_reference_definitions_are_refused(self):
        for text, reason in (
                ("- Prototype `code\n  #38`", "backtick"),
                ("- ```\n  #38\n  ```", "backtick"),
                ('- Prototype <span title="#38">later</span>', "HTML"),
                ("[prototype]: https://github.com/example/edition/issues/38", "bracket"),
                ("> - Prototype #38\n> - Deferred page to come", "block quote"),
                ("- Prototype ~~~ #38", "tilde")):
            with self.subTest(text=text):
                refs, problems = self.refs(text)
                self.assertEqual(refs, [])
                self.assertIn(reason, "\n".join(problems))

    def test_only_plain_top_level_items_and_wrapped_text_are_allowed(self):
        for text in ("Prototype #38", "1. Prototype #38", "+ Prototype #38",
                     " - Prototype #38", "- Prototype #38\n  - Deferred #39",
                     "- Prototype #38\n  1. Deferred #39",
                     "- Prototype #38\n  ### Deferred #39",
                     "- Prototype #38\nDeferred #39", "  Wrapped #38",
                     "-     Prototype #38", "-\tPrototype #38",
                     "- Prototype #38\n\n  Detached #39", "- Prototype #38\n      Code #39",
                     "- Prototype #38\n One space #39", "- + Nested #38",
                     "- 1) Nested #38", "- # Heading #38", "- ---", "* * * *",
                     "- Prototype #38\n  _ _ _"):
            with self.subTest(text=text):
                self.assertTrue(self.refs(text)[1])

    def test_qualified_shorthand_is_refused_even_for_this_repository(self):
        refs, problems = self.refs("- Prototype example/edition#38 and #39")
        self.assertEqual(refs, [39])
        self.assertIn("write the issue as #N on its own", "\n".join(problems))

    def test_foreign_references_refused_even_beside_local(self):
        for text in ("other/repo#38", "x=#38", "page#38", "(#38)extra", "#0", "#038",
                     "#38,#39", "fooGH-39"):
            with self.subTest(text=text):
                refs, problems = self.refs("- Prototype " + text + " and #40")
                self.assertEqual(refs, [40])
                self.assertIn("write the issue as #N on its own", "\n".join(problems))
        refs, problems = self.refs("- Prototype #38 fooGH-39")
        self.assertEqual(refs, [38])
        self.assertIn("write the issue as #N on its own", "\n".join(problems))

    def test_urls_and_forbidden_characters_are_refused(self):
        for text, reason in (
                ("https://example.invalid/page(#38)", "URL"),
                ("https://elsewhere.invalid/?next=https://github.com/example/edition/issues/38", "URL"),
                ("https://elsewhere.invalid/#https://github.com/example/edition/issues/38", "URL"),
                ("https://github.com/example/edition/issues/38/garbage", "URL"),
                ("https://github.com/other/repo/issues/38", "URL"),
                ("www.example.invalid", "URL"),
                ("WWW.GITHUB.COM/example/edition/issues/39", "URL"),
                ("~", "tilde"), ("|", "pipe"),
                ("\\", "backslash"), ("\t", "tab"), ("<!-- unclosed", "comment")):
            with self.subTest(text=text):
                refs, problems = self.refs("- Prototype " + text + " #38")
                self.assertEqual(refs, [])
                self.assertIn(reason, "\n".join(problems))
        refs, problems = self.refs(
            "- Prototype #38, see WWW.GITHUB.COM/example/edition/issues/39")
        self.assertEqual(refs, [])
        self.assertIn("URL", "\n".join(problems))

    def test_each_list_item_needs_its_issue(self):
        refs, problems = self.refs("- Prototype #38\n- Page to come\n* Test to come")
        self.assertEqual(refs, [38])
        self.assertEqual(len(problems), 2)
        self.assertIn("Page to come", problems[0])
        self.assertIn("Test to come", problems[1])

    def test_comments_code_and_own_parts_do_not_supply_issues(self):
        for text in ("<!-- #38 -->", "```\n#38\n```", "~~~\n#38\n~~~",
                     "    #38", "`#38`", "- Prototype <!-- #38 -->",
                     "<!-- safe_push:commits begin -->\n#38\n"
                     "<!-- safe_push:commits end -->"):
            with self.subTest(text=text):
                refs, problems = self.refs(text)
                self.assertEqual(refs, [])
                self.assertTrue(problems)

    def test_issue_must_be_open_labelled_and_not_a_pull_request(self):
        self.assertEqual(safe_push.unfinished_issue_problems(38, issue(), REPOSITORY_URL), [])
        for data, wanted in ((issue(labels=[]), "lacks the label"),
                             (issue(state="closed"), "is closed"),
                             (issue(pull_request={}), "is a pull request"),
                             (issue(number=39), "another number"),
                             ({}, "unreadable"), (None, "unreadable")):
            with self.subTest(data=data):
                self.assertIn(wanted, "\n".join(
                    safe_push.unfinished_issue_problems(38, data, REPOSITORY_URL)))

    def test_old_template_does_not_require_the_section(self):
        with mock.patch.object(safe_push, "read_issues") as read:
            ctx = safe_push.Context(ROOT, "", "", 0, "", "example/edition", {})
            self.assertEqual(safe_push.unfinished_gate(ctx, "", "## What and why")[0], "skip")
            read.assert_not_called()
        self.assertEqual(safe_push.section_problems("", "## Reviews", False), [
            'missing from the body: the section "Reviews"'])


class ReleaseReads(unittest.TestCase):
    def setUp(self):
        self.ctx = safe_push.Context(ROOT, "", "", 0, "", "example/edition", {},
                                     gh=("stand-in",))

    def test_pure_release_judgement(self):
        self.assertEqual(safe_push.open_blockers([]), [])
        self.assertEqual(safe_push.open_blockers([issue()]), [issue()])
        self.assertEqual(safe_push.open_blockers([issue(state="closed"), issue(labels=[])]), [])
        self.assertEqual(len(safe_push.open_blockers([issue(pull_request={})])), 1)
        with self.assertRaises(ValueError):
            safe_push.open_blockers([issue(), {}])

    def test_all_concatenated_pages_are_read(self):
        self.assertEqual(safe_push.issue_pages('[]\n' + json.dumps([issue()]) + '\n[]'),
                         [issue()])
        for text in ("", "null", "{}", "[]\n[", "[]\n{}", "[]\nnull"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                safe_push.issue_pages(text)

    def test_release_gate_and_ordinary_skip(self):
        with mock.patch.object(safe_push, "read_issues", return_value=[issue()]) as read:
            self.assertEqual(safe_push.release_gate(self.ctx, {"tooling"})[0], "skip")
            read.assert_not_called()
            verdict, detail = safe_push.release_gate(self.ctx, {"release"})
            self.assertEqual(verdict, "FAIL")
            self.assertIn("#38: Finish the prototype", detail)
            read.assert_called_once_with(
                self.ctx, "repos/example/edition/issues?labels=blocks-release&state=open&per_page=100",
                paginate=True)
            read.return_value = []
            self.assertEqual(safe_push.release_gate(self.ctx, {"release"})[0], "ok")

    def test_release_label_case_cannot_bypass_blockers_or_unreadable_replies(self):
        for label in ("Release", "RELEASE"):
            with self.subTest(label=label):
                with mock.patch.object(safe_push, "read_issues", return_value=[
                        issue(labels=[{"name": "BLOCKS-RELEASE"}])]):
                    verdict, detail = safe_push.release_gate(self.ctx, {label})
                self.assertEqual(verdict, "FAIL")
                self.assertIn("#38", detail)
                with mock.patch.object(safe_push, "read_issues", side_effect=ValueError("bad")):
                    verdict, detail = safe_push.release_gate(self.ctx, {label})
                self.assertEqual(verdict, "FAIL")
                self.assertIn("unreadable", detail)

    def test_exactly_one_raw_unfinished_section_is_required(self):
        for body in ("", "## Unfinished work\nNone\n## Unfinished work\n- Prototype #38"):
            with self.subTest(body=body), mock.patch.object(safe_push, "read_issues") as read:
                verdict, detail = safe_push.unfinished_gate(self.ctx, body, "## Unfinished work")
                self.assertEqual(verdict, "FAIL")
                self.assertIn("exactly one", detail)
                read.assert_not_called()
        body = ("<!-- ## Unfinished work -->\n```\n## Unfinished work\n```\n"
                "## Unfinished work\nNone")
        self.assertEqual(safe_push.unfinished_gate(
            self.ctx, body, "## Unfinished work")[0], "FAIL")

    def test_issues_are_bound_to_the_canonical_repository_read_once(self):
        renamed = "https://api.github.com/repos/example/renamed"
        replies = [{"url": renamed},
                   issue(repository_url=renamed.upper(), labels=["Blocks-Release"]),
                   issue(number=39, repository_url=renamed)]
        with mock.patch.object(safe_push, "read_issues", side_effect=replies) as read:
            self.assertEqual(safe_push.unfinished_gate(
                self.ctx, "## Unfinished work\n- Prototype #38 and #39",
                "## Unfinished work"), ("ok", "#38, #39"))
        self.assertEqual(read.call_args_list, [
            mock.call(self.ctx, "repos/example/edition"),
            mock.call(self.ctx, "repos/example/edition/issues/38"),
            mock.call(self.ctx, "repos/example/edition/issues/39")])

    def test_transferred_or_unbound_issue_is_refused(self):
        missing = issue()
        del missing["repository_url"]
        for data, wanted in (
                (issue(repository_url="https://api.github.com/repos/other/edition"),
                 "another repository"),
                (missing, "repository_url"),
                (issue(repository_url=None), "repository_url")):
            with self.subTest(data=data), mock.patch.object(
                    safe_push, "read_issues", side_effect=[{"url": REPOSITORY_URL}, data]):
                verdict, detail = safe_push.unfinished_gate(
                    self.ctx, "## Unfinished work\n- Prototype #38", "## Unfinished work")
                self.assertEqual(verdict, "FAIL")
                self.assertIn(wanted, detail)

    def test_canonical_repository_must_be_read_successfully_through_ctx_gh(self):
        for data in (None, {}, {"url": None}, {"url": ""}, {"url": "not a repository URL"}):
            with self.subTest(data=data), mock.patch.object(
                    safe_push, "run",
                    return_value=subprocess.CompletedProcess([], 0, json.dumps(data), "")) as run:
                verdict, detail = safe_push.unfinished_gate(
                    self.ctx, "## Unfinished work\n- Prototype #38", "## Unfinished work")
                self.assertEqual(verdict, "FAIL")
                self.assertIn("repository unreadable", detail)
                run.assert_called_once_with(
                    ["stand-in", "api", "repos/example/edition"], ROOT)
        reply = subprocess.CompletedProcess([], 1, json.dumps({"url": REPOSITORY_URL}), "")
        with mock.patch.object(safe_push, "run", return_value=reply):
            verdict, detail = safe_push.unfinished_gate(
                self.ctx, "## Unfinished work\n- Prototype #38", "## Unfinished work")
        self.assertEqual(verdict, "FAIL")
        self.assertIn("repository unreadable", detail)

    def test_failed_command_with_valid_stdout_is_not_a_read(self):
        reply = subprocess.CompletedProcess([], 1, "[]", "private diagnostic")
        with mock.patch.object(safe_push, "run", return_value=reply):
            verdict, detail = safe_push.release_gate(self.ctx, {"release"})
            self.assertEqual(verdict, "FAIL")
            self.assertNotIn("private diagnostic", detail)
        with mock.patch.object(gate.shutil, "which", return_value="stand-in"), \
                mock.patch.object(gate.subprocess, "run", return_value=reply):
            with self.assertRaisesRegex(ValueError, "exit 1"):
                gate.read_live("example/edition")

    def test_standalone_gh_read_uses_every_page(self):
        reply = subprocess.CompletedProcess([], 0, '[]\n' + json.dumps([issue()]), "")
        with mock.patch.object(gate.shutil, "which", return_value="stand-in"), \
                mock.patch.object(gate.subprocess, "run", return_value=reply) as run:
            self.assertEqual(gate.read_live("example/edition"), [issue()])
            self.assertEqual(run.call_args.args[0], [
                "stand-in", "api", "--paginate",
                "repos/example/edition/issues?labels=blocks-release&state=open&per_page=100"])

    def test_missing_fields_bad_json_and_command_errors_refuse(self):
        for reply in ("null", "{}", "[]", '{"number": 38}', "{"):
            with self.subTest(reply=reply), mock.patch.object(
                    safe_push, "run", side_effect=[
                        subprocess.CompletedProcess([], 0, json.dumps({"url": REPOSITORY_URL}), ""),
                        subprocess.CompletedProcess([], 0, reply, "")]):
                verdict, detail = safe_push.unfinished_gate(
                    self.ctx, "## Unfinished work\n- Prototype #38", "## Unfinished work")
                self.assertEqual(verdict, "FAIL")
                self.assertIn("#38 unreadable", detail)
        with mock.patch.object(safe_push, "run", side_effect=OSError("private diagnostic")):
            self.assertEqual(safe_push.release_gate(self.ctx, {"release"})[0], "FAIL")

    def test_repo_resolution_and_validation(self):
        with mock.patch.dict(os.environ, {"GITHUB_REPOSITORY": "example/edition"}, clear=True):
            self.assertEqual(gate.repo_slug(None), "example/edition")
        with mock.patch.dict(os.environ, {}, clear=True), mock.patch.object(
                gate.subprocess, "run",
                return_value=subprocess.CompletedProcess([], 0, "git@github.com:example/edition.git\n", "")):
            self.assertEqual(gate.repo_slug(None), "example/edition")
        for slug in ("../edition", "example/..", "example/repo?token=x", "x/y/z", "x y/z"):
            with self.subTest(slug=slug), self.assertRaises(ValueError):
                gate.repo_slug(slug)
        with mock.patch.dict(os.environ, {}, clear=True), mock.patch.object(
                gate.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, "", "")):
            with self.assertRaises(ValueError):
                gate.repo_slug(None)

    def test_no_credentials_is_exit_two(self):
        with mock.patch.object(gate.shutil, "which", return_value=None), \
                mock.patch.dict(os.environ, {}, clear=True), redirect_stderr(io.StringIO()):
            self.assertEqual(gate.main(["--repo", "example/edition"]), 2)

    def test_rest_pagination_and_token_is_only_in_header(self):
        def response(data, link=""):
            stream = io.BytesIO(json.dumps(data).encode())
            stream.headers = {"Link": link}
            return stream

        for path in ("/repos/example/edition/issues", "/repositories/123/issues"):
            with self.subTest(path=path):
                next_url = "https://api.github.com" + path + "?page=2"
                opener = mock.Mock()
                opener.open.side_effect = [
                    response([], f'<{next_url}>; rel="next"'), response([issue()])]
                with mock.patch.object(gate.urllib.request, "build_opener", return_value=opener):
                    self.assertEqual(gate.rest_issues("example/edition", "test-token"), [issue()])
                requests = [call.args[0] for call in opener.open.call_args_list]
                self.assertEqual(requests[1].full_url, next_url)
                for request in requests:
                    self.assertNotIn("test-token", request.full_url)
                    self.assertEqual(request.get_header("Authorization"), "Bearer test-token")

    def test_rest_error_reports_only_status_and_path(self):
        opener = mock.Mock()
        opener.open.side_effect = urllib.error.HTTPError(
            "https://api.github.com/private?token=test-token", 403, "test-token", {}, None)
        with mock.patch.object(gate.urllib.request, "build_opener", return_value=opener):
            with self.assertRaises(ValueError) as raised:
                gate.rest_issues("example/edition", "test-token")
        self.assertEqual(str(raised.exception), "HTTP 403: /repos/example/edition/issues")

    def test_incomplete_rest_response_is_exit_two_without_its_bytes(self):
        opener = mock.Mock()
        opener.open.side_effect = http.client.IncompleteRead(b"private response")
        with mock.patch.object(gate.urllib.request, "build_opener", return_value=opener), \
                mock.patch.object(gate.shutil, "which", return_value=None), \
                mock.patch.dict(os.environ, {"GITHUB_TOKEN": "test-token"}, clear=True), \
                redirect_stderr(io.StringIO()) as errors:
            self.assertEqual(gate.main(["--repo", "example/edition"]), 2)
        self.assertNotIn("private response", errors.getvalue())
        self.assertNotIn("test-token", errors.getvalue())

    def test_rest_does_not_send_token_to_foreign_next_page(self):
        response = io.BytesIO(b"[]")
        response.headers = {"Link": '<https://elsewhere.invalid/issues>; rel="next"'}
        opener = mock.Mock()
        opener.open.return_value = response
        with mock.patch.object(gate.urllib.request, "build_opener", return_value=opener):
            with self.assertRaisesRegex(ValueError, "pagination"):
                gate.rest_issues("example/edition", "test-token")
        self.assertEqual(opener.open.call_count, 1)

    def test_skipped_release_job_neither_fails_nor_waits(self):
        checks = [{"name": name, "bucket": "pass"} for name in safe_push.REQUIRED_CHECKS]
        checks.append({"name": "release-gate", "bucket": "skipping"})
        self.assertEqual(safe_push.judge_checks(checks)[0], "success")


class MergeChecks(unittest.TestCase):
    def test_valid_and_missing_labels(self):
        self.assertEqual(safe_push.pr_labels([]), set())
        with self.assertRaisesRegex(ValueError, "labels are unreadable"):
            safe_push.pr_labels(None)
        self.assertEqual(safe_push.pr_labels([{"name": "tooling"}, {"name": "Release"}]),
                         {"tooling", "release"})

    def judge(self, label, extra, omit_labels=False, **changes):
        ctx = safe_push.Context(ROOT, "head", "", 0, "", "example/edition", {},
                                branch="test-gates")
        template = "## Unfinished work\n\n## Checklist\n- [ ] **Required:** Reviewed."
        view = {"headRefOid": "head", "headRefName": ctx.branch, "state": "OPEN",
                "headRepositoryOwner": {"login": "example"}, "title": "Check the gates",
                "body": template.replace("\n\n", "\nNone\n").replace("[ ]", "[x]"),
                "labels": [{"name": name} for name in ["tooling", *([label] if label else [])]]}
        view.update(changes)
        if omit_labels:
            del view["labels"]
        checks = [{"name": name, "bucket": "pass"} for name in safe_push.REQUIRED_CHECKS]
        report = safe_push.Report()
        # The release's suite gate (#301) stands in passed here; test_safe_push.py's
        # RiskPreflight tests its refusals. These tests judge the release-gate job alone.
        with mock.patch.object(safe_push, "gh_json", return_value=view), \
                mock.patch.object(safe_push, "protected_files", return_value=[]), \
                mock.patch.object(safe_push, "code_change", return_value=True), \
                mock.patch.object(safe_push, "show", return_value=template), \
                mock.patch.object(safe_push, "pr_checks", return_value=checks + [extra]), \
                mock.patch.object(safe_push, "read_issues", return_value=[]), \
                mock.patch.object(safe_push, "suite_gate",
                                  return_value=("ok", "stand-in")), \
                redirect_stdout(io.StringIO()):
            try:
                safe_push.gates(ctx, 1, report)
            except safe_push.Refusal:
                pass
        return report

    def test_removed_release_label_ignores_failing_and_pending_release_job(self):
        for bucket in ("fail", "pending"):
            with self.subTest(bucket=bucket):
                report = self.judge(None, {"name": "release-gate", "workflow": "Release gate",
                                          "bucket": bucket, "state": "IN_PROGRESS"})
                self.assertEqual(report.failed(), [])

    def test_release_label_keeps_failing_release_job(self):
        for label in ("release", "Release", "RELEASE"):
            with self.subTest(label=label):
                report = self.judge(label, {"name": "release-gate", "workflow": "Release gate",
                                           "bucket": "fail", "state": "FAILURE"})
                self.assertEqual([s.name for s in report.failed()], ["CI"])

    def test_every_other_check_still_counts(self):
        for name, workflow in (("release-gate", "CI"), ("other", "Release gate"),
                               ("release-gate", None)):
            with self.subTest(name=name, workflow=workflow):
                report = self.judge(None, {"name": name, "workflow": workflow, "bucket": "fail"})
                self.assertEqual([s.name for s in report.failed()], ["CI"])

    def test_malformed_labels_refuse_release_and_keep_stale_check(self):
        for labels in ([{"name": "tooling"}, {}], {}, "release", ["tooling"],
                       [{"name": ""}], [{"name": None}], [{"name": 2}], [None],
                       [{"name": "   "}], False, None):
            for bucket in ("fail", "pending"):
                with self.subTest(labels=labels, bucket=bucket):
                    report = self.judge(None, {"name": "release-gate", "workflow": "Release gate",
                                               "bucket": bucket}, labels=labels)
                    failed = {step.name: step.detail for step in report.failed()}
                    self.assertIn("the pull request's labels are unreadable", failed["release"])
                    self.assertIn("CI", failed)
        for bucket in ("fail", "pending"):
            with self.subTest(labels="missing", bucket=bucket):
                report = self.judge(None, {"name": "release-gate", "workflow": "Release gate",
                                           "bucket": bucket}, omit_labels=True)
                failed = {step.name: step.detail for step in report.failed()}
                self.assertIn("the pull request's labels are unreadable", failed["release"])
                self.assertIn("CI", failed)


class WatchChecks(unittest.TestCase):
    def test_watch_judges_as_the_merge_does(self):
        # gh's watch is run once, as before; its verdict leaves out a stale release-gate
        # run on an ordinary pull request, and keeps it on a release pull request.
        ctx = safe_push.Context(ROOT, "head", "", 0, "", "example/edition", {}, gh=("stand-in",))
        pr = safe_push.PR(1, "https://example.invalid/pull/1", False)
        passing = [{"name": name, "bucket": "pass"} for name in safe_push.REQUIRED_CHECKS]
        for bucket in ("fail", "pending"):
            stale = {"name": "release-gate", "workflow": "Release gate", "bucket": bucket}
            for labels, verdict in (({"tooling"}, "success"),
                                    ({"tooling", "release"},
                                     "failure" if bucket == "fail" else "pending")):
                with self.subTest(bucket=bucket, labels=labels), \
                        mock.patch.object(safe_push, "pr_checks",
                                          return_value=passing + [stale]), \
                        mock.patch.object(safe_push, "read_pr_labels",
                                          return_value=labels) as read_labels, \
                        mock.patch.object(safe_push.subprocess, "run") as run, \
                        redirect_stdout(io.StringIO()):
                    self.assertEqual(safe_push.watch_checks(ctx, pr, safe_push.Report()), verdict)
                    self.assertEqual(run.call_count, 1)
                    self.assertNotIn("timeout", run.call_args.kwargs)
                    read_labels.assert_called_once_with(ctx, pr.number)

    def test_unreadable_final_labels_retain_every_check_and_refuse(self):
        ctx = safe_push.Context(ROOT, "head", "", 0, "", "example/edition", {},
                                gh=("stand-in",))
        pr = safe_push.PR(1, "https://example.invalid/pull/1", False)
        passing = [{"name": name, "bucket": "pass"} for name in safe_push.REQUIRED_CHECKS]
        stale = {"name": "release-gate", "workflow": "Release gate", "bucket": "fail"}
        report = safe_push.Report()
        with mock.patch.object(safe_push, "pr_checks", return_value=passing + [stale]), \
                mock.patch.object(safe_push, "read_pr_labels",
                                  side_effect=ValueError("labels unreadable")), \
                mock.patch.object(safe_push.subprocess, "run"), \
                redirect_stdout(io.StringIO()):
            self.assertEqual(safe_push.watch_checks(ctx, pr, report), "unknown")
        self.assertIn("failing: release-gate", report.failed()[0].detail)


if __name__ == "__main__":
    unittest.main()
