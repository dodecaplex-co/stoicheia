#!/usr/bin/env python3
"""The unfinished work and release gates, without Lean, gh or a network.

Run with python3 -I tests/test_release_gate.py. The command's fixture mode is exercised
as a subprocess; GitHub's replies and HTTP pages are data supplied by the tests.
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
from contextlib import redirect_stderr
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_release_gate as gate
import safe_push


def issue(**changes):
    return dict({"number": 38, "title": "Finish the prototype", "state": "open",
                 "labels": [{"name": "blocks-release"}],
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


class UnfinishedWork(unittest.TestCase):
    def refs(self, text):
        body = "## Unfinished work\n\n" + text + "\n\n## Review records\n\n#99"
        return safe_push.unfinished_refs(safe_push.sections(body)["Unfinished work"],
                                         "example/edition")

    def test_template_and_required_box(self):
        template = (ROOT / safe_push.TEMPLATE).read_text()
        headings = list(safe_push.sections(template))
        self.assertLess(headings.index("Statements changed"), headings.index("Unfinished work"))
        self.assertLess(headings.index("Unfinished work"), headings.index("Review records"))
        self.assertTrue(any(kind == "Required" and '"Unfinished work"' in text
                            and "blocks-release" in text
                            for _, kind, text in safe_push.boxes(template)))
        self.assertIn('not written: the section "Unfinished work"',
                      safe_push.section_problems(template, template, False))

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
            "- Prototype #38\n- Page https://github.com/EXAMPLE/Edition/issues/39\n"
            "- Test example/edition#38 and #39"), ([38, 39], []))

    def test_foreign_references_refused_even_beside_local(self):
        for text in ("other/repo#38", "https://github.com/other/repo/issues/38"):
            with self.subTest(text=text):
                refs, problems = self.refs(text + " and #39")
                self.assertEqual(refs, [39])
                self.assertTrue(any("another repository" in p for p in problems))

    def test_each_list_item_needs_its_issue(self):
        refs, problems = self.refs("- Prototype #38\n- Page to come\n1. Test to come")
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
        self.assertEqual(safe_push.unfinished_issue_problems(38, issue()), [])
        for data, wanted in ((issue(labels=[]), "lacks the label"),
                             (issue(state="closed"), "is closed"),
                             (issue(pull_request={}), "is a pull request"),
                             (issue(number=39), "another number"),
                             ({}, "unreadable"), (None, "unreadable")):
            with self.subTest(data=data):
                self.assertIn(wanted, "\n".join(safe_push.unfinished_issue_problems(38, data)))

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
                    safe_push, "run", return_value=subprocess.CompletedProcess([], 0, reply, "")):
                verdict, detail = safe_push.unfinished_gate(
                    self.ctx, "## Unfinished work\n#38", "## Unfinished work")
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


if __name__ == "__main__":
    unittest.main()
