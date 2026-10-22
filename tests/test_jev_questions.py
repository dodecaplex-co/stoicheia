#!/usr/bin/env python3
"""Jev question controls and file containment, with no Lean, network or credentials.

    python3 -I tests/test_jev_questions.py

File access cases use temporary directories and stubs of Git's file and directory queries.
The control case generates all rows in memory against the real HEAD and reports its
duration. No case writes to the repository or its Git metadata.
"""

from __future__ import annotations

import builtins
import copy
import importlib.util
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
REPOSITORY = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    'jev_questions', REPOSITORY / 'scripts/audit/jev_questions.py')
questions = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = questions
SPEC.loader.exec_module(questions)

COMMENTARY_CHANGES = {
    '12-I.39-commentary': ('EBC is a part of DBC and the less',
                          'EBC is a part of DBC and the greater'),
    '12-I.40-commentary': ('our I.38 makes ABC equal to FCE',
                          'our I.38 makes ABC greater than FCE'),
}


class FileContainment(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name).resolve()
        self.root = self.directory / 'repository'
        self.root.mkdir()
        self.outside = self.directory / 'outside.txt'
        self.outside.write_bytes(b'outside evidence')
        self.output = self.root / 'questions.jsonl'
        self.manifest = self.root / 'manifest.json'
        self.git_dir = self.directory / 'git-private'
        self.git_common_dir = self.directory / 'git-common'
        self.git_dir.mkdir()
        self.git_common_dir.mkdir()
        self.tracked = [
            'facts.json', 'scripts/audit/jev_questions.py', 'scripts/heath.py',
            'scripts/audit/jev.py', 'AGENTS.md', '.github/workflows/ci.yml',
        ]
        for name in self.tracked:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'original tracked input')
        (self.root / 'scripts/safe_push.py').write_bytes(
            (REPOSITORY / 'scripts/safe_push.py').read_bytes())
        self.evidence = self.root / 'evidence.txt'
        self.evidence.write_bytes(b'committed evidence')
        self.committed = {'evidence.txt': b'committed evidence'}
        self.metadata = {
            'rows': 0, 'rows_by_item': {}, 'proof_units': 0, 'long_context_states': 0,
            'largest_state': {'characters': 0, 'id': 'fixture'},
            'unresolved_names': [], 'evidence_verification': 'fixture',
            'evidence_files': {'evidence.txt': questions.sha(b'committed evidence')},
        }
        for name, value in [('ROOT', self.root), ('OUTPUT', self.output),
                            ('MANIFEST', self.manifest),
                            ('DEFAULT_OUTPUTS', (self.output, self.manifest))]:
            self.enterContext(patch.object(questions, name, value))
        self.git = self.enterContext(patch.object(questions.subprocess, 'run',
                                                 side_effect=self.git_result))
        self.enterContext(patch.object(questions.heath, 'ROOT', self.root))
        self.enterContext(patch.object(questions.heath, 'REVIEW', self.root / 'review'))

    def git_result(self, command, **kwargs):
        self.assertEqual(kwargs['cwd'], self.root)
        if command[:2] == ['git', 'show']:
            path = command[2].split(':', 1)[1]
            return subprocess.CompletedProcess(
                command, 0, self.committed.get(path, b'committed evidence'), b'')
        if command[:2] == ['git', 'rev-parse']:
            if command[2:] == ['--absolute-git-dir']:
                path = self.git_dir
            else:
                self.assertEqual(command[2:], ['--path-format=absolute', '--git-common-dir'])
                path = self.git_common_dir
            return subprocess.CompletedProcess(command, 0, os.fsencode(path) + b'\n', b'')
        self.assertEqual(command[:2], ['git', 'ls-files'])
        self.assertIn('-z', command)
        return subprocess.CompletedProcess(
            command, 0, b''.join(os.fsencode(p) + b'\0' for p in self.tracked), b'')

    def run_main(self, out=None, *, check=False):
        result = (b'questions\n', b'manifest\n', self.metadata)
        args = ['--commit', '0' * 40]
        if out is not None:
            args.extend(['--out', str(out)])
        if check:
            args.append('--check')
        stdout, stderr = io.StringIO(), io.StringIO()
        with patch.object(questions, 'Generator') as generator:
            generator.return_value.finish.return_value = result
            with redirect_stdout(stdout), redirect_stderr(stderr):
                status = questions.main(args)
        return status, stderr.getvalue()

    def assert_unopened_refusal(self, action, message):
        with patch.object(Path, 'read_bytes', side_effect=AssertionError('read before refusal')):
            with patch.object(os, 'open', side_effect=AssertionError('opened before refusal')):
                with self.assertRaisesRegex(questions.Refusal, message):
                    action()

    def test_evidence_symlink_refused_before_read(self):
        link = self.root / 'link'
        link.symlink_to(self.outside)
        evidence = questions.Evidence('0' * 40)
        self.assert_unopened_refusal(lambda: evidence.read('link'), 'symlink')
        self.git.assert_not_called()

    def test_evidence_parent_symlink_refused_before_read(self):
        (self.root / 'link').symlink_to(self.directory, target_is_directory=True)
        evidence = questions.Evidence('0' * 40)
        self.assert_unopened_refusal(lambda: evidence.read('link/outside.txt'), 'symlink')
        self.git.assert_not_called()

    def test_evidence_absolute_and_parent_paths_refused_before_read(self):
        evidence = questions.Evidence('0' * 40)
        for name in (str(self.outside), '../outside.txt', 'scripts/../facts.json'):
            with self.subTest(name=name):
                self.assert_unopened_refusal(lambda: evidence.read(name), 'relative|\\.\\.')
        self.git.assert_not_called()

    def test_unchanged_rechecks_symlinks(self):
        evidence = questions.Evidence('0' * 40)
        evidence.read('evidence.txt')
        self.evidence.unlink()
        self.evidence.symlink_to(self.outside)
        self.assert_unopened_refusal(evidence.unchanged, 'symlink')

    def test_unchanged_rechecks_parent_symlinks(self):
        directory = self.root / 'nested'
        directory.mkdir()
        (directory / 'evidence.txt').write_bytes(b'committed evidence')
        evidence = questions.Evidence('0' * 40)
        evidence.read('nested/evidence.txt')
        directory.rename(self.directory / 'moved')
        directory.symlink_to(self.directory / 'moved', target_is_directory=True)
        self.assert_unopened_refusal(evidence.unchanged, 'symlink')

    def test_evidence_content_checks_remain_strict(self):
        evidence = questions.Evidence('0' * 40)
        self.assertEqual(evidence.read('evidence.txt'), 'committed evidence')
        self.evidence.write_bytes(b'changed evidence')
        with self.assertRaisesRegex(questions.Refusal, 'changed during generation'):
            evidence.unchanged()
        with self.assertRaisesRegex(questions.Refusal, 'differs from evidence commit'):
            questions.Evidence('0' * 40).read('evidence.txt')

    def test_tracked_inputs_cannot_be_outputs(self):
        for name in self.tracked:
            with self.subTest(name=name):
                path = self.root / name
                before = path.read_bytes()
                status, error = self.run_main(path)
                self.assertEqual(status, 1, error)
                self.assertIn('tracked', error)
                self.assertEqual(path.read_bytes(), before)
                self.assertFalse(self.manifest.exists())

    def test_manifest_cannot_replace_a_tracked_input(self):
        with patch.object(questions, 'MANIFEST', self.root / 'facts.json'):
            status, error = self.run_main()
        self.assertEqual(status, 1, error)
        self.assertIn('tracked', error)
        self.assertEqual((self.root / 'facts.json').read_bytes(), b'original tracked input')
        self.assertFalse(self.output.exists())

    def test_missing_tracked_case_aliases_cannot_be_outputs(self):
        self.tracked.append('CONTRIBUTING.md')
        alias = self.root / 'contributing.md'
        for destination in ('questions', 'manifest'):
            with self.subTest(destination=destination):
                with patch.object(questions, 'MANIFEST',
                                  alias if destination == 'manifest' else self.manifest):
                    status, error = self.run_main(
                        alias if destination == 'questions' else self.output)
                self.assertEqual(status, 1, error)
                self.assertIn('tracked', error)
                self.assertFalse(alias.exists())
                self.assertFalse(self.output.exists())
                self.assertFalse(self.manifest.exists())

    def test_git_metadata_cannot_be_outputs(self):
        pointer = self.root / '.git'
        pointer.write_bytes(b'gitdir: ../git-private\n')
        before = pointer.read_bytes()
        status, error = self.run_main(pointer)
        self.assertEqual(status, 1, error)
        self.assertIn('protected', error)
        self.assertEqual(pointer.read_bytes(), before)
        self.assertFalse(self.manifest.exists())
        pointer.unlink()
        pointer.mkdir()
        for directory in (pointer, self.git_dir, self.git_common_dir):
            member = directory / 'config'
            member.write_bytes(b'original metadata')
            for path in (directory, member, directory / 'new-file'):
                with self.subTest(path=path):
                    status, error = self.run_main(path)
                    self.assertEqual(status, 1, error)
                    self.assertIn('protected', error)
                    self.assertEqual(member.read_bytes(), b'original metadata')
                    self.assertFalse((directory / 'new-file').exists())
                    self.assertFalse(self.manifest.exists())

    def test_untracked_protected_files_cannot_be_outputs(self):
        self.tracked.clear()
        names = (
            'scripts/audit/jev_questions.py', 'scripts/heath.py', 'scripts/audit/jev.py',
            'scripts/new-script.py', '.github/workflows/ci.yml', 'Certificate/axioms.lock',
            'tests/new-test.py', 'review/SCHEMA.md', 'review/terms.toml', '.gitattributes',
            '.gitignore', 'lakefile.toml', 'lakefile.lean', 'lean-toolchain', 'lake-manifest.json',
            'Audit/New.lean', 'Audit.lean', 'model/Model/Audit.lean', 'model/Model.lean',
            'model/lakefile.toml', 'model/lakefile.lean', 'model/lean-toolchain',
            'model/lake-manifest.json', 'model/lock.sha256', 'AGENTS.md',
            'Elements/Foundations/New.lean', 'Elements/Companions.lean',
            'docs/briefs/0002-decisions.md', 'docs/decisions/README.md',
            'docs/decisions/2026-10-21-new.md', 'docs/PROGRAM.md', 'facts.json',
            'book/I/01.md', 'CERTIFICATE.md', 'GRAPH.md', 'README.md', 'heath/I/01.md',
        )
        for name in names:
            with self.subTest(name=name):
                path = self.root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b'original protected input')
                status, error = self.run_main(path)
                self.assertEqual(status, 1, error)
                self.assertIn('protected', error)
                self.assertEqual(path.read_bytes(), b'original protected input')
                self.assertFalse(self.manifest.exists())

    def test_missing_protected_paths_and_case_aliases_are_refused(self):
        for path in (self.root / 'scripts/new.py', self.root / 'SCRIPTS/new.py',
                     self.root / 'LAKEFILE.LEAN', self.git_common_dir / 'OBJECTS/new'):
            with self.subTest(path=path):
                status, error = self.run_main(path)
                self.assertEqual(status, 1, error)
                self.assertIn('protected', error)
                self.assertFalse(path.exists())
                self.assertFalse(self.manifest.exists())

    def test_external_hard_links_to_untracked_protected_files_are_refused(self):
        self.tracked.clear()
        metadata = self.git_common_dir / 'config'
        metadata.write_bytes(b'original metadata')
        for source in (self.root / 'scripts/audit/jev_questions.py', metadata):
            alias = self.directory / 'alias.jsonl'
            alias.hardlink_to(source)
            try:
                before = alias.read_bytes()
                status, error = self.run_main(alias)
                self.assertEqual(status, 1, error)
                self.assertIn('protected', error)
                self.assertEqual(alias.read_bytes(), before)
                self.assertFalse(self.manifest.exists())
            finally:
                alias.unlink()

    def test_git_pointer_aliases_are_refused(self):
        source = self.root / '.git'
        source.write_bytes(b'gitdir: ../git-private\n')
        alias = self.directory / 'pointer-alias.jsonl'
        alias.hardlink_to(source)
        for path in (alias, self.root / '.GIT'):
            with self.subTest(path=path):
                status, error = self.run_main(path)
                self.assertEqual(status, 1, error)
                self.assertIn('protected', error)
                self.assertEqual(source.read_bytes(), b'gitdir: ../git-private\n')
                self.assertFalse(self.manifest.exists())

    def test_protected_policy_is_read_without_executing_it(self):
        path = self.root / 'scripts/safe_push.py'
        path.write_text(path.read_text() + '\nraise AssertionError("policy executed")\n'
                        'PROTECTED += ("new-protection",)\n')
        # An unsupported extension must refuse output, not silently omit protection.
        status, error = self.run_main()
        self.assertEqual(status, 1, error)
        self.assertIn('protected path extension', error)
        self.assertFalse(self.output.exists())
        self.assertFalse(self.manifest.exists())

    def test_missing_protection_sources_refuse_output(self):
        policy = self.root / 'scripts/safe_push.py'
        policy.unlink()
        status, _ = self.run_main()
        self.assertEqual(status, 1)
        self.assertFalse(self.output.exists())
        self.assertFalse(self.manifest.exists())

    def test_git_directory_query_failure_refuses_output(self):
        original = self.git_result

        def fail_query(command, **kwargs):
            if command[:2] == ['git', 'rev-parse']:
                return subprocess.CompletedProcess(command, 1, b'', b'unavailable')
            return original(command, **kwargs)

        self.git.side_effect = fail_query
        status, error = self.run_main()
        self.assertEqual(status, 1, error)
        self.assertIn('cannot locate Git metadata', error)
        self.assertFalse(self.output.exists())
        self.assertFalse(self.manifest.exists())

    def test_manifest_cannot_replace_an_untracked_protected_input(self):
        self.tracked.clear()
        path = self.root / 'scripts/heath.py'
        before = path.read_bytes()
        with patch.object(questions, 'MANIFEST', path):
            status, error = self.run_main()
        self.assertEqual(status, 1, error)
        self.assertIn('protected', error)
        self.assertEqual(path.read_bytes(), before)
        self.assertFalse(self.output.exists())

    def assert_helper_refuses_without_opening_target(self, action):
        attempted = []

        def watch(function):
            def wrapped(path, *args, **kwargs):
                if not isinstance(path, int) and Path(path).resolve() == self.outside:
                    attempted.append(str(path))
                    raise AssertionError('outside target opened before refusal')
                return function(path, *args, **kwargs)
            return wrapped

        with patch.object(Path, 'read_text', watch(Path.read_text)), \
                patch.object(builtins, 'open', watch(builtins.open)), \
                patch.object(os, 'open', watch(os.open)):
            with self.assertRaisesRegex(questions.Refusal, 'symlink'):
                action()
        self.assertEqual(attempted, [])

    def test_terms_helper_refuses_symlink_before_opening_target(self):
        path = self.root / 'review/terms.toml'
        path.parent.mkdir()
        path.symlink_to(self.outside)
        self.assert_helper_refuses_without_opening_target(
            lambda: questions.terms(questions.Evidence('0' * 40), {'excerpts': []}, {}))

    def test_review_helper_refuses_symlink_before_opening_target(self):
        for name in ('review/I/05.toml', 'heath/I/05.md', 'review/terms.toml'):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            self.committed[name] = (REPOSITORY / name).read_bytes()
            path.write_bytes(self.committed[name])
        generator = questions.Generator.__new__(questions.Generator)
        generator.evidence = questions.Evidence('0' * 40)
        generator.index = None
        generator.facts = {'I.5': {}}
        for name in ('heath/I/05.md', 'review/terms.toml'):
            path = self.root / name
            path.unlink()
            path.symlink_to(self.outside)
            try:
                with self.subTest(name=name):
                    self.assert_helper_refuses_without_opening_target(
                        lambda: generator.proposition('I', 5))
            finally:
                path.unlink()
                path.write_bytes(self.committed[name])

    def test_both_destinations_refuse_evidence_even_if_untracked(self):
        for destination in ('questions', 'manifest'):
            with self.subTest(destination=destination):
                with patch.object(questions, 'MANIFEST',
                                  self.evidence if destination == 'manifest' else self.manifest):
                    status, error = self.run_main(
                        self.evidence if destination == 'questions' else self.output)
                self.assertEqual(status, 1, error)
                self.assertIn('evidence', error)
                self.assertEqual(self.evidence.read_bytes(), b'committed evidence')
                self.assertFalse(self.output.exists())
                self.assertFalse(self.manifest.exists())

    def test_destinations_cannot_coincide(self):
        status, error = self.run_main(self.root / 'scripts/../manifest.json')
        self.assertEqual(status, 1, error)
        self.assertIn('manifest', error)
        self.assertFalse(self.manifest.exists())

    def test_case_aliases_of_inputs_are_refused(self):
        for source, reason in ((self.root / 'facts.json', 'tracked'), (self.evidence, 'evidence')):
            with self.subTest(source=source.name):
                alias = source.with_name(source.name.upper())
                # Exercise the same file identity on case-sensitive volumes too.
                if not alias.exists():
                    alias.hardlink_to(source)
                before = source.read_bytes()
                status, error = self.run_main(alias)
                self.assertEqual(status, 1, error)
                self.assertIn(reason, error)
                self.assertEqual(source.read_bytes(), before)
                self.assertFalse(self.manifest.exists())

    def test_external_hard_link_to_tracked_input_is_refused(self):
        alias = self.directory / 'external.jsonl'
        source = self.root / 'facts.json'
        alias.hardlink_to(source)
        status, error = self.run_main(alias)
        self.assertEqual(status, 1, error)
        self.assertIn('tracked', error)
        self.assertEqual(source.read_bytes(), b'original tracked input')
        self.assertFalse(self.manifest.exists())

    def test_destinations_cannot_differ_only_in_case(self):
        status, error = self.run_main(self.manifest.with_name(self.manifest.name.upper()))
        self.assertEqual(status, 1, error)
        self.assertIn('manifest', error)
        self.assertFalse(self.manifest.exists())

    def test_both_destinations_refuse_symlinks_in_write_and_check(self):
        link = self.root / 'link'
        for parent in (False, True):
            target = self.directory if parent else self.outside
            link.symlink_to(target, target_is_directory=parent)
            path = link / self.outside.name if parent else link
            try:
                for destination in ('questions', 'manifest'):
                    for check in (False, True):
                        with self.subTest(parent=parent, destination=destination, check=check):
                            with patch.object(questions, 'MANIFEST',
                                              path if destination == 'manifest' else self.manifest):
                                status, error = self.run_main(
                                    path if destination == 'questions' else self.output, check=check)
                            self.assertEqual(status, 1, error)
                            self.assertIn('symlink', error)
                            self.assertEqual(self.outside.read_bytes(), b'outside evidence')
                            self.assertFalse(self.output.exists())
                            self.assertFalse(self.manifest.exists())
            finally:
                link.unlink()

    def test_external_output_and_check(self):
        path = self.directory / 'external.jsonl'
        self.assertEqual(self.run_main(path), (0, ''))
        self.assertEqual(path.read_bytes(), b'questions\n')
        self.assertEqual(self.manifest.read_bytes(), b'manifest\n')
        self.assertEqual(self.run_main(path, check=True), (0, ''))
        for changed in (path, self.manifest):
            before = changed.read_bytes()
            changed.write_bytes(b'stale')
            status, error = self.run_main(path, check=True)
            self.assertEqual(status, 1, error)
            self.assertIn('generated files differ', error)
            self.assertEqual(changed.read_bytes(), b'stale')
            changed.write_bytes(before)

    def test_dangling_output_symlink_is_refused(self):
        self.output.symlink_to(self.directory / 'missing')
        status, error = self.run_main()
        self.assertEqual(status, 1, error)
        self.assertIn('symlink', error)
        self.assertFalse((self.directory / 'missing').exists())
        self.assertFalse(self.manifest.exists())

    def test_parent_traversal_does_not_hide_an_output_symlink(self):
        (self.root / 'link').symlink_to(self.directory, target_is_directory=True)
        status, error = self.run_main(self.root / 'link/../questions.jsonl')
        self.assertEqual(status, 1, error)
        self.assertIn('symlink', error)
        self.assertFalse(self.output.exists())
        self.assertFalse(self.manifest.exists())

    def test_replacement_does_not_follow_a_late_final_symlink(self):
        replace = os.replace

        def plant_symlink(source, destination):
            destination.symlink_to(self.outside)
            replace(source, destination)

        before = set(self.root.iterdir())
        with patch.object(os, 'replace', side_effect=plant_symlink):
            questions.write_output(self.output, b'new questions')
        self.assertEqual(self.outside.read_bytes(), b'outside evidence')
        self.assertEqual(self.output.read_bytes(), b'new questions')
        self.assertFalse(self.output.is_symlink())
        self.assertEqual(set(self.root.iterdir()), before | {self.output})

    def test_read_does_not_follow_a_late_final_symlink(self):
        self.output.symlink_to(self.outside)
        with self.assertRaises(OSError):
            questions.read_no_follow(self.output)

    def test_git_failure_refuses_both_writes(self):
        self.git.side_effect = None
        self.git.return_value = subprocess.CompletedProcess(
            ['git', 'ls-files', '-z'], 1, b'', b'cannot read index')
        status, error = self.run_main()
        self.assertEqual(status, 1, error)
        self.assertIn('cannot list tracked files', error)
        self.assertFalse(self.output.exists())
        self.assertFalse(self.manifest.exists())

    def test_different_generations_still_refuse_both_writes(self):
        stderr = io.StringIO()
        with patch.object(questions, 'Generator') as generator:
            generator.return_value.finish.side_effect = [
                (b'first', b'manifest', self.metadata),
                (b'second', b'manifest', self.metadata),
            ]
            with redirect_stderr(stderr):
                status = questions.main(['--commit', '0' * 40])
        self.assertEqual(status, 1)
        self.assertIn('two generations differ', stderr.getvalue())
        self.assertFalse(self.output.exists())
        self.assertFalse(self.manifest.exists())

    def test_tracked_default_outputs_are_allowed_unless_evidence(self):
        self.tracked.extend([self.output.name, self.manifest.name])
        self.assertEqual(self.run_main(), (0, ''))
        for path in (self.output, self.manifest):
            with self.subTest(path=path.name):
                self.metadata['evidence_files'][path.name] = questions.sha(path.read_bytes())
                status, error = self.run_main()
                self.assertEqual(status, 1, error)
                self.assertIn('evidence', error)
                del self.metadata['evidence_files'][path.name]


class Controls(unittest.TestCase):
    def assert_commentary_controls(self, rows):
        originals = {row['id']: row for row in rows if not row['seeded']}
        controls = {row['mutation']['base_id']: row for row in rows
                    if row['seeded'] and row['item'] == 12}
        self.assertEqual(set(controls), set(COMMENTARY_CHANGES))
        for base_id, (old, new) in COMMENTARY_CHANGES.items():
            row = controls[base_id]
            state = copy.deepcopy(originals[base_id]['state'])
            before = state['commentary']
            self.assertEqual(before.count(old), 1)
            state['commentary'] = before.replace(old, new)
            self.assertEqual(row['state'], state)
            self.assertEqual(row['expected'], 'conflicts')
            self.assertEqual(row['mutation']['changes'], [{
                'operation': 'replace', 'field': ['state', 'commentary'],
                'old': old, 'new': new, 'before_sha256': questions.sha(before),
                'after_sha256': questions.sha(state['commentary']),
            }])

    def generated_rows_at(self, revision):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory) / 'checkout'
            subprocess.run(['git', 'clone', '--no-local', '--quiet', str(REPOSITORY), str(checkout)],
                           check=True, capture_output=True)
            subprocess.run(['git', 'checkout', '--quiet', '--detach', revision], cwd=checkout,
                           check=True, capture_output=True)
            generator_path = checkout / 'scripts/audit/jev_questions.py'
            shutil.copyfile(REPOSITORY / 'scripts/audit/jev_questions.py', generator_path)
            name = 'jev_questions_at_' + revision[:12]
            spec = importlib.util.spec_from_file_location(name, generator_path)
            self.assertIsNotNone(spec)
            self.assertIsNotNone(spec.loader)
            module = importlib.util.module_from_spec(spec)
            sys.modules[name] = module
            try:
                spec.loader.exec_module(module)
                rows_bytes, _, _ = module.Generator(revision).finish()
            finally:
                del sys.modules[name]
            return [json.loads(line) for line in rows_bytes.splitlines()]

    def test_commentary_controls_at_evidence_commit_and_head(self):
        head = subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=REPOSITORY, text=True).strip()
        for revision in ('39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3', head):
            with self.subTest(revision=revision):
                self.assert_commentary_controls(self.generated_rows_at(revision))

    def test_full_generation_has_ten_controls_and_exact_commentary_changes(self):
        commit = subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=REPOSITORY, text=True).strip()
        start = time.monotonic()
        generator = questions.Generator(commit)
        helper_reads = set()

        def verified_read(function):
            def wrapped(path, *args, **kwargs):
                name = path.relative_to(REPOSITORY).as_posix()
                self.assertIn(name, generator.evidence.data, f'helper read before verification: {name}')
                helper_reads.add(name)
                return function(path, *args, **kwargs)
            return wrapped

        with patch.object(Path, 'read_text', verified_read(Path.read_text)), \
                patch.object(Path, 'read_bytes', verified_read(Path.read_bytes)):
            rows_bytes, _, manifest = generator.finish()
        self.assertTrue({'review/terms.toml', 'review/I/01.toml', 'heath/I/01.md',
                         'Elements/BookI/Prop01.lean'} <= helper_reads)
        elapsed = time.monotonic() - start
        rows = [json.loads(line) for line in rows_bytes.splitlines()]
        seeded = [row for row in rows if row['seeded']]
        self.assertEqual(len(seeded), 10)
        self.assertEqual(manifest['rows'], len(rows))
        for item in range(9, 14):
            self.assertEqual(sum(row['item'] == item for row in seeded), 2)
        originals = {row['id']: row for row in rows if not row['seeded']}
        representations = [row for row in originals.values() if row['item'] == 11]
        expected_refs = {f'{book}.{n}' for book, count in (('I', 48), ('II', 14))
                         for n in range(1, count + 1)}
        self.assertEqual(len(representations), 62)
        self.assertEqual({row['ref'] for row in representations}, expected_refs)
        first = originals['11-I.1-representation']
        self.assertEqual(first['expected'], 'no bridge required')
        self.assertEqual(first['state']['bridges'], {})
        self.assertNotIn('representation', first['state']['record'])
        self.assertEqual(first['source']['record'], 'review/I/01.toml')
        self.assertIn('review/I/01.toml', first['source']['files'])
        self.assert_commentary_controls(rows)
        print(f'\nFull HEAD generation: {len(rows)} rows, {len(seeded)} seeded, {elapsed:.2f}s.')


if __name__ == '__main__':
    unittest.main()
