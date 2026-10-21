#!/usr/bin/env python3
"""Jev question controls and file containment, with no Lean, network or credentials.

    python3 -I tests/test_jev_questions.py

File access cases use temporary directories and stubs of Git's file and directory queries.
Import cases index Lean headers written to a temporary directory. Helper cases plant modules
there that leave a marker if they ever run, and run a copy of the generator beside them.
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
BASE = 'namespace Elements\n\ntheorem base : True := trivial\n\nend Elements\n'
BODY = '\nnamespace Elements\n\nend Elements\n'
IMPORTED = ('Base.lean', 'areas-p5.lean', 'areas.p5.lean', 'a"b.lean')
# Each Lean file, with the imports read from it as (imported file, the import's words to the
# end of its line), or None where it is refused as an unsupported import. Lean 4.35 accepts
# each file read, and refuses each file refused but those with `import all`, `prelude`, two
# imports on one line, a `/` in a module name or a block comment running on from an import's
# line, which the generator does not read.
HEADERS = (
    ('import Elements.Base\n' + BODY, [('Base', 'import Elements.Base\n')]),
    ('module\n\npublic import Elements.Base\n' + BODY,
     [('Base', 'public import Elements.Base\n')]),
    ('module\n\nmeta import Elements.Base\n' + BODY, [('Base', 'meta import Elements.Base\n')]),
    ('module\n\npublic meta import Elements.Base\n' + BODY,
     [('Base', 'public meta import Elements.Base\n')]),
    ('module\n\npublic /- between words -/ meta\n  import\n    Elements.Base -- the module\n'
     + BODY,
     [('Base', 'public /- between words -/ meta\n  import\n    Elements.Base -- the module\n')]),
    ('module\n\npublic import Elements.«areas-p5»\n' + BODY,
     [('areas-p5', 'public import Elements.«areas-p5»\n')]),
    ('module\n\npublic import Elements.«areas.p5»\n' + BODY,
     [('areas.p5', 'public import Elements.«areas.p5»\n')]),
    ('module public import Elements.Base\n' + BODY, [('Base', 'public import Elements.Base\n')]),
    ('module\n\npublic import Elements.«a"b»\n' + BODY, [('a"b', 'public import Elements.«a"b»\n')]),
    ('module\n\npublic import Elements.Base', [('Base', 'public import Elements.Base')]),
    ('module\n\npublic import Elements.Base -- the end',
     [('Base', 'public import Elements.Base -- the end')]),
    ('module\n\nimport Elements.Base /- closed here -/\n/- opened on\n  a later line -/\n' + BODY,
     [('Base', 'import Elements.Base /- closed here -/\n')]),
    ('module\n\npublic import Elements.Base\n\n'
     'def named («an import here» : Nat) : Nat := «an import here»\n' + BODY,
     [('Base', 'public import Elements.Base\n')]),
    ('module\n\n/- a /- nested -/ comment -/\n  public import Elements.Base\n'
     'import Elements.«areas-p5» -- the figure\n\n/-! The file. -/\n\npublic section\n' + BODY,
     [('Base', 'public import Elements.Base\n'),
      ('areas-p5', 'import Elements.«areas-p5» -- the figure\n')]),
    *((f'module\n\n{header}\n' + BODY, None) for header in (
        'meta public import Elements.Base', 'public public import Elements.Base',
        'private import Elements.Base', '@[expose] import Elements.Base',
        '@[\nexpose\n]\nimport Elements.Base', 'partial\nimport Elements.Base',
        'nonrec\nimport Elements.Base', '/-- declaration documentation -/\nimport Elements.Base',
        'import Elements.Base Elements.Base', 'import all Elements.Base',
        'import all\n  Elements.Base', 'all\nimport Elements.Base',
        'public /-- doc -/ import Elements.Base', '/-! The file. -/\nimport Elements.Base',
        'prelude\nimport Elements.Base', 'import Elements.Base import Elements.«areas-p5»',
        'public import Elements.«a/b»', 'theorem t : True := trivial\nimport Elements.Base',
        'import Elements.Base /- opened here\n  closed on a later line -/')),
)
HELPER_NAMES = ('jev_questions_test_first', 'jev_questions_test_second')


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
            'docs/briefs/0002-decisions.md', 'docs/PROGRAM.md', 'facts.json',
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


class Files(questions.Evidence):
    """Evidence read from a temporary folder, with no Git."""

    def __init__(self, root):
        super().__init__('0' * 40)
        self.root = root

    def read(self, path):
        return (self.root / path).read_text()


class LeanFiles(unittest.TestCase):
    def index(self, files):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name).resolve()
        (root / 'Elements').mkdir()
        for name, text in files.items():
            (root / 'Elements' / name).write_text(text)
        with patch.object(questions, 'ROOT', root):
            return questions.Index(Files(root))

    def calls(self, text):
        return questions.Calls(self.index({'Proof.lean': text}), {})


class Imports(LeanFiles):
    def test_headers_are_read_with_exact_spans_or_refused(self):
        targets = {name: BASE if name == 'Base.lean' else BODY for name in IMPORTED}
        for text, expected in HEADERS:
            with self.subTest(text=text):
                if expected is None:
                    with self.assertRaisesRegex(questions.Refusal, 'unsupported import'):
                        self.index({**targets, 'Header.lean': text})
                    continue
                index = self.index({**targets, 'Header.lean': text})
                spans = index.imports['Elements/Header.lean']
                self.assertEqual([(target, text[start:end]) for target, start, end in spans],
                                 [(f'Elements/{name}.lean', words) for name, words in expected])
                source = {'excerpts': []}
                self.assertEqual(index.import_text(source, 'imports', 'Elements/Header.lean'),
                                 text[spans[0][1]:spans[-1][2]])
                self.assertEqual(source['excerpts'][0]['end'], spans[-1][2])
                for target, _, _ in spans:
                    self.assertIn(target, index.visible('Elements/Header.lean'))


class CallReconciler(LeanFiles):
    """The forms of I.4's and I.8's proofs on the superposition branch, the plain forms an
    inductive may hold, and forms that could hide a use, each in a file Lean 4.35 accepts."""

    def test_every_constructor_on_a_line_is_a_member(self):
        calls = self.calls('namespace Elements\n\ninductive Pt where\n  | a | b | c\n\n'
                           'theorem uses (p : Pt) : p = .c ∨ True := Or.inr trivial\n\n'
                           'end Elements\n')
        found = calls.direct('Elements.uses')
        self.assertEqual(calls.unresolved['Elements.uses'], set())
        self.assertIn(('c', 'Elements.Pt', 'field candidates via signature closure'),
                      [(c['token'], c['name'], c['resolution']) for c in found])

    def test_open_in_names_a_namespace_within_the_current_one(self):
        calls = self.calls('namespace Elements.BookI\n\nnamespace Prop4\n\n'
                           'theorem helper : True := trivial\n\nend Prop4\n\n'
                           'open Prop4 in\ntheorem Prop4 : True := helper\n\nend Elements.BookI\n')
        self.assertEqual([c['name'] for c in calls.direct('Elements.BookI.Prop4')],
                         ['Elements.BookI.Prop4.helper'])

    def test_lean_core_list_lemmas_are_not_missing_names(self):
        calls = self.calls('namespace Elements\n\ntheorem lists : True := by\n'
                           '  have h := @List.mem_nil_iff Nat\n'
                           '  have k := @List.forall_mem_cons Nat\n'
                           '  trivial\n\nend Elements\n')
        self.assertEqual(calls.direct('Elements.lists'), [])
        self.assertEqual(calls.unresolved['Elements.lists'], set())

    def test_an_inductive_does_not_call_its_own_constructors(self):
        # Each constructor shares its name with an abbreviation declared after it.
        calls = self.calls('namespace Elements\n\ninductive Pt where\n  | a | b\n\n'
                           'abbrev a : Pt := .a\nabbrev b : Pt := .b\n\nend Elements\n')
        self.assertEqual(calls.direct('Elements.Pt'), [])

    def test_a_bar_of_or_begins_no_constructor(self):
        # Of the bars the plain forms hold, only one beside another, as in `||`, stands within a
        # constructor, outside every bracket or within one opened on an earlier line; it
        # begins no constructor, so each Known.bar after one is a use.
        text = self.known_bool('inductive Pt where\n  | a | b | c\n'
                               '  | mk (n : Nat) (h : Nat.beq n 0 || Known.bar n)\n'
                               '  | odd (n : Nat) (h : Nat.beq n 0\n  || Known.bar n)\n'
                               '  | even : (n : Nat) → Nat.beq n 0 || Known.bar n → Pt')
        calls = self.calls(text)
        self.assertEqual({member for member, owners in calls.members.items()
                          if 'Elements.Pt' in owners}, {'a', 'b', 'c', 'mk', 'odd', 'even'})
        uses = [i for i in range(text.index('inductive'), len(text))
                if text.startswith('Known.bar', i)]
        self.assertEqual([c['start'] for c in calls.direct('Elements.Pt')
                          if c['name'] == 'Elements.Known.bar'], uses)
        self.assertEqual(len(uses), 3)

    def known(self, inductive):
        return ('namespace Elements\n\n@[match_pattern] def Known.bar (n : Nat) : Nat := n + 1\n\n'
                f'{inductive}\n\nend Elements\n')

    def known_bool(self, inductive):
        return ('namespace Elements\n\ndef Known.bar (n : Nat) : Bool := n == 1\n\n'
                f'{inductive}\n\nend Elements\n')

    def assert_uses(self, text, name, members):
        calls = self.calls(text)
        self.assertEqual({member for member, owners in calls.members.items()
                          if name in owners}, members)
        uses = [i for i in range(text.index('inductive'), len(text))
                if text.startswith('Known.bar', i)]
        self.assertEqual([c['start'] for c in calls.direct(name)
                          if c['name'] == 'Elements.Known.bar'], uses)

    def test_every_form_outside_the_plain_forms_is_refused(self):
        # The first reviews' probes, which this branch once read and kept the use of: `||`
        # beside `==` or `=`; a bar within a bracket opened on an earlier line, or within ⦃ ⦄,
        # after `fun` or `match`; and, in a family, a pipe, `<|` or `|>`, outside every
        # bracket. Main's inductives use none of these forms, and each is refused, naming the
        # first character or keyword outside the plain forms; so are a modifier before a
        # `def` at four spaces, which Lean reads as a command, and a dot before a brace.
        for text, name, refused in (
                (self.known_bool('inductive Pt where\n'
                                 '  | mk (n : Nat) (h : (n == 0 || Known.bar n) = true)'),
                 'Pt', "the character '='"),
                (self.known_bool('inductive Pt where\n  | odd (n : Nat) '
                                 '(h : match n with | 0 => True | k => Known.bar k = true)'),
                 'Pt', "the keyword 'match'"),
                (self.known_bool('inductive Pt where\n'
                                 '  | even : (n : Nat) → n == 0 || Known.bar n → Pt'),
                 'Pt', "the character '='"),
                (self.known('inductive Pt where\n'
                            '  | mk (f : Nat → Nat := fun\n  | Known.bar n => n\n  | _ => 0)'),
                 'Pt', "the character '='"),
                (self.known('inductive Pt where\n  | mk (n : Nat) (h : (match n with\n'
                            '  | Known.bar k => k\n  | _ => 0) = 0)'), 'Pt', "the keyword 'match'"),
                (self.known('inductive Pt where\n'
                            '  | mk ⦃h : id = fun | Known.bar n => n | _ => 0⦄ : Pt'),
                 'Pt', "the character '='"),
                (self.known('inductive Pt where\n'
                            '  | mk (f : Nat → Nat := fun\n  | k => id <| Known.bar k)'),
                 'Pt', "the character '='"),
                (self.known('inductive Q : Nat → Type where\n  | mk : Q <| Known.bar 0'),
                 'Q', "the character '<'"),
                (self.known('inductive Q : Nat → Type where\n'
                            '  | a : Q 0 | b : Known.bar 1 |> Q'), 'Q', "the character '>'"),
                (self.known('inductive Pt where\n  | mk\n    partial def f : Nat → Nat'
                            + self.EQUATIONS), 'Pt', "the keyword 'partial'"),
                (self.known('inductive Pt where\n  | mk (n : Nat) (h : n ∈ List.cons.{0} n [])'),
                 'Pt', "a dot before '{'")):
            with self.subTest(text=text):
                self.assert_refused(text, f'Elements/Proof.lean: Elements.{name} holds {refused}, '
                                    'outside the plain forms an inductive may hold')

    def test_a_bar_outside_every_bracket_begins_a_constructor_only_where_one_can(self):
        # A command the index reads with the inductive, such as `partial def`, ends its
        # constructors. After each word ALTERNATIVES names, one row each, a bar outside every
        # bracket may begin an alternative or a pattern, and is refused with that reason.
        self.assert_uses(self.known('inductive Pt where\n  | mk\n\npartial def f : Nat → Nat\n'
                                    '  | Known.bar n => f n\n  | _ => 0'), 'Elements.Pt', {'mk'})
        family = 'inductive Q : Nat → Type where\n  | mk : Q <| '
        for inductive, word in (
                (family + 'match 0 with | Known.bar n => n | _ => 0', 'match'),
                ('inductive Q : (Nat → Nat) → Type where\n  | mk : Q fun\n'
                 '  | Known.bar n => n\n  | _ => 0', 'fun'),
                ('inductive Q : Bool → Type where\n'
                 '  | mk : Q <| 5 matches 0 | Known.bar 0', 'matches'),
                ('inductive Q : (Nat → Nat) → Type where\n  | mk : Q λ\n'
                 '  | Known.bar n => n\n  | _ => 0', 'λ'),
                (family + 'match_expr Lean.mkNatLit 0 with | Known.bar _ => 0 | _ => 1',
                 'match_expr'),
                (family + 'let_expr Nat.succ _ := Lean.mkNatLit 0 | Known.bar 0; 1', 'let_expr'),
                (family + 'by match 0 with | Known.bar n => exact n | _ => exact 0', 'by'),
                (family + 'Id.run do match 0 with | Known.bar n => pure n | _ => pure 0', 'do'),
                ('inductive Q where\n'
                 '  | a | mk with @[computed_field] f : Q → Nat | _ => Known.bar 0', 'with'),
                *((family + word + ' f : Nat → Nat | Known.bar n => n | _ => 0; f 0', word)
                  for word in ('let', 'have', 'haveI', 'letI', 'let_fun', 'let_delayed', 'let_tmp'))):
            with self.subTest(word=word):
                # match_expr and let_expr read a Lean.Expr, so their files import Lean.
                header = 'import Lean\n\n' if word in ('match_expr', 'let_expr') else ''
                with self.assertRaisesRegex(questions.Refusal,
                                            f"unsupported bar after '{word}' in Elements.Q"):
                    self.calls(header + self.known(inductive))

    def test_a_declaration_keyword_ends_the_constructors_wherever_it_stands(self):
        # Lean reads `def` as a command on a constructor's own line, and at three spaces, and
        # so `example`, `instance` and `theorem`: each equation after one is the command's, so
        # its Known.bar is a use.
        for inductive in ('  | mk def f : Nat → Nat\n  | Known.bar n => n\n  | _ => 0',
                          '  | mk\n   def f : Nat → Nat\n  | Known.bar n => n\n  | _ => 0',
                          '  | mk example : Nat → Nat\n  | Known.bar n => n\n  | _ => 0',
                          '  | mk instance : Inhabited (Nat → Nat) where default\n'
                          '  | Known.bar n => n\n  | _ => 0',
                          '  | mk theorem t : ∀ n : Nat, n = n\n  | Known.bar n => rfl\n'
                          '  | _ => rfl'):
            with self.subTest(inductive=inductive):
                self.assert_uses(self.known('inductive Pt where\n' + inductive), 'Elements.Pt',
                                 {'mk'})

    def test_an_inductive_holding_a_literal_or_quoted_name_is_refused(self):
        # A char literal, a «...» name, a raw string, a '"' or an interpolated string, each
        # holding one of a balanced pair of brackets, which would leave the second bar outside
        # every bracket.
        for g, zero, other in (("def g (_ : Char) (n : Nat) : Nat := n", "g ')' 0", "g '(' n"),
                               ('def g (_ : Nat → Nat) (n : Nat) : Nat := n',
                                'g (fun «a)» => 0) 0', 'g (fun «(b» => 0) n'),
                               ('def g (_ : String) (n : Nat) : Nat := n',
                                'g r#"")""# 0', 'g r#""(""# n'),
                               ('def g (_ : Char) (_ : String) (_ : Char) (n : Nat) : Nat := n',
                                'g \'"\' ")" \'"\' 0', 'g \'"\' "(" \'"\' n'),
                               ('def g (_ : String) (n : Nat) : Nat := n',
                                'g s!"{")"}" 0', 'g s!"{"("}" n')):
            inductive = (f'{g}\n\ninductive Pt where\n  | mk (f : Nat → Nat := '
                         f'fun | 0 => {zero} | Known.bar n => {other}) : Pt')
            with self.subTest(inductive=inductive):
                with self.assertRaisesRegex(questions.Refusal, 'unsupported string, char literal '
                                            'or quoted name in Elements.Pt'):
                    self.calls(self.known(inductive))

    def test_a_notation_with_a_bar_and_any_macro_or_elaborator_are_refused(self):
        # A notation, local or not, can make a bar an operator, and a macro or an elaborator
        # can give any syntax a meaning, as the macro here gives alternatives with no bar
        # before them. Each file imports Lean, as the macros and elaborators need.
        bar = '\n\ninductive Q : Nat → Type where\n  | mk : Q <| 0 | Known.bar 0'
        pick = '\n\ninductive Q : Nat → Type where\n  | mk : Q pick'
        for text, refused in (
                ('infixl:65 " | " => Nat.add' + bar, 'infixl with a bar'),
                ('local notation:65 a " | " b => Nat.add a b' + bar, 'notation with a bar'),
                ('open Lean in\n'
                 'macro "pick " alts:Lean.Parser.Term.matchAltsWhereDecls : term => do\n'
                 '  let a : TSyntax ``Lean.Parser.Term.matchAlts := ⟨alts.raw[0]⟩\n'
                 '  `(fun $a:matchAlts)\n\ninductive Q : (Nat → Nat) → Type where\n'
                 '  | mk : Q <| pick\n  | Known.bar n => n\n  | _ => 0', 'command macro'),
                ('syntax "pick" : term\n\nmacro_rules | `(pick) => `(0)' + pick,
                 'command macro_rules'),
                ('elab "pick" : term => return Lean.mkNatLit 0' + pick, 'command elab'),
                ('syntax "pick" : term\n\nelab_rules : term | `(pick) => return Lean.mkNatLit 0'
                 + pick, 'command elab_rules')):
            with self.subTest(refused=refused):
                with self.assertRaisesRegex(questions.Refusal, 'unsupported ' + refused):
                    self.calls('import Lean\n\n' + self.known(text))

    def test_any_other_bar_and_an_unbalanced_bracket_are_refused(self):
        # Lean accepts constructors at four spaces, and on the inductive's own line, which the
        # reconciler does not read. A command opening a line within an open bracket, here
        # `open ... in`, ends the inductive for the index, so its bracket stays open.
        for inductive, refused in (('\n    | a\n    | b', 'unsupported bar in an inductive, '),
                                   (' | a | b', 'unsupported bar in an inductive, '),
                                   ('\n  | mk ⦃h :\nopen Nat in succ 0 = 1⦄ : Pt',
                                    'unbalanced brackets in ')):
            with self.subTest(inductive=inductive):
                with self.assertRaisesRegex(questions.Refusal, refused + 'Elements.Pt'):
                    self.calls(self.known('inductive Pt where' + inductive))

    def assert_refused(self, text, message):
        with self.assertRaises(questions.Refusal) as caught:
            self.calls(text)
        self.assertIn(message, str(caught.exception))

    CHARS = ("@[match_pattern] def Known.c : Char := 'x'\n\n"
             "@[match_pattern] def Known.d : Char := 'y'\n\n")
    BOOL = 'inductive Q : Bool → Type where\n  | mk : Q <| '
    EQUATIONS = '\n  | Known.bar n => n\n  | _ => 0'

    def test_a_number_or_a_bare_bang_glued_to_a_word_or_quote_is_refused(self):
        # Lean ends a number before a letter, so `5matches` is `5` and then `matches`, and
        # `5def` is `5` and then a command; `!'a'matches` is `!`, a char literal and then
        # `matches`. Each Known after a bar here is a use the patterns would drop.
        nat, pair = 'inductive Q : Nat → Type where\n  | mk : Q ', 'def p : Nat × Nat := (5, 6)\n\n'
        for text in (self.BOOL + '5matches 0 | Known.bar 0',
                     self.BOOL + '0x5matches 0 | Known.bar 0',
                     pair + self.BOOL + 'p.1matches 0 | Known.bar 0',
                     nat + '5def f : Nat → Nat' + self.EQUATIONS,
                     nat + '5def f : Nat → Nat | Known.bar n => n | _ => 0',
                     pair + nat + 'p.1def f : Nat → Nat' + self.EQUATIONS,
                     nat + '5instance : Inhabited (Nat → Nat) where default' + self.EQUATIONS,
                     self.CHARS + self.BOOL + "!'a'matches Known.c | Known.d"):
            with self.subTest(text=text):
                self.assert_refused(self.known(text), 'unsupported number or literal glued to '
                                    'a word in Elements.Q')

    def test_a_digit_quote_or_letter_within_a_name_is_read_as_the_name(self):
        self.assert_uses(self.known("def x2 : Nat := 2\n\ndef h' : Nat := 2\n\n"
                                    "def x₁ : Nat := 1\n\ndef é : Nat := 1\n\n"
                                    "inductive Q : Nat → Type where\n"
                                    "  | mk : Q x2\n  | a : Q h'\n  | s : Q x₁\n  | e : Q é\n"
                                    "  | b : Q (Known.bar 0)"),
                         'Elements.Q', {'mk', 'a', 's', 'e', 'b'})

    def test_a_character_lean_reads_in_no_name_and_a_hash_are_refused(self):
        # Lean's own postfix `⁻¹` ends before `matches`, though `¹` is a word character to the
        # patterns; Lean's commands `#where` and `#version` are read whole, so each is followed
        # by a `def` whose equations hold a use; and a subscript cannot begin a name, so after
        # `∧ₑ`, a token of Std.Do, it begins a word Lean does not read.
        pt = 'inductive Pt where\n  | mk '
        for text, character, name in (
                ('instance : Inv Nat := ⟨Nat.succ⟩\n\ndef x : Nat := 3\n\n' + self.BOOL
                 + 'x⁻¹matches 0 | Known.bar 0', '¹', 'Q'),
                (pt + '#wheredef f : Nat → Nat' + self.EQUATIONS, '#', 'Pt'),
                (pt + '#versiondef f : Nat → Nat' + self.EQUATIONS, '#', 'Pt'),
                ('inductive Q : Std.Do.ExceptConds .pure → Type where\n'
                 '  | mk : Q <| Std.Do.ExceptConds.true ∧ₑ Std.Do.ExceptConds.true', 'ₑ', 'Q')):
            with self.subTest(text=text):
                header = 'import Std.Do\n\n' if 'Std.Do' in text else ''
                self.assert_refused(header + self.known(text),
                                    f'unsupported character {character!r} in Elements.{name}')

    def test_a_token_joining_a_name_character_to_another_and_a_binder_predicate_are_refused(self):
        # Each token ends a word where the patterns see none, so the Known after a bar is a use
        # they would drop; a binder predicate declares its token as a macro does. A token that
        # is a name, such as `nine`, is read as a name.
        for text, refused in (
                ('postfix:max "²" => fun n : Nat => n * n\n\ndef x : Nat := 3\n\n' + self.BOOL
                 + 'x²matches 0 | Known.bar 0', "postfix token '²'"),
                ('postfix:max "ж" => Nat.succ\n\ndef y : Nat := 3\n\n' + self.BOOL
                 + 'yжmatches 0 | Known.bar 0', "postfix token 'ж'"),
                ('notation "-x" => (5 : Nat)\n\n' + self.BOOL + '-xmatches 0 | Known.bar 0',
                 "notation token '-x'"),
                (self.CHARS + 'prefix:max "-x" => Char.toNat\n\n' + self.BOOL
                 + "-x'a'matches 0 | Known.bar 96", "prefix token '-x'"),
                ('infixl:65 "+x" => Nat.add\n\n' + self.BOOL + '1 +x0matches 0 | Known.bar 0',
                 "infixl token '+x'"),
                ('notation "→ₑ" => (5 : Nat)\n\n' + self.BOOL + '→ₑmatches 0 | Known.bar 0',
                 "notation token '→ₑ'"),
                (self.CHARS + 'binder_predicate x " -x " y:term => `($x = $y)\n\n'
                 "inductive Q where\n  | mk : ∀ x -x'a'matches Known.c | Known.d, Q",
                 'command binder_predicate')):
            with self.subTest(refused=refused):
                self.assert_refused(self.known(text), 'Elements/Proof.lean: unsupported ' + refused)
        self.assert_uses(self.known('notation "nine" => (9 : Nat)\n\n'
                                    'inductive Q : Nat → Type where\n  | mk : Q nine\n'
                                    '  | b : Q (Known.bar 0)'), 'Elements.Q', {'mk', 'b'})

    def test_a_recall_ends_the_constructors(self):
        # Lean reads `recall` as a command wherever it stands, as it does `def`: the equations
        # after it are the recall's, so each Known.bar in them is a use.
        f = 'def f : Nat → Nat' + self.EQUATIONS + '\n\n'
        s = ('structure S where\n  g : Nat → Nat\n\n'
             'def s : S where\n  g | Known.bar n => n | _ => 0\n\n')
        for inductive in (f + 'inductive Pt where\n  | mk recall f : Nat → Nat' + self.EQUATIONS,
                          f + 'inductive Pt where\n  | mk\n   recall f : Nat → Nat'
                          + self.EQUATIONS,
                          f + 'inductive Pt where\n'
                          '  | mk recall f : Nat → Nat | Known.bar n => n | _ => 0',
                          s + 'inductive Pt where\n'
                          '  | mk recall s : S where\n  g | Known.bar n => n | _ => 0'):
            with self.subTest(inductive=inductive):
                self.assert_uses(self.known(inductive), 'Elements.Pt', {'mk'})

    def test_a_comment_opener_or_dot_glued_to_a_symbol_is_refused(self):
        # Lean reads `\/`, `//`, `..` and a notation's `+-`, `⊗.` or no-break space and dash
        # whole, so the dash or the dot after each opens no comment and begins no field: the
        # masking would hide `match` or `matches`, and the patterns would take `..matches` or
        # `..def` for a field. The masked text of the row with `∀` is in the plain forms,
        # which would keep it.
        prop = 'inductive Q : Prop → Type where\n  | mk : Q <| False \\/-(1 : Int) = 0 ∨ '
        nat = 'inductive Q : Nat → Type where\n  | mk : Q <| '
        alternatives = 'match 0 with -- -/\n  | Known.bar n => True\n  | _ => True'
        for text, refused in (
                (prop + 'match 0 with /- -/ -- -/\n  | Known.bar n => True\n  | _ => True',
                 "comment glued to '\\\\'"),
                (prop + '5 matches 0 -- -/\n  | Known.bar 0', "comment glued to '\\\\'"),
                (prop + 'match 0 with | Known.bar n => True | _ => True -- -/',
                 "comment glued to '\\\\'"),
                ('inductive Q : Type → Type where\n'
                 '  | mk : Q {x : Int //-x = 0 ∨ ' + alternatives + '}', "comment glued to '/'"),
                ('infixl:65 " +- " => Int.sub\n\n' + self.BOOL
                 + '(1 : Int) +--1 == 0 && 5 matches 0\n  | Known.bar 0', "comment glued to '+'"),
                ('infixl:65 " +- " => Int.sub\n\ninductive Q : Type where\n'
                 '  | mk : ∀ _ : (1 : Int) +--1 == 0 && 5 matches 0\n  | Known.bar 0, Q',
                 "comment glued to '+'"),
                ('infixl:65 "  - " => Int.sub\n\ninductive Q : Type where\n'
                 '  | mk : ∀ _ : (1 : Int) --1 == 0 && 5 matches 0\n  | Known.bar 0, Q',
                 "comment glued to '\\xa0'"),
                (self.BOOL + 'Nat.succ ..matches 0 | Known.bar 0', 'dot glued to a symbol'),
                (nat + 'Nat.succ ..def f : Nat → Nat' + self.EQUATIONS, 'dot glued to a symbol'),
                ('notation "⊗." => (5 : Nat)\n\n' + self.BOOL + '⊗.matches 0 | Known.bar 0',
                 'dot glued to a symbol')):
            with self.subTest(text=text):
                self.assert_refused(self.known(text), f'unsupported {refused} in Elements.Q')
        # A dot after a bracket or a name, and a comment after a name or a space, keep their uses.
        self.assert_uses(self.known("def p : Nat × Nat := (5, 6)\n\ndef h' : Nat := 2\n\n"
                                    'inductive L where\n  | eq (n : Nat)\n\n'
                                    'inductive Q : L → Nat → Type where\n'
                                    "  | mk : Q (.eq p.1) (p).2 -- a comment\n"
                                    "  | a : Q (.eq h') h'-- another\n  /-- A doc. -/\n"
                                    '  | b : Q (.eq 0) (Known.bar 0) /- a block -/'),
                         'Elements.Q', {'mk', 'a', 'b'})

    def test_a_doc_comment_or_token_the_masking_reads_otherwise_is_refused(self):
        # Lean's doc comment opens with all of `/--`, so in `/--/ -- -/` it ends at the `-/`,
        # where the masking's ends at `/--/` and a line comment opens; and Lean reads a
        # notation's `/--+` whole, where the masking opens a comment. Each would hide
        # `matches`, and the masked text after it is in the plain forms.
        for text, refused in (
                ('inductive Q : Bool → Type where\n  /--/ -- -/ | mk : Q <| 5 matches 0\n'
                 '  | Known.bar 0', 'doc comment opening /--/'),
                ('/--/\ninductive P : Type where -- -/ def g : Bool := 5 matches 0\n'
                 '  | Known.bar 0', 'doc comment opening /--/'),
                ('prefix:max "/--+" => id\n\ninductive Q : Type where\n'
                 '  | mk : ∀ _ : /--+ 5 matches 0 -- -/\n  | Known.bar 0, Q',
                 "prefix token '/--+'")):
            with self.subTest(text=text):
                self.assert_refused(self.known(text), 'Elements/Proof.lean: unsupported ' + refused)


class HelperModules(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name).resolve()
        self.root = self.directory / 'repository'
        (self.root / 'scripts/audit').mkdir(parents=True)
        self.markers = self.directory / 'markers'
        self.markers.mkdir()
        for name in HELPER_NAMES:
            self.addCleanup(sys.modules.pop, name, None)

    def helper(self, path, marker):
        """Write a module that leaves a marker file if it ever runs."""
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f'from pathlib import Path\nPath({str(self.markers / marker)!r}).touch()\n')

    def ran(self):
        return sorted(path.name for path in self.markers.iterdir())

    def load(self, second):
        with patch.object(questions, 'ROOT', self.root):
            return questions.helper_modules(tuple(zip(HELPER_NAMES, ('scripts/heath.py', second))))

    def test_no_helper_runs_until_every_helper_path_passes(self):
        self.helper(self.root / 'scripts/heath.py', 'first')
        outside = self.directory / 'outside.py'
        self.helper(outside, 'outside')
        self.helper(self.directory / 'elsewhere/jev.py', 'elsewhere')
        (self.root / 'scripts/audit/link.py').symlink_to(outside)
        (self.root / 'scripts/linked').symlink_to(self.directory / 'elsewhere',
                                                  target_is_directory=True)
        refused = (('scripts/audit/link.py', 'symlink'), ('scripts/linked/jev.py', 'symlink'),
                   (str(outside), 'relative'), ('../outside.py', 'relative'),
                   ('scripts/audit/missing.py', 'not a regular file'),
                   ('scripts/audit', 'not a regular file'))
        for path, message in refused:
            with self.subTest(path=path):
                with self.assertRaisesRegex(questions.Refusal, message):
                    self.load(path)
                self.assertEqual(self.ran(), [])
                self.assertFalse(set(HELPER_NAMES) & sys.modules.keys())
        # With the second path accepted, both helpers run, each from its checked path.
        self.helper(self.root / 'scripts/audit/jev.py', 'second')
        first, second = self.load('scripts/audit/jev.py')
        self.assertEqual(self.ran(), ['first', 'second'])
        self.assertEqual(Path(first.__file__), self.root / 'scripts/heath.py')
        self.assertEqual(Path(second.__file__), self.root / 'scripts/audit/jev.py')
        self.assertIs(sys.modules[HELPER_NAMES[1]], second)

    def test_generator_runs_no_helper_when_a_helper_path_is_refused(self):
        generator = self.root / 'scripts/audit/jev_questions.py'
        shutil.copyfile(REPOSITORY / 'scripts/audit/jev_questions.py', generator)
        self.helper(self.root / 'scripts/heath.py', 'heath')
        outside = self.directory / 'outside.py'
        self.helper(outside, 'jev')
        (self.root / 'scripts/audit/jev.py').symlink_to(outside)
        result = subprocess.run([sys.executable, '-I', str(generator), '--commit', '0' * 40],
                                cwd=self.directory, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertRegex(result.stderr, r'^refused: .*scripts/audit/jev\.py: symlink component')
        self.assertEqual(self.ran(), [])


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
