#!/usr/bin/env python3
"""Jev question controls, the calibration set, its tally and file containment, with no Lean,
network or credentials.

    python3 -I tests/test_jev_questions.py

File access cases use temporary directories and stubs of Git's file and directory queries.
Import cases index Lean headers written to a temporary directory. Helper cases plant modules
there that leave a marker if they ever run, and run a copy of the generator beside them.
One full generation against the real HEAD, the audit of Books I to III and then its
calibration set, is made in memory once and shared by the control, Book III, calibration,
figure restoring and tally cases, which report its duration; the controls are generated
again, at the evidence commit of the audit of Books I and II, in a clone. Figures are restored
from that generation's manifest into a temporary repository. The tally reads result lines built
here as `jev.py run` builds them for the generated file, with jev.py's own request builder and
answer reader, and, in one case, the output of jev.py's own run, its key and replies stood in
for; P15's images are read from a temporary tree. No case writes to the repository or its Git
metadata.
"""

from __future__ import annotations

import builtins
import copy
import hashlib
import importlib.util
import io
import json
import os
import re
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
    '12-I.39-commentary': ('equal triangles on opposite sides of BC need not make AD parallel to BC',
                          'equal triangles on opposite sides of BC must make AD parallel to BC'),
    '12-I.40-commentary': ('with BC and CE meeting at C', 'with BC and CE apart'),
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
        'public /- opened\nclosed -/ import Elements.Base',
        'prelude\nimport Elements.Base', 'import Elements.Base import Elements.«areas-p5»',
        'public import Elements.«a/b»', 'theorem t : True := trivial\nimport Elements.Base',
        'import Elements.Base /- opened here\n  closed on a later line -/')),
)
HELPER_NAMES = ('jev_questions_test_first', 'jev_questions_test_second')


class TemporaryRepository:
    """A repository in a temporary folder, with Git's file and directory queries stubbed."""

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


class FileContainment(TemporaryRepository, unittest.TestCase):
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

    def test_suffixed_declaration_names_are_visible(self):
        tools = ('namespace Elements\n\ntheorem helper? : True := trivial\n\n'
                 'def import! : Nat := 0\n\ndef macro? : Nat := 0\n\nend Elements\n')
        header = ('import Elements.Tools\n\nnamespace Elements\n\n'
                  'theorem uses : True := helper?\n\nend Elements\n')
        index = self.index({'Tools.lean': tools, 'Header.lean': header})
        self.assertIn('Elements/Tools.lean', index.visible('Elements/Header.lean'))
        self.assertEqual(index.get('Elements.import!').name, 'Elements.import!')
        self.assertEqual(index.get('Elements.macro?').name, 'Elements.macro?')
        start = header.index('helper?')
        self.assertEqual([(call['name'], call['token'], call['start'], call['end'])
                          for call in questions.Calls(index, {}).direct('Elements.uses')],
                         [('Elements.helper?', 'helper?', start, start + len('helper?'))])


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

    def test_suffixed_constructor_names_and_calls_remain_distinct(self):
        text = ('namespace Elements\n\ninductive Pt where\n  | mk | mk! | def! | match?\n\n'
                'def uses : Pt × Pt := (.mk, .mk!)\n\nend Elements\n')
        calls = self.calls(text)
        self.assertEqual({member for member, owners in calls.members.items()
                          if 'Elements.Pt' in owners}, {'mk', 'mk!', 'def!', 'match?'})
        start_mk = text.index('.mk,') + 1
        start_mk_bang = text.index('.mk!') + 1
        self.assertEqual([(call['token'], call['start'], call['end']) for call in
                          calls.direct('Elements.uses') if call['name'] == 'Elements.Pt'
                          and call['resolution'] == 'field candidates via signature closure'],
                         [('mk', start_mk, start_mk + 2),
                          ('mk!', start_mk_bang, start_mk_bang + 3)])

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
                                   ('\n| a\n| b', 'unsupported bar in an inductive, '),
                                   ('\n | a\n | b', 'unsupported bar in an inductive, '),
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
        # The shared masking now reads `/--/ -- -/` as Lean does, but the generator keeps
        # refusing `/--/`. Lean reads a notation's `/--+` whole, where the masking opens a
        # comment. Each form could hide `matches` from a reader that accepted it, and the
        # masked text after it is in the plain forms.
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

    def test_a_header_lean_reads_within_a_comment_name_or_string_is_refused(self):
        # The masking reads '"' as opening a string, so Lean may open a block comment or an
        # interpolated string within it that the masking reads as code; and a «...» name over two
        # lines is code to the masking. The inductive is then no inductive to Lean, and the
        # Known after the bar is in g's `matches`. Lean leaves each at a `-/`, `»` or `{` that a
        # masked comment hides.
        for text, refused in (
                ('def g : Bool := \'"\'.isAlpha || 5 matches 0 /- "\n'
                 'inductive P : Type where -- -/\n  | Known.bar 0', '{ or -/ in a comment'),
                ('def g : Bool := (fun «_a\ninductive P : Type where -- » => 5) 0 matches 0\n'
                 '  | Known.bar 0', 'string, char literal or quoted name'),
                ('def g : String := \'"\'.toString ++ s!"\n'
                 'inductive P : Type where -- {5 matches 0\n  | Known.bar 0\n &&\n'
                 'open Nat in true}" ++ \'"\'.toString', '{ or -/ in a comment'),
                ('def g : String := \'"\'.toString ++ s!"\n'
                 'inductive P : Type where /- {5 matches 0 -- -/\n  | Known.bar 0\n &&\n'
                 'open Nat in true}" ++ \'"\'.toString', '{ or -/ in a comment')):
            with self.subTest(text=text):
                self.assert_refused(self.known(text), f'unsupported {refused} in Elements.P')


class CoreNames(LeanFiles):
    """Lean's own names the reader exempts, each read whole (`Calls.CORE_NAMES`, and a
    structure's or a class's `mk` and `mk.injEq`), and names ending in their words that it
    reports unresolved; Lean would refuse the second kind too, as names of nothing."""

    CORE = ('namespace Elements\n\nstructure Pair where\n  a : Nat\n  b : Nat\n\n'
            'class Named (α : Type) where\n  name : α → Nat\n\ndef count : Nat := 0\n\n'
            'theorem uses : True := by\n{}  trivial\n\nend Elements\n')

    def test_lean_s_own_names_are_recognised_whole(self):
        # And.intro, Iff.rfl and List's lemmas as Book III and Book Zero write them; a
        # structure's or a class's constructor, and the equation Lean generates for it.
        calls = self.calls(self.CORE.format(
            '  have h := And.intro trivial trivial\n  have k := @Iff.rfl True\n'
            '  have m := @List.mem_map\n  have n := (@List.mem_map).1\n'
            '  have o := @List.map_congr_left\n  have p := @List.Pairwise.sublist\n'
            '  have q := Pair.mk 1 2\n  have r := @Pair.mk.injEq\n  have s := @Named.mk\n'))
        calls.direct('Elements.uses')
        self.assertEqual(calls.unresolved['Elements.uses'], set())

    def test_an_unknown_name_ending_in_a_word_of_lean_s_own_is_unresolved(self):
        # Each of the five words the core names end in, after a first word that names nothing,
        # another of Lean's types, a local, a def, or in the wrong place after a structure.
        for written in ('Missing.intro', 'Missing.rfl', 'Missing.mem_map', 'Missing.mk',
                        'Missing.injEq', 'Missing.mk.injEq', 'And.rfl', 'Iff.intro', 'Array.mem_map',
                        'h.rfl', 'count.mk', 'count.mk.injEq', 'Pair.intro', 'Pair.injEq',
                        'Pair.mk.rfl', 'Named.rfl'):
            with self.subTest(written=written):
                calls = self.calls(self.CORE.format(f'  have h := trivial\n  have x := @{written}\n'))
                calls.direct('Elements.uses')
                unresolved = calls.unresolved['Elements.uses']
                self.assertTrue(unresolved)
                self.assertTrue(all(written in found for found in unresolved), unresolved)

    def test_each_of_lean_s_four_choice_names_resolves_as_iii_26_writes_it(self):
        # III.26's helpers build a function on points from a proof that each image exists:
        # `choose` and `choose_spec` as fields of that proof, `Classical.epsilon` and
        # `True.intro` whole (#656). Each is read alone.
        exists = '  have e : ∃ n : Nat, n = 0 := ⟨0, rfl⟩\n'
        for name, body in (
                ('choose', exists + '  have c := e.choose\n'),
                ('choose_spec', exists + '  have d := e.choose_spec\n'),
                ('Classical.epsilon', '  have k := Classical.epsilon (fun n : Nat => n = 0)\n'),
                ('True.intro', '  have t := True.intro\n')):
            with self.subTest(name=name):
                calls = self.calls(self.CORE.format(body))
                calls.direct('Elements.uses')
                self.assertEqual(calls.unresolved['Elements.uses'], set())

    def test_a_choice_name_outside_the_four_is_still_unresolved(self):
        # Lean's other names for choice, and the two whole names' last words after another
        # first word, are no part of the list.
        for written in ('Classical.choice', 'Classical.indefiniteDescription', 'Missing.epsilon',
                        'True.epsilon', 'Classical.intro', 'Missing.True.intro'):
            with self.subTest(written=written):
                calls = self.calls(self.CORE.format(f'  have h := trivial\n  have x := @{written}\n'))
                calls.direct('Elements.uses')
                unresolved = calls.unresolved['Elements.uses']
                self.assertTrue(unresolved)
                self.assertTrue(all(written in found for found in unresolved), unresolved)


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


HEAD = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPOSITORY, text=True).strip()
EVIDENCE_COMMIT = '39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3'
BOOKS_I_II = (('I', 48), ('II', 14))
_SHARED = {}


def shared():
    """One full generation at HEAD, the audit and then the calibration from it, shared by every
    case below; each helper read is checked to be of evidence already verified."""
    if not _SHARED:
        start = time.monotonic()
        generator = questions.Generator(HEAD)
        helper_reads = set()

        def verified_read(function):
            def wrapped(path, *args, **kwargs):
                name = path.relative_to(REPOSITORY).as_posix()
                if name not in generator.evidence.data:
                    raise AssertionError(f'helper read before verification: {name}')
                helper_reads.add(name)
                return function(path, *args, **kwargs)
            return wrapped

        with patch.object(Path, 'read_text', verified_read(Path.read_text)), \
                patch.object(Path, 'read_bytes', verified_read(Path.read_bytes)):
            rows_bytes, _, manifest = generator.finish()
            audit_seconds = time.monotonic() - start
            files, calibration = questions.Calibration(generator).finish()
        _SHARED.update(generator=generator, rows=[json.loads(line) for line in rows_bytes.splitlines()],
                       manifest=manifest, helper_reads=helper_reads, files=files,
                       calibration=calibration, audit_seconds=audit_seconds,
                       seconds=time.monotonic() - start)
        print(f'\nShared HEAD generation: audit {audit_seconds:.2f}s; with the calibration '
              f'{_SHARED["seconds"]:.2f}s.')
    return _SHARED


def calibration_rows(question):
    data = shared()['files'][f'{questions.CALIBRATION}-{question}.jsonl']
    return [json.loads(line) for line in data.splitlines()]


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

    def generated_rows_at(self, revision, books):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory) / 'checkout'
            subprocess.run(['git', 'clone', '--no-local', '--quiet', str(REPOSITORY), str(checkout)],
                           check=True, capture_output=True)
            subprocess.run(['git', 'checkout', '--quiet', '--detach', revision], cwd=checkout,
                           check=True, capture_output=True)
            generator_path = checkout / 'scripts/audit/jev_questions.py'
            shutil.copyfile(REPOSITORY / 'scripts/audit/jev_questions.py', generator_path)
            # The generator holds its own copy of the comment reader (#349), so nothing but
            # itself is copied into the evidence commit's checkout.
            name = 'jev_questions_at_' + revision[:12]
            spec = importlib.util.spec_from_file_location(name, generator_path)
            self.assertIsNotNone(spec)
            self.assertIsNotNone(spec.loader)
            module = importlib.util.module_from_spec(spec)
            sys.modules[name] = module
            try:
                spec.loader.exec_module(module)
                rows_bytes, _, _ = module.Generator(revision, books).finish()
            finally:
                del sys.modules[name]
            return [json.loads(line) for line in rows_bytes.splitlines()]

    def test_commentary_controls_at_evidence_commit_and_head(self):
        # The evidence commit of the audit of Books I and II holds those two books' records
        # and Lean, and none of the words Book III's rows need; it is read with its books.
        with self.subTest(revision=EVIDENCE_COMMIT):
            self.assert_commentary_controls(self.generated_rows_at(EVIDENCE_COMMIT, BOOKS_I_II))
        with self.subTest(revision=HEAD):
            self.assert_commentary_controls(shared()['rows'])

    def test_i40_anchor_is_unique_and_a_missing_anchor_is_told_apart(self):
        # #350: I.40's anchor went missing when its commentary was rewritten (read-through 02,
        # #34), and the refusal called it not unique. The new anchor occurs once and plants a
        # reversed claim; a missing anchor is refused as missing.
        rows = shared()['rows']
        commentary = next(r for r in rows if r['id'] == '12-I.40-commentary')['state']['commentary']
        old, new = COMMENTARY_CHANGES['12-I.40-commentary']
        self.assertEqual(commentary.count(old), 1)
        self.assertEqual(commentary.count(new), 0)
        generator = shared()['generator']
        again = questions.Generator.__new__(questions.Generator)
        again.__dict__.update(generator.__dict__)
        again.rows = [copy.deepcopy(r) for r in generator.rows if not r['seeded']]
        again.coverage = copy.deepcopy(generator.coverage)
        stale = next(r for r in again.rows if r['id'] == '12-I.40-commentary')
        stale['state']['commentary'] = commentary.replace(old, 'with BC and CE at C')
        with self.assertRaisesRegex(questions.Refusal, 'anchor occurs 0 times, not once'):
            again.controls()
        stale['state']['commentary'] = commentary.replace(old, old + ' ' + old)
        with self.assertRaisesRegex(questions.Refusal, 'anchor occurs 2 times, not once'):
            again.controls()

    def test_full_generation_has_ten_controls_and_exact_commentary_changes(self):
        found = shared()
        self.assertTrue({'review/terms.toml', 'review/I/01.toml', 'heath/I/01.md',
                         'Elements/BookI/Prop01.lean', 'review/III/01.toml',
                         'Elements/BookIII/Prop01.lean'} <= found['helper_reads'])
        rows, manifest = found['rows'], found['manifest']
        seeded = [row for row in rows if row['seeded']]
        self.assertEqual(len(seeded), 10)
        self.assertEqual(manifest['rows'], len(rows))
        for item in range(9, 14):
            self.assertEqual(sum(row['item'] == item for row in seeded), 2)
        originals = {row['id']: row for row in rows if not row['seeded']}
        representations = [row for row in originals.values() if row['item'] == 11]
        expected_refs = {f'{book}.{n}' for book, count in (('I', 48), ('II', 14), ('III', 37))
                         for n in range(1, count + 1)}
        self.assertEqual(len(representations), 99)
        self.assertEqual({row['ref'] for row in representations}, expected_refs)
        first = originals['11-I.1-representation']
        self.assertEqual(first['expected'], 'no bridge required')
        self.assertEqual(first['state']['bridges'], {})
        self.assertNotIn('representation', first['state']['record'])
        self.assertEqual(first['source']['record'], 'review/I/01.toml')
        self.assertIn('review/I/01.toml', first['source']['files'])
        self.assert_commentary_controls(rows)
        print(f'\nFull HEAD generation: {len(rows)} rows, {len(seeded)} seeded, '
              f'{found["audit_seconds"]:.2f}s.')


class BookThree(unittest.TestCase):
    def test_every_question_is_asked_of_all_37_propositions(self):
        rows = [row for row in shared()['rows'] if not row['seeded']]
        for item, suffix in ((9, 'scope'), (10, 'citations'), (11, 'representation'),
                             (12, 'commentary'), (13, 'figure')):
            with self.subTest(item=item):
                ids = {row['id'] for row in rows if row['item'] == item}
                for n in range(1, 38):
                    self.assertIn(f'{item:02d}-III.{n}-{suffix}', ids)
        self.assertEqual(shared()['manifest']['books'], ['I', 'II', 'III'])
        self.assertEqual(shared()['manifest']['unresolved_names'], [])

    def test_every_pass_record_gets_bridges_that_exist_and_n_a_none(self):
        generator = shared()['generator']
        rows = {row['ref']: row for row in shared()['rows'] if row['item'] == 11 and not row['seeded']}
        for ref, row in rows.items():
            book = ref.split('.')[0]
            with self.subTest(ref=ref):
                verdict = generator.bundle(book, int(ref.split('.')[1]))
                bridges = row['state']['bridges']
                self.assertEqual(row['expected'] == 'bridge stated', bool(bridges))
                for name in bridges:
                    self.assertIn(name, generator.index.decls)
                    path = generator.index.get(name).path
                    # A later book's bridge never serves an earlier book.
                    later = {'I': ('/BookII/', '/BookIII/'), 'II': ('/BookIII/',), 'III': ()}[book]
                    self.assertFalse(any(part in path for part in later), (name, path))
                for name in row['state']['represented_objects']:
                    self.assertIn('Elements.' + name, generator.index.decls)
                self.assertEqual(sorted(bridges), sorted(set(verdict[1])))
        for n in (13, 14, 16, 18, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37):
            self.assertTrue(rows[f'III.{n}']['state']['bridges'], n)
        state = rows['III.35']['state']
        self.assertTrue({'sq', 'Square'} <= set(state['definitions']))
        self.assertTrue(set(questions.SQUARE_BRIDGES) <= set(state['bridges']))

    def test_iii_18_gets_the_mixed_angle_bundle_and_its_own_two_bridges(self):
        # III.18's record passes its representations on the angle of contact (#130), as III.16's
        # and III.31's on mixed angles; its row adds Prop18.branch and Prop18.contact_locallyEqual.
        generator = shared()['generator']
        rows = {row['ref']: row for row in shared()['rows'] if row['item'] == 11 and not row['seeded']}
        record = questions.tomllib.loads(generator.evidence.read('review/III/18.toml'))
        self.assertEqual(record['review']['items']['representations'], 'pass')
        self.assertEqual(questions.CONTACT_BRIDGES, ['Elements.BookIII.Prop18.branch',
                                                     'Elements.BookIII.Prop18.contact_locallyEqual'])
        for n, extra in ((16, []), (18, questions.CONTACT_BRIDGES), (31, [])):
            with self.subTest(ref=f'III.{n}'):
                state = rows[f'III.{n}']['state']
                self.assertEqual(rows[f'III.{n}']['expected'], 'bridge stated')
                self.assertEqual(sorted(state['bridges']), sorted(questions.MIXED_BRIDGES + extra))
                self.assertEqual(state['represented_objects'], questions.MIXED_DEFINITIONS)
                self.assertTrue(set(questions.MIXED_DEFINITIONS) <= set(state['definitions']))
        # No other proposition of Book III gets the mixed angles or the angle of contact.
        for n in range(1, 38):
            definitions, bridges = questions.bundle('III', n)
            with self.subTest(n=n):
                self.assertEqual(bool(set(questions.MIXED_BRIDGES) & set(bridges)), n in (16, 18, 31))
                self.assertEqual(bool(set(questions.CONTACT_BRIDGES) & set(bridges)), n == 18)

    def test_iii_13_gets_both_readings_of_touching_and_its_three_agreements(self):
        # III.13's record passes its representations on touching read of the whole circles,
        # which its companions prove the same as Definition III.3 read at the point of contact
        # (#126); its row supplies both readings and the three agreements. III.11 and III.12
        # carry the same tag and mark the item `n/a`, so they get none.
        generator = shared()['generator']
        rows = {row['ref']: row for row in shared()['rows'] if row['item'] == 11 and not row['seeded']}
        record = questions.tomllib.loads(generator.evidence.read('review/III/13.toml'))
        self.assertEqual(record['review']['items']['representations'], 'pass')
        self.assertEqual(questions.TOUCHING_BRIDGES, ['Elements.BookIII.Prop13.touchesInternally_iff',
                                                      'Elements.BookIII.Prop13.touchesExternally_iff',
                                                      'Elements.BookIII.Prop13.circlesTouch_iff'])
        words = ['TouchesInternally', 'TouchesExternally', 'CirclesTouch',
                 'TouchesInternallyAt', 'TouchesExternallyAt', 'CirclesTouchAt']
        state = rows['III.13']['state']
        self.assertEqual(rows['III.13']['expected'], 'bridge stated')
        self.assertEqual(sorted(state['bridges']), sorted(questions.TOUCHING_BRIDGES))
        self.assertEqual(state['represented_objects'], words)
        # The words at the point are said with `Touching.Near`, which the glossary supplies too.
        self.assertTrue(set(words) | {'Touching.Near'} <= set(state['definitions']))
        # Each agreement is one of the companions the record names, and is attached.
        self.assertEqual(sorted(state['attached_statements']), sorted(record['statement']['companions']))
        self.assertEqual(sorted(questions.heath.parse_ref(a).lean for a in state['attached_statements']),
                         sorted(questions.TOUCHING_BRIDGES))
        for n in (11, 12):
            with self.subTest(ref=f'III.{n}'):
                other = questions.tomllib.loads(generator.evidence.read(f'review/III/{n}.toml'))
                self.assertEqual(other['representation']['tags'], ['touching-whole-circles'])
                self.assertEqual(other['review']['items']['representations'], 'n/a')
                self.assertEqual(generator.bundle('III', n), ([], []))
                self.assertEqual(rows[f'III.{n}']['expected'], 'no bridge required')
                self.assertEqual(rows[f'III.{n}']['state']['bridges'], {})
        # No other proposition of Book III gets the agreements.
        for n in range(1, 38):
            definitions, bridges = questions.bundle('III', n)
            with self.subTest(n=n):
                self.assertEqual(bool(set(questions.TOUCHING_BRIDGES) & set(bridges)), n == 13)
                self.assertEqual('TouchesInternallyAt' in definitions, n == 13)

    def test_superposition_records_get_the_bridges_they_checked(self):
        # Records I.4 and I.8 check Atom/Lit/Metric.Holds, their holds_map bridges,
        # Derives.sound and Rule.apply, and the laws each cites, with their meaning; I.8's,
        # holds_prop7 and SameSideOf.of_line, which give I.7's law, too. The laws' proofs are
        # read from facts.json, each proof of each law of the entry's `cited_laws`; of them, the
        # core that I.4 and I.8 cite with or without Metric 9's law is named here.
        checked = {'Elements.Superposition.Atom.holds_map', 'Elements.Superposition.Lit.holds_map',
                   'Elements.Superposition.Metric.holds_map', 'Elements.Superposition.Derives.sound',
                   'Elements.Superposition.Rule.apply'}
        laws = {'Elements.Superposition.Cited.holds_' + law for law in ('lenSymm', 'neOfLen', 'rayUnique')}
        meanings = {'Superposition.Atom.Holds', 'Superposition.Lit.Holds', 'Superposition.Metric.Holds',
                    'Superposition.Cited.Holds', 'Superposition.Law.Holds', 'Superposition.Cited.law'}
        self.assertEqual(questions.CITED_EXTRAS, {'I.4': [], 'I.8': ['Elements.SameSideOf.of_line']})
        generator = shared()['generator']
        rows = {row['ref']: row for row in shared()['rows'] if row['item'] == 11 and not row['seeded']}
        for ref, core in (('I.4', {'Elements.Superposition.Cited.holds_' + law for law in
                                   ('angleSymm', 'rayOfAngle', 'rayOfAngleSide')}),
                          ('I.8', {'Elements.BookI.Prop8.holds_prop7', 'Elements.SameSideOf.of_line'})):
            with self.subTest(ref=ref):
                proofs = ['Elements.' + proof['name'] for law in generator.facts[ref]['cited_laws']
                          for proof in law['proofs']]
                cited = proofs + questions.CITED_EXTRAS[ref]
                self.assertEqual(generator.cited_laws(ref), cited)
                self.assertEqual(generator.record_checked(ref)[-len(cited):], tuple(cited))
                state = rows[ref]['state']
                self.assertEqual(set(state['bridges']), checked | set(cited))
                self.assertTrue(laws | core <= set(state['bridges']), (laws | core) - set(state['bridges']))
                self.assertTrue(meanings <= set(state['definitions']))
                self.assertTrue(meanings <= set(state['represented_objects']))
                # Each law, as data, is what the bridges' `c.Holds` speaks of.
                self.assertIn('| prop7 =>', state['definitions']['Superposition.Cited.law'])
        self.assertIn('Cited.prop7.Holds primitives',
                      rows['I.8']['state']['bridges']['Elements.BookI.Prop8.holds_prop7'])

    def test_cited_laws_are_refused_where_the_certificate_gives_no_law_or_no_proof(self):
        # An entry of facts.json with no cited law, or a law with no proof, is refused, never
        # read as a derivation that cites nothing; the extras follow the proofs read.
        generator = questions.Generator.__new__(questions.Generator)
        for fact, message in (({}, 'gives its derivation no cited_laws'),
                              ({'cited_laws': []}, 'gives its derivation no cited_laws'),
                              ({'cited_laws': [{'law': 'lenSymm', 'proofs': []}]},
                               'no proof of its law lenSymm')):
            generator.facts = {'I.4': fact}
            with self.subTest(fact=fact), self.assertRaisesRegex(questions.Refusal, message):
                generator.cited_laws('I.4')
        generator.facts = {'I.8': {'cited_laws': [{'law': 'prop7',
                                                   'proofs': [{'name': 'BookI.Prop8.holds_prop7'}]}]}}
        self.assertEqual(generator.cited_laws('I.8'),
                         ['Elements.BookI.Prop8.holds_prop7', 'Elements.SameSideOf.of_line'])

    def test_figures_taken_by_their_outline_get_book_zero_s_bridges(self):
        rows = {row['ref']: row for row in shared()['rows'] if row['item'] == 11 and not row['seeded']}
        words = {'Figures.Outline', 'Figures.Outline.Region', 'Figures.Outline.area', 'Figures.Divides',
                 'Figures.Covers', 'Apart', 'Fitted', 'Rectilineal'}
        bridges = {'Elements.Figures.division_exists', 'Elements.Figures.Apart.area_eq_of_same_region',
                   'Elements.Figures.area_eq', 'Elements.Fitted.fan'}
        for ref, extra in (('I.45', {'Elements.BookI.Prop45.fan_boundary'}), ('II.14', set())):
            with self.subTest(ref=ref):
                state = rows[ref]['state']
                self.assertTrue(words <= set(state['definitions']), words - set(state['definitions']))
                self.assertTrue(bridges | extra <= set(state['bridges']))
                self.assertIn(f'{ref} outline', state['attached_statements'])
        # II.14's square, a control of P13, is read through I.45's figures and Book Zero.
        control = next(row for row in calibration_rows('P13') if row['ref'] == 'II.14')
        self.assertEqual(control['state'], rows['II.14']['state'])

    def test_every_pass_record_s_row_supplies_what_its_record_names(self):
        generator = shared()['generator']
        rows = {row['ref']: row for row in shared()['rows'] if row['item'] == 11 and not row['seeded']}
        records = {ref: questions.tomllib.loads(generator.evidence.read(
            f'review/{ref.split(".")[0]}/{int(ref.split(".")[1]):02d}.toml')) for ref in rows}
        passed = [ref for ref, record in records.items()
                  if record['review'].get('items', {}).get('representations') == 'pass']
        self.assertEqual(len(passed), 47)
        self.assertIn('III.13', passed)
        self.assertIn('III.18', passed)
        for ref in passed:
            with self.subTest(ref=ref):
                self.assertEqual(generator.checked(ref, records[ref], rows[ref]['state']), [])
        required = {ref: tuple(dict.fromkeys((*generator.record_checked(ref),
                                             *questions.OUTLINE_CHECKED.get(ref, ()))))
                    for ref in set(questions.RECORD_CHECKED) | set(questions.OUTLINE_CHECKED)}
        for ref, names in required.items():
            for name in names:
                state = copy.deepcopy(rows[ref]['state'])
                short = name.removeprefix('Elements.')
                if name in state['bridges']:
                    del state['bridges'][name]
                elif short in state['definitions']:
                    del state['definitions'][short]
                else:
                    attachments = [attached for attached in state['attached_statements']
                                   if questions.heath.parse_ref(attached).lean == name]
                    self.assertEqual(len(attachments), 1, (ref, name))
                    del state['attached_statements'][attachments[0]]
                with self.subTest(ref=ref, missing=name):
                    self.assertIn(name, generator.checked(ref, records[ref], state))
        for ref, table, name in (('III.16', 'definitions', 'MixedAngle.WellFormed'),
                                 ('II.1', 'definitions', 'InOrder'),
                                 ('III.13', 'definitions', 'TouchesInternallyAt'),
                                 ('III.13', 'definitions', 'TouchesExternallyAt'),
                                 ('III.13', 'definitions', 'CirclesTouchAt'),
                                 ('III.18', 'definitions', 'MixedAngle'),
                                 ('III.18', 'definitions', 'MixedAngle.WellFormed'),
                                 ('III.18', 'bridges', 'Elements.BookIII.Prop18.branch')):
            with self.subTest(ref=ref, missing=name):
                state = copy.deepcopy(rows[ref]['state'])
                del state[table][name]
                full = name if name.startswith('Elements.') else 'Elements.' + name
                self.assertEqual(generator.checked(ref, records[ref], state), [full])
        # III.18's note names its companion Prop18.contact_locallyEqual, which its row supplies
        # both as a bridge and as an attached statement: it is missing only without either.
        name = 'Elements.BookIII.Prop18.contact_locallyEqual'
        state = copy.deepcopy(rows['III.18']['state'])
        self.assertIn('III.18 contact_locallyEqual', state['attached_statements'])
        del state['bridges'][name]
        self.assertEqual(generator.checked('III.18', records['III.18'], state), [])
        del state['attached_statements']['III.18 contact_locallyEqual']
        self.assertEqual(generator.checked('III.18', records['III.18'], state), [name])


def recomputed_lists(question, revision=HEAD):
    """The entry's hash rule, written again here from the records at the revision."""
    key = {'P11': ('statement', 'scope', 'full'), 'P12': ('items', 'passages', 'pass'),
           'P13': ('items', 'representations', 'pass'), 'P14': ('items', 'commentary', 'pass'),
           'P15': ('items', 'figures', 'pass')}[question]
    result = {}
    for book, count, take in (('I', 48, 4), ('II', 14, 2), ('III', 37, 4)):
        eligible = []
        for n in range(1, count + 1):
            text = subprocess.check_output(['git', 'show', f'{revision}:review/{book}/{n:02d}.toml'],
                                           cwd=REPOSITORY)
            record = questions.tomllib.loads(text.decode('utf-8'))
            value = (record['statement'][key[1]] if key[0] == 'statement'
                     else record['review'].get('items', {}).get(key[1]))
            if record['review']['stage'] == 'full' and value == key[2]:
                eligible.append(f'{book}.{n}')
        eligible.sort(key=lambda ref: hashlib.sha256(
            ('jev-calibration ' + question + ' ' + ref).encode('utf-8')).hexdigest())
        result[book] = (eligible[:take], eligible[take:2 * take])
    return result


def entry_lists(path):
    """The lists an entry's table gives, read from the entry at HEAD: for each question, the
    cells of its row that read 'controls; then plants', by the table's own book headings."""
    text = subprocess.check_output(['git', 'show', f'{HEAD}:{path}'], cwd=REPOSITORY, text=True)
    lists, books = {}, None
    for line in text.splitlines():
        cells = [cell.strip() for cell in line.strip().strip('|').split('|')]
        if cells[0] == 'Question' and all(cell.startswith('Book ') for cell in cells[1:]):
            books = [cell.removeprefix('Book ') for cell in cells[1:]]
        elif books and cells[0] in questions.QUESTIONS and all('; then ' in c for c in cells[1:]):
            lists[cells[0]] = {book: tuple(part.replace(',', '') for part in cell.split('; then '))
                               for book, cell in zip(books, cells[1:])}
    return lists


# The commit of main the rulings entry names: its records give, by the hash rule, the bar's
# lists with P13's list for Book III restated.
RULINGS_COMMIT = '110a01809ed48fc49871137d9a0fb968cad92d11'
# Each plant's kind, by the entry's rule with the rulings' three kinds of P12, and each kind
# passed over, with why it did not apply: its test's reason, or the kind ruling's.
NO_CLAUSE = 'the main conclusion has one clause'
NO_ATTACHED = 'the row has no attached statement'
NO_FORM = 'the commentary names the form of the proof only within quotation marks, or not at all'
KIND_RULING = 'docs/decisions/2026-10-26-jev-kind-not-applying.md'
NO_GENUINE_FAULT = ('no single supplied bridge carries a needed connection alone: '
                    '`Rectangle.eq_rect` and `Rectangle.contained` each give `rect`, and '
                    '`Square.eq_sq` and `Square.described` each give `sq`')
EXPECTED_KINDS = {
    'P11': [('I.8', 1, []), ('I.19', 4, [(2, NO_CLAUSE), (3, NO_ATTACHED)]), ('I.29', 4, [(3, NO_ATTACHED)]),
            ('I.9', 4, []), ('II.9', 1, []), ('II.8', 4, [(2, NO_CLAUSE), (3, NO_ATTACHED)]),
            ('III.37', 4, [(3, NO_ATTACHED)]), ('III.11', 4, []), ('III.36', 1, []), ('III.28', 2, [])],
    'P12': [('I.21', 1, []), ('I.45', 2, []), ('I.15', 3, []), ('I.40', 1, []), ('II.5', 2, []),
            ('II.7', 3, []), ('III.37', 1, []), ('III.31', 2, []), ('III.24', 3, []), ('III.36', 1, [])],
    'P13': [('I.37', 1, []), ('I.46', 2, []), ('I.43', 3, []), ('I.36', 4, []),
            ('II.8', 1, [(5, NO_GENUINE_FAULT)]), ('II.6', 1, []), ('III.37', 2, []), ('III.28', 3, []),
            ('III.27', 4, []), ('III.36', 1, [(5, NO_GENUINE_FAULT)])],
    'P14': [('I.47', 1, []), ('I.38', 2, []), ('I.13', 3, []), ('I.7', 4, []), ('II.1', 1, [(5, NO_FORM)]),
            ('II.10', 1, []), ('III.25', 2, []), ('III.20', 3, []), ('III.4', 4, []),
            ('III.14', 1, [(5, NO_FORM)])],
    'P15': [('I.22', 1, []), ('I.34', 2, []), ('I.7', 3, []), ('I.13', 4, []), ('II.5', 1, []),
            ('II.10', 2, []), ('III.1', 3, []), ('III.22', 4, []), ('III.19', 1, []), ('III.15', 2, [])],
}
# The rulings entry's three kinds of P12, and the bar's fourth, which it drops.
P12_KINDS = (('a call of an unrelated proposition whose result is not used', 'a dummy citation'),
             ('a call whose result is bound while the step it is for is done another way',
              'a dummy citation'),
             ('a hypothesis added and used only in a binding nothing uses', 'an artificial hypothesis use'))
DROPPED_KIND = 'an existing hypothesis mentioned in a step that does no work'


class Calibration(unittest.TestCase):
    def test_each_file_has_twenty_rows_ten_and_ten(self):
        manifest = shared()['calibration']
        for question in questions.QUESTIONS:
            with self.subTest(question=question):
                rows = calibration_rows(question)
                self.assertEqual(len(rows), 20)
                self.assertEqual(sum(row['seeded'] for row in rows), 10)
                self.assertEqual([row['calibration']['role'] for row in rows].count('control'), 10)
                name = f'{questions.CALIBRATION}-{question}.jsonl'
                self.assertEqual(manifest['files'][name]['rows'], 20)
                self.assertEqual(manifest['files'][name]['sha256'],
                                 questions.sha(shared()['files'][name]))

    def test_the_lists_are_the_hash_rule_and_the_entry_table(self):
        manifest = shared()['calibration']
        for question in questions.QUESTIONS:
            with self.subTest(question=question):
                lists = recomputed_lists(question)
                entry = manifest['questions'][question]
                for book in ('I', 'II', 'III'):
                    self.assertEqual([c['ref'] for c in entry['controls'] if c['book'] == book],
                                     lists[book][0])
                    self.assertEqual([p['ref'] for p in entry['plants'] if p['book'] == book],
                                     lists[book][1])
                    self.assertEqual(questions.CALIBRATION_LISTS[question][book],
                                     (' '.join(lists[book][0]), ' '.join(lists[book][1])))
                for listed in entry['controls'] + entry['plants']:
                    self.assertEqual(listed['hash'], hashlib.sha256(
                        f'jev-calibration {question} {listed["ref"]}'.encode()).hexdigest())

    def test_the_lists_are_the_bar_s_with_p13_book_iii_as_the_rulings_restate_it(self):
        bar, rulings = entry_lists(questions.ENTRY), entry_lists(questions.RULINGS)
        self.assertEqual(set(bar), set(questions.QUESTIONS))
        self.assertEqual(rulings, {'P13': {'III': ('III.18 III.33 III.24 III.26',
                                                   'III.37 III.28 III.27 III.36')}})
        expected = copy.deepcopy(bar)
        expected['P13']['III'] = rulings['P13']['III']
        self.assertEqual(questions.CALIBRATION_LISTS, expected)
        # The rulings change P13's list for Book III alone: III.18 a control, III.37 a plant,
        # and III.29 out of the set.
        self.assertEqual(bar['P13']['III'], ('III.33 III.24 III.26 III.37', 'III.28 III.27 III.36 III.29'))
        self.assertEqual({(question, book) for question, books in bar.items() for book in books
                          if books[book] != questions.CALIBRATION_LISTS[question][book]},
                         {('P13', 'III')})

    def test_the_lists_are_the_hash_rule_at_the_commit_the_rulings_name(self):
        for question in questions.QUESTIONS:
            with self.subTest(question=question):
                lists = recomputed_lists(question, RULINGS_COMMIT)
                for book in ('I', 'II', 'III'):
                    self.assertEqual(questions.CALIBRATION_LISTS[question][book],
                                     (' '.join(lists[book][0]), ' '.join(lists[book][1])))

    def test_other_lists_than_the_entry_table_are_refused(self):
        calibration = questions.Calibration.__new__(questions.Calibration)
        calibration.generator = shared()['generator']
        calibration.evidence = calibration.generator.evidence
        # Another list for Book II, and the bar's own list for Book III, which the rulings restate.
        for book, lists in (('II', ('II.1 II.14', 'II.8 II.6')),
                            ('III', ('III.33 III.24 III.26 III.37', 'III.28 III.27 III.36 III.29'))):
            changed = copy.deepcopy(questions.CALIBRATION_LISTS)
            changed['P13'][book] = lists
            with self.subTest(book=book), patch.object(questions, 'CALIBRATION_LISTS', changed):
                with self.assertRaisesRegex(questions.Refusal,
                                            f'P13 Book {book}: .*stops for a ruling') as refused:
                    calibration.lists('P13')
                self.assertIn(f'{questions.ENTRY} as {questions.RULINGS}', str(refused.exception))

    def test_p12_has_the_rulings_three_kinds_and_not_the_fourth(self):
        kinds = questions.KINDS['P12']
        self.assertEqual([(kind.name, kind.expected) for kind in kinds], list(P12_KINDS))
        self.assertNotIn(DROPPED_KIND, [kind.name for kind in kinds])
        self.assertEqual([kind.test for kind in kinds], [None, questions.body_calls_a_proposition, None])
        self.assertEqual(shared()['calibration']['questions']['P12']['kinds'],
                         [name for name, _ in P12_KINDS])
        self.assertEqual({plant.kind for (question, _), plant in questions.PLANTS.items()
                          if question == 'P12'}, {1, 2, 3})
        # Every other question keeps the bar's kinds.
        self.assertEqual({question: len(kinds) for question, kinds in questions.KINDS.items()},
                         {'P11': 4, 'P12': 3, 'P13': 5, 'P14': 5, 'P15': 4})

    def test_each_plant_takes_the_kind_the_rule_gives(self):
        manifest = shared()['calibration']
        for question, expected in EXPECTED_KINDS.items():
            with self.subTest(question=question):
                plants = manifest['questions'][question]['plants']
                self.assertEqual([(plant['ref'], plant['kind'],
                                   [(passed['kind'], passed['reason']) for passed in plant['passed_over']])
                                  for plant in plants], expected)
                for plant in plants:
                    self.assertEqual(questions.PLANTS[(question, plant['ref'])].kind, plant['kind'])
        # A change for each plant of the lists, and for no other proposition: none for III.29,
        # which the rulings take out of the set.
        listed = {(question, ref) for question, books in questions.CALIBRATION_LISTS.items()
                  for _, plants in books.values() for ref in plants.split()}
        self.assertEqual(set(questions.PLANTS), listed)
        self.assertNotIn(('P13', 'III.29'), questions.PLANTS)

    def test_the_kind_ruling_passes_over_p13_s_fifth_kind_on_ii_8_and_iii_36_alone(self):
        self.assertEqual(questions.KIND_RULING, KIND_RULING)
        self.assertTrue((REPOSITORY / KIND_RULING).is_file())
        self.assertEqual(questions.NOT_APPLYING, {('P13', 'II.8', 5): NO_GENUINE_FAULT,
                                                  ('P13', 'III.36', 5): NO_GENUINE_FAULT})
        manifest = shared()['calibration']
        fifth = questions.KINDS['P13'][4].name
        # Passed over with the table's reason, recorded as a test's reason is, and the ruling named:
        # for II.8's and III.36's P13 plants, and for no other plant of any question.
        ruled = {(question, plant['ref']): plant['passed_over']
                 for question, entry in manifest['questions'].items() for plant in entry['plants']
                 if any('ruling' in passed for passed in plant['passed_over'])}
        passed = [{'kind': 5, 'name': fifth, 'reason': NO_GENUINE_FAULT, 'ruling': KIND_RULING}]
        self.assertEqual(ruled, {('P13', 'II.8'): passed, ('P13', 'III.36'): passed})
        # The kind's test passes on each row: the table, not the test, passes the kind over.
        calibration = questions.Calibration(shared()['generator'])
        for ref, k in (('II.8', 4), ('III.36', 9)):
            with self.subTest(ref=ref):
                base = calibration.base('P13', ref)
                self.assertEqual(len(base['state']['bridges']), 5)
                self.assertIsNone(questions.KINDS['P13'][4].test(calibration, base))
                self.assertEqual(calibration.kind('P13', k, base), (1, ruled[('P13', ref)]))
                with patch.dict(questions.NOT_APPLYING, clear=True):
                    self.assertEqual(calibration.kind('P13', k, base), (5, []))
        # II.8 and III.36 take the first kind, every supplied bridge removed, as I.37 and II.6 do.
        plants = {plant['ref']: plant for plant in manifest['questions']['P13']['plants']}
        for ref in ('I.37', 'II.8', 'II.6', 'III.36'):
            with self.subTest(ref=ref):
                self.assertEqual((plants[ref]['kind'], plants[ref]['what']), (1, 'every supplied bridge removed'))
                self.assertEqual(questions.PLANTS[('P13', ref)].operations, (('remove', None),))
        for ref in ('II.8', 'III.36'):
            with self.subTest(ref=ref):
                row = next(r for r in calibration_rows('P13') if r['ref'] == ref)
                self.assertEqual(sorted(row['mutation']['base_state']['bridges']),
                                 ['Elements.Rectangle.congr', 'Elements.Rectangle.contained',
                                  'Elements.Rectangle.eq_rect', 'Elements.Square.described',
                                  'Elements.Square.eq_sq'])
                for table in ('bridges', 'bridge_context', 'bridge_placement', 'bridge_imports'):
                    self.assertEqual(row['state'][table], {})
        # No plant of P13 takes the fifth kind.
        self.assertEqual([plant['ref'] for plant in plants.values() if plant['kind'] == 5], [])

    def test_a_table_entry_for_an_unlisted_base_or_a_bad_kind_is_refused(self):
        calibration = questions.Calibration(shared()['generator'])
        questions.check_not_applying()
        # III.29 left the set; III.18 is a control; P12 has three kinds and P13 five; P99 is no
        # question; and an entry gives a reason.
        for key, reason in ((('P13', 'III.29', 1), 'a reason'), (('P13', 'III.18', 1), 'a reason'),
                            (('P12', 'III.36', 4), 'a reason'), (('P13', 'III.36', 6), 'a reason'),
                            (('P13', 'III.36', 0), 'a reason'), (('P13', 'III.36', '5'), 'a reason'),
                            (('P99', 'III.36', 1), 'a reason'), (('P13', 'III.36', 5), '')):
            with self.subTest(key=key, reason=reason), \
                    patch.dict(questions.NOT_APPLYING, {key: reason}, clear=True):
                with self.assertRaisesRegex(questions.Refusal, 'names no plant') as refused:
                    calibration.finish()
                self.assertIn(KIND_RULING, str(refused.exception))
                self.assertIn('nothing is written', str(refused.exception))
        # A listed base and a valid kind that no plant reaches: I.8's first kind, due, applies.
        with patch.dict(questions.NOT_APPLYING, {('P11', 'I.8', 3): 'a reason'}):
            with self.assertRaisesRegex(questions.Refusal,
                                        r"P11: the table of .* names \[\('P11', 'I\.8', 3\)\], which no "
                                        'plant reaches; nothing is written'):
                calibration.finish()

    def test_when_no_kind_applies_the_refusal_says_the_next_base_replaces_it(self):
        calibration = questions.Calibration(shared()['generator'])
        # A P13 row that supplies no bridge: every kind's test fails; for II.8 and III.36 the table
        # passes the fifth over first, and the refusal records it with the others.
        for ref, k, ruled in (('III.18', 0, False), ('II.8', 4, True), ('III.36', 9, True)):
            with self.subTest(ref=ref):
                with self.assertRaisesRegex(questions.Refusal, 'no kind of .* applies') as refused:
                    calibration.kind('P13', k, {'ref': ref, 'state': {'bridges': {}}})
                message = str(refused.exception)
                for words in (questions.ENTRY, questions.RULINGS,
                              f'nothing is written. By {KIND_RULING} the next base by the hash rule '
                              'replaces this one, and that replacement is recorded, in a dated entry '
                              "and the generator's lists, before anything is sent"):
                    self.assertIn(words, message)
                self.assertNotIn('stops for a ruling', message)
                self.assertEqual(NO_GENUINE_FAULT in message, ruled)

    def test_p12_plants_make_their_kind_s_fault(self):
        # Kind 1 binds a call of a proposition the row did not cite, and adds its evidence; kind 2
        # a call of one the body already calls; each binding is used nowhere else. Kind 3 adds a
        # hypothesis used only in a binding nothing uses.
        name = r"[^\W\d][\w'!?]*"

        def occurrences(word, text):
            return len(re.findall(r"(?<![\w.'])" + re.escape(word) + r"(?![\w'])", text))

        def added(pattern, change):
            return set(re.findall(pattern, change['new'])) - set(re.findall(pattern, change['old']))

        for row in calibration_rows('P12'):
            if row['calibration']['role'] != 'plant':
                continue
            with self.subTest(ref=row['ref']):
                base, kind, proof = row['mutation']['base_state'], row['calibration']['kind'], row['state']['lean_proof']
                changes = [c for c in row['mutation']['changes'] if c.get('field') == ['state', 'lean_proof']]
                bound = set().union(*(added(r'have (' + name + ')', c) for c in changes))
                hypotheses = set().union(*(added(r'\((' + name + ') :', c) for c in changes))
                cited = [c['ref'] for c in row['mutation']['changes'] if c['operation'] == 'add evidence'
                         and 'ref' in c]
                self.assertEqual(len(bound), 1)
                self.assertEqual(occurrences(next(iter(bound)), proof), 1)
                if kind == 3:
                    self.assertEqual((len(changes), len(hypotheses), cited), (2, 1, []))
                    hypothesis = next(iter(hypotheses))
                    self.assertEqual(occurrences(hypothesis, base['lean_proof']), 0)
                    # In the statement, and in the binding nothing uses.
                    self.assertEqual(occurrences(hypothesis, proof), 2)
                    binding = next(c for c in changes if bound & added(r'have (' + name + ')', c))
                    self.assertEqual(occurrences(hypothesis, binding['new']), 1)
                    continue
                self.assertEqual((len(changes), hypotheses), (1, set()))
                call = re.search(r'(?:Book([IVX]+)\.)?Prop(\d+)', changes[0]['new'].replace(changes[0]['old'], '', 1))
                ref = f'{call.group(1) or row["ref"].split(".")[0]}.{int(call.group(2))}'
                if kind == 1:
                    self.assertEqual(cited, [ref])
                    self.assertNotIn(ref, base['citation_origins']['source'])
                    self.assertIn(ref, row['state']['citation_origins']['source'])
                else:
                    self.assertEqual(cited, [])
                    self.assertIn(ref, base['citation_origins']['source'])

    def test_every_p13_control_and_plant_base_supplies_what_its_record_checked(self):
        generator = shared()['generator']
        entry = shared()['calibration']['questions']['P13']
        self.assertEqual([control['ref'] for control in entry['controls'] if control['book'] == 'III'],
                         ['III.18', 'III.33', 'III.24', 'III.26'])
        for row in calibration_rows('P13'):
            p = questions.heath.parse_ref(row['ref'])
            record = questions.tomllib.loads(generator.evidence.read(f'review/{p.book}/{p.n:02d}.toml'))
            plant = row['calibration']['role'] == 'plant'
            state = row['mutation']['base_state'] if plant else row['state']
            with self.subTest(ref=row['ref']):
                self.assertEqual(record['review']['items']['representations'], 'pass')
                self.assertTrue(state['bridges'])
                self.assertEqual(generator.checked(row['ref'], record, state), [])
                if plant and row['calibration']['kind'] == 5:
                    # The one bridge removed; the others kept.
                    removed = set(state['bridges']) - set(row['state']['bridges'])
                    self.assertEqual(len(removed), 1)
                    self.assertEqual(set(row['state']['bridges']), set(state['bridges']) - removed)
                    self.assertTrue(row['state']['bridges'])

    def test_the_manifest_the_bar_and_the_refusals_name_both_entries(self):
        manifest = shared()['calibration']
        for record in (manifest, manifest['bar'], questions.BAR):
            self.assertEqual((record['entry'], record['rulings']), (questions.ENTRY, questions.RULINGS))
        for path in (questions.ENTRY, questions.RULINGS):
            subprocess.run(['git', 'cat-file', '-e', f'{HEAD}:{path}'], cwd=REPOSITORY, check=True)
        calibration = questions.Calibration(shared()['generator'])
        # No kind applies to a P13 row that supplies no bridge.
        with self.assertRaisesRegex(questions.Refusal, 'no kind of .* applies') as unplanted:
            calibration.kind('P13', 0, {'ref': 'III.18', 'state': {'bridges': {}}})
        # A change of another kind than the rule gives.
        entry = next(p for p in manifest['questions']['P12']['plants'] if p['ref'] == 'I.40')
        with patch.dict(questions.PLANTS, {('P12', 'I.40'): questions.Plant(3, 'another kind', 'none', ())}):
            with self.assertRaisesRegex(questions.Refusal,
                                        'gives kind 1, and the generator holds a change of kind 3') as mismatched:
                calibration.plant('P12', 3, entry)
        for refused in (unplanted, mismatched):
            self.assertIn(questions.ENTRY, str(refused.exception))
            self.assertIn(questions.RULINGS, str(refused.exception))

    def test_controls_are_the_audit_rows_and_plants_keep_their_constraints(self):
        audit = {row['id']: row for row in shared()['rows'] if not row['seeded']}
        manifest = shared()['calibration']
        for question, spec in questions.QUESTIONS.items():
            entry = manifest['questions'][question]
            rows = {row['id']: row for row in calibration_rows(question)}
            controls = {c['ref'] for c in entry['controls']}
            plants = {p['ref'] for p in entry['plants']}
            with self.subTest(question=question):
                self.assertFalse(controls & plants)
                self.assertEqual([p['book'] for p in entry['plants']],
                                 ['I'] * 4 + ['II'] * 2 + ['III'] * 4)
                for row in rows.values():
                    self.assertEqual(row['id'], f'{spec.item:02d}-{row["ref"]}-{spec.suffix}')
                    base = audit[row['id']]
                    self.assertEqual(row['question'], base['question'])
                    if row['calibration']['role'] == 'control':
                        self.assertFalse(row['seeded'])
                        self.assertEqual(row['state'], base['state'])
                        self.assertEqual(row.get('assets'), base.get('assets'))
                        self.assertEqual(row['expected'], spec.clean)
                    else:
                        self.assertTrue(row['seeded'])
                        self.assertIn(row['expected'], spec.defects)
                        self.assertEqual(row['mutation']['base_state_sha256'],
                                         questions.sha(questions.dumps(base['state'])))
                        self.assertEqual(row['mutation']['state_sha256'],
                                         questions.sha(questions.dumps(row['state'])))
                        self.assertNotEqual((row['state'], row.get('assets')),
                                            (base['state'], base.get('assets')))
                for k, plant in enumerate(entry['plants']):
                    kinds = questions.KINDS[question]
                    self.assertEqual(plant['expected'], kinds[plant['kind'] - 1].expected)
                    self.assertEqual(questions.PLANTS[(question, plant['ref'])].kind, plant['kind'])
                    # Counting round from the k-th kind, each kind passed over is recorded.
                    due = k % len(kinds) + 1
                    skipped = [(due - 1 + step) % len(kinds) + 1
                               for step in range((plant['kind'] - due) % len(kinds))]
                    self.assertEqual([p['kind'] for p in plant['passed_over']], skipped)
                    self.assertTrue(plant['justification'])

    def test_plants_keep_their_state_before_whole_and_what_they_remove(self):
        # Beside the hashes, locally and in the manifest: never in what run sends.
        audit = {row['id']: row for row in shared()['rows'] if not row['seeded']}
        manifest = shared()['calibration']
        carried = json.loads(shared()['files'][f'{questions.CALIBRATION}-manifest.json'])
        removed = 0
        for question in questions.QUESTIONS:
            listed = {p['id']: p for p in manifest['questions'][question]['plants']}
            committed = {p['id']: p for p in carried['questions'][question]['plants']}
            for row in calibration_rows(question):
                if row['calibration']['role'] != 'plant':
                    continue
                with self.subTest(question=question, id=row['id']):
                    base = audit[row['id']]
                    self.assertEqual(row['mutation']['base_state'], base['state'])
                    self.assertEqual(committed[row['id']]['state_before'], base['state'])
                    self.assertEqual(committed[row['id']]['state_sha256_before'],
                                     questions.sha(questions.dumps(base['state'])))
                    self.assertEqual(committed[row['id']]['assets_before'], base.get('assets', {}))
                    self.assertEqual(committed[row['id']]['changes'], row['mutation']['changes'])
                    self.assertEqual(listed[row['id']]['state_sha256_before'],
                                     row['mutation']['base_state_sha256'])
                    for change in row['mutation']['changes']:
                        if change['operation'] == 'remove':
                            value = base
                            for part in change['field']:
                                value = value[part]
                            self.assertEqual(change['old'], value)
                            removed += 1
                    # What run sends is built from the state, the question and the images
                    # alone: the same with every local field taken away.
                    bare = {key: row[key] for key in ('id', 'state', 'question', 'assets') if key in row}
                    with patch.object(questions.jev, 'load_asset',
                                      lambda root, rel, width: ('png', rel.encode(), 300, 300)):
                        self.assertEqual(questions.jev.build(row, 'jev-1.13.0', True, REPOSITORY, 700),
                                         questions.jev.build(bare, 'jev-1.13.0', True, REPOSITORY, 700))
                        body = questions.jev.build(row, 'jev-1.13.0', True, REPOSITORY, 700)[0]
                    self.assertEqual(set(body), {'model', 'state', 'questions', *(['assets'] if 'assets' in row else [])})
        self.assertTrue(removed)

    def test_kind_four_needs_a_declaration_named_outside_quotation(self):
        calibration = questions.Calibration.__new__(questions.Calibration)
        calibration.index = shared()['generator'].index
        row = copy.deepcopy(next(r for r in shared()['rows'] if r['id'] == '12-III.4-commentary'))
        test = questions.KINDS['P14'][3].test
        self.assertIsNone(test(calibration, row))
        commentary = row['state']['commentary']
        self.assertEqual(commentary.count('(`onRay_of_angle_eq`)'), 1)
        # The same declaration, named only within a quotation, does not make kind 4 apply.
        row['state']['commentary'] = commentary.replace('(`onRay_of_angle_eq`)', '"`onRay_of_angle_eq`"')
        self.assertIn('outside quotation marks', test(calibration, row))
        # A name of no declaration of the row, outside quotation, does not either.
        row['state']['commentary'] = commentary.replace('`onRay_of_angle_eq`', '`circles_meet`')
        self.assertIn('outside quotation marks', test(calibration, row))
        # The other four kinds read the commentary outside quotation too.
        for k, words in ((0, 'less'), (1, 'I.17'), (2, 'statement'), (4, 'reductio')):
            with self.subTest(kind=k + 1):
                quoted = {**row, 'state': {**row['state'], 'commentary': f'"{words}" and nothing else.'}}
                self.assertIsNotNone(questions.KINDS['P14'][k].test(calibration, quoted))
                plain = {**row, 'state': {**row['state'], 'commentary': f'{words} and nothing else.'}}
                self.assertIsNone(questions.KINDS['P14'][k].test(calibration, plain))

    def test_every_commentary_plant_changes_text_outside_quotation(self):
        for plant in calibration_rows('P14'):
            if plant['calibration']['role'] != 'plant':
                continue
            with self.subTest(id=plant['id']):
                before = plant['mutation']['base_state']['commentary']
                for change in plant['mutation']['changes']:
                    at = before.index(change['old'])
                    self.assertEqual(questions.outside_quotes(before)[at:at + len(change['old'])],
                                     change['old'])
                    self.assertNotIn('"', change['new'])
        # A change within a quotation is refused.
        calibration = questions.Calibration(shared()['generator'])
        entry = next(p for p in shared()['calibration']['questions']['P14']['plants'] if p['ref'] == 'I.13')
        inside = questions.Plant(3, 'within a quotation', 'none', (
            ('replace', ['state', 'commentary'], 'or angles equal to two right angles',
             'or angles less than two right angles'),))
        with patch.dict(questions.PLANTS, {('P14', 'I.13'): inside}):
            with self.assertRaisesRegex(questions.Refusal, 'outside quotation marks'):
                calibration.plant('P14', 2, entry)

    def test_no_local_label_leaks_and_ids_say_nothing_of_the_role(self):
        for question in questions.QUESTIONS:
            rows = calibration_rows(question)
            with self.subTest(question=question):
                self.assertEqual(len({row['id'] for row in rows}), 20)
                for row in rows:
                    self.assertFalse(set(row['state']) & set(questions.LOCAL_LABELS))
                    sent = json.dumps([row['state'], row['question'], sorted(row.get('assets', {}))],
                                      ensure_ascii=False)
                    self.assertNotRegex(sent, questions.ROLE_WORDS)
                    self.assertNotRegex(row['id'], '(?i)seeded|control|plant')
                    self.assertEqual(jev_check(row), [])
                    # What a change brings into what is sent; an image's local path is not sent.
                    for change in row.get('mutation', {}).get('changes', []):
                        if isinstance(change.get('new'), str) and change['field'][0] == 'state':
                            self.assertNotRegex(change['new'], questions.SIGN_WORDS)
                        for _, new in change.get('edits', []):
                            self.assertNotRegex(new, questions.SIGN_WORDS)

    def test_changed_figures_are_copies_never_in_figures(self):
        manifest = shared()['calibration']
        self.assertEqual(len(manifest['figures']), 5)
        for path, figure in manifest['figures'].items():
            self.assertTrue(path.startswith(
                'docs/reports/acceptance/jev/calibration-books-I-III-figures/'))
            self.assertTrue(figure['from'].startswith('figures/'))
            data = shared()['files'][path.split('/', 4)[-1]]
            self.assertEqual(questions.sha(data), figure['sha256'])
            committed = subprocess.check_output(['git', 'show', f'{HEAD}:{figure["from"]}'],
                                                cwd=REPOSITORY)
            self.assertEqual(questions.sha(committed), figure['from_sha256'])
            self.assertNotEqual(data, committed)
        status = subprocess.check_output(['git', 'status', '--porcelain', '--', 'figures'],
                                         cwd=REPOSITORY, text=True)
        self.assertEqual(status, '')

    def test_the_manifest_carries_each_copy_exactly(self):
        files = shared()['files']
        # As committed: the manifest's own bytes, read back.
        carried = json.loads(files[f'{questions.CALIBRATION}-manifest.json'])['figures']
        self.assertEqual(len(carried), 5)
        self.assertEqual(sorted(carried), sorted(shared()['calibration']['figures']))
        for path, figure in carried.items():
            with self.subTest(path=path):
                self.assertEqual(set(figure), {'from', 'from_sha256', 'sha256', 'text'})
                data = figure['text'].encode('utf-8')
                self.assertEqual('sha256:' + hashlib.sha256(data).hexdigest(), figure['sha256'])
                self.assertEqual(data, files[path.split('/', 4)[-1]])

    def test_check_passes_and_finds_a_changed_file(self):
        files, manifest = shared()['files'], shared()['calibration']

        class Stub:
            def __init__(self, generator, directory):
                pass

            def finish(self):
                return files, manifest

        with tempfile.TemporaryDirectory(dir=REPOSITORY) as directory:
            out = Path(directory).resolve() / 'calibration'
            out.mkdir()
            args = ['--commit', HEAD, '--calibration', '--out', str(out)]
            with patch.object(questions, 'Calibration', Stub), \
                    patch.object(questions, 'Generator', lambda commit: None):
                stdout = io.StringIO()
                with redirect_stdout(stdout):
                    self.assertEqual(questions.main(args), 0)
                    self.assertEqual(questions.main(args + ['--check']), 0)
                written = sorted(p.relative_to(out).as_posix() for p in out.rglob('*') if p.is_file())
                self.assertEqual(written, sorted(files))
                carried = json.loads((out / f'{questions.CALIBRATION}-manifest.json').read_bytes())
                for path, figure in carried['figures'].items():
                    self.assertEqual(figure['text'].encode('utf-8'),
                                     (out / path.split('/', 4)[-1]).read_bytes())
                # A copy present is compared; a copy absent is not, as in a committed tree.
                figures = sorted(out.glob(questions.CALIBRATION_FIGURES + '/*.svg'))
                before = figures[0].read_bytes()
                figures[0].write_bytes(before + b'\n')
                stderr = io.StringIO()
                with redirect_stdout(io.StringIO()), redirect_stderr(stderr):
                    self.assertEqual(questions.main(args + ['--check']), 1)
                self.assertIn('generated files differ', stderr.getvalue())
                self.assertIn(figures[0].name, stderr.getvalue())
                figures[0].write_bytes(before)
                for figure in figures[1:]:
                    figure.unlink()
                stdout = io.StringIO()
                with redirect_stdout(stdout):
                    self.assertEqual(questions.main(args + ['--check']), 0)
                self.assertIn('1 present and compared', stdout.getvalue())
                figures[0].unlink()
                stdout = io.StringIO()
                with redirect_stdout(stdout):
                    self.assertEqual(questions.main(args + ['--check']), 0)
                self.assertIn('0 present and compared', stdout.getvalue())
                # The manifest, which carries the copies' text, is compared always.
                manifest_path = out / f'{questions.CALIBRATION}-manifest.json'
                manifest_path.write_bytes(manifest_path.read_bytes().replace(b'<svg', b'<svg ', 1))
                stderr = io.StringIO()
                with redirect_stdout(io.StringIO()), redirect_stderr(stderr):
                    self.assertEqual(questions.main(args + ['--check']), 1)
                self.assertIn('manifest.json', stderr.getvalue())

    def test_custom_directory_assets_load_and_restore_to_the_same_layout(self):
        if not shutil.which('rsvg-convert'):
            self.skipTest('rsvg-convert renders the figures, and is not on the PATH')
        generator = shared()['generator']
        with tempfile.TemporaryDirectory(dir=REPOSITORY) as temporary:
            out = Path(temporary).resolve() / 'custom'
            out.mkdir()
            args = ['--commit', HEAD, '--calibration', '--out', str(out)]
            with patch.object(questions, 'Generator', return_value=generator):
                self.assertEqual(questions.main(args), 0)
            p15 = out / f'{questions.CALIBRATION}-P15.jsonl'
            stdout, stderr = io.StringIO(), io.StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                status = questions.jev.main(['run', str(p15), '--dry-run',
                                             '--assets-root', str(REPOSITORY)])
            self.assertEqual(status, 0, stderr.getvalue())
            rows = [json.loads(line) for line in p15.read_text().splitlines()]
            prefix = (out.relative_to(REPOSITORY) / questions.CALIBRATION_FIGURES).as_posix() + '/'
            changed = sorted({path for row in rows for path in row.get('assets', {}).values()
                              if path.startswith(prefix)})
            self.assertEqual(len(changed), 5)
            copies = [REPOSITORY / path for path in changed]
            before = {path: path.read_bytes() for path in copies}
            for path in copies:
                path.unlink()
            manifest = out / f'{questions.CALIBRATION}-manifest.json'
            stdout, stderr = io.StringIO(), io.StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                status = questions.main(['--restore-figures', str(manifest)])
            self.assertEqual(status, 0, stderr.getvalue())
            self.assertEqual({path: path.read_bytes() for path in copies}, before)

    def test_external_calibration_directory_is_refused_before_generation(self):
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary).resolve() / 'calibration'
            stderr = io.StringIO()
            with patch.object(questions, 'Generator') as generator, \
                    redirect_stdout(io.StringIO()), redirect_stderr(stderr):
                status = questions.main(['--commit', HEAD, '--calibration', '--out', str(out)])
            self.assertEqual(status, 1, stderr.getvalue())
            generator.assert_not_called()
            self.assertIn('must be inside the repository', stderr.getvalue())
            self.assertFalse(out.exists())

    def test_figures_directory_and_descendants_are_refused_before_generation(self):
        figures = REPOSITORY / 'figures'
        before = {path.relative_to(figures): path.read_bytes()
                  for path in figures.rglob('*') if path.is_file()}
        for out in (figures, figures / 'calibration-output'):
            with self.subTest(out=out.relative_to(REPOSITORY)):
                stderr = io.StringIO()
                with patch.object(questions, 'Generator') as generator, \
                        redirect_stdout(io.StringIO()), redirect_stderr(stderr):
                    status = questions.main(['--commit', HEAD, '--calibration', '--out', str(out)])
                self.assertEqual(status, 1, stderr.getvalue())
                generator.assert_not_called()
                self.assertIn('must not be figures/', stderr.getvalue())
                after = {path.relative_to(figures): path.read_bytes()
                         for path in figures.rglob('*') if path.is_file()}
                self.assertEqual(after, before)

    def test_dry_run_loads_every_request_and_figure(self):
        if not shutil.which('rsvg-convert'):
            self.skipTest('rsvg-convert renders the figures, and is not on the PATH')
        files = shared()['files']
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            # The assets as they stand once written: the committed figures and the copies.
            shutil.copytree(REPOSITORY / 'figures', root / 'figures')
            for name, data in files.items():
                path = root / 'docs/reports/acceptance/jev' / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            for question in questions.QUESTIONS:
                with self.subTest(question=question):
                    name = f'{questions.CALIBRATION}-{question}.jsonl'
                    path = root / 'docs/reports/acceptance/jev' / name
                    stdout, stderr = io.StringIO(), io.StringIO()
                    with redirect_stdout(stdout), redirect_stderr(stderr):
                        status = questions.jev.main(['run', str(path), '--dry-run',
                                                     '--assets-root', str(root)])
                    self.assertEqual(status, 0, stderr.getvalue())


class RestoreFigures(TemporaryRepository, unittest.TestCase):
    """--restore-figures, from the shared generation's manifest, into a temporary repository."""

    def setUp(self):
        # The shared generation reads the real repository, so it comes before the stubs.
        files = shared()['files']
        self.carried = files[f'{questions.CALIBRATION}-manifest.json']
        self.copies = {name: data for name, data in files.items()
                       if name.startswith(questions.CALIBRATION_FIGURES + '/')}
        super().setUp()
        self.jev = self.root / 'docs/reports/acceptance/jev'
        self.figures = self.jev / questions.CALIBRATION_FIGURES

    def restore(self, manifest: bytes):
        path = self.directory / 'calibration-manifest.json'
        path.write_bytes(manifest)
        stdout, stderr = io.StringIO(), io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            status = questions.main(['--restore-figures', str(path)])
        self.assertFalse([call for call in self.git.call_args_list if call.args[0][:2] == ['git', 'show']])
        return status, stdout.getvalue() + stderr.getvalue()

    def changed(self, change) -> bytes:
        manifest = json.loads(self.carried)
        change(manifest['figures'])
        return json.dumps(manifest).encode('utf-8')

    def written(self):
        return sorted(p.relative_to(self.root).as_posix() for p in self.root.rglob('*.svg'))

    def test_writes_identical_bytes_into_an_empty_tree(self):
        self.assertFalse(self.jev.exists())
        self.assertEqual(self.restore(self.carried)[0], 0)
        for name, data in self.copies.items():
            self.assertEqual((self.jev / name).read_bytes(), data)
        self.assertEqual(self.written(), sorted(f'docs/reports/acceptance/jev/{name}' for name in self.copies))
        # Again, over identical files: nothing differs, and nothing is replaced.
        status, output = self.restore(self.carried)
        self.assertEqual(status, 0, output)
        self.assertIn('0 written, 5 already there and identical', output)
        stderr = io.StringIO()
        with redirect_stderr(stderr):
            self.assertEqual(questions.main(['--restore-figures', 'x', '--check']), 1)
        self.assertIn('takes its manifest and nothing else', stderr.getvalue())

    def test_a_tampered_text_is_refused_and_nothing_written(self):
        def tamper(figures):
            last = figures[sorted(figures)[-1]]
            last['text'] = last['text'].replace('<text', '<text ', 1)

        status, output = self.restore(self.changed(tamper))
        self.assertEqual(status, 1, output)
        self.assertIn('not its recorded', output)
        self.assertEqual(self.written(), [])
        self.assertFalse(self.figures.exists())
        # A path given twice, of which JSON would keep the second, is refused too.
        name, figure = next(iter(json.loads(self.carried)['figures'].items()))
        entry = f'{json.dumps(name)}: {json.dumps(figure)}'
        status, output = self.restore(f'{{"figures": {{{entry}, {entry}}}, "evidence_files": {{}}}}'.encode())
        self.assertEqual(status, 1, output)
        self.assertIn('a key is repeated', output)
        self.assertEqual(self.written(), [])

    def test_a_path_outside_the_figure_paths_is_refused(self):
        first = sorted(json.loads(self.carried)['figures'])[0]
        for outside in ('figures/I/34.svg', 'docs/reports/acceptance/jev/I-34.svg',
                        f'docs/reports/acceptance/jev/{questions.CALIBRATION_FIGURES}/I-35.svg',
                        '../outside.svg', str(self.directory / 'outside.svg')):
            with self.subTest(outside=outside):
                def move(figures):
                    figures[outside] = figures.pop(first)

                status, output = self.restore(self.changed(move))
                self.assertEqual(status, 1, output)
                self.assertIn("not one of the calibration's figure paths", output)
                self.assertEqual(self.written(), [])
                self.assertFalse((self.directory / 'outside.svg').exists())

    def test_a_differing_file_is_not_overwritten(self):
        self.figures.mkdir(parents=True)
        name = sorted(self.copies)[0]
        (self.jev / name).write_bytes(b'<svg/>\n')
        status, output = self.restore(self.carried)
        self.assertEqual(status, 1, output)
        self.assertIn('differ, and are not replaced', output)
        self.assertEqual((self.jev / name).read_bytes(), b'<svg/>\n')
        self.assertEqual(self.written(), [f'docs/reports/acceptance/jev/{name}'])


def jev_check(row):
    return questions.jev.check_row(row, row['id'], set())


class TallyLines:
    """Result lines built as `jev.py run` builds them for the actual calibration file: the
    row's labels, what the run records, the fingerprint of the request jev.py's own `build` and
    `encode` make, and answers jev.py's own `answer_of` accepts."""

    QUESTION = 'P13'

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        # Resolved, since an output or input path may hold no symlink, as /var is on macOS.
        self.directory = Path(temporary.name).resolve()
        self.questions = self.directory / 'questions.jsonl'
        self.use(shared()['files'][f'{questions.CALIBRATION}-{self.QUESTION}.jsonl'])
        self.requests = {}

    def use(self, data):
        """Ask the questions of this file."""
        self.data = data
        self.questions.write_bytes(data)
        self.rows = [json.loads(line) for line in data.splitlines()]

    def request(self, row, model):
        """The request `jev.py run` sends for the row, with the order check, and its SHA-256."""
        if (row['id'], model) not in self.requests:
            body, _ = questions.jev.build(row, model, True, questions.ROOT, 700)
            self.requests[row['id'], model] = (
                body, hashlib.sha256(questions.jev.encode(body)).hexdigest())
        return self.requests[row['id'], model]

    def made(self, row, model='jev-1.13.0'):
        """What cmd_run writes on every line: the row's labels and the run's record."""
        line = {key: row[key] for key in questions.jev.LABELS if key in row}
        line.update(time='2026-10-26T00:00:00Z', model_requested=model, order_check=True,
                    input_sha256=hashlib.sha256(self.data).hexdigest(), input_rows=len(self.rows),
                    request_sha256=self.request(row, model)[1], latency_s=1.234, status=200)
        return line

    def line(self, row, first, second=None, *, model='jev-1.13.0', answered_by=None):
        """A line for an answer, as cmd_run makes it from a reply that gives it."""
        body, _ = self.request(row, model)
        backwards = body['questions']['q' + questions.jev.REVERSED]

        def answer(choice, criteria, confidence):
            return {'choice': choice, 'confidence': confidence,
                    'probabilities': {option: float(option == choice) for option in criteria}}

        reply = {'model': answered_by or model, 'usage': {'input_tokens': 4000, 'output_tokens': 1},
                 'answers': {'q': answer(first, row['question']['criteria'], 0.9),
                             'q' + questions.jev.REVERSED: answer(second or first,
                                                                  backwards['criteria'], 0.8)}}
        line = self.made(row, model)
        line['model'] = reply['model']
        line.update(questions.jev.answer_of(reply, 'q', row['question']))
        again = questions.jev.answer_of(reply, 'q' + questions.jev.REVERSED, backwards)
        again['consistent'] = again['choice'] == line['choice']
        line['reversed'] = again
        line['usage'] = reply['usage']
        line['agrees'] = line['choice'] == row['expected']
        if line['model'] != model:
            line['model_differs'] = True
        return line

    def failed(self, row, status=500):
        """A line for a request that failed, as cmd_run makes it."""
        line = self.made(row)
        line.update(status=status, error=f'HTTP {status}' if status else 'cannot connect: refused')
        return line

    def clean_run(self):
        return [self.line(row, row['expected']) for row in self.rows]

    def tally(self, lines):
        results = self.directory / 'results.jsonl'
        results.write_text(''.join(json.dumps(line, ensure_ascii=False) + '\n' for line in lines))
        return self.tally_file(results)

    def tally_file(self, results, *options):
        stdout, stderr = io.StringIO(), io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            status = questions.main(['--tally', str(self.questions), str(results), *options])
        return status, stdout.getvalue(), stderr.getvalue()

    def refused(self, lines, message):
        status, out, err = self.tally(lines)
        self.assertEqual(status, 1, out + err)
        self.assertIn(message, err)
        self.assertNotIn('clears', out)

    def by_role(self, role):
        return [i for i, row in enumerate(self.rows) if row['calibration']['role'] == role]


class Tally(TallyLines, unittest.TestCase):
    """The tally's verdicts on P13's file, and its refusals."""

    def test_found_in_both_orders_clears_the_bar(self):
        status, out, _ = self.tally(self.clean_run())
        self.assertEqual(status, 0, out)
        self.assertIn('10 of 10 planted faults found', out)
        self.assertIn('0 of 10 controls false alarms', out)
        self.assertIn('exits 0; 20 of 20 first answers as expected', out)
        self.assertIn(f'{self.QUESTION} clears its bar.', out)

    def test_a_plant_missed_in_one_order(self):
        lines = self.clean_run()
        for k in self.by_role('plant')[:2]:
            lines[k] = self.line(self.rows[k], 'bridge missing or inadequate', 'bridge stated')
        status, out, _ = self.tally(lines)
        self.assertEqual(status, 1)
        self.assertIn('8 of 10 planted faults found', out)
        self.assertIn('2. 8 of 10 planted faults found in both orders (at least 9): fails', out)
        self.assertEqual(out.count('; missed'), 2)

    def test_cannot_tell_is_neither_found_nor_a_false_alarm(self):
        lines = self.clean_run()
        plant, control = self.by_role('plant')[0], self.by_role('control')[0]
        lines[plant] = self.line(self.rows[plant], 'cannot tell')
        lines[control] = self.line(self.rows[control], 'cannot tell', 'no bridge required')
        status, out, _ = self.tally(lines)
        self.assertEqual(status, 0, out)
        self.assertIn('9 of 10 planted faults found', out)
        self.assertIn('0 of 10 controls false alarms', out)
        self.assertIn('18 of 20 first answers as expected', out)

    def test_a_false_alarm_in_the_reversed_order_only(self):
        lines = self.clean_run()
        for k in self.by_role('control')[:3]:
            lines[k] = self.line(self.rows[k], 'bridge stated', 'bridge missing or inadequate')
        status, out, _ = self.tally(lines)
        self.assertEqual(status, 1)
        self.assertIn('3 of 10 controls false alarms (at most 2): fails', out)
        self.assertIn('20 of 20 first answers as expected', out)
        k = self.by_role('control')[2]
        lines[k] = self.line(self.rows[k], 'bridge stated')
        self.assertEqual(self.tally(lines)[0], 0)

    def test_condition_four_is_jev_score_itself(self):
        # Five controls answered "cannot tell": no false alarm, every plant found, and 15 of 20
        # first answers as expected, under the bar `jev.py score --bar 0.8` holds to.
        lines = self.clean_run()
        for k in self.by_role('control')[:5]:
            lines[k] = self.line(self.rows[k], 'cannot tell')
        status, out, _ = self.tally(lines)
        self.assertEqual(status, 1, out)
        self.assertIn('3. 0 of 10 controls false alarms (at most 2): holds', out)
        self.assertIn('exits 1; 15 of 20 first answers as expected (at least 80%): fails', out)
        # Whatever the tally counts, the fourth condition is what score returns.
        score = questions.jev.main
        with patch.object(questions.jev, 'main', side_effect=lambda argv: 1 if argv[0] == 'score'
                          else score(argv)) as called:
            status, out, _ = self.tally(self.clean_run())
        self.assertEqual(status, 1, out)
        self.assertEqual(called.call_args.args[0][0::2], ['score', '--bar'])
        self.assertEqual(called.call_args.args[0][3], '0.8')
        self.assertIn('exits 1; 20 of 20 first answers as expected (at least 80%): fails', out)

    def test_a_failed_request_fails_condition_one(self):
        for request_status, message in ((500, 'failed request: HTTP 500'),
                                        (None, 'failed request: cannot connect: refused')):
            with self.subTest(status=request_status):
                lines = self.clean_run()
                k = self.by_role('control')[0]
                lines[k] = self.failed(self.rows[k], request_status)
                status, out, _ = self.tally(lines)
                self.assertEqual(status, 1)
                self.assertIn('19 of 20 rows answered; 1 failed requests', out)
                self.assertIn(message, out)

    def test_a_failed_request_without_an_error_is_refused(self):
        for request_status in (500, None):
            with self.subTest(status=request_status):
                lines = self.clean_run()
                k = self.by_role('plant')[0]
                lines[k] = self.made(self.rows[k])
                lines[k]['status'] = request_status
                self.refused(lines, 'a failed request without an error')

    def test_a_non_http_integer_or_boolean_status_is_refused(self):
        for request_status in (-1, 0, 99, 600, 999, False, True):
            with self.subTest(status=request_status):
                lines = self.clean_run()
                k = self.by_role('plant')[0]
                lines[k] = self.failed(self.rows[k], request_status)
                self.refused(lines, 'latency or status is not as jev.py run writes it')

    def test_impossible_times_and_latencies_are_refused(self):
        changes = ({'time': '2026-99-99T99:99:99Z'},
                   {'time': '2026-02-29T00:00:00Z'},
                   {'time': '2026-10-26T24:00:00Z'},
                   {'time': '2026-10-26T23:60:00Z'},
                   {'time': '2026-10-26T23:59:60Z'},
                   {'latency_s': 0}, {'latency_s': -0.001})
        for change in changes:
            with self.subTest(change=change):
                lines = self.clean_run()
                lines[self.by_role('plant')[0]].update(change)
                self.refused(lines, 'time, model asked for, latency or status')

    def test_only_reachable_partial_answer_stages_are_accepted(self):
        k = self.by_role('control')[0]
        row = self.rows[k]
        answered = self.line(row, row['expected'])
        error = questions.SHAPE_ERROR + 'reversed answer)'
        shapes = ({}, {'model': None},
                  {key: answered[key] for key in ('model', 'choice', 'probabilities', 'confidence')})
        for partial in shapes:
            with self.subTest(fields=sorted(partial)):
                lines = self.clean_run()
                lines[k] = dict(self.made(row), **partial, error=error, body='malformed reply')
                status, out, err = self.tally(lines)
                self.assertEqual(status, 1, out + err)
                self.assertEqual(err, '')
                self.assertIn('19 of 20 rows answered; 1 failed requests', out)

    def test_unreachable_partial_answer_stages_are_refused(self):
        k = self.by_role('plant')[0]
        row = self.rows[k]
        answered = self.line(row, row['expected'])
        fields = ('model', 'choice', 'probabilities', 'confidence')
        allowed = (set(), {'model'}, set(fields))
        for mask in range(1 << len(fields)):
            selected = {field for bit, field in enumerate(fields) if mask & (1 << bit)}
            if selected in allowed:
                continue
            with self.subTest(fields=sorted(selected)):
                partial = {field: answered[field] for field in selected}
                lines = self.clean_run()
                lines[k] = dict(self.made(row), **partial,
                                error=questions.SHAPE_ERROR + 'partial answer)', body='malformed reply')
                self.refused(lines, 'partial answer fields are not a stage')
        for partial in ({'model': answered['model']},
                        {**{key: answered[key] for key in fields}, 'model': None},
                        {**{key: answered[key] for key in fields}, 'choice': 'not an option'}):
            with self.subTest(partial=partial):
                lines = self.clean_run()
                lines[k] = dict(self.made(row), **partial,
                                error=questions.SHAPE_ERROR + 'partial answer)', body='malformed reply')
                self.refused(lines, 'partial answer is not as jev.py run writes it')

    def test_another_model_fails_condition_one(self):
        lines = self.clean_run()
        lines[0] = self.line(self.rows[0], self.rows[0]['expected'], answered_by='jev-1.14.0')
        self.assertIs(lines[0]['model_differs'], True)
        status, out, _ = self.tally(lines)
        self.assertEqual(status, 1)
        self.assertIn('models jev-1.13.0, jev-1.14.0: fails', out)
        lines = [self.line(row, row['expected'], model='jev-1.14.0') for row in self.rows]
        status, out, _ = self.tally(lines)
        self.assertEqual(status, 1, out)
        self.assertIn('20 of 20 rows answered; 0 failed requests; models jev-1.14.0: fails', out)

    def test_agrees_is_required_and_says_whether_the_first_answer_is_expected(self):
        # The review's counterexamples: correct choices with every `agrees` false, or with none.
        self.refused([dict(line, agrees=False) for line in self.clean_run()],
                     'its agrees is not whether its first answer is the expected one')
        self.refused([{k: v for k, v in line.items() if k != 'agrees'} for line in self.clean_run()],
                     "an answer without ['agrees']")
        lines = self.clean_run()
        lines[5]['agrees'] = 1
        self.refused(lines, 'its agrees is not whether')

    def test_the_calibration_file_must_have_its_exact_shape(self):
        rows = [json.loads(line) for line in self.data.splitlines()]
        plants = [r for r in rows if r['calibration']['role'] == 'plant']
        controls = [r for r in rows if r['calibration']['role'] == 'control']
        cases = (
            # The review's counterexample: nine plants and one control.
            (plants[:9] + controls[:1], '10 rows, 1 controls and 9 plants'),
            ([r for r in rows if r is not controls[-1]], '19 rows, 9 controls and 10 plants'),
            ([dict(r, calibration=dict(r['calibration'], role='plant')) if r is controls[0] else r
              for r in rows], '20 rows, 9 controls and 11 plants'),
            # A proposition in two rows, under two ids.
            ([dict(controls[0], id=controls[1]['id'] + '-again') if r is controls[1] else r
              for r in rows], 'a proposition is in two rows'),
            ([dict(r, expected='bridge missing or inadequate') if r is controls[0] else r
              for r in rows], 'is not a control row of P13'),
            ([dict(r, calibration=dict(r['calibration'], hash='0' * 64)) if r is plants[0] else r
              for r in rows], 'is not a plant row of P13'),
            # III.29, which the rulings take out of the set, in place of the control III.18.
            ([dict(r, ref='III.29', id='11-III.29-representation') if r['ref'] == 'III.18' else r
              for r in rows], 'not III.18 III.33 III.24 III.26, the list of '
             f'{questions.ENTRY} as {questions.RULINGS}'),
        )
        for changed, message in cases:
            with self.subTest(message=message):
                self.use(b''.join(json.dumps(r, ensure_ascii=False).encode() + b'\n' for r in changed))
                self.refused(self.clean_run(), message)
        # A label repeated: two rows with one id, which jev.py's reader refuses.
        self.use(b''.join(json.dumps(dict(r, id=rows[0]['id']) if r is rows[1] else r,
                                     ensure_ascii=False).encode() + b'\n' for r in rows))
        status, _, err = self.tally([])
        self.assertEqual(status, 1)
        self.assertIn('is used twice', err)

    def test_calibration_question_and_ref_must_be_text(self):
        rows = [json.loads(line) for line in self.data.splitlines()]
        invalid = (('missing', None, True), ('null', None, False), ('list', [], False),
                   ('object', {}, False), ('numeric', 13, False))
        for field, message in (('question', 'every calibration.question must be text'),
                               ('ref', 'every ref must be text')):
            for kind, value, missing in invalid:
                with self.subTest(field=field, kind=kind):
                    changed = copy.deepcopy(rows)
                    target = changed[0]['calibration'] if field == 'question' else changed[0]
                    if missing:
                        del target[field]
                    else:
                        target[field] = value
                    self.use(b''.join(json.dumps(row, ensure_ascii=False).encode() + b'\n'
                                      for row in changed))
                    status, out, err = self.tally([])
                    self.assertEqual(status, 1, out + err)
                    self.assertTrue(err.startswith('refused: '), err)
                    self.assertIn(message, err)
                    self.assertNotIn('Traceback', out + err)

    def test_a_label_or_line_repeated_or_not_the_row_s_is_refused(self):
        self.refused(self.clean_run() + [self.clean_run()[0]], 'answered twice')
        for key, value in (('ref', 'I.1'), ('item', 9), ('seeded', 1), ('id', 'nowhere')):
            with self.subTest(key=key):
                lines = self.clean_run()
                lines[3][key] = value
                self.refused(lines, 'is no row of' if key == 'id' else f"its {key} is not the row's")
        lines = self.clean_run()
        del lines[3]['seeded']
        self.refused(lines, 'not a line that jev.py run writes')

    def test_request_fingerprints_are_those_of_the_requests_run_builds(self):
        # The review's counterexample, an all-zero fingerprint; another row's; another model's.
        for name, fingerprint in (('zero', '0' * 64), ('another row', self.request(self.rows[4], 'jev-1.13.0')[1]),
                                  ('another model', self.request(self.rows[3], 'jev-1.14.0')[1]),
                                  ('upper case', self.request(self.rows[3], 'jev-1.13.0')[1].upper())):
            with self.subTest(fingerprint=name):
                lines = self.clean_run()
                lines[3]['request_sha256'] = fingerprint
                self.refused(lines, 'its request_sha256 is not that of the request jev.py run builds')

    def test_a_mismatched_input_or_a_foreign_line_is_refused(self):
        for change, message in (({'input_sha256': '1' * 64}, 'another input'),
                                ({'input_rows': 21}, 'another input'),
                                ({'input_rows': 20.0}, 'another input'),
                                ({'order_check': False}, 'without the order check'),
                                ({'expected': 'no bridge required'}, "its expected is not the row's"),
                                ({'time': 'yesterday'}, 'its time'),
                                ({'latency_s': True}, 'its time'),
                                ({'reversed': None}, 'its reversed asking'),
                                ({'choice': 'cannot tell'}, 'its answer is not as jev.py run writes it'),
                                ({'model_differs': False}, 'model_differs')):
            with self.subTest(change=change):
                lines = self.clean_run()
                lines[3].update(change)
                self.refused(lines, message)
        lines = self.clean_run()
        del lines[3]['request_sha256']
        self.refused(lines, 'not a line that jev.py run writes')

    def test_an_unanswered_row_fails_condition_one(self):
        status, out, _ = self.tally(self.clean_run()[1:])
        self.assertEqual(status, 1)
        self.assertIn('19 of 20 rows answered', out)
        self.assertIn('unanswered', out)


@unittest.skipUnless(shutil.which('rsvg-convert'), 'rsvg-convert renders the figures, and is not on the PATH')
class TallyFigures(TallyLines, unittest.TestCase):
    """The tally of P15, whose requests carry images: each request is built again, its images
    read from a tree holding the committed figures and the restored copies."""

    QUESTION = 'P15'

    def setUp(self):
        super().setUp()
        self.root = self.directory / 'repository'
        shutil.copytree(REPOSITORY / 'figures', self.root / 'figures')
        for name, data in shared()['files'].items():
            if name.startswith(questions.CALIBRATION_FIGURES + '/'):
                path = self.root / 'docs/reports/acceptance/jev' / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
        self.enterContext(patch.object(questions, 'ROOT', self.root))

    def test_found_in_both_orders_clears_the_bar(self):
        self.assertTrue(all(row.get('assets') for row in self.rows))
        status, out, _ = self.tally(self.clean_run())
        self.assertEqual(status, 0, out)
        self.assertIn('P15 clears its bar.', out)

    def test_an_image_row_s_fingerprint_is_checked(self):
        lines = self.clean_run()
        k = next(i for i, row in enumerate(self.rows) if row['ref'] == 'I.13')
        lines[k]['request_sha256'] = '0' * 64
        self.refused(lines, 'its request_sha256 is not that of the request jev.py run builds')

    def test_a_changed_figure_not_restored_is_refused(self):
        lines = self.clean_run()
        next(self.root.glob(f'docs/reports/acceptance/jev/{questions.CALIBRATION_FIGURES}/I-13.svg')).unlink()
        self.refused(lines, 'cannot be built again')

    def test_a_run_at_another_svg_width_is_tallied_at_that_width(self):
        # The review's probe: jev.py's own run, its figures rendered at 701, with its key and
        # its replies stood in for, so that no key is read and nothing is sent. Its lines are
        # accepted at the width it was given, and refused at the default.
        results = self.directory / 'results.jsonl'
        rows = iter(self.rows)

        def reply(method, url, key, timeout, body=None, images=False):
            if method == 'GET':
                return questions.jev.Reply(200, b'{"models": [{"name": "jev-1.13.0"}]}', 0.1)
            row, asked = next(rows), json.loads(body)['questions']
            answers = {qid: {'choice': row['expected'], 'confidence': 0.9,
                             'probabilities': {option: float(option == row['expected'])
                                               for option in q['criteria']}}
                       for qid, q in asked.items()}
            usage = {'input_tokens': 4000, 'output_tokens': 1}
            return questions.jev.Reply(200, json.dumps({'model': 'jev-1.13.0', 'answers': answers,
                                                        'usage': usage}).encode(), 1.0)

        stderr = io.StringIO()
        with patch.object(questions.jev, 'read_key', lambda: 'stand-in'), \
                patch.object(questions.jev, 'request', reply), \
                redirect_stdout(io.StringIO()), redirect_stderr(stderr):
            status = questions.jev.main(['run', str(self.questions), '--out', str(results),
                                         '--svg-width', '701', '--assets-root', str(self.root),
                                         '--base-url', 'http://127.0.0.1:9'])
        self.assertEqual(status, 0, stderr.getvalue())
        self.assertIsNone(next(rows, None))
        written = [json.loads(line) for line in results.read_text().splitlines()]
        self.assertEqual([line['id'] for line in written], [row['id'] for row in self.rows])
        # The width is in what is sent: no figure's request is the one built at 700.
        self.assertTrue(all(line['request_sha256'] != self.request(row, 'jev-1.13.0')[1]
                            for line, row in zip(written, self.rows)))
        status, out, err = self.tally_file(results, '--svg-width', '701')
        self.assertEqual(status, 0, out + err)
        self.assertIn('P15 clears its bar.', out)
        for options in ((), ('--svg-width', str(questions.SVG_WIDTH))):
            with self.subTest(options=options):
                status, out, err = self.tally_file(results, *options)
                self.assertEqual(status, 1, out + err)
                self.assertIn('its request_sha256 is not that of the request jev.py run builds', err)
                self.assertNotIn('clears', out)
        # The width is the tally's alone.
        for argv, message in ((['--commit', 'HEAD', '--svg-width', '701'], '--svg-width is for --tally alone'),
                              (['--restore-figures', 'x', '--svg-width', '701'], 'takes its manifest and nothing else')):
            stderr = io.StringIO()
            with redirect_stdout(io.StringIO()), redirect_stderr(stderr):
                self.assertEqual(questions.main(argv), 1)
            self.assertIn(message, stderr.getvalue())


if __name__ == '__main__':
    unittest.main()
