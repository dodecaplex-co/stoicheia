"""Check that the model's committed results are the present harness's.

    python3 -I tests/model/results_check.py    # CI's `model` job, after run.py --fast

`run.py --full --write` heads each file it writes in results/ with the commit it ran at and
the sha256 of the harness (HARNESS in run.py), and names the same commit in the counts of
MODEL.md. Apart from its self-test, which runs run.py on a made-up harness of its own, this
check runs no harness. It fails, naming each file, unless
* the files in results/ are exactly those --write writes, each a regular file that reads;
* each names, once, a commit whose harness files its run read as committed, and the harness
  as it hashes now, and all name the same commit; summary.txt names, once, the Python and
  the date its counts were written with;
* MODEL.md has one block of counts, and it names that commit;
* the runs' output in results/ is what run.py's `judge` accepts, as --write requires: each
  run reached its last line and reported each law and derived property once, none found a
  counterexample in the plane, every mutation was caught, the grid and angle checks found
  no failure, and the hyperbolic plane failed the laws that must fail there and no other;
  and
* summary.txt and the counts in MODEL.md are what --write makes of the runs' output in
  results/.
So a change to any file of HARNESS fails it until `run.py --full --write` is run on the
change, committed, and what it writes is committed too (docs/WORKFLOW.md, section 8). It
reads what a run wrote, and cannot tell a header written by hand from a run's: the security
review, which every change under tests/ gets, reads the results' diff. A results file holds
what its run printed, not how its process exited or what it wrote to stderr, so `judge`
here takes each run to have exited 0; that it did is --write's to check, not this one's.

It is not a file of HARNESS, so a change to it alone needs no new run. Its self-test runs
first: it writes results as --write does, from made-up runs, into a temporary folder, plants
each fault the check exists to catch, and checks that each is caught and that the results
unchanged pass. It drives --write's guards too, and runs `run.py --full --write` for real,
in a git repository of its own, on a made-up harness that changes and restores the
checkout's harness while the run goes on, and on one stopped by SIGTERM partway. For each
of SIGTERM, SIGHUP and SIGINT, it also stops publication after a file is moved to its
backup, after a replacement, after the check for a pending signal, after the signals are
blocked again and while the old files are removed, and checks each time that every earlier
file returns; and it changes a harness file during publication and checks that the earlier
files return.
"""
import contextlib
import hashlib
import importlib.util
import itertools
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run as runner  # noqa: E402
from run import (COMMITTED, COUNTS, COUNTS_FROM, EUCLIDEAN, EXPECTED_TO_FAIL,  # noqa: E402
                 HARNESS, HARNESS_LINE, LAST_LINE, LAWS, MODEL_MD, RESULTS, ROOT, SUMMARY, git,
                 harness_hash, judge, parse_results, plan, result_file, search_names,
                 short_commit, write, written)
from derived import PROPERTIES  # noqa: E402

PAGE = 'A page.\n\n<!-- counts:begin -->\nx\n<!-- counts:end -->\n'   # a MODEL.md to write into


def shown(path):
    """a path as a message names it: from the repository's root when it is inside"""
    rel = os.path.relpath(path, ROOT)
    return path if rel.startswith('..') else rel


def safe(name):
    """a name found in results/, as a message shows it: quoted when it holds anything odd"""
    return name if re.fullmatch(r'[\w.+-]+', name, re.A) else ascii(name)


class Unreadable(Exception):
    """a file of results/, or MODEL.md, that does not read: a problem, not a traceback"""


def header_of(path):
    """{key: [values]} from the `# key: value` lines that head a results file"""
    fields = {}
    try:
        with open(path, encoding='utf-8', errors='replace') as f:
            for line in f:
                if not line.startswith('# '):
                    break
                key, sep, value = line[2:].rstrip('\n').partition(': ')
                if sep:
                    fields.setdefault(key, []).append(value)
    except OSError:
        raise Unreadable(f'{shown(path)} does not read') from None
    return fields


def read(path):
    try:
        with open(path, encoding='utf-8', errors='replace') as f:
            return f.read()
    except OSError:
        raise Unreadable(f'{shown(path)} does not read') from None


def body_of(text):
    """what a run printed: a results file after its header and the blank line that ends it"""
    head, sep, body = text.partition('\n\n')
    return body if sep and all(line.startswith('# ') for line in head.split('\n')) else None


def first_difference(have, want):
    """the number of the first line at which `have` is not `want`, or None"""
    if have == want:
        return None
    a, b = have.split('\n'), want.split('\n')
    return 1 + next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))


def made_again(results, model_md):
    """The problems with the runs' output in results/, as run.py's `judge` finds them, which
    stop --write from writing; and, when it finds none, with summary.txt and MODEL.md's
    counts, against what --write makes of that output, with the provenance summary.txt
    names. Their first line names the Python that wrote them, which here is summary.txt's.
    The output records no exit status or stderr, so each run is taken to have exited 0."""
    runs = plan(True)
    for r in runs:
        r.out = body_of(read(os.path.join(results, result_file(r))))
        if r.out is None:
            return [f'{shown(results)}/{result_file(r)} has no blank line after its header']
        r.seconds, r.command, r.code, r.err = 0.0, '', 0, ''
        r.laws, r.derived, r.twice = parse_results(r.out, search_names)
    refused = judge(runs)
    if refused:
        return [f"the runs' output in {shown(results)}/ is what run.py refuses to write: {b}"
                for b in refused]
    prov = {k: v[0] for k, v in header_of(os.path.join(results, SUMMARY)).items()}
    with tempfile.TemporaryDirectory() as tmp:
        page = os.path.join(tmp, 'MODEL.md')
        with open(page, 'w', encoding='utf-8') as f:
            f.write(PAGE)
        write(runs, prov, os.path.join(tmp, 'results'), page)
        summary = read(os.path.join(tmp, 'results', SUMMARY))
        counts = COUNTS.search(read(page)).group(0).replace(
            f'Python {platform.python_version()}.', f'Python {prov["python"].split()[0]}.', 1)
    problems = []
    if (n := first_difference(read(os.path.join(results, SUMMARY)), summary)) is not None:
        problems.append(f"{shown(results)}/{SUMMARY} is not what --write makes of the runs' "
                        f'output in {shown(results)}/: it differs from line {n}')
    page = read(model_md)
    block = COUNTS.search(page)
    if (n := first_difference(block.group(0), counts)) is not None:
        line = page.count('\n', 0, block.start()) + n
        problems.append(f"{shown(model_md)}'s counts are not what --write makes of the runs' "
                        f'output in {shown(results)}/: they differ from its line {line}')
    return problems


def check_results(results=RESULTS, model_md=MODEL_MD, harness=None):
    """(the problems, the commits the results name). A problem is a file of results/ that is
    missing, or one --write does not write, or one that is not a regular file or does not
    read; a file that names no commit or harness, or one twice, or a commit its run did not
    read as committed, or a harness other than `harness` (by default the harness now); a
    summary.txt that names no Python or date, or one twice; files that name more than one
    commit or harness between them; a MODEL.md that is not a regular file or does not read,
    or whose counts are not one block naming the results' commit; and, when there is no other,
    runs' output that run.py's `judge` refuses, or summary.txt or MODEL.md's counts not what
    --write makes of it. Runs no harness."""
    harness = harness or harness_hash()
    where = shown(results)
    if os.path.islink(results) or not os.path.isdir(results):
        return [f'{where} is not a folder: --write writes one'], []
    present = set(os.listdir(results))
    expected = written()
    problems = [f'{where}/{n} is missing: --write writes it' for n in sorted(expected - present)]
    problems += [f'{where}/{safe(n)} is not a file --write writes'
                 for n in sorted(present - expected)]
    commits, harnesses = {}, {}
    for name in sorted(expected & present):
        path = os.path.join(results, name)
        if os.path.islink(path):
            problems.append(f'{where}/{name} is a symbolic link: --write writes a file')
            continue
        if not os.path.isfile(path):
            problems.append(f'{where}/{name} is not a regular file: --write writes one')
            continue
        try:
            fields = header_of(path)
        except Unreadable as e:
            problems.append(str(e))
            continue
        wanted = [('commit', 'commit', r'([0-9a-f]{40}) \(([^()]*)\)', commits),
                  ('harness' if name == SUMMARY else HARNESS_LINE, 'harness', r'([0-9a-f]{64})',
                   harnesses)]
        if name == SUMMARY:   # made_again writes the counts from these
            wanted += [('python', 'Python', r'([0-9]+\.[0-9]+\.[0-9]+\S*) \(.+\)', {}),
                       ('date', 'date', r'([0-9]{4}-[0-9]{2}-[0-9]{2})', {})]
        for key, label, form, named in wanted:
            values = fields.get(key, [])
            if len(values) > 1:
                problems.append(f'{where}/{name} names its {label} {len(values)} times')
                continue
            m = re.fullmatch(form, values[0]) if values else None
            if not m:
                problems.append(f'{where}/{name} names no {label} in its header')
                continue
            if label == 'commit' and m.group(2) != COMMITTED:
                problems.append(f'{where}/{name} names commit {m.group(1)[:12]} without '
                                f'"({COMMITTED})": its run read other harness files')
                continue
            named.setdefault(m.group(1), []).append(name)
    for value, names in sorted(harnesses.items()):
        if value != harness:
            problems += [f'{where}/{n} names harness {value[:12]}..., not {harness[:12]}..., '
                         'the harness as it hashes now' for n in names]
    for label, named in (('commits', commits), ('harnesses', harnesses)):
        if len(named) > 1:
            problems.append(f'the results name {len(named)} {label}: ' + '; '.join(
                f'{v[:12]} in {", ".join(ns)}' for v, ns in sorted(named.items())))
    page = shown(model_md)
    if os.path.islink(model_md) or not os.path.isfile(model_md):
        problems.append(f'{page} is not a regular file')
        return problems, sorted(commits)
    try:
        blocks = [m.group(0) for m in COUNTS.finditer(read(model_md))]
    except Unreadable as e:
        problems.append(str(e))
        return problems, sorted(commits)
    if len(blocks) != 1:
        problems.append(f'{page} has {len(blocks) or "no"} counts blocks, not one')
    elif not (m := re.search(re.escape(COUNTS_FROM) + r'([0-9a-f]{12})`', blocks[0])):
        problems.append(f"{page}'s counts name no commit")
    else:
        for commit, names in sorted(commits.items()):
            if short_commit(commit) != m.group(1):
                problems.append(f"{page}'s counts name commit {m.group(1)}, not {commit[:12]}, "
                                + ('the commit of the results' if len(commits) == 1
                                   else f'the commit of {", ".join(names)}'))
    if not problems:
        try:
            problems = made_again(results, model_md)
        except Unreadable as e:
            problems = [str(e)]
    return problems, sorted(commits)


ENDS = {'mutations': ['15/15 mutations caught'], 'grid_check': ['failures 0 Counter()'],
        'angle_check': ['triple incidence grid failures: 0 []', 'float failures: {}'],
        'hyperbolic': ['self-test: made up']}   # what each passing run reports, as judge reads it


def made_up_runs():
    """The runs of the full plan, each with a little made-up output that run.py accepts: in
    the plane and the hyperbolic plane a row for each law, with a counterexample only to
    the laws that must fail in the hyperbolic plane, there; in the exhaustive and structured
    runs one for each derived property too; and each run's verdicts and last line."""
    runs = plan(True)
    for i, r in enumerate(runs):
        rows = ([f'{law} {i + 9} {i + 5} '
                 f'{int(r.key == "hyperbolic" and law in EXPECTED_TO_FAIL) * (i + 1)}'
                 for law in LAWS]
                if r.key.startswith(EUCLIDEAN + ('hyperbolic',)) else [])
        if r.key in ('exhaustive', 'structured'):
            rows += [f'{p} {i + 7} {i + 3} 0' for p in PROPERTIES]
        last = next((v for k, v in LAST_LINE.items() if r.key.startswith(k)), r.key + ':')
        rows += ENDS.get(r.key, []) + [f'{last} made up by the self-test']
        r.out = '\n'.join(rows) + '\n'
        r.seconds, r.command = 1.0, 'python3 -I'
        r.laws, r.derived, r.twice = parse_results(r.out, search_names)
    return runs


def write_guard_self_test():
    """Drive --write's guards with stable, invalid and changing provenance, without running a
    harness: in the checkout, which hands its provenance to a run from a copy of the harness,
    and in that run, which writes."""
    commit = 'a' * 40
    harness = 'b' * 64

    def prov(sha=commit, state=COMMITTED, digest=harness, date='2000-01-01'):
        return dict(commit=f'{sha} ({state})', harness=digest,
                    python=f'{platform.python_version()} (self-test)', date=date)

    def exercise(provenances, start=None, copy=harness, in_place=False):
        """--full --write: in the checkout when `start` is None, else in a run from a copy of
        the harness, handed the provenance `start`; the copy hashes as `copy`. A run handed
        `start` runs from a copy elsewhere than the checkout, unless `in_place`."""
        launched = []

        class GuardRun:
            key = 'hyperbolic'
            seconds = 0.0
            laws = {}
            derived = {}

            def go(self):
                launched.append(self.key)

        run = GuardRun()
        writer = mock.Mock()
        child = mock.MagicMock()   # subprocess.Popen, for the run from a copy
        child.return_value.__enter__.return_value.wait.return_value = 0
        snapshot = None if start is None else {'root': ROOT, 'provenance': start}
        checkout = (runner.CHECKOUT if start is None or in_place
                    else os.path.join(os.path.dirname(HERE), 'checkout'))
        patches = (mock.patch.object(runner.sys, 'argv', ['run.py', '--full', '--write']),
                   mock.patch.object(runner, 'FROM_SNAPSHOT', snapshot),
                   mock.patch.object(runner, 'CHECKOUT', checkout),
                   mock.patch.object(runner, 'harness_hash', return_value=copy),
                   mock.patch.object(runner, 'committed_file', return_value=b''),
                   mock.patch.object(runner, 'stop_as_exit'),
                   mock.patch.object(runner.subprocess, 'Popen', child),
                   mock.patch.object(runner.subprocess, 'run', side_effect=AssertionError(
                       'the guard self-test ran a process')),
                   mock.patch.object(runner, 'self_test'),
                   mock.patch.object(runner, 'check_names', return_value=(0, [])),
                   mock.patch.object(runner, 'check_lock', return_value=(True, 'self-test')),
                   mock.patch.object(runner, 'plan', return_value=[run]),
                   mock.patch.object(runner, 'judge', return_value=[]),
                   mock.patch.object(runner, 'totals', return_value=({}, 0)),
                   mock.patch.object(runner, 'derived_table', return_value=''),
                   mock.patch.object(runner, 'EXPECTED_TO_FAIL', set()),
                   mock.patch.object(runner, 'provenance', side_effect=provenances),
                   mock.patch.object(runner, 'write', writer),
                   mock.patch('builtins.print'))
        with contextlib.ExitStack() as stack:   # one `with` of them all is too deep for 3.11
            for patch in patches:
                stack.enter_context(patch)
            try:
                if start is None:
                    stopped = runner.bootstrap(['--full', '--write'])
                else:
                    runner.main()
                    stopped = None
            except SystemExit as e:
                stopped = e.code
        return launched, writer, child, stopped

    before = prov()
    launched, writer, child, stopped = exercise([before])
    handed = child.call_args
    if stopped != 0 or launched or writer.called or child.call_count != 1 \
            or handed.args[0][1:2] + handed.args[0][3:] != ['-I', '--full', '--write'] \
            or os.path.dirname(handed.args[0][2]) == HERE \
            or json.loads(handed.kwargs['env'][runner.SNAPSHOT]) != {'root': ROOT,
                                                                     'provenance': before}:
        raise AssertionError('--write in the checkout did not hand its provenance to a run '
                             'from a copy of the harness')

    launched, writer, child, stopped = exercise([prov(date='2000-01-02')], start=before)
    if stopped is not None or launched != ['hyperbolic'] or writer.call_count != 1 \
            or writer.call_args.args[1] is not before \
            or writer.call_args.kwargs.get('expected_signature') \
            != runner.provenance_signature(before) or child.called:
        raise AssertionError('--write refused stable provenance or did not use its initial record')

    refused = 0
    for initial in (prov(state='harness files differ from this commit'),
                    prov(sha='unknown', state='state unknown')):
        for given in ({}, {'start': initial}):
            launched, writer, child, stopped = exercise([initial], **given)
            if launched or writer.called or child.called or "not a commit's" not in str(stopped):
                raise AssertionError('--write did not refuse invalid initial provenance before '
                                     'running')
            refused += 1

    for given, says in (({}, 'does not hash as the harness checked out does'),
                        ({'start': before}, 'does not hash as its provenance says')):
        launched, writer, child, stopped = exercise([before], copy='e' * 64, **given)
        if launched or writer.called or child.called or says not in str(stopped):
            raise AssertionError('--write did not refuse a copy of the harness that hashes '
                                 'otherwise before running')
        refused += 1

    launched, writer, child, stopped = exercise([before], start=before, in_place=True)
    if launched or writer.called or child.called \
            or 'this run is not from a copy of the harness' not in str(stopped):
        raise AssertionError(f'--write ran in place, not from a copy, when {runner.SNAPSHOT} '
                             'was set')
    refused += 1

    # Imported, as this check imports it, run.py takes no root or provenance from SNAPSHOT.
    spec = importlib.util.spec_from_file_location('run_imported', os.path.join(HERE, 'run.py'))
    imported = importlib.util.module_from_spec(spec)
    planted = json.dumps({'root': os.path.join(ROOT, 'elsewhere'), 'provenance': before})
    with mock.patch.dict(os.environ, {runner.SNAPSHOT: planted}):
        spec.loader.exec_module(imported)
        kept = os.environ.get(runner.SNAPSHOT) == planted
    if imported.FROM_SNAPSHOT is not None or imported.ROOT != ROOT or not kept:
        raise AssertionError(f'run.py, imported, read {runner.SNAPSHOT}')

    changed = [prov(sha='c' * 40),
               prov(state='harness files differ from this commit'),
               prov(digest='d' * 64)]
    for after in changed:
        launched, writer, child, stopped = exercise([after], start=before)
        if launched != ['hyperbolic'] or writer.called \
                or 'provenance changed while it ran' not in str(stopped):
            raise AssertionError('--write did not refuse changed provenance before writing')
        refused += 1
    print(f'model write guard self-test: stable provenance handed on and passed; {refused} '
          'invalid starts, copies, runs in place and changes refused; imported, run.py reads '
          f'no {runner.SNAPSHOT}')


PLANT = 'MODEL_SELF_TEST_PLANT'   # the made-up harness's orders: 'aba', 'stay', 'term' or none
CHECKOUT_IMPORT = 'MODEL_SELF_TEST_CHECKOUT'
FAKE_EXHAUSTIVE = "Law 9 5 0\nderived.P 7 3 0\nexhaustive axioms run: 1\n"   # what it prints
LIVE_IMPORT = f"""import os
if os.path.dirname(os.path.abspath(__file__)) == os.environ.get({CHECKOUT_IMPORT!r}):
    with open('checkout-imported', 'a') as marker:
        marker.write(os.path.basename(__file__) + '\\n')
"""
FAKE = {   # the made-up harness: every file of HARNESS but run.py, which is the real one
    'model.py': LIVE_IMPORT + "def read_laws():\n    return {'Ax': 'Law'}, set()\n",
    'derived.py': LIVE_IMPORT + "PROPERTIES = ('derived.P',)\n",
    'search.py': LIVE_IMPORT + f"""import shutil
import sys
AXIOMS = [('Law', None, None)]
if __name__ == '__main__':
    live = os.path.join('tests', 'model', 'exhaustive.py')
    if os.environ.get({PLANT!r}) in ('aba', 'stay') and sys.argv[2] == '3':
        shutil.copyfile(live, 'exhaustive.kept')
        with open(live) as f:
            text = f.read()
        with open(live, 'w') as f:
            f.write(text.replace('Law 9 5 0', 'Law 9 6 0'))
    print('Law 9 5 0')
    print('axioms checked: 1')
""",
    'exhaustive.py': f"""import os
with open(os.path.join('tests', 'model', 'exhaustive.py')) as f, open('seen', 'w') as g:
    g.write(f.read())
print({FAKE_EXHAUSTIVE!r}, end='')
""",
    'structured.py': f"""import os
if os.environ.get({PLANT!r}) == 'aba':
    os.replace('exhaustive.kept', os.path.join('tests', 'model', 'exhaustive.py'))
print('Law 9 5 0')
print('derived.P 7 3 0')
print('structured total counterexamples: 0')
""",
    'mutations.py': f"""import os
import time
if os.environ.get({PLANT!r}) == 'term':   # its pid, to see that the SIGTERM stopped it
    with open('mutations.new', 'w') as f:
        f.write(str(os.getpid()))
    os.replace('mutations.new', 'mutations.pid')
    time.sleep(30)
print('15/15 mutations caught')
""",
    'grid_check.py': "print('failures 0')\n",
    'angle_check.py': ("print('triple incidence grid failures: 0 []')\n"
                       "print('float failures: {}')\n"),
    'hyperbolic.py': LIVE_IMPORT + """AXIOMS = [('Law', None)]
if __name__ == '__main__':
    print('Law 9 5 0')
    print('self-test: made up')
    print('axioms checked: 1')
""",
    'laws.toml': '# made up for the self-test\n',
}


def running(pid):
    """whether there is still a process `pid`"""
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:   # there, but another user's
        return True
    return True


def stopped_by_sigterm(command, root, env):
    """Run `command` in `root` until the made-up mutations.py has started, then send it
    SIGTERM; the finished process, and the pid mutations.py ran as, or None"""
    pid = os.path.join(root, 'mutations.pid')
    with subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True) as p:
        deadline = time.monotonic() + 60
        while not os.path.exists(pid) and p.poll() is None and time.monotonic() < deadline:
            time.sleep(0.01)
        if p.poll() is None:
            p.send_signal(signal.SIGTERM)
        try:
            out, err = p.communicate(timeout=60)
        except subprocess.TimeoutExpired:
            p.kill()
            out, err = p.communicate()
            err += '\n(it was still running a minute after SIGTERM, and was killed)'
    started = int(read(pid)) if os.path.exists(pid) else None
    return subprocess.CompletedProcess(command, p.returncode, out, err), started


def snapshot_self_test():
    """Run `run.py --full --write` for real, on a made-up harness that runs in moments, in a
    git repository of its own. The harness's last search writes another exhaustive.py into
    the checkout, and its structured run puts the committed one back, so that the checkout
    is as committed when the run begins and when it ends, but not while exhaustive.py runs.
    What is written must be the committed exhaustive.py's output, under the commit and its
    harness's hash. Left in place, the other file must stop the run with nothing written;
    there from the start, it must stop the run before anything runs. Where there are POSIX
    signals, a run sent SIGTERM while its mutations.py runs must exit as sys.exit does, with
    no results/, MODEL.md unchanged, no model-harness-* folder left in the temporary folder
    it was given, and mutations.py no longer running."""
    if set(FAKE) != set(HARNESS) - {'run.py'}:
        raise AssertionError('snapshot self-test: the made-up harness is not HARNESS')
    env = {k: v for k, v in os.environ.items()
           if not k.startswith('GIT_') and k not in (runner.SNAPSHOT, PLANT, CHECKOUT_IMPORT)}
    env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM='1')

    def put(path, text):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, 'w', encoding='utf-8') as f:
            f.write(text)

    for plant in ('aba', 'stay', 'dirty') + (('term',) if os.name == 'posix' else ()):
        with tempfile.TemporaryDirectory() as root:
            model = os.path.join(root, 'tests', 'model')
            for name, text in FAKE.items():
                put(os.path.join(model, name), text)
            shutil.copyfile(os.path.join(HERE, 'run.py'), os.path.join(model, 'run.py'))
            lock = '[axioms]\nAx = "made up"\n'
            put(os.path.join(root, 'Certificate', 'axioms.lock'), lock)
            put(os.path.join(model, 'lock.sha256'),
                hashlib.sha256(lock.encode()).hexdigest() + '  Certificate/axioms.lock\n')
            put(os.path.join(root, 'facts.json'), json.dumps({'axiom_modules': {'Ax': 'M'}}))
            put(os.path.join(model, 'MODEL.md'), PAGE)
            for args in (['init', '-q'], ['add', '.'], ['commit', '-q', '-m', 'A']):
                subprocess.run(['git', '-c', 'user.name=self-test',
                                '-c', 'user.email=self-test@example.invalid', *args],
                               cwd=root, env=env, check=True, capture_output=True)
            commit = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=root, env=env, check=True,
                                    capture_output=True, text=True).stdout.strip()
            committed = harness_hash(model)
            if plant == 'dirty':
                with open(os.path.join(model, 'exhaustive.py'), 'a') as f:
                    f.write('# not committed\n')
            command = [sys.executable, '-I', os.path.join(model, 'run.py'), '--full', '--write']
            run_env = dict(env, **{CHECKOUT_IMPORT: model},
                           **({PLANT: plant} if plant != 'dirty' else {}))
            if plant == 'term':
                tmp = os.path.join(root, 'tmp')   # its own, so a copy left there is this run's
                os.mkdir(tmp)
                p, pid = stopped_by_sigterm(command, root, dict(run_env, TMPDIR=tmp))
            else:
                p = subprocess.run(command, cwd=root, capture_output=True, text=True,
                                   env=run_env)
            results = os.path.join(model, 'results')
            imported = os.path.join(root, 'checkout-imported')
            if os.path.exists(imported):
                raise AssertionError('snapshot self-test: the checkout harness was imported before '
                                     f'snapshot dispatch: {read(imported)}')
            if plant == 'term':
                copies = sorted(n for n in os.listdir(tmp) if n.startswith('model-harness-'))
                wrong = [what for what, there in (
                    ('mutations.py never started', pid is None),
                    (f'it exited {p.returncode}, not {128 + signal.SIGTERM}',
                     p.returncode != 128 + signal.SIGTERM),
                    ('it wrote results/', os.path.exists(results)),
                    ('it changed MODEL.md', read(os.path.join(model, 'MODEL.md')) != PAGE),
                    ('it left its copy, ' + ', '.join(copies), copies),
                    ('its mutations.py is still running', pid is not None and running(pid)),
                ) if there]
                if wrong:
                    raise AssertionError('snapshot self-test: a run stopped by SIGTERM was not '
                                         f'stopped as it should be: {"; ".join(wrong)}: '
                                         f'{p.stdout}{p.stderr}')
                continue
            if plant == 'aba':
                path = os.path.join(results, 'exhaustive.txt')
                fields = header_of(path) if p.returncode == 0 and os.path.isfile(path) else {}
                if fields.get('commit') != [f'{commit} ({COMMITTED})'] \
                        or fields.get(HARNESS_LINE) != [committed] \
                        or body_of(read(path)) != FAKE_EXHAUSTIVE:
                    raise AssertionError('snapshot self-test: a harness changed and restored '
                                         'while it ran was written as the commit\'s: '
                                         f'{p.stdout}{p.stderr}')
                if 'Law 9 6 0' not in read(os.path.join(root, 'seen')) \
                        or harness_hash(model) != committed:
                    raise AssertionError('snapshot self-test: the checkout was not changed and '
                                         'restored while exhaustive.py ran')
                continue
            says = ('provenance changed while it ran' if plant == 'stay'
                    else "not a commit's committed files")
            if p.returncode == 0 or says not in p.stderr or os.path.exists(results) \
                    or read(os.path.join(model, 'MODEL.md')) != PAGE \
                    or (plant == 'dirty') == os.path.exists(os.path.join(root, 'seen')):
                raise AssertionError(f'snapshot self-test: a harness {plant} was not refused as '
                                     f'it should be: {p.stdout}{p.stderr}')
    print('model write snapshot self-test: a harness changed and restored while it ran wrote '
          "the commit's output; changed and left, or changed from the start, nothing"
          + ('; stopped by SIGTERM, nothing, with its copy removed and its harness stopped'
             if os.name == 'posix' else ''))


def output_tree(root):
    entries = {}
    for parent, dirs, files in os.walk(root):
        for name in sorted(dirs + files):
            path = os.path.join(parent, name)
            rel = os.path.relpath(path, root)
            if os.path.islink(path):
                entries[rel] = ('link', os.readlink(path))
            elif os.path.isdir(path):
                entries[rel] = ('directory',)
            else:
                with open(path, 'rb') as f:
                    entries[rel] = ('file', f.read())
    return entries


def publication_signal_self_test():
    """Interrupt each publication boundary and require its whole prior tree back."""
    stops = [getattr(signal, name) for name in ('SIGTERM', 'SIGHUP', 'SIGINT')
             if hasattr(signal, name)]
    if os.name != 'posix' or not hasattr(signal, 'pthread_sigmask') or not stops:
        return

    for stop in stops:
        for timing in ('after backup rename', 'after replacement', 'after pending check',
                       'after second block', 'during backup cleanup'):
            with tempfile.TemporaryDirectory() as tmp:
                results = os.path.join(tmp, 'results')
                model_md = os.path.join(tmp, 'MODEL.md')
                with open(model_md, 'w', encoding='utf-8') as f:
                    f.write(PAGE)
                old = dict(commit='a' * 40 + f' ({COMMITTED})', harness='b' * 64,
                           python=f'{platform.python_version()} (self-test)', date='2000-01-01')
                old_runs = made_up_runs()
                write(old_runs, old, results, model_md)
                linked = os.path.join(results, result_file(old_runs[0]))
                link_target = os.path.join(tmp, 'linked-result.txt')
                os.replace(linked, link_target)
                os.symlink(link_target, linked)
                missing = os.path.join(results, result_file(old_runs[1]))
                os.unlink(missing)
                before = output_tree(tmp)
                new = dict(old, commit='c' * 40 + f' ({COMMITTED})', date='2000-01-02')
                real_replace = os.replace
                real_pending = signal.sigpending
                real_mask = signal.pthread_sigmask
                real_unlink = os.unlink
                sent = False
                blocks = 0

                def interrupting_replace(source, destination):
                    nonlocal sent
                    real_replace(source, destination)
                    if timing == 'after backup rename' and destination.endswith('.old') \
                            and not sent:
                        sent = True
                        os.kill(os.getpid(), stop)
                    if timing == 'after replacement' and destination == model_md and not sent:
                        sent = True
                        if not os.path.isfile(destination):
                            raise AssertionError('publication signal preceded the replacement')
                        os.kill(os.getpid(), stop)

                def interrupting_pending():
                    nonlocal sent
                    pending = real_pending()
                    if timing == 'after pending check' and not sent:
                        sent = True
                        os.kill(os.getpid(), stop)
                    return pending

                def interrupting_mask(how, mask):
                    nonlocal blocks, sent
                    previous_mask = real_mask(how, mask)
                    if how == signal.SIG_BLOCK and stop in set(mask):
                        blocks += 1
                        if timing == 'after second block' and blocks == 2 and not sent:
                            sent = True
                            os.kill(os.getpid(), stop)
                    return previous_mask

                def interrupting_unlink(path, *args, **kwargs):
                    nonlocal sent
                    real_unlink(path, *args, **kwargs)
                    if timing == 'during backup cleanup' and path.endswith('.old') and not sent:
                        sent = True
                        os.kill(os.getpid(), stop)

                previous = {sig: signal.getsignal(sig) for sig in stops}
                runner.stop_as_exit()
                if hasattr(signal, 'SIGINT'):
                    # A shell's background job starts with SIGINT ignored: give it Python's
                    # own handler, so that the interruption the test sends is one.
                    signal.signal(signal.SIGINT, signal.default_int_handler)
                stopped = None
                try:
                    with contextlib.ExitStack() as stack:
                        stack.enter_context(mock.patch.object(
                            runner.os, 'replace', side_effect=interrupting_replace))
                        stack.enter_context(mock.patch.object(
                            runner.signal, 'sigpending', side_effect=interrupting_pending))
                        stack.enter_context(mock.patch.object(
                            runner.signal, 'pthread_sigmask', side_effect=interrupting_mask))
                        stack.enter_context(mock.patch.object(
                            runner.os, 'unlink', side_effect=interrupting_unlink))
                        write(made_up_runs(), new, results, model_md)
                except SystemExit as e:
                    stopped = e.code
                except KeyboardInterrupt:
                    stopped = 128 + signal.SIGINT
                finally:
                    for sig, handler in previous.items():
                        signal.signal(sig, handler)
                after = output_tree(tmp)
                if not sent or stopped != 128 + stop or after != before:
                    raise AssertionError(f'model publication self-test: '
                                         f'{signal.Signals(stop).name} {timing} did not restore '
                                         'the previous output set without temporary files: '
                                         f'stopped {stopped}; '
                                         f'added {sorted(after.keys() - before.keys())}; '
                                         f'removed {sorted(before.keys() - after.keys())}')
    print('model publication self-test: SIGTERM, SIGHUP and SIGINT, sent at five points of '
          'publication, put every earlier file back and leave no temporary file')


def publication_provenance_self_test():
    """Change and leave a harness file during publication; require the prior outputs back."""
    with tempfile.TemporaryDirectory() as tmp:
        model = os.path.join(tmp, 'tests', 'model')
        os.makedirs(model)
        for name in HARNESS:
            shutil.copyfile(os.path.join(HERE, name), os.path.join(model, name))
        env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
        env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM='1')
        for args in (['init', '-q'], ['add', '.'], ['commit', '-q', '-m', 'A']):
            subprocess.run(['git', '-c', 'user.name=self-test',
                            '-c', 'user.email=self-test@example.invalid', *args],
                           cwd=tmp, env=env, check=True, capture_output=True)
        published = os.path.join(tmp, 'published')
        os.makedirs(published)
        results = os.path.join(published, 'results')
        model_md = os.path.join(published, 'MODEL.md')
        with open(model_md, 'w', encoding='utf-8') as f:
            f.write(PAGE)
        with mock.patch.object(runner, 'ROOT', tmp), mock.patch.object(runner, 'CHECKOUT', model):
            prov = runner.provenance()
            signature = runner.provenance_signature(prov)
            write(made_up_runs(), prov, results, model_md)
            before = output_tree(published)
            harness_file = os.path.join(model, 'search.py')
            real_replace = os.replace
            changed = False

            def changing_replace(source, destination):
                nonlocal changed
                real_replace(source, destination)
                if destination == model_md and not changed:
                    changed = True
                    with open(harness_file, 'a', encoding='utf-8') as f:
                        f.write('\n# changed during publication\n')

            stopped = None
            try:
                with mock.patch.object(runner.os, 'replace', side_effect=changing_replace):
                    write(made_up_runs(), prov, results, model_md,
                          expected_signature=signature)
            except SystemExit as e:
                stopped = e.code
        if not changed or 'provenance changed while it ran' not in str(stopped) \
                or output_tree(published) != before \
                or '# changed during publication' not in read(harness_file):
            raise AssertionError('model publication self-test: a harness changed and left during '
                                 'publication did not restore the previous output set and fail')
    print('model publication self-test: a harness changed and left during publication restores '
          'the previous output set and fails')


def self_test():
    """Write results as --write does, from made-up runs, into a temporary folder; plant each
    fault the check exists to catch in a fresh copy, and check that it is caught; and check
    that the results unchanged pass."""
    write_guard_self_test()
    snapshot_self_test()
    publication_signal_self_test()
    publication_provenance_self_test()
    runs = sorted(written() - {SUMMARY})
    if len(runs) < 4:
        raise AssertionError('results self-test: the full plan writes fewer than four runs')
    caught = 0
    with tempfile.TemporaryDirectory() as tmp:
        prov = dict(commit='a' * 40 + f' ({COMMITTED})', harness=harness_hash(),
                    python=f'{platform.python_version()} (self-test)', date='2000-01-01')
        copies = itertools.count(1)

        def fresh():
            d = os.path.join(tmp, f'copy{next(copies)}')
            os.makedirs(d)
            md = os.path.join(d, 'MODEL.md')
            with open(md, 'w', encoding='utf-8') as f:
                f.write(PAGE)
            write(made_up_runs(), prov, os.path.join(d, 'results'), md)
            return os.path.join(d, 'results'), md

        def edit(path, pattern, new, count=1):
            text = read(path)
            text, n = re.subn(pattern, new, text, count=count, flags=re.M)
            if n < 1:
                raise AssertionError(f'results self-test: nothing to plant in {path}')
            with open(path, 'w', encoding='utf-8') as f:
                f.write(text)

        def expect(label, results, md, *found, harness=prov['harness']):
            nonlocal caught
            problems, _ = check_results(results, md, harness)
            if not found and problems:
                raise AssertionError(f'results self-test: {label} refused: {problems}')
            for text in found:
                if not any(text in p for p in problems):
                    raise AssertionError(f'results self-test: {label} escaped: no problem says '
                                         f'{text!r} in {problems}')
            caught += bool(found)

        results, md = fresh()
        expect('results as --write writes them', results, md)

        # The harness changed: computed as provenance() computes it, over a copy of its files.
        harness = os.path.join(tmp, 'harness')
        os.makedirs(harness)
        for f in HARNESS:
            shutil.copyfile(os.path.join(HERE, f), os.path.join(harness, f))
        if harness_hash(harness) != harness_hash():
            raise AssertionError('results self-test: a copy of the harness hashes otherwise')
        with open(os.path.join(harness, 'run.py'), 'a') as f:
            f.write('\n')
        changed = harness_hash(harness)
        if changed == harness_hash():
            raise AssertionError('results self-test: a changed harness file leaves its hash')
        expect('a changed harness', results, md,
               *[f'{n} names harness {prov["harness"][:12]}' for n in sorted(written())],
               harness=changed)

        results, md = fresh()
        edit(os.path.join(results, runs[0]), rf'^(# {HARNESS_LINE}: )\S+', r'\g<1>' + '0' * 64)
        expect('a changed harness line', results, md,
               f'{runs[0]} names harness 000000000000', 'the results name 2 harnesses')

        results, md = fresh()
        edit(os.path.join(results, runs[0]), rf'^(# {HARNESS_LINE}: .*\n)', r'\1\1')
        expect('a harness line twice', results, md, f'{runs[0]} names its harness 2 times')

        results, md = fresh()
        edit(os.path.join(results, runs[1]), rf'^(# {HARNESS_LINE}: )(\S+)',
             lambda m: m.group(1) + m.group(2).upper())
        expect('a harness in capitals', results, md, f'{runs[1]} names no harness')

        results, md = fresh()
        os.remove(os.path.join(results, runs[1]))
        expect('a missing file', results, md, f'{runs[1]} is missing')

        results, md = fresh()
        for name in ('stray.txt', 'stray\x1b[2J.txt'):
            with open(os.path.join(results, name), 'w') as f:
                f.write('# commit: none\n')
        expect('a stray file', results, md, 'stray.txt is not a file --write writes',
               "'stray\\x1b[2J.txt' is not a file --write writes")

        results, md = fresh()
        os.rename(os.path.join(results, runs[2]), os.path.join(tmp, 'elsewhere.txt'))
        os.symlink(os.path.join(tmp, 'elsewhere.txt'), os.path.join(results, runs[2]))
        expect('a symbolic link', results, md, f'{runs[2]} is a symbolic link')

        results, md = fresh()
        os.remove(os.path.join(results, SUMMARY))
        os.makedirs(os.path.join(results, SUMMARY))
        expect('a folder for a file', results, md, f'{SUMMARY} is not a regular file')

        # A file that does not read: open refuses it, as it refuses a file with no read
        # permission to anyone but root, so that the plant holds whoever runs the check.
        real_open = open
        for name in (runs[3], 'MODEL.md'):
            results, md = fresh()
            locked = md if name == 'MODEL.md' else os.path.join(results, name)

            def refusing(path, *args, **kwargs):
                if path == locked:
                    raise PermissionError(13, 'Permission denied', path)
                return real_open(path, *args, **kwargs)
            with mock.patch('builtins.open', refusing):
                expect(f'{name} that does not read', results, md, f'{name} does not read')

        results, md = fresh()
        edit(os.path.join(results, runs[2]), r'\A(?:# .*\n)+', '')
        expect('a file with no header', results, md,
               f'{runs[2]} names no commit', f'{runs[2]} names no harness')

        results, md = fresh()
        edit(os.path.join(results, runs[3]), r'^(# commit: )[0-9a-f]+', r'\g<1>' + '1' * 40)
        expect('a changed commit line', results, md, 'the results name 2 commits')

        for key, label in (('python', 'Python'), ('date', 'date')):
            results, md = fresh()
            edit(os.path.join(results, SUMMARY), rf'^# {key}: .*\n', '')
            expect(f'summary.txt with no {label}', results, md, f'{SUMMARY} names no {label}')

        results, md = fresh()
        edit(os.path.join(results, SUMMARY), r'^(# date: .*\n)', r'\1\1')
        expect('summary.txt with its date twice', results, md,
               f'{SUMMARY} names its date 2 times')

        for state in ('harness files differ from this commit', 'state unknown'):
            results, md = fresh()
            for name in written():
                edit(os.path.join(results, name), re.escape(f'({COMMITTED})'), f'({state})')
            expect(f'a run that read other harness files ({state})', results, md,
                   *[f'{n} names commit aaaaaaaaaaaa without' for n in sorted(written())])

        results, md = fresh()
        edit(md, '^(' + re.escape(COUNTS_FROM) + ')[^`]*', r'\g<1>' + 'f' * 12)
        expect("another commit in MODEL.md's counts", results, md,
               "counts name commit ffffffffffff")

        results, md = fresh()
        edit(md, '^(' + re.escape(COUNTS_FROM) + ')[^`]*', r'\g<1>unknown')
        expect("no commit in MODEL.md's counts", results, md, "counts name no commit")

        results, md = fresh()
        with open(md, 'a', encoding='utf-8') as f:
            f.write(PAGE)
        expect('two counts blocks in MODEL.md', results, md, 'has 2 counts blocks')

        results, md = fresh()
        os.rename(md, md + '.real')
        os.symlink(md + '.real', md)
        expect('MODEL.md a symbolic link', results, md, 'MODEL.md is not a regular file')

        results, md = fresh()
        edit(md, r'^(In the plane: \*\*)[\d,]+', r'\g<1>1')
        expect("MODEL.md's total edited", results, md,
               "MODEL.md's counts are not what --write makes")

        results, md = fresh()
        edit(os.path.join(results, SUMMARY), r'^(configurations meeting .*: )[\d,]+', r'\g<1>1')
        expect("summary.txt's total edited", results, md,
               f"{SUMMARY} is not what --write makes")

        results, md = fresh()
        edit(os.path.join(results, 'search-seed1.txt'), rf'^({LAWS[0]} \d+ )\d+', r'\g<1>1')
        expect("a run's output edited, its summary not", results, md,
               f"{SUMMARY} is not what --write makes", "MODEL.md's counts are not what")

        # Output run.py refuses to write, whether or not its summary and counts change.
        law, prop = re.escape(LAWS[0]), next(iter(PROPERTIES))
        holds = next(n for n in LAWS if n not in EXPECTED_TO_FAIL)
        refused = "is what run.py refuses to write: "
        plants = [
            ('a counterexample in the plane, its hits unchanged', 'search-seed1.txt',
             rf'^({law} \d+ \d+) 0$', r'\1 1', f'search-seed1: a counterexample to {LAWS[0]} '),
            ('a row twice, its hits unchanged', 'search-seed2.txt', rf'^({law} .*\n)', r'\1\1',
             f'search-seed2 reported {LAWS[0]} twice'),
            ('a row missing', 'search-seed3.txt', rf'^{law} .*\n', '',
             f'search-seed3 reported {len(LAWS) - 1} laws, not {len(LAWS)}'),
            ('a derived property missing', 'exhaustive.txt', rf'^{re.escape(prop)} .*\n', '',
             f'exhaustive did not report derived property {prop}'),
            ('output that stops short', 'structured.txt',
             rf'^{re.escape(LAST_LINE["structured"])}.*\n', '',
             'structured stopped before its last line'),
            ('a mutation not caught', 'mutations.txt', r'^15/15', '14/15',
             'not every mutation was caught'),
            ('a grid failure', 'grid_check.txt', r'^failures 0', 'failures 1',
             'grid_check found a failure'),
            ('an angle failure', 'angle_check.txt', r'grid failures: 0 ', 'grid failures: 1 ',
             'angle_check found a failure'),
            ('a counterexample in the hyperbolic plane', 'hyperbolic.txt',
             rf'^({re.escape(holds)} \d+ \d+) 0$', r'\1 1',
             f'hyperbolic: a counterexample to {holds}'),
            ('no hyperbolic self-test', 'hyperbolic.txt', r'^self-test:.*\n', '',
             "the hyperbolic model's self-test did not pass"),
        ] + [(f'{n} holding in the hyperbolic plane', 'hyperbolic.txt',
              rf'^({re.escape(n)} \d+ \d+) \d+$', r'\1 0',
              f'the hyperbolic run found no counterexample to {n}')
             for n in sorted(EXPECTED_TO_FAIL)]
        for label, name, pattern, new, says in plants:
            results, md = fresh()
            edit(os.path.join(results, name), pattern, new)
            expect(label, results, md, refused + says)
    print(f'results self-test: {caught} planted faults caught; results as --write writes them '
          'pass')


def main():
    if sys.argv[1:]:
        sys.exit(__doc__)
    self_test()
    now = harness_hash()
    problems, commits = check_results(harness=now)
    if not problems:
        print(f'results: the {len(written())} files of tests/model/results/ name commit '
              f'{commits[0][:12]}, its harness files as committed, and the harness as it '
              f"hashes now ({now[:12]}...); MODEL.md's counts name the same commit; and they "
              "and summary.txt are what --write makes of the runs' output")
        return
    print("results: tests/model/results/ and the counts in MODEL.md are not the present "
          "harness's:")
    for p in problems:
        print('  ' + p)
    if len(commits) == 1:   # which files of the harness changed, when git has that commit
        changed = git('diff', '--name-only', commits[0], '--',
                      *[f'tests/model/{f}' for f in HARNESS])
        if changed:
            print(f'  harness files changed since {commits[0][:12]}: '
                  + ', '.join(changed.split()))
    print('Commit the change, run `python3 -I tests/model/run.py --full --write` on it, and '
          'commit what it writes, in the same pull request (docs/WORKFLOW.md, section 8).')
    sys.exit(1)


if __name__ == '__main__':
    main()
