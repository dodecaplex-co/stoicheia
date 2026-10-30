"""Run the model evidence for the axioms and retained derived properties.

    python3 -I tests/model/run.py --fast           # CI: well under two minutes
    python3 -I tests/model/run.py --full [--write] # about eight minutes
    python3 -I tests/model/run.py --ties           # the ties to the Lean alone

Two checks tie the model to the Lean before anything runs:
* laws.toml names a law for each axiom: exactly the axioms of Certificate/axioms.lock
  and of facts.json's `axiom_modules` (and its `axiom_types`, once that field exists),
  in both directions; and search.py and hyperbolic.py each implement exactly the laws
  it names, each once;
* lock.sha256 holds the sha256 of Certificate/axioms.lock, so that a change to any
  axiom's statement stops this run until someone revisits the model (MODEL.md,
  "Changing the axioms") and updates the hash.

--fast runs the counterexample search at 2,000 samples per axiom (seed 1), a reduced
structured run (5,000 per axiom, seed 11), all 15 mutations, the two independent grid and
angle checks, and the hyperbolic model at 300 per axiom (seed 1).

--full runs the search at 20,000 per axiom with seeds 1, 2 and 3, the exhaustive
enumeration, the structured run at 100,000 per axiom (seed 11), the mutations, both
independent checks, and the hyperbolic model at 20,000 per axiom (seed 1).  With --write
it first copies the files of HARNESS as the commit checked out has them, out of git's
objects, into a private folder, checks that they hash as the files checked out do, and
runs again from that copy, so that every module the run imports and every harness it runs
is that commit's, whatever the checkout does meanwhile. It writes nothing unless the
harness files are as committed when it begins, and the commit, their state and their hash
are the same when it ends; stopped by SIGTERM, SIGHUP or SIGINT while it runs or
publishes, it stops the run from the copy, rolls any publication back, removes the copy
and writes nothing. Then it saves each harness's output in results/, under a header naming
the commit, the harness's hash, the seeds and the Python; writes the axiom-by-axiom table
to results/summary.txt; and brings the counts in MODEL.md up to date.
results_check.py, beside this file but not one of HARNESS, holds what --write wrote to the
harness as it hashes now, and to what `judge` accepts (docs/WORKFLOW.md, section 8).

The run passes when every harness runs to its last line, no harness finds a counterexample
in the plane or reports a law or derived property twice, every mutation is caught,
every axiom's hypotheses are met somewhere, and every retained derived property is
reported and exercised by each exhaustive or structured run. In the hyperbolic plane
every axiom holds except those laws.toml says must fail there (Postulate 5), which must fail.
Derived-property totals are reported separately. While a property is still an axiom,
its unchanged predicate also supplies evidence that the axiom's hypotheses were met.
"""
import datetime
import hashlib
import io
import json
import os
import platform
import re
import signal
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SNAPSHOT = 'MODEL_HARNESS_SNAPSHOT'   # set for a run from a copy: the checkout, the provenance
FROM_SNAPSHOT = (json.loads(os.environ.pop(SNAPSHOT))
                 if __name__ == '__main__' and SNAPSHOT in os.environ else None)
ROOT = FROM_SNAPSHOT['root'] if FROM_SNAPSHOT else os.path.dirname(os.path.dirname(HERE))
CHECKOUT = os.path.join(ROOT, 'tests', 'model')   # HERE, unless this run is from a copy
RESULTS = os.path.join(CHECKOUT, 'results')
LOCK = os.path.join(ROOT, 'Certificate', 'axioms.lock')
LOCK_HASH = os.path.join(CHECKOUT, 'lock.sha256')
MODEL_MD = os.path.join(CHECKOUT, 'MODEL.md')
HARNESS = ['model.py', 'search.py', 'derived.py', 'exhaustive.py', 'structured.py', 'mutations.py',
           'grid_check.py', 'angle_check.py', 'hyperbolic.py', 'run.py', 'laws.toml']
PLACEHOLDER = 'TODO'
SUMMARY = 'summary.txt'
COUNTS = re.compile(r'(<!-- counts:begin -->\n).*?(\n<!-- counts:end -->)', re.S)   # in MODEL.md
COUNTS_FROM = 'Counts from `run.py --full --write` at commit `'   # the counts' first words
HARNESS_LINE = 'harness sha256'   # a run's header names its harness so; the summary, `harness`
COMMITTED = 'harness files as committed'   # a commit's state, when the run read its harness


def arguments(argv):
    args = set(argv)
    if args != {'--ties'} and (not args or not args <= {'--fast', '--full', '--write'}
                               or ('--fast' in args) == ('--full' in args)
                               or ('--write' in args and '--full' not in args)):
        sys.exit(__doc__)
    return args


def git(*args):
    try:
        p = subprocess.run(['git', *args], capture_output=True, text=True, cwd=ROOT)
        return p.stdout.strip() if p.returncode == 0 else None
    except OSError:
        return None


def harness_hash(here=HERE):
    """the sha256 of the harness: each file of HARNESS, in order, by its name and its bytes.
    The results name it (provenance), and results_check.py compares it with theirs."""
    h = hashlib.sha256()
    for f in HARNESS:
        with open(os.path.join(here, f), 'rb') as fh:
            h.update(f.encode() + b'\0' + fh.read())
    return h.hexdigest()


def provenance():
    sha = git('rev-parse', 'HEAD') or 'unknown'
    changed = git('status', '--porcelain', '--', *[f'tests/model/{f}' for f in HARNESS])
    state = (COMMITTED if changed == '' else
             'harness files differ from this commit' if changed else 'state unknown')
    py = f'{platform.python_version()} ({platform.python_implementation()}, {platform.system()} {platform.machine()})'
    return dict(commit=f'{sha} ({state})', harness=harness_hash(CHECKOUT), python=py,
                date=datetime.date.today().isoformat())


def provenance_signature(prov):
    """the commit, harness state and harness hash that decide whether --write may write"""
    match = re.fullmatch(r'([0-9a-f]{40}) \(([^()]*)\)', prov['commit'])
    return (match.group(1), match.group(2), prov['harness']) if match else None


def committed_file(commit, name):
    """a file of HARNESS as `commit` has it, out of git's objects, or None"""
    try:
        p = subprocess.run(['git', 'cat-file', 'blob', f'{commit}:tests/model/{name}'],
                           capture_output=True, cwd=ROOT)
    except OSError:
        return None
    return p.stdout if p.returncode == 0 else None


def stop_as_exit():
    """SIGTERM and SIGHUP end this process as sys.exit does, so that its temporary folder
    is removed and the run it waits on is stopped"""
    for name in ('SIGTERM', 'SIGHUP'):
        if hasattr(signal, name):
            signal.signal(getattr(signal, name), lambda n, _: sys.exit(128 + n))


def run_from_snapshot(argv):
    """--write: run this file again, with `argv`, from a copy of the harness as the commit
    checked out has it, made in a private folder out of git's objects, once it hashes as the
    harness checked out does; the run's exit status"""
    stop_as_exit()
    prov = provenance()
    signature = provenance_signature(prov)
    if signature is None or signature[1] != COMMITTED:
        sys.exit("the model harness is not a commit's committed files, so nothing is written")
    commit = signature[0]
    with tempfile.TemporaryDirectory(prefix='model-harness-') as snap:
        for name in HARNESS:
            data = committed_file(commit, name)
            if data is None:
                sys.exit(f'git has no tests/model/{name} at {commit[:12]}, so nothing is written')
            with open(os.path.join(snap, name), 'xb') as f:
                f.write(data)
        if harness_hash(snap) != prov['harness']:
            sys.exit(f'the harness as {commit[:12]} has it does not hash as the harness checked '
                     'out does, so nothing is written')
        print(f'running the harness as {commit[:12]} has it, from a copy out of git', flush=True)
        env = dict(os.environ, **{SNAPSHOT: json.dumps({'root': ROOT, 'provenance': prov})})
        with subprocess.Popen([sys.executable, '-I', os.path.join(snap, 'run.py'), *argv],
                              env=env) as child:
            try:
                return child.wait()
            except BaseException:
                child.terminate()
                child.wait()
                raise


def bootstrap(argv):
    args = arguments(argv)
    return run_from_snapshot(argv) if '--write' in args and FROM_SNAPSHOT is None else None


if __name__ == '__main__':
    bootstrap_status = bootstrap(sys.argv[1:])
    if bootstrap_status is not None:
        sys.exit(bootstrap_status)


sys.path.insert(0, HERE)
_argv, sys.argv = sys.argv, sys.argv[:1]   # the harness modules read sys.argv when imported
import search  # noqa: E402
import hyperbolic  # noqa: E402
from derived import PROPERTIES  # noqa: E402
from model import read_laws  # noqa: E402
sys.argv = _argv

try:
    LAW_OF, EXPECTED_TO_FAIL = read_laws()   # {axiom: its law}; the laws that must fail
    LAWS_PROBLEM = None
except ValueError as e:
    LAW_OF, EXPECTED_TO_FAIL, LAWS_PROBLEM = {}, set(), str(e)
AXIOM_OF = {law: axiom for axiom, law in LAW_OF.items()}
LAWS = [name for name, _, _ in search.AXIOMS]   # in search.py's order, for the tables


def lean_name(law):
    """a law's name in the harness -> its axiom's name, as the lock and facts.json have it"""
    return AXIOM_OF.get(law, law)


# ---------------------------------------------------------------- the ties to the Lean

def locked_axioms():
    """the names in Certificate/axioms.lock's [axioms] table, or None if it has none"""
    import tomllib
    try:
        with open(LOCK, 'rb') as f:
            table = tomllib.load(f).get('axioms')
    except (OSError, tomllib.TOMLDecodeError):
        return None
    return set(table) if isinstance(table, dict) else None


def check_names():
    """(the number of axioms in facts.json, the problems): laws.toml names exactly the
    axioms of the lock and of facts.json, and each harness implements exactly its laws"""
    with open(os.path.join(ROOT, 'facts.json')) as f:
        facts = json.load(f)
    lean = set(facts['axiom_modules'])
    if LAWS_PROBLEM:
        return len(lean), [LAWS_PROBLEM]
    problems, named = [], set(LAW_OF)
    others = [("facts.json's axiom_modules", lean)]
    if 'axiom_types' in facts:
        others.append(("facts.json's axiom_types", set(facts['axiom_types'])))
    locked = locked_axioms()
    if locked is not None:
        others.insert(0, ('Certificate/axioms.lock', locked))
    elif os.path.exists(LOCK):
        problems.append('Certificate/axioms.lock has no [axioms] table that reads')
    for label, names in others:
        for n in sorted(names - named):
            problems.append(f'{n}, an axiom in {label}, has no law in tests/model/laws.toml')
        for n in sorted(named - names):
            problems.append(f'{n} has a law in tests/model/laws.toml, but is not an axiom in {label}')
    laws = set(AXIOM_OF)
    for label, names in (('search.py', LAWS), ('hyperbolic.py', [n for n, *_ in hyperbolic.AXIOMS])):
        if len(names) != len(set(names)):
            problems.append(f'{label} implements a law twice')
        for n in sorted(laws - set(names)):
            problems.append(f'{label} does not implement {n}, the law laws.toml names for {AXIOM_OF[n]}')
        for n in sorted(set(names) - laws):
            problems.append(f'{label} implements {n}, a law laws.toml does not name')
    return len(lean), problems


def read_lock_hash():
    with open(LOCK_HASH) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith('#'):
                return line.split()[0]
    return None


def check_lock():
    """(ok, message)"""
    pinned = read_lock_hash()
    have = os.path.exists(LOCK)
    actual = hashlib.sha256(open(LOCK, 'rb').read()).hexdigest() if have else None
    if pinned in (None, PLACEHOLDER):
        if not have:
            return True, ('pending: Certificate/axioms.lock does not exist yet, and lock.sha256 '
                          'still holds its TODO')
        return False, ('Certificate/axioms.lock now exists: write its hash into tests/model/lock.sha256 '
                       f'in place of the TODO, after checking MODEL.md against it:\n    {actual}  '
                       'Certificate/axioms.lock')
    if not have:
        return False, 'lock.sha256 pins Certificate/axioms.lock, but the lock is missing'
    if actual != pinned:
        return False, ('Certificate/axioms.lock has changed since the model was last checked against '
                       'it. Revisit the model for the changed axioms, as tests/model/MODEL.md, '
                       '"Changing the axioms", says (laws.toml, the laws in search.py and '
                       'hyperbolic.py, and MODEL.md itself), then update lock.sha256 to\n'
                       f'    {actual}  Certificate/axioms.lock')
    return True, f'Certificate/axioms.lock matches lock.sha256 ({actual[:16]}...)'


# ---------------------------------------------------------------- running the harnesses

def parse_results(out, axiom_names):
    """Read axiom and derived-property rows without relying on registry overlap."""
    laws, properties, twice = {}, {}, set()
    for line in out.splitlines():
        m = re.match(r'^(\S+)\s+(\d+)\s+(\d+)\s+(\d+)\b', line)
        if not m:
            continue
        name = m.group(1)
        if name.startswith('derived.'):
            rows = properties
        elif name in axiom_names:
            rows = laws
        else:
            continue
        if name in rows:
            twice.add(name)
        rows[name] = tuple(int(m.group(i)) for i in (2, 3, 4))
    return laws, properties, twice


class Run:
    def __init__(self, key, script, args=(), env=None, seeds='', what=''):
        self.key, self.script, self.args, self.env = key, script, [str(a) for a in args], env
        self.seeds, self.what = seeds, what

    def go(self):
        cmd = [sys.executable, '-I', os.path.join(HERE, self.script), *self.args]
        env = dict(os.environ, **(self.env or {}))
        t = time.time()
        p = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT, env=env)
        self.seconds = time.time() - t
        self.code, self.out, self.err = p.returncode, p.stdout, p.stderr
        self.laws, self.derived, self.twice = parse_results(self.out, search_names)
        envs = ' '.join(f'{k}={v}' for k, v in (self.env or {}).items())
        self.command = ' '.join(filter(None, [envs, 'python3 -I', 'tests/model/' + self.script, *self.args]))
        return self


search_names = set(LAWS)


def plan(full):
    if full:
        runs = [Run(f'search-seed{s}', 'search.py', [20000, s], seeds=str(s),
                    what='random search, 20,000 samples per axiom') for s in (1, 2, 3)]
        runs += [Run('exhaustive', 'exhaustive.py', seeds='7 (for derived.area_congruent\'s isometries)',
                     what='every configuration on small grids'),
                 Run('structured', 'structured.py', [100000, 11], seeds='11',
                     what='structured search, 100,000 samples per axiom or derived property')]
    else:
        runs = [Run('search-seed1', 'search.py', [2000, 1], seeds='1', what='random search, 2,000 samples per axiom'),
                Run('structured', 'structured.py', [5000, 11], seeds='11',
                    what='structured search, 5,000 samples per axiom or derived property')]
    runs += [Run('mutations', 'mutations.py', what='15 deliberately weakened statements'),
             Run('grid_check', 'grid_check.py', what='a second, independent exact grid check'),
             Run('angle_check', 'angle_check.py', seeds='1', what='a second, independent angle and area check'),
             Run('hyperbolic', 'hyperbolic.py', [20000 if full else 300, 1], seeds='1',
                 what=f'the hyperbolic plane, {"20,000" if full else "300"} samples per axiom')]
    return runs


EUCLIDEAN = ('search', 'exhaustive', 'structured')
LAST_LINE = {'search': 'axioms checked:', 'exhaustive': 'exhaustive axioms run:',
             'structured': 'structured total counterexamples:', 'hyperbolic': 'axioms checked:'}


def judge(runs):
    """the list of failures"""
    bad = []
    for r in runs:
        if r.code != 0:
            bad.append(f'{r.key} exited with status {r.code}:\n{r.err.strip()[-2000:]}')
        for law in sorted(r.twice):
            bad.append(f'{r.key} reported {law} twice')
        last = next((v for k, v in LAST_LINE.items() if r.key.startswith(k)), None)
        if last and not re.search('^' + re.escape(last), r.out, re.M):
            bad.append(f'{r.key} stopped before its last line')
        expected = set(PROPERTIES) if r.key in ('exhaustive', 'structured') else set()
        for name in sorted(expected - set(r.derived)):
            bad.append(f'{r.key} did not report derived property {name}')
        for name in sorted(set(r.derived) - expected):
            bad.append(f'{r.key} reported unexpected derived property {name}')
        for name, (_, hits, cex) in r.derived.items():
            if not hits:
                bad.append(f'{r.key}: the hypotheses of {name} were never met')
            if cex:
                bad.append(f'{r.key}: a counterexample to {name} in the plane')
    plane = [r for r in runs if r.key.startswith(EUCLIDEAN)]
    for r in plane:
        for law, (_, _, cex) in r.laws.items():
            if cex:
                bad.append(f'{r.key}: a counterexample to {law} in the plane')
        if r.key.startswith('search') and len(r.laws) != len(LAWS):
            bad.append(f'{r.key} reported {len(r.laws)} laws, not {len(LAWS)}')
    for law in LAWS:
        if not any(r.laws.get(law, (0, 0, 0))[1]
                   or r.derived.get('derived.' + law, (0, 0, 0))[1] for r in plane):
            bad.append(f'no harness in this run met the hypotheses of {law}')
    by = {r.key: r for r in runs}
    m = re.search(r'^(\d+)/(\d+) mutations caught', by['mutations'].out, re.M)
    if not m or m.group(1) != m.group(2) or m.group(2) != '15':
        bad.append('not every mutation was caught')
    m = re.search(r'^failures (\d+)', by['grid_check'].out, re.M)
    if not m or m.group(1) != '0':
        bad.append('grid_check found a failure')
    if not re.search(r'triple incidence grid failures: 0 ', by['angle_check'].out) or \
            'float failures: {}' not in by['angle_check'].out:
        bad.append('angle_check found a failure')
    h = by['hyperbolic']
    if 'self-test:' not in h.out:
        bad.append("the hyperbolic model's self-test did not pass")
    for law in LAWS:
        tried, hits, cex = h.laws.get(law, (0, 0, 0))
        if law in EXPECTED_TO_FAIL:
            if not cex:
                bad.append(f'the hyperbolic run found no counterexample to {law}, which must fail there')
        elif cex:
            bad.append(f'hyperbolic: a counterexample to {law}')
        if not hits:
            bad.append(f'hyperbolic: the hypotheses of {law} were never met')
    return bad


def self_test():
    """Plant reporting faults, including after the axiom names have disappeared."""
    from types import SimpleNamespace

    def fixture(key, out):
        laws, properties, twice = parse_results(out, search_names)
        return SimpleNamespace(key=key, out=out, err='', code=0,
                               laws=laws, derived=properties, twice=twice)

    # The re-keyed checks still witness coverage while these declarations are axioms.
    axioms = '\n'.join(f'{name} 1 {int("derived." + name not in PROPERTIES)} 0' for name in LAWS)
    hyp = '\n'.join(f'{name} 1 1 {int(name in EXPECTED_TO_FAIL)}' for name in LAWS)
    properties = '\n'.join(f'{name} 1 1 0' for name in PROPERTIES)
    laws, rows, twice = parse_results(properties, set())
    if laws or set(rows) != set(PROPERTIES) or twice:
        raise AssertionError('derived rows depend on the axiom registry')
    base = [fixture('search-seed1', axioms + '\naxioms checked:'),
            fixture('mutations', '15/15 mutations caught'),
            fixture('grid_check', 'failures 0'),
            fixture('angle_check', 'triple incidence grid failures: 0 ; float failures: {}'),
            fixture('hyperbolic', hyp + '\nself-test:\naxioms checked:')]
    checked = 0
    for key in ('exhaustive', 'structured'):
        good = properties + '\n' + LAST_LINE[key]
        runs = base + [fixture(key, good)]
        if judge(runs):
            raise AssertionError(f'{key}: valid derived-property report refused')
        faults = [('completion', properties, 'stopped before its last line')]
        for name in PROPERTIES:
            row = f'{name} 1 1 0'
            faults += [
                ('missing', good.replace(row, ''), f'did not report derived property {name}'),
                ('duplicate', good + '\n' + row, f'reported {name} twice'),
                ('unexercised', good.replace(row, f'{name} 1 0 0'), f'hypotheses of {name} were never met'),
                ('counterexample', good.replace(row, f'{name} 1 1 1'), f'counterexample to {name} in the plane'),
            ]
        faults.append(('unknown', good + '\nderived.unknown 1 1 0',
                       'reported unexpected derived property derived.unknown'))
        for kind, out, message in faults:
            bad = judge(base + [fixture(key, out)])
            if not any(message in problem for problem in bad):
                raise AssertionError(f'{key}: {kind} reporting fault escaped')
            checked += 1
        failed = fixture(key, good)
        failed.code = 1
        if not any('exited with status 1' in p for p in judge(base + [failed])):
            raise AssertionError(f'{key}: failed process accepted')
        checked += 1
    print(f'derived-property self-test: {checked} reporting faults caught; registry-independent parsing passed')


# ---------------------------------------------------------------- writing the results


def short_commit(commit):
    """the commit as MODEL.md's counts name it"""
    return commit.split()[0][:12]


def result_file(r):
    """the file in results/ that --write writes a run's output to"""
    return r.key + '.txt'


def written():
    """the files --write writes in results/: one for each run of the full plan, and the summary"""
    return {result_file(r) for r in plan(True)} | {SUMMARY}


def header(r, prov):
    lines = [f'{r.key}: {r.what}',
             f'command: {r.command}',
             f'seeds: {r.seeds or "none (deterministic)"}',
             f'commit: {prov["commit"]}',
             f'{HARNESS_LINE}: {prov["harness"]}',
             f'python: {prov["python"]}',
             f'date: {prov["date"]}',
             f'time: {r.seconds:.1f} s']
    return ''.join(f'# {x}\n' for x in lines) + '\n'


def totals(runs, derived=False):
    plane = [r for r in runs if r.key.startswith(EUCLIDEAN)]
    met = {r.key: sum(h for _, h, _ in (r.derived if derived else r.laws).values()) for r in plane}
    return met, sum(met.values())


def derived_table(runs):
    """Separate evidence for the retained properties, also when writing results."""
    by = {r.key: r for r in runs}
    rows = ['| Derived property | Exhaustive | Structured |', '|---|--:|--:|']
    for name in PROPERTIES:
        cells = [f'{by[key].derived[name][1]:,}' if key in by and name in by[key].derived else '·'
                 for key in ('exhaustive', 'structured')]
        rows.append('| `' + name + '` | ' + ' | '.join(cells) + ' |')
    return '\n'.join(rows)


def law_table(runs, markdown):
    plane_search = [r for r in runs if r.key.startswith('search')]
    by = {r.key: r for r in runs}
    rows = []
    for law in LAWS:
        s = sum(r.laws.get(law, (0, 0, 0))[1] for r in plane_search)
        e = by['exhaustive'].laws.get(law, (0, 0, 0))[1] if 'exhaustive' in by and law in by['exhaustive'].laws else None
        st = by['structured'].laws.get(law, (0, 0, 0))[1] if law in by['structured'].laws else None
        _, hh, hc = by['hyperbolic'].laws.get(law, (0, 0, 0))
        hyp = f'{hh:,} met, {hc:,} fail' if law in EXPECTED_TO_FAIL else f'{hh:,}'
        rows.append((f'`{lean_name(law)}`' if markdown else lean_name(law), f'{s:,}',
                     '·' if e is None else f'{e:,}', '·' if st is None else f'{st:,}', hyp))
    head = ('Axiom', 'Search, seeds 1-3', 'Exhaustive', 'Structured', 'Hyperbolic')
    if markdown:
        out = ['| ' + ' | '.join(head) + ' |', '|---|--:|--:|--:|--:|']
        out += ['| ' + ' | '.join(r) + ' |' for r in rows]
    else:
        w = [max(len(x[i]) for x in rows + [head]) for i in range(5)]
        out = ['  '.join(x.ljust(w[i]) if i == 0 else x.rjust(w[i]) for i, x in enumerate(row))
               for row in [head] + rows]
    return '\n'.join(out)


def counts_block(runs, prov):
    met, total = totals(runs)
    _, derived_total = totals(runs, derived=True)
    h = {r.key: r for r in runs}['hyperbolic']
    hyp_met = sum(x[1] for x in h.laws.values())
    fails = '; '.join(f'`{lean_name(law)}` failed {h.laws.get(law, (0, 0, 0))[2]:,} times'
                      for law in sorted(EXPECTED_TO_FAIL))
    return '\n'.join([
        f'{COUNTS_FROM}{short_commit(prov["commit"])}`, '
        f'{prov["date"]}, Python {platform.python_version()}. Each number is how many configurations '
        'met the axiom\'s hypotheses (for the search, over the three seeds); none of them was a '
        'counterexample. A dot means that harness does not enumerate the axiom.',
        '',
        f'In the plane: **{total:,}** configurations met an axiom\'s hypotheses '
        f'({sum(v for k, v in met.items() if k.startswith("search")):,} in the search, '
        f'{met.get("exhaustive", 0):,} exhaustive, {met.get("structured", 0):,} structured), '
        'with no counterexample, and all 15 mutations were caught. In the hyperbolic plane: '
        f'{hyp_met:,} configurations met an axiom\'s hypotheses; '
        + (f'{fails} and every other axiom held.' if fails else 'every axiom held.'),
        '',
        law_table(runs, markdown=True),
        '',
        f'Separately, **{derived_total:,}** configurations met a retained derived property\'s '
        'hypotheses, with no counterexample. These do not count toward the axiom totals.',
        '',
        derived_table(runs)])


def publish(outputs, expected_signature=None):
    """Replace every `(path, text)` as one publication, restoring every prior directory entry
    if publication is interrupted. Destination symbolic links are replaced, not followed.
    SIGTERM, SIGHUP and SIGINT are held back until every file is replaced or every file is
    back, so that no handler runs during a rollback, not even a second signal's: a Ctrl-C
    reaches both processes of a --write, and the one that made the copy then sends this
    one SIGTERM."""
    stages = []
    journal = []
    stops = {getattr(signal, name) for name in ('SIGTERM', 'SIGHUP', 'SIGINT')
             if hasattr(signal, name)}
    caller_mask = (signal.pthread_sigmask(signal.SIG_BLOCK, stops)
                   if stops and hasattr(signal, 'pthread_sigmask') else None)
    held = stops - set(caller_mask) if caller_mask is not None else set()

    def interrupted():
        return bool(held) and bool(signal.sigpending() & held)

    def remember(path):
        if not os.path.lexists(path):
            return None
        if os.path.islink(path):
            return ('link', os.readlink(path))
        if not os.path.isfile(path):
            raise OSError(f'{path} is not a regular file or symbolic link')
        details = os.stat(path, follow_symlinks=False)
        with open(path, 'rb') as f:
            return ('file', f.read(), details.st_mode & 0o7777,
                    details.st_atime_ns, details.st_mtime_ns)

    def remake(path, prior):
        if prior is None:
            return
        if prior[0] == 'link':
            os.symlink(prior[1], path)
            return
        with open(path, 'xb') as f:
            f.write(prior[1])
        os.chmod(path, prior[2])
        os.utime(path, ns=(prior[3], prior[4]))

    def restore():
        for path, backup, prior in reversed(journal):
            if os.path.lexists(path):
                os.unlink(path)
            if backup is not None and os.path.lexists(backup):
                os.replace(backup, path)
            else:
                remake(path, prior)

    def clean_stages():
        for _, new in stages:
            if os.path.lexists(new):
                os.unlink(new)

    try:
        try:
            for path, text in outputs:
                new = os.path.join(os.path.dirname(path),
                                   f'.{os.path.basename(path)}.{os.getpid()}.new')
                with open(new, 'x') as f:
                    stages.append((path, new))
                    f.write(text)
            for path, new in stages:
                if os.path.isdir(path) and not os.path.islink(path):
                    raise IsADirectoryError(path)
                prior = remember(path)
                backup = None
                if os.path.lexists(path):
                    backup = os.path.join(os.path.dirname(path),
                                          f'.{os.path.basename(path)}.{os.getpid()}.old')
                    if os.path.lexists(backup):
                        raise FileExistsError(backup)
                    os.replace(path, backup)
                journal.append((path, backup, prior))
                os.replace(new, path)
            if expected_signature is not None \
                    and provenance_signature(provenance()) != expected_signature:
                sys.exit('the model harness provenance changed while it ran, so nothing is '
                         'written')
            if interrupted():
                raise InterruptedError('publication interrupted')
            for _, backup, _ in journal:
                if backup is not None:
                    os.unlink(backup)
            clean_stages()
            if interrupted():
                raise InterruptedError('publication interrupted')
        except BaseException:
            restore()
            clean_stages()
            raise
    finally:
        if caller_mask is not None:
            signal.pthread_sigmask(signal.SIG_SETMASK, caller_mask)


def write(runs, prov, results=RESULTS, model_md=MODEL_MD, expected_signature=None):
    outputs = []
    for r in runs:
        outputs.append((os.path.join(results, result_file(r)), header(r, prov) + r.out))
    met, total = totals(runs)
    with io.StringIO() as f:
        f.write(''.join(f'# {k}: {v}\n' for k, v in prov.items()) + '\n')
        f.write(f'configurations meeting an axiom\'s hypotheses in the plane: {total:,}\n')
        for k, v in met.items():
            f.write(f'  {k}: {v:,}\n')
        f.write('counterexamples in the plane: 0; mutations caught: 15 of 15\n\n')
        f.write(law_table(runs, markdown=False) + '\n')
        derived_met, derived_total = totals(runs, derived=True)
        f.write(f'\nconfigurations meeting a derived property\'s hypotheses: {derived_total:,}\n')
        for k, v in derived_met.items():
            if v:
                f.write(f'  {k}: {v:,}\n')
        f.write(derived_table(runs) + '\n')
        outputs.append((os.path.join(results, SUMMARY), f.getvalue()))
    with open(model_md) as f:
        md = f.read()
    new, n = COUNTS.subn(lambda m: m.group(1) + counts_block(runs, prov) + m.group(2), md)
    if n != 1:
        sys.exit('MODEL.md has no counts block to update')
    outputs.append((model_md, new))
    made_results = not os.path.lexists(results)
    try:
        os.makedirs(results, exist_ok=True)
        publish(outputs, expected_signature)
    except BaseException:
        if made_results and os.path.isdir(results) and not os.listdir(results):
            os.rmdir(results)
        raise


# ---------------------------------------------------------------- main

def main():
    args = arguments(sys.argv[1:])
    full = '--full' in args
    self_test()
    n, problems = check_names()
    print(f'names: laws.toml names {len(LAW_OF)} laws; facts.json declares {n} axioms'
          + (' -- they agree, with the lock and the harness' if not problems else ''))
    ok, msg = check_lock()
    print('lock: ' + msg)
    if problems or not ok:
        for p in problems:
            print('  ' + p)
        sys.exit(1)
    if args == {'--ties'}:
        print('the ties to the Lean hold')
        return
    write_prov = None
    write_signature = None
    if '--write' in args:
        if os.path.realpath(HERE) == os.path.realpath(CHECKOUT):
            sys.exit(f'{SNAPSHOT} is set, but this run is not from a copy of the harness, so '
                     'nothing is written')
        stop_as_exit()
        write_prov = FROM_SNAPSHOT['provenance']
        write_signature = provenance_signature(write_prov)
        if write_signature is None or write_signature[1] != COMMITTED:
            sys.exit("the model harness is not a commit's committed files, so nothing is written")
        if harness_hash() != write_prov['harness']:
            sys.exit('this copy of the harness does not hash as its provenance says, so nothing '
                     'is written')
    runs = []
    for r in plan(full):
        print(f'  {r.key:14s} ...', end='', flush=True)
        r.go()
        runs.append(r)
        hits = sum(h for _, h, _ in r.laws.values())
        derived_hits = sum(h for _, h, _ in r.derived.values())
        print(f' {r.seconds:6.1f} s'
              + (f', {hits:,} configurations met an axiom hypothesis' if r.laws else '')
              + (f'; {derived_hits:,} met a derived-property hypothesis' if r.derived else ''))
    bad = judge(runs)
    met, total = totals(runs)
    print(f'plane: {total:,} configurations met an axiom\'s hypotheses; counterexamples: '
          f'{sum(c for r in runs if r.key.startswith(EUCLIDEAN) for *_, c in r.laws.values())}')
    _, derived_total = totals(runs, derived=True)
    print(f'derived properties: {derived_total:,} configurations met a hypothesis; counterexamples: '
          f'{sum(c for r in runs for *_, c in r.derived.values())}')
    print(derived_table(runs))
    h = {r.key: r for r in runs}['hyperbolic']
    failed = '; '.join(f'{law} failed {h.laws.get(law, (0, 0, 0))[2]:,} times'
                       for law in sorted(EXPECTED_TO_FAIL))
    print(f'hyperbolic: {failed} (as it must); counterexamples to the other axioms: '
          f'{sum(c for k, (_, _, c) in h.laws.items() if k not in EXPECTED_TO_FAIL)}')
    if bad:
        print('FAILED:')
        for b in bad:
            print('  ' + b)
        sys.exit(1)
    if '--write' in args:
        if provenance_signature(provenance()) != write_signature:
            sys.exit('the model harness provenance changed while it ran, so nothing is written')
        write(runs, write_prov, expected_signature=write_signature)
        print('wrote tests/model/results/ and the counts in MODEL.md')
    print('model evidence: all checks pass')


if __name__ == '__main__':
    main()
