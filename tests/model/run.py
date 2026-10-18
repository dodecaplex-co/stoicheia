"""Run the model evidence for the axioms.

    python3 -I tests/model/run.py --fast           # CI: well under two minutes
    python3 -I tests/model/run.py --full [--write] # about seven minutes
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
it saves each harness's output in results/, under a header naming the commit, the
seeds and the Python; writes the axiom-by-axiom table to results/summary.txt; and brings
the counts in MODEL.md up to date.

The run passes when no harness finds a counterexample in the plane or reports a law
twice, every mutation is caught, every axiom's hypotheses are met somewhere, and in the
hyperbolic plane every axiom holds except those laws.toml says must fail there (Postulate
5), which must fail.
"""
import datetime
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
RESULTS = os.path.join(HERE, 'results')
LOCK = os.path.join(ROOT, 'Certificate', 'axioms.lock')
LOCK_HASH = os.path.join(HERE, 'lock.sha256')
MODEL_MD = os.path.join(HERE, 'MODEL.md')
HARNESS = ['model.py', 'search.py', 'exhaustive.py', 'structured.py', 'mutations.py',
           'grid_check.py', 'angle_check.py', 'hyperbolic.py', 'run.py', 'laws.toml']
PLACEHOLDER = 'TODO'

sys.path.insert(0, HERE)
_argv, sys.argv = sys.argv, sys.argv[:1]   # the harness modules read sys.argv when imported
import search  # noqa: E402
import hyperbolic  # noqa: E402
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
        self.laws, self.twice = {}, set()
        for line in self.out.splitlines():
            m = re.match(r'^(\S+)\s+(\d+)\s+(\d+)\s+(\d+)\b', line)
            if m and m.group(1) in search_names:
                if m.group(1) in self.laws:
                    self.twice.add(m.group(1))
                self.laws[m.group(1)] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
        envs = ' '.join(f'{k}={v}' for k, v in (self.env or {}).items())
        self.command = ' '.join(filter(None, [envs, 'python3 -I', 'tests/model/' + self.script, *self.args]))
        return self


search_names = set(LAWS)


def plan(full):
    if full:
        runs = [Run(f'search-seed{s}', 'search.py', [20000, s], seeds=str(s),
                    what='random search, 20,000 samples per axiom') for s in (1, 2, 3)]
        runs += [Run('exhaustive', 'exhaustive.py', seeds='7 (for area_congruent\'s isometries)',
                     what='every configuration on small grids'),
                 Run('structured', 'structured.py', [100000, 11], seeds='11',
                     what='structured search, 100,000 samples per axiom')]
    else:
        runs = [Run('search-seed1', 'search.py', [2000, 1], seeds='1', what='random search, 2,000 samples per axiom'),
                Run('structured', 'structured.py', [5000, 11], seeds='11',
                    what='structured search, 5,000 samples per axiom')]
    runs += [Run('mutations', 'mutations.py', what='15 deliberately weakened axioms'),
             Run('grid_check', 'grid_check.py', what='a second, independent exact grid check'),
             Run('angle_check', 'angle_check.py', seeds='1', what='a second, independent angle and area check'),
             Run('hyperbolic', 'hyperbolic.py', [20000 if full else 300, 1], seeds='1',
                 what=f'the hyperbolic plane, {"20,000" if full else "300"} samples per axiom')]
    return runs


EUCLIDEAN = ('search', 'exhaustive', 'structured')


def judge(runs):
    """the list of failures"""
    bad = []
    for r in runs:
        if r.code != 0:
            bad.append(f'{r.key} exited with status {r.code}:\n{r.err.strip()[-2000:]}')
        for law in sorted(r.twice):
            bad.append(f'{r.key} reported {law} twice')
    plane = [r for r in runs if r.key.startswith(EUCLIDEAN)]
    for r in plane:
        for law, (_, _, cex) in r.laws.items():
            if cex:
                bad.append(f'{r.key}: a counterexample to {law} in the plane')
        if r.key.startswith('search') and len(r.laws) != len(LAWS):
            bad.append(f'{r.key} reported {len(r.laws)} laws, not {len(LAWS)}')
    for law in LAWS:
        if not any(r.laws.get(law, (0, 0, 0))[1] for r in plane):
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


# ---------------------------------------------------------------- writing the results

def git(*args):
    try:
        p = subprocess.run(['git', *args], capture_output=True, text=True, cwd=ROOT)
        return p.stdout.strip() if p.returncode == 0 else None
    except OSError:
        return None


def provenance():
    sha = git('rev-parse', 'HEAD') or 'unknown'
    changed = git('status', '--porcelain', '--', *[f'tests/model/{f}' for f in HARNESS])
    state = ('harness files as committed' if changed == '' else
             'harness files differ from this commit' if changed else 'state unknown')
    h = hashlib.sha256()
    for f in HARNESS:
        h.update(f.encode() + b'\0' + open(os.path.join(HERE, f), 'rb').read())
    py = f'{platform.python_version()} ({platform.python_implementation()}, {platform.system()} {platform.machine()})'
    return dict(commit=f'{sha} ({state})', harness=h.hexdigest(), python=py,
                date=datetime.date.today().isoformat())


def header(r, prov):
    lines = [f'{r.key}: {r.what}',
             f'command: {r.command}',
             f'seeds: {r.seeds or "none (deterministic)"}',
             f'commit: {prov["commit"]}',
             f'harness sha256: {prov["harness"]}',
             f'python: {prov["python"]}',
             f'date: {prov["date"]}',
             f'time: {r.seconds:.1f} s']
    return ''.join(f'# {x}\n' for x in lines) + '\n'


def totals(runs):
    plane = [r for r in runs if r.key.startswith(EUCLIDEAN)]
    met = {k: sum(h for _, h, _ in r.laws.values()) for k, r in ((r.key, r) for r in plane)}
    return met, sum(met.values())


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
    h = {r.key: r for r in runs}['hyperbolic']
    hyp_met = sum(x[1] for x in h.laws.values())
    p5 = h.laws['Postulate5'][2]
    return '\n'.join([
        f'Counts from `run.py --full --write` at commit `{prov["commit"].split()[0][:12]}`, '
        f'{prov["date"]}, Python {platform.python_version()}. Each number is how many configurations '
        'met the axiom\'s hypotheses (for the search, over the three seeds); none of them was a '
        'counterexample. A dot means that harness does not enumerate the axiom.',
        '',
        f'In the plane: **{total:,}** configurations met an axiom\'s hypotheses '
        f'({sum(v for k, v in met.items() if k.startswith("search")):,} in the search, '
        f'{met.get("exhaustive", 0):,} exhaustive, {met.get("structured", 0):,} structured), '
        'with no counterexample, and all 15 mutations were caught. In the hyperbolic plane: '
        f'{hyp_met:,} configurations met an axiom\'s hypotheses; Postulate 5 failed {p5:,} times and '
        'every other axiom held.',
        '',
        law_table(runs, markdown=True)])


def write(runs, prov):
    os.makedirs(RESULTS, exist_ok=True)
    for r in runs:
        with open(os.path.join(RESULTS, r.key + '.txt'), 'w') as f:
            f.write(header(r, prov) + r.out)
    met, total = totals(runs)
    with open(os.path.join(RESULTS, 'summary.txt'), 'w') as f:
        f.write(''.join(f'# {k}: {v}\n' for k, v in prov.items()) + '\n')
        f.write(f'configurations meeting an axiom\'s hypotheses in the plane: {total:,}\n')
        for k, v in met.items():
            f.write(f'  {k}: {v:,}\n')
        f.write('counterexamples in the plane: 0; mutations caught: 15 of 15\n\n')
        f.write(law_table(runs, markdown=False) + '\n')
    with open(MODEL_MD) as f:
        md = f.read()
    new, n = re.subn(r'(<!-- counts:begin -->\n).*?(\n<!-- counts:end -->)',
                     lambda m: m.group(1) + counts_block(runs, prov) + m.group(2), md, flags=re.S)
    if n != 1:
        sys.exit('MODEL.md has no counts block to update')
    with open(MODEL_MD, 'w') as f:
        f.write(new)


# ---------------------------------------------------------------- main

def main():
    args = set(sys.argv[1:])
    if args != {'--ties'} and (not args or not args <= {'--fast', '--full', '--write'}
                               or ('--fast' in args) == ('--full' in args)
                               or ('--write' in args and '--full' not in args)):
        sys.exit(__doc__)
    full = '--full' in args
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
    runs = []
    for r in plan(full):
        print(f'  {r.key:14s} ...', end='', flush=True)
        r.go()
        runs.append(r)
        hits = sum(h for _, h, _ in r.laws.values())
        print(f' {r.seconds:6.1f} s' + (f', {hits:,} configurations met a hypothesis' if r.laws else ''))
    bad = judge(runs)
    met, total = totals(runs)
    print(f'plane: {total:,} configurations met an axiom\'s hypotheses; counterexamples: '
          f'{sum(c for r in runs if r.key.startswith(EUCLIDEAN) for *_, c in r.laws.values())}')
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
        write(runs, provenance())
        print('wrote tests/model/results/ and the counts in MODEL.md')
    print('model evidence: all checks pass')


if __name__ == '__main__':
    main()
