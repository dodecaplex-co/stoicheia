"""Check that the model's committed results are the present harness's.

    python3 -I tests/model/results_check.py    # CI's `model` job, after run.py --fast

`run.py --full --write` heads each file it writes in results/ with the commit it ran at and
the sha256 of the harness (HARNESS in run.py), and names the same commit in the counts of
MODEL.md. This check runs no harness. It fails, naming each file, unless
* the files in results/ are exactly those --write writes, each a regular file;
* each names, once, a commit whose harness files its run read as committed, and the harness
  as it hashes now, and all name the same commit;
* MODEL.md has one block of counts, and it names that commit; and
* summary.txt and the counts in MODEL.md are what --write makes of the runs' output in
  results/.
So a change to any file of HARNESS fails it until `run.py --full --write` is run on the
change, committed, and what it writes is committed too (docs/WORKFLOW.md, section 8). It
reads what a run wrote, and cannot tell a header written by hand from a run's: the security
review, which every change under tests/ gets, reads the results' diff.

It is not a file of HARNESS, so a change to it alone needs no new run. Its self-test runs
first: it writes results as --write does, from made-up runs, into a temporary folder, plants
each fault the check exists to catch, and checks that each is caught and that the results
unchanged pass.
"""
import itertools
import os
import platform
import re
import shutil
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from run import (COMMITTED, COUNTS, COUNTS_FROM, EUCLIDEAN, HARNESS, HARNESS_LINE,  # noqa: E402
                 LAWS, MODEL_MD, RESULTS, ROOT, SUMMARY, git, harness_hash, parse_results,
                 plan, result_file, search_names, short_commit, write, written)
from derived import PROPERTIES  # noqa: E402

PAGE = 'A page.\n\n<!-- counts:begin -->\nx\n<!-- counts:end -->\n'   # a MODEL.md to write into


def shown(path):
    """a path as a message names it: from the repository's root when it is inside"""
    rel = os.path.relpath(path, ROOT)
    return path if rel.startswith('..') else rel


def safe(name):
    """a name found in results/, as a message shows it: quoted when it holds anything odd"""
    return name if re.fullmatch(r'[\w.+-]+', name, re.A) else ascii(name)


def header_of(path):
    """{key: [values]} from the `# key: value` lines that head a results file"""
    fields = {}
    with open(path, encoding='utf-8', errors='replace') as f:
        for line in f:
            if not line.startswith('# '):
                break
            key, sep, value = line[2:].rstrip('\n').partition(': ')
            if sep:
                fields.setdefault(key, []).append(value)
    return fields


def read(path):
    with open(path, encoding='utf-8', errors='replace') as f:
        return f.read()


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
    """The problems with summary.txt and MODEL.md's counts, against what --write makes of the
    runs' output in results/, with the provenance summary.txt names. Their first line names
    the Python that wrote them, which here is summary.txt's."""
    runs = plan(True)
    for r in runs:
        r.out = body_of(read(os.path.join(results, result_file(r))))
        if r.out is None:
            return [f'{shown(results)}/{result_file(r)} has no blank line after its header']
        r.seconds, r.command = 0.0, ''
        r.laws, r.derived, r.twice = parse_results(r.out, search_names)
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
    missing, or one --write does not write, or one that is not a regular file; a file that
    names no commit or harness, or one twice, or a commit its run did not read as committed,
    or a harness other than `harness` (by default the harness now); files that name more than
    one commit or harness between them; a MODEL.md that is not a regular file, or whose
    counts are not one block naming the results' commit; and, when there is no other,
    summary.txt or MODEL.md's counts not what --write makes of the runs' output. Runs no
    harness."""
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
        fields = header_of(path)
        for key, label, form, named in (
                ('commit', 'commit', r'([0-9a-f]{40}) \(([^()]*)\)', commits),
                ('harness' if name == SUMMARY else HARNESS_LINE, 'harness', r'([0-9a-f]{64})',
                 harnesses)):
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
    blocks = [m.group(0) for m in COUNTS.finditer(read(model_md))]
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
        problems = made_again(results, model_md)
    return problems, sorted(commits)


def made_up_runs():
    """The runs of the full plan, each with a little made-up output: in the plane and the
    hyperbolic plane a row for each law, and in the exhaustive and structured runs one for
    each derived property too."""
    runs = plan(True)
    for i, r in enumerate(runs):
        rows = ([f'{law} {i + 9} {i + 5} 0' for law in LAWS]
                if r.key.startswith(EUCLIDEAN + ('hyperbolic',)) else [])
        if r.key in ('exhaustive', 'structured'):
            rows += [f'{p} {i + 7} {i + 3} 0' for p in PROPERTIES]
        r.out = '\n'.join(rows + [f'{r.key}: made up by the self-test']) + '\n'
        r.seconds, r.command = 1.0, 'python3 -I'
        r.laws, r.derived, r.twice = parse_results(r.out, search_names)
    return runs


def self_test():
    """Write results as --write does, from made-up runs, into a temporary folder; plant each
    fault the check exists to catch in a fresh copy, and check that it is caught; and check
    that the results unchanged pass."""
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

        results, md = fresh()
        edit(os.path.join(results, runs[2]), r'\A(?:# .*\n)+', '')
        expect('a file with no header', results, md,
               f'{runs[2]} names no commit', f'{runs[2]} names no harness')

        results, md = fresh()
        edit(os.path.join(results, runs[3]), r'^(# commit: )[0-9a-f]+', r'\g<1>' + '1' * 40)
        expect('a changed commit line', results, md, 'the results name 2 commits')

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
