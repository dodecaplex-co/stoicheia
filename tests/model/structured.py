"""Structured random search: the hypotheses' incidence pattern is built by construction
(so they hold often), over a large lattice and over rational points, with rational
rotations for congruent copies. Axiom checks come from search.py; retained derived
properties use the same predicates, independently kept in derived.py.
Usage: python3 -I structured.py [samples_per_axiom] [seed]   (defaults 50000 and 11)"""
import math
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search  # noqa: E402
from derived import PROPERTIES  # noqa: E402
from model import *  # noqa

CHECK = {name: f for name, kinds, f in search.AXIOMS}
CHECK.update(PROPERTIES)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 50000
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 11)


def rp():
    r = rng.random()
    if r < 0.5:
        return (rng.randint(-20, 20), rng.randint(-20, 20))
    if r < 0.8:
        return fix((Fr(rng.randint(-40, 40), rng.randint(1, 5)), Fr(rng.randint(-40, 40), rng.randint(1, 5))))
    return (rng.randint(-3, 3), rng.randint(-3, 3))


def line_thru(A, pool=()):
    while True:
        B = rng.choice(pool) if pool and rng.random() < 0.3 else rp()
        if B != A:
            return line_through(A, B)


def pt_on(L, pool=()):
    cands = [P for P in pool if on_line(P, L)]
    if cands and rng.random() < 0.25:
        return rng.choice(cands)
    if rng.random() < 0.5:
        return lattice_on_line(L, rng, spread=8)
    return fix(rational_on_line(L, rng, spread=20) if rng.random() < 0.5 else
               (lambda t: (t[0] / rng.randint(1, 3) if False else t[0], t[1]))(rational_on_line(L, rng, spread=20)))


def any_pt(pool=()):
    if pool and rng.random() < 0.2:
        return rng.choice(pool)
    return rp()


def circ(pool=()):
    r = rng.random()
    if pool and r < 0.4:
        A = rng.choice(pool)
        B = any_pt()
        if A != B:
            return (A[0], A[1], d2(A, B))
    Cc = rng.choice(pool) if pool and r < 0.6 else rp()
    return (Cc[0], Cc[1], rng.choice([1, 2, 4, 5, 9, 25, 50, 65, 100, 169, Fr(9, 4), Fr(25, 9)]))


def pt_on_circle(c):
    """rational point on circle via rational parametrisation from a rational point if any"""
    P = lattice_on_circle(c, rng) if not any(isinstance(t, Fr) for t in c) else None
    if P is None:
        return None
    # rotate P about centre by a Pythagorean rotation to get many rational points
    a, b, h = rng.choice([(3, 4, 5), (5, 12, 13), (8, 15, 17), (1, 0, 1)])
    cx, cy = centre(c)
    x, y = P[0] - cx, P[1] - cy
    return fix((cx + Fr(a * x - b * y, h), cy + Fr(b * x + a * y, h)))


results = []


def run(name, gen, n=N):
    f = CHECK[name]
    hits = cex = 0
    first = None
    for _ in range(n):
        try:
            cfg = gen()
        except AssertionError:
            cfg = None
        if cfg is None:
            continue
        cfg['_rng'] = rng
        try:
            r = f(cfg)
        except ZeroDivisionError:
            r = None
        if r is None:
            continue
        hits += 1
        if not r:
            cex += 1
            first = first or {k: v for k, v in cfg.items() if k != '_rng'}
    results.append((name, hits, cex))
    print(f"{name:40s} {n:8d} {hits:8d} {cex:5d}", flush=True)
    if first:
        print('    first counterexample:', first, flush=True)


# --- generators
def g_p4():
    B = rp(); u = rp()
    if u == (0, 0):
        return None
    A = (B[0] - rng.randint(1, 3) * u[0], B[1] - rng.randint(1, 3) * u[1])
    D = (B[0] + rng.randint(1, 3) * u[0], B[1] + rng.randint(1, 3) * u[1])
    k = rng.choice([1, 2, Fr(1, 2)])
    w = (-u[1] * k, u[0] * k)
    if rng.random() < 0.3:
        w = (w[0] + rng.choice([0, 1]) * u[0], w[1] + rng.choice([0, 1]) * u[1])
    C = fix((B[0] + w[0], B[1] + w[1]))
    return dict(A=A, B=B, C=C, D=D)


def g_p5():
    pool = []
    A, B, C, D = rp(), rp(), rp(), rp()
    if rng.random() < 0.3:
        D = fix((A[0] + (C[0] - B[0]) * rng.choice([1, 2, Fr(1, 2)]), A[1] + (C[1] - B[1]) * rng.choice([1, 2, Fr(1, 2)])))  # near-parallel
    if A == B or B == C or C == D:
        return None
    return dict(A=A, B=B, C=C, D=D, L=line_through(A, B), M=line_through(B, C), N=line_through(C, D))


def g_ti(withE=False):
    A = rp()
    L = line_thru(A); M = line_thru(A) if rng.random() < 0.9 else L; N = line_thru(A) if rng.random() < 0.9 else M
    B, C, D = pt_on(L, [A]), pt_on(M, [A]), pt_on(N, [A])
    d = dict(A=A, B=B, C=C, D=D, L=L, M=M, N=N)
    if withE:
        d['E'] = any_pt([A, B, C, D])
    return d


def g_pasch(names='ABC'):
    def g():
        A = rp(); Cc = rp()
        if A == Cc:
            return None
        B = fix(lattice_between(A, Cc, rng)) if rng.random() < 0.8 else rp()
        pool = [A, B, Cc]
        r = rng.random()
        if r < 0.4:
            L = line_thru(rng.choice(pool), pool)
        else:
            L = line_through(rp(), rp()) if True else None
        return dict(A=A, B=B, C=Cc, L=L)
    return g


def g_pasch4():
    B = rp(); L = line_thru(B); M = line_thru(B) if rng.random() < 0.9 else L
    return dict(A=pt_on(M, [B]), B=B, C=pt_on(M, [B]), L=L, M=M)


def g_angle2():
    A = rp(); L = line_thru(A); M = line_thru(A) if rng.random() < 0.9 else L
    B, C = pt_on(L, [A]), pt_on(M, [A])
    D = any_pt([A, B, C])
    if rng.random() < 0.4:  # put D within / near the angle
        D = fix(lattice_between(B, C, rng)) if B != C else D
    return dict(A=A, B=B, C=C, D=D, L=L, M=M)


def g_adj():
    A = rp(); B = rp()
    if A == B:
        return None
    L = line_through(A, B)
    C = fix(lattice_between(A, B, rng))
    u = sub(B, A)
    D = fix((C[0] - u[1] * rng.choice([1, 2, Fr(1, 3)]), C[1] + u[0] * rng.choice([1, 2, Fr(1, 3)]))) if rng.random() < 0.7 else rp()
    return dict(A=A, B=B, C=C, D=D, L=L)


def g_rays():
    A = rp(); L = line_thru(A); M = line_thru(A) if rng.random() < 0.85 else L
    return dict(A=A, B=pt_on(L, [A]), B2=pt_on(L, [A]), C=pt_on(M, [A]), C2=pt_on(M, [A]), L=L, M=M)


def g_area_line():
    A = rp(); B = rp()
    if A == B:
        return None
    L = line_through(A, B)
    Cc = fix(lattice_between(A, B, rng)) if rng.random() < 0.5 else pt_on(L, [A, B])
    return dict(A=A, B=B, C=Cc, D=rp(), L=L)


def g_cong():
    A, B, Cc = rp(), rp(), rp()
    a, b, h = rng.choice([(3, 4, 5), (5, 12, 13), (8, 15, 17), (1, 0, 1), (0, 1, 1), (7, 24, 25)])
    refl = rng.random() < 0.5
    D = rp()

    def iso(X):
        x, y = X[0] - A[0], X[1] - A[1]
        if refl:
            y = -y
        return fix((D[0] + Fr(a * x - b * y, h), D[1] + Fr(b * x + a * y, h)))
    E, F = iso(B), iso(Cc)
    if rng.random() < 0.2:
        E, F = F, E
    return dict(A=A, B=B, C=Cc, D=D, E=E, F=F)


def g_chord():
    c = circ([rp()])
    if any(isinstance(t, Fr) for t in c):
        return None
    B = pt_on_circle(c); Cc = pt_on_circle(c)
    if B is None or Cc is None or B == Cc:
        return None
    L = line_through(B, Cc)
    A = fix(lattice_between(B, Cc, rng)) if rng.random() < 0.6 else pt_on(L, [B, Cc])
    return dict(A=A, B=B, C=Cc, L=L, al=c)


def g_convex(kind):
    def g():
        c = circ([rp()])
        pool = [P for P in (pt_on_circle(c), pt_on_circle(c)) if P is not None] if not any(isinstance(t, Fr) for t in c) else []
        A = rng.choice(pool) if pool and rng.random() < 0.6 else fix((c[0] + rng.randint(-3, 3), c[1] + rng.randint(-3, 3)))
        if kind == 'in':
            B = rng.choice(pool) if pool and rng.random() < 0.6 else any_pt([A, centre(c)])
            if A == B:
                return None
            return dict(A=A, B=B, C=fix(lattice_between(A, B, rng)), al=c)
        Cc = rng.choice(pool) if pool and rng.random() < 0.5 else any_pt([A])
        if A == Cc:
            return None
        k = rng.choice([2, 3, Fr(3, 2), Fr(5, 4)])
        B = fix((A[0] + k * (Cc[0] - A[0]), A[1] + k * (Cc[1] - A[1])))
        return dict(A=A, B=B, C=Cc, al=c)
    return g


def g_two_circles():
    O1 = rp()
    O2 = O1 if rng.random() < 0.15 else (O1[0] + rng.randint(-6, 6), O1[1] + rng.randint(-6, 6))
    R1 = rng.choice([1, 2, 4, 5, 9, 10, 13, 16, 25, 50])
    R2 = R1 if rng.random() < 0.2 else rng.choice([1, 2, 4, 5, 9, 10, 13, 16, 25, 50])
    if rng.random() < 0.3:  # tangent circles: |O1O2| = r1 + r2 or |r1 - r2| with square radii
        r1, r2 = rng.randint(1, 4), rng.randint(1, 4)
        u = rng.choice([(1, 0), (0, 1), (3, 4), (-4, 3)])
        n = 5 if u in [(3, 4), (-4, 3)] else 1
        dd = rng.choice([r1 + r2, abs(r1 - r2)])
        O2 = (O1[0] + dd * u[0] // n if dd * u[0] % n == 0 else O1[0] + Fr(dd * u[0], n),
              O1[1] + dd * u[1] // n if dd * u[1] % n == 0 else O1[1] + Fr(dd * u[1], n))
        O2 = fix(O2)
        R1, R2 = r1 * r1, r2 * r2
    return (O1[0], O1[1], R1), (O2[0], O2[1], R2)


def g_cm(kind):
    def g():
        c1, c2 = g_two_circles()
        if kind == 'side':
            Cc, D = centre(c1), centre(c2)
            L = line_through(Cc, D) if Cc != D else line_thru(Cc)
            return dict(al=c1, be=c2, B=rp(), C=Cc, D=D, L=L)
        if kind == 'nss':
            if any(isinstance(t, Fr) for t in c1 + c2):
                return None
            com = [P for P in (lattice_on_circle(c1, rng) for _ in range(30)) if P is not None and on_circle(P, c2)]
            if len(com) < 1:
                return None
            Cc, D = rng.choice(com), rng.choice(com)
            A, B = centre(c1), centre(c2)
            L = line_through(A, B) if A != B else line_thru(A)
            return dict(A=A, B=B, C=Cc, D=D, L=L, al=c1, be=c2)
        if any(isinstance(t, Fr) for t in c1):
            return None
        A = lattice_on_circle(c1, rng)
        if A is None:
            return None
        if kind == 'oio':
            B = any_pt([A, centre(c1), centre(c2)])
            return dict(A=A, B=B, al=c1, be=c2)
        if any(isinstance(t, Fr) for t in c2):
            return None
        B = lattice_on_circle(c2, rng)
        if B is None:
            return None
        return dict(A=A, B=B, al=c1, be=c2)
    return g


def g_lc():
    c = circ([rp()])
    B = fix((c[0] + rng.randint(-2, 2), c[1] + rng.randint(-2, 2)))
    L = line_thru(B)
    return dict(B=B, C=pt_on(L, [B]), L=L, al=c)


def g_lmc_opp():
    c = circ([rp()])
    A = fix((c[0] + rng.randint(-3, 3), c[1] + rng.randint(-3, 3)))
    B = fix((c[0] + rng.randint(-3, 3), c[1] + rng.randint(-3, 3)))
    if not any(isinstance(t, Fr) for t in c) and rng.random() < 0.5:
        A = lattice_on_circle(c, rng) or A
        B = lattice_on_circle(c, rng) or B
    if A == B:
        return None
    M = fix(lattice_between(A, B, rng))
    L = line_thru(M) if rng.random() < 0.8 else line_through(rp(), rp()) if True else None
    return dict(A=A, B=B, L=L, al=c)


def g_sup():
    A, B, Cc = rp(), rp(), rp()
    D = rp(); L = line_thru(D)
    G = pt_on(L, [D])
    return dict(A=A, B=B, C=Cc, D=D, G=G, H=rp(), L=L)


# Added when the harness came into the repository: the existence rules with hypotheses,
# which exhaustive.py does not enumerate, and the rules whose hypotheses search.py's
# sampler meets only rarely (it prefers to reuse what it has drawn, so two lines are
# usually one).
def g_two_lines():
    L = line_thru(rp())
    return dict(L=L, M=line_thru(rp()) if rng.random() < 0.9 else L)


def g_pt_line():
    L = line_thru(rp())
    return dict(B=pt_on(L) if rng.random() < 0.1 else rp(), L=L)


def g_seg():
    B = rp(); L = line_thru(B)
    return dict(B=B, C=pt_on(L, [B]), L=L)


def g_lines_meet():
    A, B = rp(), rp()
    if A == B:
        return None
    return dict(A=A, B=B, L=line_thru(rp()), M=line_through(A, B))


def g_between():
    A, Cc = rp(), rp()
    if A == Cc:
        return None
    B = fix(lattice_between(A, Cc, rng))
    r = rng.random()
    if r < 0.35:
        D = fix(lattice_between(A, B, rng))                  # between A and B
    elif r < 0.7:
        k = rng.choice([2, 3, Fr(3, 2)])                      # beyond C
        D = fix((B[0] + k * (Cc[0] - B[0]), B[1] + k * (Cc[1] - B[1])))
    else:
        D = pt_on(line_through(A, Cc), [A, B, Cc])
    return dict(A=A, B=B, C=Cc, D=D)


def g_circ_pts():
    c = circ([rp()])
    if any(isinstance(t, Fr) for t in c):
        return None
    B = pt_on_circle(c)
    if B is None:
        return None
    A = centre(c)
    r = rng.random()
    if r < 0.4:
        Cc = pt_on_circle(c) or B
    elif r < 0.6:
        Cc = fix(lattice_between(A, B, rng))
    else:
        Cc = any_pt([A, B])
    be = c if rng.random() < 0.3 or Cc == A else (A[0], A[1], d2(A, Cc))
    return dict(A=A, B=B, C=Cc, al=c, be=be)


def g_centres():
    c = circ([rp()])
    return dict(A=any_pt([centre(c)]), B=any_pt([centre(c)]), al=c)


print(f"{'axiom / derived property':40s} {'samples':>8s} {'hyp':>8s} {'cex':>5s}")
run('Postulate4', g_p4)
run('Postulate5', g_p5)
for n in ['derived.triple_incidence1', 'derived.triple_incidence2']:
    run(n, g_ti)
run('derived.triple_incidence3', lambda: g_ti(True))
for n in ['derived.pasch1', 'pasch2', 'derived.pasch3', 'derived.same_side_or', 'same_side_trans', 'derived.on_line_of_between', 'derived.on_line_of_between_ends']:
    run(n, g_pasch())
run('derived.pasch4', g_pasch4)
run('angle_add_of_inside', g_angle2)
run('derived.inside_of_angle_add', g_angle2)
run('derived.adjacent_eq_of_right', g_adj)
run('angle_eq_of_same_rays', g_rays)
run('area_add_of_between', g_area_line)
run('derived.between_of_area_add', g_area_line)
run('derived.area_congruent', g_cong)
run('derived.between_of_inside_chord', g_chord)
run('derived.inside_of_between', g_convex('in'))
run('derived.outside_of_between', g_convex('out'))
run('circles_meet_same_side', g_cm('side'))
run('derived.circles_meet_opposite_side', g_cm('side'))
run('derived.not_same_side_of_circles_meet', g_cm('nss'))
run('derived.circles_meet_of_on_inside_outside', g_cm('oio'))
run('circles_meet', g_cm('five'))
run('line_circle_between', g_lc)
run('line_circle_beyond', g_lc)
run('derived.line_meets_circle_of_opposite_sides', g_lmc_opp)
run('superposition', g_sup)
run('derived.exists_point_on_line_off_line', g_two_lines)
run('derived.exists_point_between', g_seg)
run('derived.exists_point_same_side', g_pt_line)
run('derived.exists_point_opposite_side', g_pt_line)
run('lines_meet_of_opposite_sides', g_lines_meet)
for n in ['derived.between_of_between_left', 'derived.between_of_between_right', 'derived.not_between_of_between_between']:
    run(n, g_between)
for n in ['Definition15', 'circle_eq', 'derived.on_circle_of_len_eq', 'derived.inside_of_len_lt', 'derived.len_lt_of_inside']:
    run(n, g_circ_pts)
# Appended so the existing generators keep their random sequence.
run('derived.centre_unique', g_centres)
run('derived.exists_point_outside_circle', lambda: dict(al=circ()))

def g_inside_line():
    c = circ([rp()])
    A = centre(c)
    if rng.random() < 0.5:
        A = any_pt([A])
    return dict(A=A, L=line_thru(A), al=c)


def g_two_pts():
    A = rp()
    return dict(A=A, B=A if rng.random() < 0.3 else any_pt([A]), C=any_pt([A]))


# The rules prepared for retirement that this search did not yet sample, as derived properties.
for n in ['derived.ne_of_between', 'derived.ne_of_between_ends']:
    run(n, g_between)
for n in ['derived.same_side_refl', 'derived.same_side_symm']:
    run(n, g_pasch())
for n in ['derived.centre_inside', 'derived.inside_not_on']:
    run(n, g_centres)
run('derived.eq_of_len_eq_zero', g_two_pts)
run('derived.area_swap', g_two_pts)
run('derived.line_meets_circle_of_inside', g_inside_line)
run('derived.exists_point_on_circle', lambda: dict(al=circ()))

print('structured total counterexamples:', sum(r[2] for r in results))
print('never met:', [r[0] for r in results if r[1] == 0])
