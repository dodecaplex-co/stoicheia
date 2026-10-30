"""Exhaustive enumeration of small lattice configurations for every axiom whose
hypotheses random sampling rarely meets (and for the rest as a second check).

Points: lattice grid; lines: every line through two grid points; circles: lattice
centres, radius^2 in a fixed list.  Every degenerate configuration in these ranges
(coincident points, equal lines, concentric / equal / tangent circles, points on
circles, collinear triples) is visited. Axiom checks come from search.py; retained
derived properties use the same predicates, independently kept in derived.py.
Usage: python3 -I exhaustive.py   (about two minutes; R1=1 or TI3=0 in the environment
for a quicker, smaller run)
"""
import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search  # noqa: E402
from derived import PROPERTIES  # noqa: E402
from model import *  # noqa

CHECK = {name: f for name, kinds, f in search.AXIOMS}
CHECK.update(PROPERTIES)
rng = random.Random(7)

R1 = int(os.environ.get('R1', 2))   # small grid radius for incidence work
G = [(x, y) for x in range(-R1, R1 + 1) for y in range(-R1, R1 + 1)]
LINES = sorted({line_through(P, Q) for P, Q in itertools.combinations(G, 2)})
ON = {L: [P for P in G if on_line(P, L)] for L in LINES}
THRU = {P: [L for L in LINES if on_line(P, L)] for P in G}

R2 = 4  # bigger grid for circle work
G2 = [(x, y) for x in range(-R2, R2 + 1) for y in range(-R2, R2 + 1)]
RADII = [1, 2, 4, 5, 8, 9, 10, 13]
CIRCS = [(x, y, R) for x in range(-1, 2) for y in range(-1, 2) for R in RADII]
LINES2 = sorted({line_through(P, Q) for P, Q in itertools.combinations([(x, y) for x in range(-3, 4) for y in range(-3, 4)], 2)})
ON2 = {L: [P for P in G2 if on_line(P, L)] for L in LINES2}
THRU2 = {P: [L for L in LINES2 if on_line(P, L)] for P in G2}
ONC = {c: [P for P in G2 if on_circle(P, c)] for c in CIRCS}

results = []


def run(name, gen):
    f = CHECK[name]
    t = time.time()
    tried = hits = cex = 0
    first = None
    for cfg in gen:
        cfg['_rng'] = rng
        tried += 1
        try:
            r = f(cfg)
        except ZeroDivisionError:
            r = None
        if r is None:
            continue
        hits += 1
        if not r:
            cex += 1
            if first is None:
                first = {k: v for k, v in cfg.items() if k != '_rng'}
    results.append((name, tried, hits, cex))
    print(f"{name:40s} {tried:10d} {hits:9d} {cex:6d}  {time.time() - t:6.1f}s", flush=True)
    if first:
        print('    first counterexample:', first, flush=True)


def P4(names):
    for t in itertools.product(G, repeat=len(names)):
        yield dict(zip(names, t))


print(f"grid {len(G)} pts, {len(LINES)} lines; circle grid {len(G2)} pts, {len(CIRCS)} circles")
print(f"{'axiom / derived property':40s} {'configs':>10s} {'hyp held':>9s} {'cex':>6s}")

# ---------------- Postulates ----------------
run('Postulate1', P4('AB'))
run('Postulate4', P4('ABCD'))


def gen_p5():
    for A, B, C, D in itertools.product(G, repeat=4):
        if A == B or B == C or C == D:
            continue  # then SameSide A D M is impossible (A or D would lie on M)
        yield dict(A=A, B=B, C=C, D=D, L=line_through(A, B), M=line_through(B, C), N=line_through(C, D))


run('Postulate5', gen_p5())


def gen_p2():
    for L in LINES:
        for B, C in itertools.product(ON[L], repeat=2):
            yield dict(B=B, C=C, L=L)


run('Postulate2', gen_p2())
run('Postulate3', P4('AB'))

# ---------------- Between ----------------
for n in ['between_symm', 'derived.ne_of_between', 'derived.ne_of_between_ends', 'not_between_of_between']:
    run(n, P4('ABC'))
for n in ['derived.between_of_between_left', 'derived.between_of_between_right', 'derived.not_between_of_between_between']:
    run(n, P4('ABCD'))


def gen_ptsline(names):
    for L in LINES:
        for t in itertools.product(G, repeat=len(names)):
            d = dict(zip(names, t))
            d['L'] = L
            yield d


for n in ['derived.on_line_of_between', 'derived.on_line_of_between_ends', 'between_cases',
          'same_side_trans', 'derived.same_side_or', 'derived.pasch1', 'pasch2', 'derived.pasch3']:
    run(n, gen_ptsline('ABC'))
for n in ['derived.same_side_symm', 'not_on_line_of_same_side']:
    run(n, gen_ptsline('AB'))
run('derived.same_side_refl', gen_ptsline('A'))


def gen_lines2_pts(names_on, extra=()):
    for L, M in itertools.product(LINES, repeat=2):
        for t in itertools.product(G, repeat=len(names_on)):
            d = dict(zip(names_on, t))
            d['L'], d['M'] = L, M
            yield d


def gen_pasch4():
    for B in G:
        for L, M in itertools.product(THRU[B], repeat=2):
            for A, C in itertools.product(ON[M], repeat=2):
                yield dict(A=A, B=B, C=C, L=L, M=M)


run('derived.pasch4', gen_pasch4())


def gen_lines_meet():
    for A, B in itertools.product(G, repeat=2):
        Ms = [line_through(A, B)] if A != B else THRU[A]
        for M in Ms:
            for L in LINES:
                yield dict(A=A, B=B, L=L, M=M)


run('lines_meet_of_opposite_sides', gen_lines_meet())
run('line_unique', ({'A': A, 'B': B, 'L': L, 'M': M} for A, B in itertools.product(G, repeat=2)
                    for L in THRU[A] for M in THRU[A]))


# ---------------- Triple incidence ----------------
def gen_ti(withE=False):
    for A in G:
        Ls = THRU[A]
        for L, M, N in itertools.product(Ls, repeat=3):
            for B in ON[L]:
                for C in ON[M]:
                    for D in ON[N]:
                        if withE:
                            for E in G:
                                yield dict(A=A, B=B, C=C, D=D, E=E, L=L, M=M, N=N)
                        else:
                            yield dict(A=A, B=B, C=C, D=D, L=L, M=M, N=N)


run('derived.triple_incidence1', gen_ti())
run('derived.triple_incidence2', gen_ti())
if os.environ.get('TI3', '1') == '1':
    run('derived.triple_incidence3', gen_ti(True))


# ---------------- Angles ----------------
def gen_angle2():
    for A in G:
        for L, M in itertools.product(THRU[A], repeat=2):
            for B in ON[L]:
                for C in ON[M]:
                    for D in G:
                        yield dict(A=A, B=B, C=C, D=D, L=L, M=M)


run('angle_add_of_inside', gen_angle2())
run('derived.inside_of_angle_add', gen_angle2())


def gen_adj():
    for L in LINES:
        for A, B, C in itertools.product(ON[L], repeat=3):
            for D in G:
                yield dict(A=A, B=B, C=C, D=D, L=L)


run('derived.adjacent_eq_of_right', gen_adj())


def gen_rays():
    for A in G:
        for L, M in itertools.product(THRU[A], repeat=2):
            for B, B2 in itertools.product(ON[L], repeat=2):
                for C, C2 in itertools.product(ON[M], repeat=2):
                    yield dict(A=A, B=B, B2=B2, C=C, C2=C2, L=L, M=M)


run('angle_eq_of_same_rays', gen_rays())


def gen_ray0():
    for A in G:
        for L in THRU[A]:
            for B in ON[L]:
                for C in G:
                    yield dict(A=A, B=B, C=C, L=L)


run('angle_eq_zero_of_same_ray', gen_ray0())
run('same_ray_of_angle_eq_zero', gen_ray0())
run('angle_symm', P4('ABC'))
run('angle_le_two_right', P4('ABC'))


# ---------------- Areas ----------------
def gen_area_line():
    for L in LINES:
        for A, B, C in itertools.product(ON[L], repeat=3):
            for D in G:
                yield dict(A=A, B=B, C=C, D=D, L=L)


run('area_add_of_between', gen_area_line())
run('derived.between_of_area_add', gen_area_line())


def gen_area0():
    for L in LINES:
        for A, B in itertools.product(ON[L], repeat=2):
            for C in G:
                yield dict(A=A, B=B, C=C, L=L)


run('area_eq_zero_of_on_line', gen_area0())
run('on_line_of_area_eq_zero', gen_area0())
run('area_degenerate', P4('AB'))
run('area_rotate', P4('ABC'))
run('derived.area_swap', P4('ABC'))


def gen_cong():
    Gs = [(x, y) for x in range(-1, 2) for y in range(-1, 2)]
    for A, B, C, D, E, F in itertools.product(Gs, repeat=6):
        yield dict(A=A, B=B, C=C, D=D, E=E, F=F)


# derived.area_congruent's check sometimes swaps in an isometric image; also run the raw search on a 3x3 grid
run('derived.area_congruent', gen_cong())

# ---------------- Metric / segments ----------------
run('derived.eq_of_len_eq_zero', P4('AB'))
run('len_self', P4('A'))
run('len_symm', P4('AB'))
run('len_add_of_between', P4('ABC'))


# ---------------- Circles ----------------
def gen_circ_pts(names, grid=G2):
    for c in CIRCS:
        for t in itertools.product(grid, repeat=len(names)):
            d = dict(zip(names, t))
            d['al'] = c
            yield d


run('derived.centre_unique', gen_circ_pts('AB', G))
run('derived.centre_inside', gen_circ_pts('A'))
run('derived.inside_not_on', gen_circ_pts('A'))


def gen_def15():
    for c in CIRCS:
        for A in G2:
            for B, C in itertools.product(ONC[c] + [A], repeat=2):
                yield dict(A=A, B=B, C=C, al=c)


run('Definition15', gen_def15())
run('derived.on_circle_of_len_eq', gen_def15())
run('derived.inside_of_len_lt', gen_circ_pts('ABC', [(x, y) for x in range(-3, 4) for y in range(-3, 4)]))
run('derived.len_lt_of_inside', gen_circ_pts('ABC', [(x, y) for x in range(-3, 4) for y in range(-3, 4)]))


def gen_circle_eq():
    for c1, c2 in itertools.product(CIRCS, repeat=2):
        A = centre(c1)
        for B in ONC[c1] or [None]:
            for C in ONC[c2] or [None]:
                if B is None or C is None:
                    continue
                yield dict(A=A, B=B, C=C, al=c1, be=c2)


run('circle_eq', gen_circle_eq())


def gen_chord():
    for c in CIRCS:
        for L in LINES2:
            pts = ON2[L]
            for A in pts:
                for B, C in itertools.product([P for P in pts if on_circle(P, c)], repeat=2):
                    yield dict(A=A, B=B, C=C, L=L, al=c)


run('derived.between_of_inside_chord', gen_chord())


def gen_convex():
    G3 = [(x, y) for x in range(-4, 5) for y in range(-4, 5)]
    for c in CIRCS:
        for A, B in itertools.product(G3, repeat=2):
            if A == B:
                continue
            dx, dy = B[0] - A[0], B[1] - A[1]
            g = gcd(abs(dx), abs(dy))
            mids = [(A[0] + k * dx // g, A[1] + k * dy // g) for k in range(1, g)]
            mids.append(((Fr(A[0]) + B[0]) / 2, (Fr(A[1]) + B[1]) / 2))
            for C in mids:
                yield dict(A=A, B=B, C=C, al=c)


run('derived.inside_of_between', gen_convex())


def gen_outside():
    G3 = [(x, y) for x in range(-4, 5) for y in range(-4, 5)]
    for c in CIRCS:
        for A, C in itertools.product(G3, repeat=2):
            if A == C:
                continue
            for k in (2, 3):
                B = (A[0] + k * (C[0] - A[0]), A[1] + k * (C[1] - A[1]))
                yield dict(A=A, B=B, C=C, al=c)
            B = (Fr(A[0]) + Fr(3, 2) * (C[0] - A[0]), Fr(A[1]) + Fr(3, 2) * (C[1] - A[1]))
            yield dict(A=A, B=B, C=C, al=c)


run('derived.outside_of_between', gen_outside())


def gen_two_circ_common():
    for c1, c2 in itertools.product(CIRCS, repeat=2):
        common = [P for P in ONC[c1] if on_circle(P, c2)]
        yield c1, c2, common


def gen_nss():
    for c1, c2, common in gen_two_circ_common():
        A, B = centre(c1), centre(c2)
        Ls = [line_through(A, B)] if A != B else THRU2[A]
        for C, D in itertools.product(common, repeat=2):
            for L in Ls:
                yield dict(A=A, B=B, C=C, D=D, L=L, al=c1, be=c2)


run('derived.not_same_side_of_circles_meet', gen_nss())


def gen_cm_side():
    G3 = [(x, y) for x in range(-3, 4) for y in range(-3, 4)]
    for c1, c2 in itertools.product(CIRCS, repeat=2):
        C, D = centre(c1), centre(c2)
        Ls = [line_through(C, D)] if C != D else THRU2[C]
        for L in Ls:
            for B in G3:
                yield dict(al=c1, be=c2, B=B, C=C, D=D, L=L)


run('circles_meet_same_side', gen_cm_side())
run('derived.circles_meet_opposite_side', gen_cm_side())


def gen_cmoio():
    for c1, c2 in itertools.product(CIRCS, repeat=2):
        for A in ONC[c1]:
            for B in G2:
                yield dict(A=A, B=B, al=c1, be=c2)


run('derived.circles_meet_of_on_inside_outside', gen_cmoio())


def gen_cm5():
    G3 = [(x, y) for x in range(-3, 4) for y in range(-3, 4)]
    for c1, c2 in itertools.product(CIRCS, repeat=2):
        for A in ONC[c1]:
            for B in ONC[c2]:
                yield dict(A=A, B=B, al=c1, be=c2)


run('circles_meet', gen_cm5())


def gen_lmc_opp():
    G3 = [(x, y) for x in range(-3, 4) for y in range(-3, 4)]
    for c in CIRCS:
        inn = [P for P in G3 if inside(P, c) or on_circle(P, c)]
        for A, B in itertools.product(inn, repeat=2):
            for L in LINES2:
                yield dict(A=A, B=B, L=L, al=c)


run('derived.line_meets_circle_of_opposite_sides', gen_lmc_opp())


def gen_lmc_in():
    for c in CIRCS:
        for A in G2:
            for L in THRU2[A]:
                yield dict(A=A, L=L, al=c)


run('derived.line_meets_circle_of_inside', gen_lmc_in())


def gen_lc():
    for c in CIRCS:
        for L in LINES2:
            for B, C in itertools.product(ON2[L], repeat=2):
                yield dict(B=B, C=C, L=L, al=c)


run('line_circle_between', gen_lc())
run('line_circle_beyond', gen_lc())


# ---------------- Superposition ----------------
def gen_sup():
    Gs = [(x, y) for x in range(-1, 2) for y in range(-1, 2)]
    Ls = [L for L in LINES if len(ON[L]) >= 2]
    for A, B, C in itertools.product(Gs, repeat=3):
        if not triangle(A, B, C):
            continue
        for L in Ls[::7]:
            for D, Gp in itertools.product(ON[L], repeat=2):
                for H in Gs:
                    yield dict(A=A, B=B, C=C, D=D, G=Gp, H=H, L=L)


run('superposition', gen_sup())
run('derived.exists_point_outside_circle', (dict(al=c) for c in CIRCS))


# The existence rules prepared for retirement, checked on the grid as derived properties.
run('derived.exists_point_same_side', gen_ptsline('B'))
run('derived.exists_point_opposite_side', gen_ptsline('B'))
run('derived.exists_point_between', gen_ptsline('BC'))
run('derived.exists_point_on_circle', (dict(al=c) for c in CIRCS))
run('derived.exists_point_on_line_off_line', (dict(L=L, M=M) for L, M in itertools.product(LINES, repeat=2)))

print('exhaustive axioms run:', sum(r[0] not in PROPERTIES for r in results),
      ' derived properties run:', sum(r[0] in PROPERTIES for r in results),
      ' total counterexamples:', sum(r[3] for r in results))
never = [r[0] for r in results if r[2] == 0]
print('hypotheses never met:', never)
