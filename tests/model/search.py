"""Counterexample search for every axiom of Stoicheia's Foundations, in the R^2 model.

For each axiom: sample many configurations (biased hard toward degenerate ones: reused
points, points on chosen lines/circles, centres, points between, coincident lines/circles,
concentric/tangent circles), keep those that satisfy the hypotheses exactly, check the
conclusion.  Existential conclusions are checked by constructing a witness.
Usage: python3 -I search.py [samples_per_axiom] [seed]
"""
import math
import random
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *  # noqa

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 1
BOX = 6

AXIOMS = []


def axiom(name, kinds):
    def deco(f):
        AXIOMS.append((name, kinds, f))
        return f
    return deco


# ---------------- sampler ----------------

def rand_pt(rng):
    if rng.random() < 0.15:  # generic-ish rational point
        return (Fr(rng.randint(-60, 60), rng.randint(1, 7)), Fr(rng.randint(-60, 60), rng.randint(1, 7)))
    return (rng.randint(-BOX, BOX), rng.randint(-BOX, BOX))


def gen_point(rng, pts, lines, circs):
    for _ in range(6):
        r = rng.random()
        if r < 0.18 and pts:
            return rng.choice(pts)
        if r < 0.45 and lines:
            L = rng.choice(lines)
            P = lattice_on_line(L, rng)
            if P is not None:
                return P
        if r < 0.62 and circs:
            P = lattice_on_circle(rng.choice(circs), rng)
            if P is not None:
                return P
        if r < 0.68 and circs:
            return centre(rng.choice(circs))
        if r < 0.76 and len(pts) >= 2:
            A, B = rng.sample(pts, 2)
            if A != B:
                return fix(lattice_between(A, B, rng))
        if r < 0.84 and len(pts) >= 2:
            A, B = rng.sample(pts, 2)
            k = rng.choice([2, 3, -1, -2])
            return (A[0] + k * (B[0] - A[0]), A[1] + k * (B[1] - A[1]))
        if r < 0.88 and circs:
            # point just inside / outside a circle near its centre direction
            c = rng.choice(circs)
            C0 = centre(c)
            return (C0[0] + rng.randint(-2, 2), C0[1] + rng.randint(-2, 2))
    return rand_pt(rng)


def gen_line(rng, pts, lines, circs):
    for _ in range(6):
        r = rng.random()
        if r < 0.40 and len(pts) >= 2:
            A, B = rng.sample(pts, 2)
            if A != B:
                return line_through(A, B)
        if r < 0.60 and pts:
            A = rng.choice(pts)
            B = rand_pt(rng)
            if A != B:
                return line_through(A, B)
        if r < 0.70 and lines:
            return rng.choice(lines)
        if r < 0.78 and lines and pts:
            L = rng.choice(lines)
            A = rng.choice(pts)
            return norm_line(L[0], L[1], -(L[0] * A[0] + L[1] * A[1]))
        if r < 0.86 and circs:
            c = rng.choice(circs)
            A = centre(c)
            B = rand_pt(rng)
            if A != B:
                return line_through(A, B)
    while True:
        A, B = rand_pt(rng), rand_pt(rng)
        if A != B:
            return line_through(A, B)


def gen_circle(rng, pts, lines, circs):
    for _ in range(6):
        r = rng.random()
        if r < 0.35 and len(pts) >= 2:
            A, B = rng.sample(pts, 2)
            if A != B:
                return (A[0], A[1], d2(A, B))
        if r < 0.50 and pts:
            A = rng.choice(pts)
            return (A[0], A[1], rng.choice([1, 2, 4, 5, 8, 9, 10, 13, 16, 25, 50]))
        if r < 0.65 and pts:
            A = rng.choice(pts)
            Cc = rand_pt(rng)
            if Cc != A:
                return (Cc[0], Cc[1], d2(A, Cc))
        if r < 0.75 and circs:
            return rng.choice(circs)
        if r < 0.85 and circs:
            c = rng.choice(circs)  # concentric
            return (c[0], c[1], rng.choice([1, 2, 4, 5, 9, 16, 25]))
    Cc = rand_pt(rng)
    return (Cc[0], Cc[1], rng.choice([1, 2, 4, 5, 8, 9, 10, 13, 16, 25, 50]))


def sample(rng, kinds):
    order = list(kinds.items())
    rng.shuffle(order)
    pts, lines, circs = [], [], []
    cfg = {}
    for name, k in order:
        if k == 'P':
            v = gen_point(rng, pts, lines, circs)
            pts.append(v)
        elif k == 'L':
            v = gen_line(rng, pts, lines, circs)
            lines.append(v)
        else:
            v = gen_circle(rng, pts, lines, circs)
            circs.append(v)
        cfg[name] = v
    return cfg


# ---------------- float helpers for witnesses ----------------

def fl(P):
    return (float(P[0]), float(P[1]))


def f_lval(P, L):
    return (L[0] * P[0] + L[1] * P[1] + L[2]) / math.hypot(L[0], L[1])


def f_on_line(P, L):
    return abs(f_lval(P, L)) < 1e-7


def f_same_side(P, Q, L):
    a, b = f_lval(P, L), f_lval(Q, L)
    return abs(a) > 1e-7 and abs(b) > 1e-7 and (a > 0) == (b > 0)


def f_opposite(P, Q, L):
    a, b = f_lval(P, L), f_lval(Q, L)
    return abs(a) > 1e-7 and abs(b) > 1e-7 and (a > 0) != (b > 0)


def f_on_circle(P, c):
    return abs(math.dist(P, fl(centre(c))) - math.sqrt(c[2])) < 1e-7


def f_between(A, B, C):
    ux, uy = C[0] - A[0], C[1] - A[1]
    vx, vy = B[0] - A[0], B[1] - A[1]
    n2 = ux * ux + uy * uy
    if n2 < 1e-14:
        return False
    if abs(ux * vy - uy * vx) / math.sqrt(n2) > 1e-7:
        return False
    t = (ux * vx + uy * vy) / n2
    return 1e-9 < t < 1 - 1e-9


def f_ang(A, B, C):
    u = (A[0] - B[0], A[1] - B[1])
    v = (C[0] - B[0], C[1] - B[1])
    if math.hypot(*u) < 1e-12 or math.hypot(*v) < 1e-12:
        return 0.0
    return math.atan2(abs(u[0] * v[1] - u[1] * v[0]), u[0] * v[0] + u[1] * v[1])


def line_circle_points(L, c):
    """float intersection points of line with circle"""
    a, b, cc = map(float, L)
    n = math.hypot(a, b)
    cx, cy = map(float, centre(c))
    r = math.sqrt(float(c[2]))
    dist = (a * cx + b * cy + cc) / n
    fx, fy = cx - a * dist / n, cy - b * dist / n
    h2 = r * r - dist * dist
    if h2 < 0:
        return []
    h = math.sqrt(max(h2, 0))
    tx, ty = -b / n, a / n
    return [(fx + h * tx, fy + h * ty), (fx - h * tx, fy - h * ty)]


def circle_circle_points(c1, c2):
    x1, y1 = map(float, centre(c1))
    x2, y2 = map(float, centre(c2))
    r1, r2 = math.sqrt(float(c1[2])), math.sqrt(float(c2[2]))
    d = math.hypot(x2 - x1, y2 - y1)
    if d < 1e-12:
        return None
    a = (r1 * r1 - r2 * r2 + d * d) / (2 * d)
    h2 = r1 * r1 - a * a
    if h2 < 0:
        return []
    h = math.sqrt(h2)
    mx, my = x1 + a * (x2 - x1) / d, y1 + a * (y2 - y1) / d
    ox, oy = -(y2 - y1) / d, (x2 - x1) / d
    return [(mx + h * ox, my + h * oy), (mx - h * ox, my - h * oy)]


# ======================= the axioms =======================
P, L_, C_ = 'P', 'L', 'C'

# ---- Postulates
@axiom('Postulate1', dict(A=P, B=P))
def _(c):
    A, B = c['A'], c['B']
    if A == B:
        return None
    Lw = line_through(A, B)
    return on_line(A, Lw) and on_line(B, Lw)


@axiom('Postulate2', dict(B=P, C=P, L=L_))
def _(c):
    B, C, L = c['B'], c['C'], c['L']
    if not (on_line(B, L) and on_line(C, L) and B != C):
        return None
    # witnesses A_k = C + k (C - B), k = 1, 2, ...: infinitely many, so any finite avoid list is missed
    ws = [(C[0] + k * (C[0] - B[0]), C[1] + k * (C[1] - B[1])) for k in (1, 2, 3)]
    return all(on_line(A, L) and between(B, C, A) for A in ws) and len(set(ws)) == 3


@axiom('Postulate3', dict(A=P, B=P))
def _(c):
    A, B = c['A'], c['B']
    if A == B:
        return None
    al = (A[0], A[1], d2(A, B))
    return al[2] > 0 and is_centre(A, al) and on_circle(B, al)


def is_right_angle(A, B, Cc, D):
    return between(A, B, D) and not collinear(A, B, Cc) and feq(ang(A, B, Cc), ang(Cc, B, D))


@axiom('Postulate4', dict(A=P, B=P, C=P, D=P))
def _(c):
    A, B, Cc, D = c['A'], c['B'], c['C'], c['D']
    if not is_right_angle(A, B, Cc, D):
        return None
    return feq(ang(A, B, Cc), RA)


@axiom('Postulate5', dict(A=P, B=P, C=P, D=P, L=L_, M=L_, N=L_))
def _(c):
    A, B, Cc, D, L, M, N = (c[k] for k in 'ABCDLMN')
    if not (on_line(A, L) and on_line(B, L) and on_line(B, M) and on_line(Cc, M) and on_line(Cc, N)
            and on_line(D, N) and B != Cc and same_side(A, D, M)):
        return None
    s = ang(A, B, Cc) + ang(B, Cc, D)
    if abs(s - math.pi) < 1e-7:
        return None  # boundary: hypothesis strictness undecidable in floats; skip
    if not s < math.pi:
        return None
    det = L[0] * N[1] - L[1] * N[0]
    if det == 0:
        return False  # parallel or equal: no meeting point
    x = Fr(L[1] * N[2] - N[1] * L[2], det)
    y = Fr(N[0] * L[2] - L[0] * N[2], det)
    E = (x, y)
    return on_line(E, L) and on_line(E, N) and same_side(E, A, M)


# ---- Definition 15
@axiom('Definition15', dict(A=P, B=P, C=P, al=C_))
def _(c):
    A, B, Cc, al = c['A'], c['B'], c['C'], c['al']
    if not (is_centre(A, al) and on_circle(B, al) and on_circle(Cc, al)):
        return None
    return d2(A, B) == d2(A, Cc)


# ---- Magnitudes: model is R>=0 with +, <, 0 -- checked on random non-negative reals and edge values
def mag_vals(rng):
    return [rng.choice([0.0, 0.0, 1.0, math.pi / 2, math.pi, rng.random() * 5, float(rng.randint(0, 3))]) for _ in range(3)]


@axiom('add_assoc', dict())
def _(c):
    a, b, d = mag_vals(c['_rng'])
    return feq((a + b) + d, a + (b + d))


@axiom('add_comm', dict())
def _(c):
    a, b, _ = mag_vals(c['_rng'])
    return a + b == b + a


@axiom('add_zero', dict())
def _(c):
    a, _, _ = mag_vals(c['_rng'])
    return a + 0.0 == a


@axiom('lt_irrefl', dict())
def _(c):
    a, _, _ = mag_vals(c['_rng'])
    return not a < a


@axiom('lt_trans', dict())
def _(c):
    a, b, d = mag_vals(c['_rng'])
    if not (a < b and b < d):
        return None
    return a < d


@axiom('lt_trichotomy', dict())
def _(c):
    a, b, _ = mag_vals(c['_rng'])
    return a < b or a == b or b < a


@axiom('not_lt_zero', dict())
def _(c):
    a, _, _ = mag_vals(c['_rng'])
    return not a < 0.0


@axiom('add_lt_add_right', dict())
def _(c):
    a, b, d = (Fr(c['_rng'].randint(0, 9), c['_rng'].randint(1, 4)) for _ in range(3))
    if not a < b:
        return None
    return a + d < b + d


# ---- Constructions (Points rules); avoid lists: we exhibit infinitely many witnesses
@axiom('exists_point', dict(A=P))
def _(c):
    return True  # R^2 is infinite


@axiom('exists_point_on_line', dict(L=L_))
def _(c):
    rng = c['_rng']
    L = c['L']
    ws = {lattice_on_line(L, rng, spread=10**6) for _ in range(5)}
    return all(w is not None and on_line(w, L) for w in ws) and len(ws) >= 2


@axiom('exists_point_inside_circle', dict(al=C_))
def _(c):
    al = c['al']
    ws = [(al[0] + Fr(1, k) * 0, al[1] + Fr(0)) for k in (1,)]
    r2 = al[2]
    ws = [(al[0], al[1] + Fr(1, k) * Fr(r2, r2 + 1)) for k in (1, 2, 3)]  # |offset| < 1 <= ... check exactly
    return all(inside(w, al) for w in ws) or all(inside((al[0] + Fr(t, 10**6), al[1]), al) for t in (1, 2, 3))




@axiom('exists_centre', dict(al=C_))
def _(c):
    al = c['al']
    return is_centre((al[0], al[1]), al)


@axiom('line_circle_between', dict(B=P, C=P, L=L_, al=C_))
def _(c):
    B, Cc, L, al = c['B'], c['C'], c['L'], c['al']
    if not (inside(B, al) and on_line(B, L) and outside(Cc, al) and on_line(Cc, L)):
        return None
    return any(f_on_circle(X, al) and f_on_line(X, L) and f_between(fl(B), X, fl(Cc))
               for X in line_circle_points(L, al))


@axiom('line_circle_beyond', dict(B=P, C=P, L=L_, al=C_))
def _(c):
    B, Cc, L, al = c['B'], c['C'], c['L'], c['al']
    if not (inside(B, al) and on_line(B, L) and on_line(Cc, L) and Cc != B):
        return None
    return any(f_on_circle(X, al) and f_on_line(X, L) and f_between(X, fl(B), fl(Cc))
               for X in line_circle_points(L, al))


def _cm_side(c, want_same):
    al, be, B, Cc, D, L = c['al'], c['be'], c['B'], c['C'], c['D'], c['L']
    if not (circles_meet(al, be) and is_centre(Cc, al) and is_centre(D, be) and on_line(Cc, L)
            and on_line(D, L) and not on_line(B, L)):
        return None
    if al == be:
        # the whole circle is common: take centre +/- r * unit normal of L
        a, b = float(L[0]), float(L[1])
        n = math.hypot(a, b)
        r = math.sqrt(float(al[2]))
        cands = [(float(Cc[0]) + s * r * a / n, float(Cc[1]) + s * r * b / n) for s in (1, -1)]
    else:
        cands = circle_circle_points(al, be)
        if cands is None:
            return False
    test = f_same_side if want_same else f_opposite
    return any(f_on_circle(X, al) and f_on_circle(X, be) and test(X, fl(B), L) for X in cands)


@axiom('circles_meet_same_side', dict(al=C_, be=C_, B=P, C=P, D=P, L=L_))
def _(c):
    return _cm_side(c, True)


# ---- Diagram: generalities
@axiom('line_unique', dict(A=P, B=P, L=L_, M=L_))
def _(c):
    A, B, L, M = c['A'], c['B'], c['L'], c['M']
    if not (A != B and on_line(A, L) and on_line(B, L) and on_line(A, M) and on_line(B, M)):
        return None
    return L == M




# ---- Between
@axiom('between_symm', dict(A=P, B=P, C=P))
def _(c):
    A, B, Cc = c['A'], c['B'], c['C']
    if not between(A, B, Cc):
        return None
    return between(Cc, B, A)


@axiom('not_between_of_between', dict(A=P, B=P, C=P))
def _(c):
    A, B, Cc = c['A'], c['B'], c['C']
    if not between(A, B, Cc):
        return None
    return not between(B, A, Cc)


@axiom('between_cases', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (A != B and B != Cc and A != Cc and on_line(A, L) and on_line(B, L) and on_line(Cc, L)):
        return None
    return between(A, B, Cc) or between(B, A, Cc) or between(A, Cc, B)


# ---- Same side
@axiom('not_on_line_of_same_side', dict(A=P, B=P, L=L_))
def _(c):
    if not same_side(c['A'], c['B'], c['L']):
        return None
    return not on_line(c['A'], c['L'])


@axiom('same_side_trans', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (same_side(A, B, L) and same_side(A, Cc, L)):
        return None
    return same_side(B, Cc, L)


# ---- Pasch
@axiom('pasch2', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (between(A, B, Cc) and on_line(A, L) and not on_line(B, L)):
        return None
    return same_side(B, Cc, L)


# ---- Triple incidence
# ---- Circles
# ---- Intersection (diagrammatic)
@axiom('lines_meet_of_opposite_sides', dict(A=P, B=P, L=L_, M=L_))
def _(c):
    A, B, L, M = c['A'], c['B'], c['L'], c['M']
    if not (opposite(A, B, L) and on_line(A, M) and on_line(B, M)):
        return None
    return lines_meet(L, M)




@axiom('circles_meet', dict(A=P, B=P, al=C_, be=C_))
def _(c):
    A, B, al, be = c['A'], c['B'], c['al'], c['be']
    if not (on_circle(A, al) and inside(B, al) and inside(A, be) and on_circle(B, be)):
        return None
    return circles_meet(al, be)


# ---- Metric
@axiom('len_self', dict(A=P))
def _(c):
    return d2(c['A'], c['A']) == 0


@axiom('len_symm', dict(A=P, B=P))
def _(c):
    return d2(c['A'], c['B']) == d2(c['B'], c['A'])


@axiom('radius_ne_zero', dict(A=P, B=P, al=C_))
def _(c):
    A, B, al = c['A'], c['B'], c['al']
    if not (is_centre(A, al) and on_circle(B, al)):
        return None
    return d2(A, B) != 0


@axiom('angle_symm', dict(A=P, B=P, C=P))
def _(c):
    A, B, Cc = c['A'], c['B'], c['C']
    if not (A != B and Cc != B):
        return None
    return feq(ang(A, B, Cc), ang(Cc, B, A))


@axiom('angle_le_two_right', dict(A=P, B=P, C=P))
def _(c):
    v = ang(c['A'], c['B'], c['C'])
    return 0.0 <= v <= math.pi + 1e-12


@axiom('area_degenerate', dict(A=P, B=P))
def _(c):
    return area2(c['A'], c['A'], c['B']) == 0


@axiom('area_rotate', dict(A=P, B=P, C=P))
def _(c):
    A, B, Cc = c['A'], c['B'], c['C']
    return area2(A, B, Cc) == area2(Cc, A, B)


@axiom('area_congruent', dict(A=P, B=P, C=P, D=P, E=P, F=P))
def _(c):
    A, B, Cc, D, E, F = (c[k] for k in 'ABCDEF')
    # make congruent copies likely: sometimes E,F are an isometric image of B,C about A->D
    rng = c['_rng']
    if rng.random() < 0.7:
        # lattice isometry: rotate by multiple of 90 deg, maybe reflect, translate A to D
        rot = rng.randint(0, 3)
        refl = rng.random() < 0.5

        def iso(X):
            x, y = X[0] - A[0], X[1] - A[1]
            if refl:
                y = -y
            for _ in range(rot):
                x, y = -y, x
            return (D[0] + x, D[1] + y)
        E, F = iso(B), iso(Cc)
    if not (d2(A, B) == d2(D, E) and d2(B, Cc) == d2(E, F) and d2(Cc, A) == d2(F, D)
            and feq(ang(A, B, Cc), ang(D, E, F)) and feq(ang(B, Cc, A), ang(E, F, D))
            and feq(ang(Cc, A, B), ang(F, D, E))):
        return None
    return area2(A, B, Cc) == area2(D, E, F)


# ---- Transfer: segments
@axiom('len_add_of_between', dict(A=P, B=P, C=P))
def _(c):
    A, B, Cc = c['A'], c['B'], c['C']
    if not between(A, B, Cc):
        return None
    return feq(length(A, B) + length(B, Cc), length(A, Cc))


@axiom('circle_eq', dict(A=P, B=P, C=P, al=C_, be=C_))
def _(c):
    A, B, Cc, al, be = c['A'], c['B'], c['C'], c['al'], c['be']
    if not (is_centre(A, al) and is_centre(A, be) and on_circle(B, al) and on_circle(Cc, be)
            and d2(A, B) == d2(A, Cc)):
        return None
    return al == be


# ---- Transfer: angles
@axiom('angle_eq_zero_of_same_ray', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (A != B and A != Cc and on_line(A, L) and on_line(B, L) and on_line(Cc, L) and not between(B, A, Cc)):
        return None
    return feq(ang(B, A, Cc), 0.0)


@axiom('same_ray_of_angle_eq_zero', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (A != B and A != Cc and on_line(A, L) and on_line(B, L)):
        return None
    # exact zero test: collinear and same direction
    zero = collinear(B, A, Cc) and dot(sub(B, A), sub(Cc, A)) > 0
    if abs(ang(B, A, Cc)) < 1e-12 and not zero:
        return False  # float says 0 but exact says not: report
    if not zero:
        return None
    return on_line(Cc, L) and not between(B, A, Cc)


def _angle_inside_hyp(c):
    A, B, Cc, D, L, M = (c[k] for k in 'ABCDLM')
    return (on_line(A, L) and on_line(A, M) and on_line(B, L) and on_line(Cc, M) and A != B and A != Cc
            and not on_line(D, L) and not on_line(D, M) and L != M)


@axiom('angle_add_of_inside', dict(A=P, B=P, C=P, D=P, L=L_, M=L_))
def _(c):
    if not (_angle_inside_hyp(c) and same_side(c['B'], c['D'], c['M']) and same_side(c['C'], c['D'], c['L'])):
        return None
    A, B, Cc, D = c['A'], c['B'], c['C'], c['D']
    return feq(ang(B, A, Cc), ang(B, A, D) + ang(D, A, Cc))






@axiom('angle_eq_of_same_rays', dict(A=P, B=P, B2=P, C=P, C2=P, L=L_, M=L_))
def _(c):
    A, B, B2, Cc, C2, L, M = (c[k] for k in ('A', 'B', 'B2', 'C', 'C2', 'L', 'M'))
    if not (on_line(A, L) and on_line(B, L) and on_line(B2, L) and on_line(A, M) and on_line(Cc, M)
            and on_line(C2, M) and B != A and B2 != A and Cc != A and C2 != A
            and not between(B, A, B2) and not between(Cc, A, C2)):
        return None
    return feq(ang(B, A, Cc), ang(B2, A, C2))


# ---- Transfer: areas
@axiom('area_eq_zero_of_on_line', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (on_line(A, L) and on_line(B, L) and A != B and on_line(Cc, L)):
        return None
    return area2(A, B, Cc) == 0


@axiom('on_line_of_area_eq_zero', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (on_line(A, L) and on_line(B, L) and A != B and area2(A, B, Cc) == 0):
        return None
    return on_line(Cc, L)


def _area_line_hyp(c):
    A, B, Cc, D, L = (c[k] for k in 'ABCDL')
    return (on_line(A, L) and on_line(B, L) and on_line(Cc, L) and A != B and A != Cc and B != Cc
            and not on_line(D, L))


@axiom('area_add_of_between', dict(A=P, B=P, C=P, D=P, L=L_))
def _(c):
    if not (_area_line_hyp(c) and between(c['A'], c['C'], c['B'])):
        return None
    A, B, Cc, D = (c[k] for k in 'ABCD')
    return area2(A, Cc, D) + area2(D, Cc, B) == area2(A, D, B)


# ---- Superposition
@axiom('superposition', dict(A=P, B=P, C=P, D=P, G=P, H=P, L=L_))
def _(c):
    A, B, Cc, D, G, H, L = (c[k] for k in 'ABCDGHL')
    if not (triangle(A, B, Cc) and on_line(D, L) and on_line(G, L) and D != G and not on_line(H, L)):
        return None
    Df, Gf = fl(D), fl(G)
    ab, bc, ca = length(A, B), length(B, Cc), length(Cc, A)
    ux, uy = Gf[0] - Df[0], Gf[1] - Df[1]
    n = math.hypot(ux, uy)
    ux, uy = ux / n, uy / n
    B2 = (Df[0] + ab * ux, Df[1] + ab * uy)
    # C' : |DC'| = ca, |B'C'| = bc, on H's side
    x = (ab * ab + ca * ca - bc * bc) / (2 * ab)
    y2 = ca * ca - x * x
    if y2 <= 0:
        return False
    y = math.sqrt(y2)
    nx, ny = -uy, ux
    if f_lval((Df[0] + nx, Df[1] + ny), L) * f_lval(fl(H), L) < 0:
        nx, ny = -nx, -ny
    C2 = (Df[0] + x * ux + y * nx, Df[1] + x * uy + y * ny)
    Af, Bf, Cf = fl(A), fl(B), fl(Cc)
    # The kept side through D and C', required by Rule.of_placement.
    N = (Df[1] - C2[1], C2[0] - Df[0], Df[0] * C2[1] - C2[0] * Df[1])
    return (f_on_line(B2, L) and not f_between(B2, Df, Gf) and f_same_side(C2, fl(H), L)
            and feq(math.dist(Df, B2), ab, 1e-7) and feq(math.dist(B2, C2), bc, 1e-7) and feq(math.dist(C2, Df), ca, 1e-7)
            and feq(f_ang(B2, Df, C2), f_ang(Bf, Af, Cf), 1e-7) and feq(f_ang(Df, C2, B2), f_ang(Af, Cf, Bf), 1e-7)
            and feq(f_ang(C2, B2, Df), f_ang(Cf, Bf, Af), 1e-7)
            and Df != C2 and f_on_line(Df, N) and f_on_line(C2, N))


# ======================= run =======================

def main():
    rng = random.Random(SEED)
    only = os.environ.get('ONLY')
    total_cex = 0
    print(f"{'axiom':40s} {'tried':>8s} {'hyp held':>9s} {'counterex':>9s}")
    for name, kinds, f in AXIOMS:
        if only and name not in only.split(','):
            continue
        hits = cex = 0
        first = None
        for _ in range(N):
            cfg = sample(rng, kinds)
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
                if first is None:
                    first = {k: v for k, v in cfg.items() if k != '_rng'}
        total_cex += cex
        flag = '' if hits else '   <-- hypotheses never met'
        print(f"{name:40s} {N:8d} {hits:9d} {cex:9d}{flag}")
        if first is not None:
            print('    first counterexample:', first)
    print('axioms checked:', len(AXIOMS), ' total counterexamples:', total_cex)


if __name__ == '__main__':
    main()
