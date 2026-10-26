"""The hyperbolic plane as a second model: every law but Postulate 5 should hold there.

We read the words in the Beltrami-Klein model of the hyperbolic plane.

* A point is a rational point of the open unit disc; a line is a chord, the part of a
  Euclidean line a x + b y + c = 0 inside the disc.  OnLine, Between and SameSide are the
  Euclidean ones restricted to the disc, so those checks are exact and use model.py's code.
* Lengths are hyperbolic.  For rational points P, Q the number
      cosh^2 d(P, Q) = (1 - P.Q)^2 / ((1 - |P|^2) (1 - |Q|^2))
  is rational, so "equal lengths", "on the circle" and "inside the circle" are decided
  exactly.  A circle is (cx, cy, rho) with centre (cx, cy) and rho = cosh^2 of its radius.
* Angles are measured on the hyperboloid.  The cosine's sign and its square are rational,
  so right angles, zero angles and equal angles are decided exactly; sums of angles are
  compared in floating point.
* The area of a triangle is its angle defect, pi minus its angle sum, and 0 when its
  corners lie on one line (a repeated corner included).  The right angle is pi/2.

Postulate 5 should fail: two chords can make interior angles less than two right angles
with a third and still never meet inside the disc.  Every other law should hold.  The
run reports both: Postulate 5's counterexamples show that the search can see a false
law, and no counterexample for the others is the evidence.  Which laws must fail is
read from laws.toml.  Where circles cross we use 60-digit decimals, so that two circles
that only touch are told apart from two that cut.

Usage: python3 -I hyperbolic.py [samples_per_axiom] [seed]
"""
import math
import os
import random
import sys
from decimal import Decimal, getcontext
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import (between, collinear, feq, line_through, lval, on_line, opposite, read_laws,  # noqa: E402
                   same_side, sgn)

N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 1
getcontext().prec = 60
TOUCH = Decimal(10) ** -40   # below this, two circles touch rather than cut

AXIOMS = []


def axiom(name, kinds, gen=None):
    def deco(f):
        AXIOMS.append((name, kinds, f, gen))
        return f
    return deco


# ======================= the model =======================

def P2(x, y):
    return (Fr(x), Fr(y))


def in_disc(P):
    return P[0] * P[0] + P[1] * P[1] < 1


def ch2(P, Q):
    """cosh^2 of the hyperbolic distance, exactly"""
    num = (1 - P[0] * Q[0] - P[1] * Q[1]) ** 2
    den = (1 - P[0] ** 2 - P[1] ** 2) * (1 - Q[0] ** 2 - Q[1] ** 2)
    return Fr(num) / Fr(den)


def dist(P, Q):
    """the hyperbolic distance (sinh^2 d = cosh^2 d - 1 is exact, so short lengths stay accurate)"""
    return math.asinh(math.sqrt(float(ch2(P, Q) - 1)))


def centre(c):
    return (c[0], c[1])


def make_circle(C, P):
    """the circle with centre C through P (C != P)"""
    c = (C[0], C[1], ch2(C, P))
    SEEDS.setdefault(c, P)
    return c


def F_circ(P, c):
    """< 0 inside the circle, 0 on it, > 0 outside (for P in the disc)"""
    C = centre(c)
    k = 1 - C[0] ** 2 - C[1] ** 2
    return (1 - C[0] * P[0] - C[1] * P[1]) ** 2 - c[2] * k * (1 - P[0] ** 2 - P[1] ** 2)


def on_circle(P, c):
    return ch2(P, centre(c)) == c[2]


def inside(P, c):
    return ch2(P, centre(c)) < c[2]


def outside(P, c):
    return ch2(P, centre(c)) > c[2]


def is_centre(P, c):
    return P == centre(c)


def mink(u, v):
    return u[0] * v[0] + u[1] * v[1] - u[2] * v[2]


def lift(P):
    return (P[0], P[1], 1)


def tangent(A, B):
    """a tangent vector at B pointing toward A (exact, up to a positive factor)"""
    a, b = lift(A), lift(B)
    k = Fr(mink(a, b)) / mink(b, b)
    return (a[0] - k * b[0], a[1] - k * b[1], a[2] - k * b[2])


def ang_parts(A, B, C):
    u, v = tangent(A, B), tangent(C, B)
    uu, vv, uv = mink(u, u), mink(v, v), mink(u, v)
    return uv, uu * vv - uv * uv, uu * vv   # |u||v| cos, (|u||v| sin)^2, (|u||v|)^2


def ang(A, B, C):
    if A == B or C == B:
        return 0.0
    n, s, _ = ang_parts(A, B, C)
    return math.atan2(math.sqrt(float(s)), float(n))


def ang_key(A, B, C):
    """(sign of the cosine, cosine squared): equal keys exactly when the angles are equal"""
    if A == B or C == B:
        return (1, Fr(1))
    n, s, d = ang_parts(A, B, C)
    return (sgn(n), Fr(n * n) / d)


def ang_eq(A, B, C, D, E, F):
    return ang_key(A, B, C) == ang_key(D, E, F)


def is_right(A, B, C):
    return A != B and C != B and ang_parts(A, B, C)[0] == 0


def ang_zero(A, B, C):
    return ang_key(A, B, C) == (1, Fr(1))


def area(A, B, C):
    if collinear(A, B, C):
        return 0.0
    return math.pi - (ang(B, A, C) + ang(A, B, C) + ang(A, C, B))


def area_zero(A, B, C):
    return collinear(A, B, C) or area(A, B, C) == 0.0


def triangle(A, B, C):
    return not collinear(A, B, C)


def meet_point(L, M):
    det = L[0] * M[1] - L[1] * M[0]
    if det == 0:
        return None
    return (Fr(L[1] * M[2] - M[1] * L[2], det), Fr(M[0] * L[2] - L[0] * M[2], det))


def lines_meet(L, M):
    if L == M:
        return False
    E = meet_point(L, M)
    return E is not None and in_disc(E)


def line_base(L):
    """the foot of the origin on L, and a direction along L"""
    a, b, c = L
    n2 = a * a + b * b
    return (Fr(-a * c, n2), Fr(-b * c, n2)), (-b, a)


def quad_along(P0, d, c):
    """coefficients (A0, A1, A2) of F_circ(P0 + t d, c) as a polynomial in t"""
    C = centre(c)
    k = 1 - C[0] ** 2 - C[1] ** 2
    rho = c[2]
    al = 1 - C[0] * P0[0] - C[1] * P0[1]
    be = C[0] * d[0] + C[1] * d[1]
    ga = 1 - P0[0] ** 2 - P0[1] ** 2
    de = P0[0] * d[0] + P0[1] * d[1]
    ep = d[0] ** 2 + d[1] ** 2
    return al * al - rho * k * ga, -2 * al * be + 2 * rho * k * de, be * be + rho * k * ep


def dec(x):
    x = Fr(x)
    return Decimal(x.numerator) / Decimal(x.denominator)


def cc_solve(c1, c2):
    """common points of two different circles on the hyperboloid: X = a C1 + b C2 + g n, with
    C1, C2 the unit centres, n the unit normal to both.  Returns (a, b, g2) in 60-digit
    decimals, or None for concentric circles."""
    x1, x2 = centre(c1), centre(c2)
    if x1 == x2:
        return None
    k1, k2 = 1 - x1[0] ** 2 - x1[1] ** 2, 1 - x2[0] ** 2 - x2[1] ** 2
    q = dec(x1[0] * x2[0] + x1[1] * x2[1] - 1) / (dec(k1) * dec(k2)).sqrt()   # <C1, C2> = -cosh d
    h1, h2 = dec(c1[2]).sqrt(), dec(c2[2]).sqrt()                            # cosh r1, cosh r2
    b = -(h2 + h1 * q) / (q * q - 1)
    a = h1 + b * q
    g2 = -1 + a * a + b * b - 2 * a * b * q
    return a, b, g2


def circles_meet(c1, c2):
    """two points in common"""
    if c1 == c2:
        return True
    r = cc_solve(c1, c2)
    if r is None:
        return False
    return r[2] > TOUCH


def reflect(P, L):
    """the hyperbolic mirror image of P in the line L (exact)"""
    a, b, c = L
    n = (a, b, -c)
    X = lift(P)
    k = Fr(2 * mink(X, n)) / mink(n, n)
    Y = (X[0] - k * n[0], X[1] - k * n[1], X[2] - k * n[2])
    return (Y[0] / Y[2], Y[1] / Y[2])


def perpendicular(P, L):
    """the line through P at right angles to L: it passes through L's pole"""
    a, b, c = L
    Q = (P[0] + a, P[1] + b) if c == 0 else (Fr(-a, c), Fr(-b, c))
    return line_through(P, Q)


# ---------- floating point, for witnesses ----------

def H(P):
    """Klein point -> hyperboloid"""
    x, y = float(P[0]), float(P[1])
    s = 1.0 / math.sqrt(1.0 - x * x - y * y)
    return (x * s, y * s, s)


def K(X):
    return (X[0] / X[2], X[1] / X[2])


def unit_toward(X, Y):
    t = tuple(Y[i] + mink(Y, X) * X[i] for i in range(3))
    n = math.sqrt(mink(t, t))
    return tuple(v / n for v in t)


def expmap(X, u, s):
    return tuple(math.cosh(s) * X[i] + math.sinh(s) * u[i] for i in range(3))


def f_ch2(P, Q):
    return (1 - P[0] * Q[0] - P[1] * Q[1]) ** 2 / ((1 - P[0] ** 2 - P[1] ** 2) * (1 - Q[0] ** 2 - Q[1] ** 2))


def f_dist(P, Q):
    return math.asinh(math.sqrt(max(f_ch2(P, Q) - 1.0, 0.0)))


def f_ang(A, B, C):
    a, b, c = H(A), H(B), H(C)
    u, v = unit_toward(b, a), unit_toward(b, c)
    s2 = max(mink(u, u) * mink(v, v) - mink(u, v) ** 2, 0.0)   # sin^2, from the Gram determinant
    return math.atan2(math.sqrt(s2), mink(u, v))


def f_side(P, L):
    return (L[0] * float(P[0]) + L[1] * float(P[1]) + L[2]) / math.hypot(L[0], L[1])


def f_on_circle(P, c):
    return abs(f_ch2(P, (float(c[0]), float(c[1]))) - float(c[2])) < 1e-9 * float(c[2])


def roots_along(P0, d, c):
    """the parameters t where P0 + t d meets the circle, in 60-digit decimals"""
    A0, A1, A2 = quad_along(P0, d, c)
    disc = dec(A1 * A1 - 4 * A0 * A2)
    if disc < 0:
        return []
    r = disc.sqrt()
    return [(-dec(A1) - r) / (2 * dec(A2)), (-dec(A1) + r) / (2 * dec(A2))]


def f_point(P0, d, t):
    return (float(dec(P0[0]) + t * dec(d[0])), float(dec(P0[1]) + t * dec(d[1])))


# ======================= the sampler =======================

DEN = [2, 3, 4, 5, 6, 8, 10, 12]
SEEDS = {}   # circle -> a rational point on it


def rand_pt(rng):
    while True:
        q = rng.choice(DEN)
        P = P2(Fr(rng.randint(-q, q), q), Fr(rng.randint(-q, q), q))
        if P[0] ** 2 + P[1] ** 2 < Fr(81, 100):
            return P


def pt_on_line(L, rng):
    F, d = line_base(L)
    room = (1 - F[0] ** 2 - F[1] ** 2) / (d[0] ** 2 + d[1] ** 2)   # t^2 < room keeps F + t d in the disc
    if room <= 0:
        return None
    # an exact binary fraction: rounding it to a small denominator could make it 0 when the
    # line's coefficients are large, and then every point drawn would be the foot F
    tmax = Fr(math.sqrt(float(room)) * 0.97)
    for _ in range(8):
        q = rng.choice(DEN)
        t = tmax * Fr(rng.randint(-q, q), q)
        if t * t < room:
            return (F[0] + t * d[0], F[1] + t * d[1])
    return F if in_disc(F) else None


def pts_on_line(L, k=4):
    """2k - 1 different rational points of the chord L, evenly spaced about the foot F"""
    F, d = line_base(L)
    room = (1 - F[0] ** 2 - F[1] ** 2) / (d[0] ** 2 + d[1] ** 2)
    tmax = Fr(math.sqrt(float(room)) * 0.97)
    return [(F[0] + tmax * Fr(j, k) * d[0], F[1] + tmax * Fr(j, k) * d[1]) for j in range(-k + 1, k)]


def pt_on_circle(c, rng):
    """a second rational point of the conic through a known one, along a small integer direction"""
    P0 = SEEDS.get(c)
    if P0 is None:
        return None
    for _ in range(6):
        d = (rng.randint(-3, 3), rng.randint(-3, 3))
        if d == (0, 0):
            continue
        A0, A1, A2 = quad_along(P0, d, c)   # A0 = 0, since P0 is on the circle
        t = -A1 / A2
        if t != 0:
            return (P0[0] + t * d[0], P0[1] + t * d[1])
    return P0


def gen_point(rng, pts, lines, circs):
    """each branch has its own share of the draws; a branch that cannot apply draws again"""
    for _ in range(6):
        r = rng.random()
        if r < 0.18:
            if pts:
                return rng.choice(pts)
        elif r < 0.42:
            P = pt_on_line(rng.choice(lines), rng) if lines else None
            if P is not None:
                return P
        elif r < 0.58:
            P = pt_on_circle(rng.choice(circs), rng) if circs else None
            if P is not None:
                return P
        elif r < 0.64:
            if circs:
                return centre(rng.choice(circs))
        elif r < 0.72:
            if len(pts) >= 2:
                A, B = rng.sample(pts, 2)
                if A != B:
                    t = Fr(rng.randint(1, 4), 5)
                    return (A[0] + t * (B[0] - A[0]), A[1] + t * (B[1] - A[1]))
        elif r < 0.80:
            if len(pts) >= 2:
                A, B = rng.sample(pts, 2)
                k = rng.choice([Fr(3, 2), Fr(2), Fr(-1, 2), Fr(-1)])
                P = (A[0] + k * (B[0] - A[0]), A[1] + k * (B[1] - A[1]))
                if in_disc(P):
                    return P
        elif r < 0.86:
            if circs:
                C0 = centre(rng.choice(circs))
                P = (C0[0] + Fr(rng.randint(-2, 2), 10), C0[1] + Fr(rng.randint(-2, 2), 10))
                if in_disc(P):
                    return P
        elif r < 0.92:
            if lines and pts:
                return reflect(rng.choice(pts), rng.choice(lines))
        else:
            return rand_pt(rng)
    return rand_pt(rng)


def gen_line(rng, pts, lines, circs):
    for _ in range(6):
        r = rng.random()
        if r < 0.38:
            if len(pts) >= 2:
                A, B = rng.sample(pts, 2)
                if A != B:
                    return line_through(A, B)
        elif r < 0.56:
            if pts:
                A, B = rng.choice(pts), rand_pt(rng)
                if A != B:
                    return line_through(A, B)
        elif r < 0.66:
            if lines:
                return rng.choice(lines)
        elif r < 0.78:
            if lines and pts:
                return perpendicular(rng.choice(pts), rng.choice(lines))
        elif r < 0.86:
            if circs:
                A, B = centre(rng.choice(circs)), rand_pt(rng)
                if A != B:
                    return line_through(A, B)
        else:
            break
    while True:
        A, B = rand_pt(rng), rand_pt(rng)
        if A != B:
            return line_through(A, B)


def gen_circle(rng, pts, lines, circs):
    for _ in range(6):
        r = rng.random()
        if r < 0.35:
            if len(pts) >= 2:
                A, B = rng.sample(pts, 2)
                if A != B:
                    return make_circle(A, B)
        elif r < 0.52:
            if pts:
                A, B = rng.choice(pts), rand_pt(rng)
                if A != B:
                    return make_circle(A, B) if rng.random() < 0.5 else make_circle(B, A)
        elif r < 0.62:
            if circs:
                return rng.choice(circs)
        elif r < 0.74:   # concentric
            if circs:
                c = rng.choice(circs)
                B = rand_pt(rng)
                if B != centre(c):
                    return make_circle(centre(c), B)
        elif r < 0.86:   # touching an existing circle at its known point T
            if circs:
                c = rng.choice(circs)
                C1, T = centre(c), SEEDS[c]
                s = rng.choice([Fr(1, 3), Fr(1, 2), Fr(2, 3), Fr(-1, 2), Fr(-1, 3)])
                C2 = (T[0] + s * (T[0] - C1[0]), T[1] + s * (T[1] - C1[1]))
                if in_disc(C2) and C2 != T:
                    return make_circle(C2, T)
        else:
            break
    A = rand_pt(rng)
    B = rand_pt(rng)
    while B == A:
        B = rand_pt(rng)
    return make_circle(A, B)


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


# ---------- structured generators: hypotheses that random sampling rarely meets ----------

def g_line_thru(rng, A):
    while True:
        B = rand_pt(rng)
        if B != A:
            return line_through(A, B)


def g_pt_on(rng, L, pool=()):
    cands = [P for P in pool if on_line(P, L)]
    if cands and rng.random() < 0.25:
        return rng.choice(cands)
    return pt_on_line(L, rng) or line_base(L)[0]


def g_right(rng):
    """A - B - D on a line, and C on the perpendicular at B (or anywhere, sometimes)"""
    B = rand_pt(rng)
    L = g_line_thru(rng, B)
    D = g_pt_on(rng, L)
    if D == B:
        return None
    s = rng.choice([Fr(1, 2), Fr(1), Fr(1, 3)])
    A = (B[0] + s * (B[0] - D[0]), B[1] + s * (B[1] - D[1]))
    if not in_disc(A):
        return None
    M = perpendicular(B, L) if rng.random() < 0.75 else g_line_thru(rng, B)
    C = g_pt_on(rng, M)
    return A, B, C, D, L


def gs_p4(rng):
    r = g_right(rng)
    return None if r is None else dict(A=r[0], B=r[1], C=r[2], D=r[3])


def gs_angle(rng):
    A = rand_pt(rng)
    L = g_line_thru(rng, A)
    M = g_line_thru(rng, A) if rng.random() < 0.9 else L
    B, C = g_pt_on(rng, L, [A]), g_pt_on(rng, M, [A])
    D = rand_pt(rng)
    if rng.random() < 0.5 and B != C:
        t = Fr(rng.randint(1, 4), 5)
        D = (B[0] + t * (C[0] - B[0]), B[1] + t * (C[1] - B[1]))
    return dict(A=A, B=B, C=C, D=D, L=L, M=M)


def gs_area_line(rng):
    A, B = rand_pt(rng), rand_pt(rng)
    if A == B:
        return None
    L = line_through(A, B)
    if rng.random() < 0.6:
        t = Fr(rng.randint(1, 5), 6)
        C = (A[0] + t * (B[0] - A[0]), A[1] + t * (B[1] - A[1]))
    else:
        C = g_pt_on(rng, L, [A, B])
    return dict(A=A, B=B, C=C, D=rand_pt(rng), L=L)


def gs_pasch(rng):
    A, C = rand_pt(rng), rand_pt(rng)
    if A == C:
        return None
    t = Fr(rng.randint(1, 4), 5)
    B = (A[0] + t * (C[0] - A[0]), A[1] + t * (C[1] - A[1])) if rng.random() < 0.8 else rand_pt(rng)
    pool = [A, B, C]
    L = g_line_thru(rng, rng.choice(pool)) if rng.random() < 0.4 else g_line_thru(rng, rand_pt(rng))
    return dict(A=A, B=B, C=C, L=L)


def gs_cong(rng):
    A, B, C = rand_pt(rng), rand_pt(rng), rand_pt(rng)
    img = [A, B, C]
    for _ in range(rng.randint(1, 3)):
        P, Q = rand_pt(rng), rand_pt(rng)
        if P != Q:
            L = line_through(P, Q)
            img = [reflect(X, L) for X in img]
    D, E, F = img
    if rng.random() < 0.2:
        E, F = F, E
    return dict(A=A, B=B, C=C, D=D, E=E, F=F)


def g_circle(rng, pool=()):
    C = rng.choice(pool) if pool and rng.random() < 0.3 else rand_pt(rng)
    P = rand_pt(rng)
    while P == C:
        P = rand_pt(rng)
    return make_circle(C, P)


def gs_chord(rng):
    c = g_circle(rng)
    B, C = pt_on_circle(c, rng), pt_on_circle(c, rng)
    if B is None or C is None or B == C:
        return None
    L = line_through(B, C)
    if rng.random() < 0.6:
        t = Fr(rng.randint(1, 4), 5)
        A = (B[0] + t * (C[0] - B[0]), B[1] + t * (C[1] - B[1]))
    else:
        A = g_pt_on(rng, L, [B, C])
    return dict(A=A, B=B, C=C, L=L, al=c)


def g_two_circles(rng):
    """two circles through a common point P (they then share P's mirror image in the line of
    centres), or concentric, or equal, or touching"""
    P = rand_pt(rng)
    C1 = rand_pt(rng)
    while C1 == P:
        C1 = rand_pt(rng)
    c1 = make_circle(C1, P)
    r = rng.random()
    if r < 0.5:
        C2 = rand_pt(rng)
        while C2 == P:
            C2 = rand_pt(rng)
    elif r < 0.65:
        C2 = C1
    elif r < 0.85:   # touching at P
        s = rng.choice([Fr(1, 2), Fr(-1, 2), Fr(1, 3)])
        C2 = (P[0] + s * (P[0] - C1[0]), P[1] + s * (P[1] - C1[1]))
        if not in_disc(C2) or C2 == P:
            return None
    else:
        return c1, c1, P
    if rng.random() < 0.15:
        Q = rand_pt(rng)
        if Q != C2:
            return c1, make_circle(C2, Q), P
    return c1, make_circle(C2, P), P


def gs_cm(kind):
    def g(rng):
        r = g_two_circles(rng)
        if r is None:
            return None
        c1, c2, P = r
        C, D = centre(c1), centre(c2)
        L = line_through(C, D) if C != D else g_line_thru(rng, C)
        if kind == 'side':
            return dict(al=c1, be=c2, B=rand_pt(rng), C=C, D=D, L=L)
        on1 = [P] + [pt_on_circle(c1, rng) for _ in range(5)]
        in2 = [X for X in on1 if inside(X, c2)]
        A = rng.choice(in2) if in2 and rng.random() < 0.8 else rng.choice(on1)
        on2 = [P] + [pt_on_circle(c2, rng) for _ in range(5)]
        in1 = [X for X in on2 if inside(X, c1)]
        B = rng.choice(in1) if in1 and rng.random() < 0.8 else rng.choice(on2)
        return dict(A=A, B=B, al=c1, be=c2)
    return g


def gs_lc(rng):
    c = g_circle(rng)
    C0 = centre(c)
    B = (C0[0] + Fr(rng.randint(-1, 1), 10), C0[1] + Fr(rng.randint(-1, 1), 10))
    if not in_disc(B):
        return None
    L = g_line_thru(rng, B)
    return dict(B=B, C=g_pt_on(rng, L, [B]), L=L, al=c)


def g_along(A, B, t):
    return (A[0] + t * (B[0] - A[0]), A[1] + t * (B[1] - A[1]))


def gs_between(rng):
    A, C = rand_pt(rng), rand_pt(rng)
    if A == C:
        return None
    B = g_along(A, C, Fr(rng.randint(1, 5), 6))
    r = rng.random()
    if r < 0.35:
        D = g_along(A, B, Fr(rng.randint(1, 3), 4))            # between A and B
    elif r < 0.7:
        D = g_along(B, C, rng.choice([Fr(3, 2), Fr(5, 4), 2]))  # beyond C
    else:
        D = g_pt_on(rng, line_through(A, C), [A, B, C])
    if not in_disc(D):
        return None
    return dict(A=A, B=B, C=C, D=D)


def gs_circ_pts(rng):
    """a circle, its centre, points on it (mirror images keep the distance exactly), inside, outside"""
    c = g_circle(rng)
    A, S = centre(c), SEEDS[c]
    B = rng.choice([S, pt_on_circle(c, rng)])
    r = rng.random()
    if r < 0.4:
        C = reflect(B, g_line_thru(rng, A))
    elif r < 0.6:
        C = g_along(A, B, Fr(rng.randint(1, 5), 6))
    elif r < 0.8:
        C = pt_on_circle(c, rng)
    else:
        C = rand_pt(rng)
    be = c if rng.random() < 0.3 else make_circle(A, rng.choice([C, rand_pt(rng)]) if C != A else S)
    if rng.random() < 0.1:
        A = rand_pt(rng)
    return dict(A=A, B=B, C=C, al=c, be=be)


def gs_rays(rng):
    A = rand_pt(rng)
    L = g_line_thru(rng, A)
    M = g_line_thru(rng, A) if rng.random() < 0.85 else L
    B, C = g_pt_on(rng, L, [A]), g_pt_on(rng, M, [A])
    B2 = g_along(A, B, Fr(rng.randint(1, 5), 4)) if rng.random() < 0.6 else g_pt_on(rng, L, [A])
    C2 = g_along(A, C, Fr(rng.randint(1, 5), 4)) if rng.random() < 0.6 else g_pt_on(rng, M, [A])
    if not (in_disc(B2) and in_disc(C2)):
        return None
    return dict(A=A, B=B, B2=B2, C=C, C2=C2, L=L, M=M)


def gs_sup(rng):
    A, B, C, D, Hh = (rand_pt(rng) for _ in range(5))
    L = g_line_thru(rng, D)
    G = g_pt_on(rng, L, [D])
    return dict(A=A, B=B, C=C, D=D, G=G, H=Hh, L=L)


def gs_lines_meet(rng):
    L = g_line_thru(rng, rand_pt(rng))
    A, B = rand_pt(rng), rand_pt(rng)
    if A == B:
        return None
    return dict(A=A, B=B, L=L, M=line_through(A, B))


# ======================= the axioms =======================
P, L_, C_ = 'P', 'L', 'C'

# ---- Postulates
@axiom('Postulate1', dict(A=P, B=P))
def _(c):
    A, B = c['A'], c['B']
    if A == B:
        return None
    Lw = line_through(A, B)
    return on_line(A, Lw) and on_line(B, Lw) and Lw[2] ** 2 < Lw[0] ** 2 + Lw[1] ** 2


@axiom('Postulate2', dict(B=P, C=P, L=L_))
def _(c):
    B, C, L = c['B'], c['C'], c['L']
    if not (on_line(B, L) and on_line(C, L) and B != C):
        return None
    ws, t = [], Fr(1, 2)
    while len(ws) < 3 and t > Fr(1, 2 ** 60):
        A = (C[0] + t * (C[0] - B[0]), C[1] + t * (C[1] - B[1]))
        if in_disc(A):
            ws.append(A)
        t /= 2
    return len(set(ws)) == 3 and all(on_line(A, L) and between(B, C, A) for A in ws)


@axiom('Postulate3', dict(A=P, B=P))
def _(c):
    A, B = c['A'], c['B']
    if A == B:
        return None
    al = make_circle(A, B)
    return al[2] > 1 and is_centre(A, al) and on_circle(B, al)


@axiom('Postulate4', dict(A=P, B=P, C=P, D=P), gs_p4)
def _(c):
    A, B, C, D = c['A'], c['B'], c['C'], c['D']
    if not (between(A, B, D) and not collinear(A, B, C) and ang_eq(A, B, C, C, B, D)):
        return None
    return is_right(A, B, C)


def gs_p5(rng):
    A, B, C, D = rand_pt(rng), rand_pt(rng), rand_pt(rng), rand_pt(rng)
    if A == B or B == C or C == D:
        return None
    return dict(A=A, B=B, C=C, D=D, L=line_through(A, B), M=line_through(B, C), N=line_through(C, D))


@axiom('Postulate5', dict(A=P, B=P, C=P, D=P, L=L_, M=L_, N=L_), gs_p5)
def _(c):
    A, B, C, D, L, M, Nn = (c[k] for k in 'ABCDLMN')
    if not (on_line(A, L) and on_line(B, L) and on_line(B, M) and on_line(C, M) and on_line(C, Nn)
            and on_line(D, Nn) and B != C and same_side(A, D, M)):
        return None
    s = ang(A, B, C) + ang(B, C, D)
    if abs(s - math.pi) < 1e-9 or not s < math.pi:
        return None
    E = meet_point(L, Nn)
    return E is not None and in_disc(E) and same_side(E, A, M)


# ---- Definition 15
@axiom('Definition15', dict(A=P, B=P, C=P, al=C_), gs_circ_pts)
def _(c):
    A, B, C, al = c['A'], c['B'], c['C'], c['al']
    if not (is_centre(A, al) and on_circle(B, al) and on_circle(C, al)):
        return None
    return ch2(A, B) == ch2(A, C)


# ---- Magnitudes: lengths, angles and defects of the model, with 0 and the right angle
def mag_vals(rng):
    def one():
        A, B, C = rand_pt(rng), rand_pt(rng), rand_pt(rng)
        return rng.choice([0.0, math.pi / 2, math.pi, dist(A, B), ang(A, B, C), area(A, B, C)])
    return [one() for _ in range(3)]


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
    rng = c['_rng']
    a, b, d = (Fr(rng.randint(0, 9), rng.randint(1, 4)) for _ in range(3))
    if not a < b:
        return None
    return a + d < b + d


# ---- Constructions (Points rules): we exhibit several witnesses; there are infinitely many
@axiom('exists_point', dict())
def _(c):
    return True   # the disc has infinitely many points


@axiom('exists_point_on_line', dict(L=L_))
def _(c):
    L = c['L']
    ws = pts_on_line(L) + [pt_on_line(L, c['_rng'])]
    return all(w is not None and on_line(w, L) and in_disc(w) for w in ws) and len(set(ws)) >= 7


@axiom('exists_point_inside_circle', dict(al=C_))
def _(c):
    al = c['al']
    C, S = centre(al), SEEDS[al]
    ws = [C] + [(C[0] + Fr(1, k) * (S[0] - C[0]), C[1] + Fr(1, k) * (S[1] - C[1])) for k in (2, 3)]
    return all(inside(w, al) for w in ws)




@axiom('exists_centre', dict(al=C_))
def _(c):
    al = c['al']
    return is_centre(centre(al), al) and in_disc(centre(al))


@axiom('line_circle_between', dict(B=P, C=P, L=L_, al=C_), gs_lc)
def _(c):
    B, C, L, al = c['B'], c['C'], c['L'], c['al']
    if not (inside(B, al) and on_line(B, L) and outside(C, al) and on_line(C, L)):
        return None
    d = (C[0] - B[0], C[1] - B[1])
    if not (F_circ(B, al) < 0 < F_circ(C, al)):   # so a crossing lies strictly between them
        return False
    for t in roots_along(B, d, al):
        if 0 < t < 1:
            X = f_point(B, d, t)
            if f_on_circle(X, al) and abs(f_side(X, L)) < 1e-9:
                return True
    return False


@axiom('line_circle_beyond', dict(B=P, C=P, L=L_, al=C_), gs_lc)
def _(c):
    B, C, L, al = c['B'], c['C'], c['L'], c['al']
    if not (inside(B, al) and on_line(B, L) and on_line(C, L) and C != B):
        return None
    d = (C[0] - B[0], C[1] - B[1])
    for t in roots_along(B, d, al):
        if t < 0:   # beyond B, away from C: Between A B C
            X = f_point(B, d, t)
            if f_on_circle(X, al) and abs(f_side(X, L)) < 1e-9 and X[0] ** 2 + X[1] ** 2 < 1:
                return True
    return False


def _cm_side(c, want_same):
    al, be, B, C, D, L = c['al'], c['be'], c['B'], c['C'], c['D'], c['L']
    if not (circles_meet(al, be) and is_centre(C, al) and is_centre(D, be) and on_line(C, L)
            and on_line(D, L) and not on_line(B, L)):
        return None
    if al == be:
        # the whole circle is common: go out the radius from the centre, square to L, both ways
        X0 = H(C)
        nL = (float(L[0]), float(L[1]), -float(L[2]))
        w = tuple(v / math.sqrt(mink(nL, nL)) for v in nL)
        r = math.acosh(math.sqrt(float(al[2])))
        cands = [K(expmap(X0, w, r)), K(expmap(X0, tuple(-v for v in w), r))]
    else:
        a, b, g2 = cc_solve(al, be)
        c1, c2 = lift(centre(al)), lift(centre(be))
        k1, k2 = -mink(c1, c1), -mink(c2, c2)
        C1 = tuple(dec(v) / dec(k1).sqrt() for v in c1)
        C2 = tuple(dec(v) / dec(k2).sqrt() for v in c2)
        cr = (c1[1] * c2[2] - c1[2] * c2[1], c1[2] * c2[0] - c1[0] * c2[2], c1[0] * c2[1] - c1[1] * c2[0])
        n = (cr[0], cr[1], -cr[2])   # Minkowski-orthogonal to both centres
        nn = dec(mink(n, n)).sqrt()
        g = g2.sqrt()
        cands = []
        for sg in (1, -1):
            X = tuple(a * C1[i] + b * C2[i] + sg * g * dec(n[i]) / nn for i in range(3))
            cands.append((float(X[0] / X[2]), float(X[1] / X[2])))
    sB = f_side(B, L)
    for X in cands:
        s = f_side(X, L)
        if not (f_on_circle(X, al) and f_on_circle(X, be)) or abs(s) < 1e-12:
            continue
        if (s > 0) == (sB > 0) if want_same else (s > 0) != (sB > 0):
            return True
    return False


@axiom('circles_meet_same_side', dict(al=C_, be=C_, B=P, C=P, D=P, L=L_), gs_cm('side'))
def _(c):
    return _cm_side(c, True)


# ---- Diagram: generalities
@axiom('line_unique', dict(A=P, B=P, L=L_, M=L_))
def _(c):
    A, B, L, M = c['A'], c['B'], c['L'], c['M']
    if not (A != B and on_line(A, L) and on_line(B, L) and on_line(A, M) and on_line(B, M)):
        return None
    return L == M




# ---- Between, same side, Pasch, triple incidence: the Euclidean rules, read in the disc
@axiom('between_symm', dict(A=P, B=P, C=P), gs_between)
def _(c):
    A, B, C = c['A'], c['B'], c['C']
    if not between(A, B, C):
        return None
    return between(C, B, A)


@axiom('not_between_of_between', dict(A=P, B=P, C=P), gs_between)
def _(c):
    A, B, C = c['A'], c['B'], c['C']
    if not between(A, B, C):
        return None
    return not between(B, A, C)


@axiom('between_cases', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, C, L = c['A'], c['B'], c['C'], c['L']
    if not (A != B and B != C and A != C and on_line(A, L) and on_line(B, L) and on_line(C, L)):
        return None
    return between(A, B, C) or between(B, A, C) or between(A, C, B)


@axiom('not_on_line_of_same_side', dict(A=P, B=P, L=L_))
def _(c):
    if not same_side(c['A'], c['B'], c['L']):
        return None
    return not on_line(c['A'], c['L'])


@axiom('same_side_trans', dict(A=P, B=P, C=P, L=L_), gs_pasch)
def _(c):
    A, B, C, L = c['A'], c['B'], c['C'], c['L']
    if not (same_side(A, B, L) and same_side(A, C, L)):
        return None
    return same_side(B, C, L)


@axiom('pasch2', dict(A=P, B=P, C=P, L=L_), gs_pasch)
def _(c):
    A, B, C, L = c['A'], c['B'], c['C'], c['L']
    if not (between(A, B, C) and on_line(A, L) and not on_line(B, L)):
        return None
    return same_side(B, C, L)


# ---- Circles
@axiom('between_of_inside_chord', dict(A=P, B=P, C=P, L=L_, al=C_), gs_chord)
def _(c):
    A, B, C, L, al = (c[k] for k in ('A', 'B', 'C', 'L', 'al'))
    if not (on_line(A, L) and on_line(B, L) and on_line(C, L) and inside(A, al) and on_circle(B, al)
            and on_circle(C, al) and B != C):
        return None
    return between(B, A, C)




# ---- Intersection (diagrammatic)
@axiom('lines_meet_of_opposite_sides', dict(A=P, B=P, L=L_, M=L_), gs_lines_meet)
def _(c):
    A, B, L, M = c['A'], c['B'], c['L'], c['M']
    if not (opposite(A, B, L) and on_line(A, M) and on_line(B, M)):
        return None
    return lines_meet(L, M)




@axiom('circles_meet', dict(A=P, B=P, al=C_, be=C_), gs_cm('five'))
def _(c):
    A, B, al, be = c['A'], c['B'], c['al'], c['be']
    if not (on_circle(A, al) and inside(B, al) and inside(A, be) and on_circle(B, be)):
        return None
    return circles_meet(al, be)


# ---- Metric
@axiom('len_self', dict(A=P))
def _(c):
    return ch2(c['A'], c['A']) == 1


@axiom('len_symm', dict(A=P, B=P))
def _(c):
    return ch2(c['A'], c['B']) == ch2(c['B'], c['A'])


@axiom('radius_ne_zero', dict(A=P, B=P, al=C_), gs_circ_pts)
def _(c):
    A, B, al = c['A'], c['B'], c['al']
    if not (is_centre(A, al) and on_circle(B, al)):
        return None
    return ch2(A, B) != 1


@axiom('angle_symm', dict(A=P, B=P, C=P))
def _(c):
    A, B, C = c['A'], c['B'], c['C']
    if not (A != B and C != B):
        return None
    return ang_eq(A, B, C, C, B, A)


@axiom('angle_le_two_right', dict(A=P, B=P, C=P))
def _(c):
    v = ang(c['A'], c['B'], c['C'])
    return 0.0 <= v <= math.pi + 1e-12


@axiom('area_degenerate', dict(A=P, B=P))
def _(c):
    return area(c['A'], c['A'], c['B']) == 0


@axiom('area_rotate', dict(A=P, B=P, C=P))
def _(c):
    A, B, C = c['A'], c['B'], c['C']
    return feq(area(A, B, C), area(C, A, B))


@axiom('area_congruent', dict(A=P, B=P, C=P, D=P, E=P, F=P), gs_cong)
def _(c):
    A, B, C, D, E, F = (c[k] for k in 'ABCDEF')
    if not (ch2(A, B) == ch2(D, E) and ch2(B, C) == ch2(E, F) and ch2(C, A) == ch2(F, D)
            and ang_eq(A, B, C, D, E, F) and ang_eq(B, C, A, E, F, D) and ang_eq(C, A, B, F, D, E)):
        return None
    return feq(area(A, B, C), area(D, E, F))


# ---- Transfer: segments
@axiom('len_add_of_between', dict(A=P, B=P, C=P), gs_pasch)
def _(c):
    A, B, C = c['A'], c['B'], c['C']
    if not between(A, B, C):
        return None
    return feq(dist(A, B) + dist(B, C), dist(A, C))


@axiom('circle_eq', dict(A=P, B=P, C=P, al=C_, be=C_), gs_circ_pts)
def _(c):
    A, B, C, al, be = c['A'], c['B'], c['C'], c['al'], c['be']
    if not (is_centre(A, al) and is_centre(A, be) and on_circle(B, al) and on_circle(C, be)
            and ch2(A, B) == ch2(A, C)):
        return None
    return al == be


# ---- Transfer: angles
@axiom('angle_eq_zero_of_same_ray', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, C, L = c['A'], c['B'], c['C'], c['L']
    if not (A != B and A != C and on_line(A, L) and on_line(B, L) and on_line(C, L) and not between(B, A, C)):
        return None
    return ang_zero(B, A, C)


@axiom('same_ray_of_angle_eq_zero', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, C, L = c['A'], c['B'], c['C'], c['L']
    if not (A != B and A != C and on_line(A, L) and on_line(B, L) and ang_zero(B, A, C)):
        return None
    return on_line(C, L) and not between(B, A, C)


def _angle_inside_hyp(c):
    A, B, C, D, L, M = (c[k] for k in 'ABCDLM')
    return (on_line(A, L) and on_line(A, M) and on_line(B, L) and on_line(C, M) and A != B and A != C
            and not on_line(D, L) and not on_line(D, M) and L != M)


@axiom('angle_add_of_inside', dict(A=P, B=P, C=P, D=P, L=L_, M=L_), gs_angle)
def _(c):
    if not (_angle_inside_hyp(c) and same_side(c['B'], c['D'], c['M']) and same_side(c['C'], c['D'], c['L'])):
        return None
    A, B, C, D = c['A'], c['B'], c['C'], c['D']
    return feq(ang(B, A, C), ang(B, A, D) + ang(D, A, C))






@axiom('angle_eq_of_same_rays', dict(A=P, B=P, B2=P, C=P, C2=P, L=L_, M=L_), gs_rays)
def _(c):
    A, B, B2, C, C2, L, M = (c[k] for k in ('A', 'B', 'B2', 'C', 'C2', 'L', 'M'))
    if not (on_line(A, L) and on_line(B, L) and on_line(B2, L) and on_line(A, M) and on_line(C, M)
            and on_line(C2, M) and B != A and B2 != A and C != A and C2 != A
            and not between(B, A, B2) and not between(C, A, C2)):
        return None
    return ang_eq(B, A, C, B2, A, C2)


# ---- Transfer: areas
@axiom('area_eq_zero_of_on_line', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, C, L = c['A'], c['B'], c['C'], c['L']
    if not (on_line(A, L) and on_line(B, L) and A != B and on_line(C, L)):
        return None
    return area(A, B, C) == 0


@axiom('on_line_of_area_eq_zero', dict(A=P, B=P, C=P, L=L_))
def _(c):
    A, B, C, L = c['A'], c['B'], c['C'], c['L']
    if not (on_line(A, L) and on_line(B, L) and A != B and area_zero(A, B, C)):
        return None
    return on_line(C, L)


def _area_line_hyp(c):
    A, B, C, D, L = (c[k] for k in 'ABCDL')
    return (on_line(A, L) and on_line(B, L) and on_line(C, L) and A != B and A != C and B != C
            and not on_line(D, L))


@axiom('area_add_of_between', dict(A=P, B=P, C=P, D=P, L=L_), gs_area_line)
def _(c):
    if not (_area_line_hyp(c) and between(c['A'], c['C'], c['B'])):
        return None
    A, B, C, D = (c[k] for k in 'ABCD')
    return feq(area(A, C, D) + area(D, C, B), area(A, D, B))


# ---- Superposition: lay the triangle down by the hyperbolic plane's own motions
@axiom('superposition', dict(A=P, B=P, C=P, D=P, G=P, H=P, L=L_), gs_sup)
def _(c):
    A, B, C, D, G, Hh, L = (c[k] for k in 'ABCDGHL')
    if not (triangle(A, B, C) and on_line(D, L) and on_line(G, L) and D != G and not on_line(Hh, L)):
        return None
    ab, bc, ca = dist(A, B), dist(B, C), dist(C, A)
    alpha = ang(B, A, C)
    X = H(D)
    u = unit_toward(X, H(G))
    w0 = unit_toward(X, H(Hh))
    w = tuple(w0[i] - mink(w0, u) * u[i] for i in range(3))
    nw = math.sqrt(mink(w, w))
    w = tuple(v / nw for v in w)   # square to L at D, toward H's side
    B2 = K(expmap(X, u, ab))
    v = tuple(math.cos(alpha) * u[i] + math.sin(alpha) * w[i] for i in range(3))
    C2 = K(expmap(X, v, ca))
    Df, Gf, Hf = (float(D[0]), float(D[1])), (float(G[0]), float(G[1])), (float(Hh[0]), float(Hh[1]))
    tol = 1e-7
    on_ray = (B2[0] - Df[0]) * (Gf[0] - Df[0]) + (B2[1] - Df[1]) * (Gf[1] - Df[1]) > 0
    # The kept side through D and C', required by Rule.of_placement.
    N = (Df[1] - C2[1], C2[0] - Df[0], Df[0] * C2[1] - C2[0] * Df[1])
    return (abs(f_side(B2, L)) < tol and on_ray and f_side(C2, L) * f_side(Hf, L) > 0
            and abs(f_side(C2, L)) > 1e-9
            and feq(f_dist(Df, B2), ab, tol) and feq(f_dist(B2, C2), bc, tol) and feq(f_dist(C2, Df), ca, tol)
            and feq(f_ang(B2, Df, C2), alpha, tol) and feq(f_ang(Df, C2, B2), ang(A, C, B), tol)
            and feq(f_ang(C2, B2, Df), ang(C, B, A), tol)
            and Df != C2 and abs(f_side(Df, N)) < tol and abs(f_side(C2, N)) < tol)


# ======================= run =======================

def selftest(rng, n=2000):
    """That the lengths, angles and areas above are the hyperbolic plane's: the hyperbolic law
    of cosines ties dist to ang; mirror images keep lengths and angles exactly; the line
    through a pole meets its polar at right angles; every triangle's angle sum is below pi."""
    worst = 0.0
    for _ in range(n):
        A, B, C = rand_pt(rng), rand_pt(rng), rand_pt(rng)
        if not triangle(A, B, C):
            continue
        a, b, c = dist(B, C), dist(C, A), dist(A, B)
        g = ang(A, C, B)
        lhs = math.cosh(c)
        rhs = math.cosh(a) * math.cosh(b) - math.sinh(a) * math.sinh(b) * math.cos(g)
        worst = max(worst, abs(lhs - rhs) / lhs)
        P, Q = rand_pt(rng), rand_pt(rng)
        if P != Q:
            L = line_through(P, Q)
            A2, B2, C2 = reflect(A, L), reflect(B, L), reflect(C, L)
            assert ch2(A2, B2) == ch2(A, B) and ang_eq(A2, B2, C2, A, B, C), 'a reflection moved a length or angle'
            Mm = perpendicular(A, L)
            X = meet_point(L, Mm)
            assert X is not None and in_disc(X), 'a perpendicular missed its line'
            if X != A:
                Y = P if P != X else Q
                assert is_right(A, X, Y), 'the pole construction did not give a right angle'
        assert area(A, B, C) > 0, 'a triangle had angle sum at least pi'
    assert worst < 1e-9, f'law of cosines off by {worst}'
    return worst


def main():
    _, expected_to_fail = read_laws()
    rng = random.Random(SEED)
    worst = selftest(random.Random(SEED + 1000))
    print(f'self-test: law of cosines, reflections, perpendiculars and angle sums on 2000 triangles'
          f' (worst relative error {worst:.1e})')
    only = os.environ.get('ONLY')
    total = {True: 0, False: 0}
    print(f"{'axiom':40s} {'tried':>8s} {'hyp held':>9s} {'counterex':>9s}")
    for name, kinds, f, gen in AXIOMS:
        if only and name not in only.split(','):
            continue
        hits = cex = 0
        first = None
        for _ in range(N):
            SEEDS.clear()
            cfg = None
            if gen is not None and rng.random() < 0.6:
                cfg = gen(rng)
            if cfg is None:
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
        total[name in expected_to_fail] += cex
        flag = '' if hits else '   <-- hypotheses never met'
        if name in expected_to_fail:
            flag += '   (expected to fail: the hyperbolic plane is not Euclidean)'
        print(f"{name:40s} {N:8d} {hits:9d} {cex:9d}{flag}")
        if first is not None and name not in expected_to_fail:
            print('    first counterexample:', first)
        elif first is not None:
            print('    for example:', {k: tuple(str(t) for t in v) if isinstance(v, tuple) else v
                                       for k, v in first.items()})
    print('axioms checked:', len(AXIOMS), ' counterexamples to the other axioms:', total[False],
          f' counterexamples to those that must fail ({", ".join(sorted(expected_to_fail))}):',
          total[True])


if __name__ == '__main__':
    main()
