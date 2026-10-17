"""A second, independent check of the triple-incidence rules (exact, on a small grid)
and of the angle, area, Postulate 4, Postulate 5 and superposition rules (in floating
point, on 200,000 random configurations, seed 1), written separately from search.py.
Usage: python3 -I angle_check.py   (from any directory; it imports nothing local)
"""
import math, random
from itertools import product
# ---- exact triple incidence on the grid ----
R = range(-2, 3)
P = [(x, y) for x in R for y in R]
from math import gcd
def line_through(a, b):
    (x1, y1), (x2, y2) = a, b
    A, B = y2 - y1, x1 - x2; C = -(A * x1 + B * y1)
    g = gcd(gcd(abs(A), abs(B)), abs(C)) or 1
    A, B, C = A // g, B // g, C // g
    if A < 0 or (A == 0 and B < 0): A, B, C = -A, -B, -C
    return (A, B, C)
LINES = sorted({line_through(a, b) for a in P for b in P if a != b})
def ev(L, p): return L[0]*p[0] + L[1]*p[1] + L[2]
def on(p, L): return ev(L, p) == 0
def ss(p, q, L): return ev(L, p) * ev(L, q) > 0
fails = []
for A in [(0, 0), (1, 0), (1, 1), (2, 2)]:
    thru = [L for L in LINES if on(A, L)]
    pts = {L: [p for p in P if on(p, L)] for L in thru}
    for L, M, N in product(thru, repeat=3):
        for B in pts[L]:
            for C in pts[M]:
                for D in pts[N]:
                    if ss(C, D, L) and ss(B, C, N):
                        if ss(B, D, M): fails.append(('TI1', A, B, C, D))
                        for E in P:
                            if ss(D, E, M) and ss(C, E, N) and not ss(C, E, L): fails.append(('TI3', A, B, C, D, E))
                    if ss(C, D, L) and not ss(B, D, M) and not on(D, M) and B != A and not ss(B, C, N):
                        fails.append(('TI2', A, B, C, D))
print('triple incidence grid failures:', len(fails), fails[:5])

# ---- float model for angles / areas ----
def sub(a, b): return (a[0]-b[0], a[1]-b[1])
def norm(v): return math.hypot(*v)
def ang(a, b, c):
    if a == b or c == b: return 0.0
    u, v = sub(a, b), sub(c, b)
    x = (u[0]*v[0] + u[1]*v[1]) / (norm(u)*norm(v)); return math.acos(max(-1, min(1, x)))
def area(a, b, c): return abs((b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])) / 2
def side(p, a, b): return (b[0]-a[0])*(p[1]-a[1]) - (b[1]-a[1])*(p[0]-a[0])
def rp(): return (random.uniform(-5, 5), random.uniform(-5, 5))
eps = 1e-9; bad = {}
def flag(n): bad[n] = bad.get(n, 0) + 1
random.seed(1)
for _ in range(200000):
    A, B, C, D = rp(), rp(), rp(), rp()
    # angle add both directions (L = AB, M = AC)
    if abs(side(C, A, B)) > 1e-6 and abs(side(D, A, B)) > 1e-6 and abs(side(D, A, C)) > 1e-6:
        inside = side(B, A, C) * side(D, A, C) > 0 and side(C, A, B) * side(D, A, B) > 0
        add = abs(ang(B, A, C) - (ang(B, A, D) + ang(D, A, C))) < 1e-9
        if inside != add: flag('angle_add (Diagram-angle 2)')
    # Postulate 5: L = AB, M = BC, N = CD, A and D same side of M
    if side(A, B, C) * side(D, B, C) > 0 and ang(A, B, C) + ang(B, C, D) < math.pi - 1e-6:
        # intersection of line AB and line CD
        d1, d2 = sub(B, A), sub(D, C)
        den = d1[0]*d2[1] - d1[1]*d2[0]
        if abs(den) < 1e-12: flag('P5 parallel')
        else:
            t = ((C[0]-A[0])*d2[1] - (C[1]-A[1])*d2[0]) / den
            E = (A[0] + t*d1[0], A[1] + t*d1[1])
            if not side(E, B, C) * side(A, B, C) > 0: flag('P5 wrong side')
    # Postulate 4 / adjacent_eq_of_right: A-B-D with D beyond B
    Dp = (2*B[0] - A[0], 2*B[1] - A[1])
    if abs(side(C, A, B)) > 1e-6:
        if abs(ang(A, B, C) + ang(C, B, Dp) - math.pi) > 1e-9: flag('supplementary')
    # area rules
    t = random.uniform(0.01, 0.99); Cb = (A[0] + t*(B[0]-A[0]), A[1] + t*(B[1]-A[1]))
    if abs(side(D, A, B)) > 1e-6:
        if abs(area(A, Cb, D) + area(D, Cb, B) - area(A, D, B)) > 1e-9: flag('area_add')
        t2 = random.choice([-0.5, 1.5, 2.0]); Co = (A[0] + t2*(B[0]-A[0]), A[1] + t2*(B[1]-A[1]))
        if abs(area(A, Co, D) + area(D, Co, B) - area(A, D, B)) < 1e-9: flag('between_of_area_add converse')
    # superposition: rigid motion A->D, B on ray D G, C on H's side of line DG
    G, H = rp(), rp()
    if abs(side(C, A, B)) > 1e-3 and norm(sub(G, D)) > 1e-3 and abs(side(H, D, G)) > 1e-3:
        u = sub(G, D); u = (u[0]/norm(u), u[1]/norm(u)); w = (-u[1], u[0])
        ab = sub(B, A); e = (ab[0]/norm(ab), ab[1]/norm(ab)); f = (-e[1], e[0])
        def co(p):
            v = sub(p, A); return (v[0]*e[0] + v[1]*e[1], v[0]*f[0] + v[1]*f[1])
        sgn = 1 if co(C)[1] * side(H, D, G) > 0 else -1
        def img(p):
            x, y = co(p); y *= sgn; return (D[0] + x*u[0] + y*w[0], D[1] + x*u[1] + y*w[1])
        B2, C2 = img(B), img(C)
        ok = (abs(side(B2, D, G)) < 1e-6 and side(C2, D, G) * side(H, D, G) > 0
              and abs(norm(sub(D, B2)) - norm(sub(A, B))) < 1e-9 and abs(norm(sub(B2, C2)) - norm(sub(B, C))) < 1e-9
              and abs(norm(sub(C2, D)) - norm(sub(C, A))) < 1e-9 and abs(ang(B2, D, C2) - ang(B, A, C)) < 1e-7
              and abs(ang(D, C2, B2) - ang(A, C, B)) < 1e-7 and abs(ang(C2, B2, D) - ang(C, B, A)) < 1e-7
              and (B2[0]-D[0])*u[0] + (B2[1]-D[1])*u[1] > 0)
        if not ok: flag('superposition')
print('float failures:', bad)
