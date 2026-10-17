"""Exhaustive exact check of System E incidence/order/circle rules in a small grid model of R^2,
written separately from search.py as a second opinion.
Usage: python3 -I grid_check.py   (from any directory; it imports nothing local)
"""
from fractions import Fraction as F
from itertools import product, combinations
from math import gcd

R = range(-2, 3)
P = [(x, y) for x in R for y in R]

def line_through(a, b):
    (x1, y1), (x2, y2) = a, b
    A, B = y2 - y1, x1 - x2
    C = -(A * x1 + B * y1)
    g = gcd(gcd(abs(A), abs(B)), abs(C)) or 1
    A, B, C = A // g, B // g, C // g
    if A < 0 or (A == 0 and B < 0):
        A, B, C = -A, -B, -C
    return (A, B, C)

LINES = sorted({line_through(a, b) for a in P for b in P if a != b})
def ev(L, p): return L[0] * p[0] + L[1] * p[1] + L[2]
def on(p, L): return ev(L, p) == 0
def ss(p, q, L): return ev(L, p) * ev(L, q) > 0
def opp(p, q, L): return (not on(p, L)) and (not on(q, L)) and not ss(p, q, L)
def col(a, b, c): return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0]) == 0
def bet(a, b, c):
    if a == c or not col(a, b, c): return False
    dot = (b[0]-a[0])*(c[0]-a[0]) + (b[1]-a[1])*(c[1]-a[1])
    n = (c[0]-a[0])**2 + (c[1]-a[1])**2
    return 0 < dot < n
def d2(a, b): return (a[0]-b[0])**2 + (a[1]-b[1])**2

CIRC = sorted({(c, d2(c, p)) for c in P for p in P if c != p})
def onc(p, a): return d2(p, a[0]) == a[1]
def ins(p, a): return d2(p, a[0]) < a[1]
def outc(p, a): return d2(p, a[0]) > a[1]

def line_meets_circle(L, a):
    # two distinct real points iff distance from centre < radius
    (A, B, C), (c, r2) = L, a
    v = A * c[0] + B * c[1] + C
    return v * v < r2 * (A * A + B * B)
def circles_meet(a, b):
    if a == b: return True
    (c1, r1), (c2, r2) = a, b
    D = d2(c1, c2)
    if D == 0: return False
    # two points iff |r1 - r2| < d < r1 + r2, with r = sqrt(r2): compare squared carefully
    # (r1 - r2)^2 < D < (r1 + r2)^2  <=>  r1sq + r2sq - D < 2 sqrt(r1sq r2sq) and D < r1sq + r2sq + 2 sqrt(...)
    s = r1 + r2 - D
    lhs_ok = (s < 0) or (s * s < 4 * r1 * r2)
    t = D - r1 - r2
    rhs_ok = (t < 0) or (t * t < 4 * r1 * r2)
    return lhs_ok and rhs_ok

fails = []
def chk(name, cond, *w):
    if not cond: fails.append((name, w))

# Betweenness
for a, b, c in product(P, repeat=3):
    if bet(a, b, c):
        chk('between_symm', bet(c, b, a), a, b, c)
        chk('ne_of_between', a != b and a != c, a, b, c)
        chk('not_between_of_between', not bet(b, a, c), a, b, c)
        for L in LINES:
            if on(a, L) and on(b, L): chk('on_line_of_between', on(c, L), a, b, c, L)
            if on(a, L) and on(c, L): chk('on_line_of_between_ends', on(b, L), a, b, c, L)
            if ss(a, c, L): chk('pasch1', ss(a, b, L), a, b, c, L)
            if on(a, L) and not on(b, L): chk('pasch2', ss(b, c, L), a, b, c, L)
            if on(b, L): chk('pasch3', not ss(a, c, L), a, b, c, L)
        for d in P:
            if bet(a, d, b): chk('between_left', bet(a, d, c), a, b, c, d)
            if bet(b, c, d): chk('between_right', bet(a, b, d), a, b, c, d)
            if bet(a, b, d): chk('between7', not bet(c, b, d), a, b, c, d)
        for al in CIRC:
            if (ins(a, al) or onc(a, al)) and (ins(c, al) or onc(c, al)):
                chk('inside_of_between', ins(b, al), a, b, c, al)
            if (ins(a, al) or onc(a, al)) and not ins(b, al):
                chk('outside_of_between', outc(c, al), a, b, c, al)
for L in LINES:
    pts = [p for p in P if on(p, L)]
    for a, b, c in product(pts, repeat=3):
        if len({a, b, c}) == 3:
            chk('between_cases', bet(a, b, c) or bet(b, a, c) or bet(a, c, b), a, b, c)
    off = [p for p in P if not on(p, L)]
    for a, b, c in product(off, repeat=3):
        if not ss(a, b, L): chk('same_side_or', ss(a, c, L) or ss(b, c, L), a, b, c, L)
        if ss(a, b, L) and ss(a, c, L): chk('same_side_trans', ss(b, c, L), a, b, c, L)
    for a, b in product(off, repeat=2):
        if opp(a, b, L):
            for M in LINES:
                if on(a, M) and on(b, M):
                    chk('Int1 lines_meet', M != L and any(on(p, L) and on(p, M) for p in [None] if False) or (M != L and (L[0]*M[1]-L[1]*M[0]) != 0), a, b, L, M)
            for al in CIRC:
                if (ins(a, al) or onc(a, al)) and (ins(b, al) or onc(b, al)):
                    chk('Int2 line_meets_circle_opp', line_meets_circle(L, al), a, b, L, al)
    for al in CIRC:
        if any(ins(p, al) for p in pts): chk('Int3 line_meets_circle_inside', line_meets_circle(L, al), L, al)
        # Circle 1
        for a in pts:
            if ins(a, al):
                for b, c in product(pts, repeat=2):
                    if b != c and onc(b, al) and onc(c, al): chk('circle1 chord', bet(b, a, c), a, b, c, al)
# Pasch 4
for L, M in product(LINES, repeat=2):
    if L == M: continue
    for b in P:
        if not (on(b, L) and on(b, M)): continue
        ms = [p for p in P if on(p, M) and p != b]
        for a, c in product(ms, repeat=2):
            if a != c and not ss(a, c, L): chk('pasch4', bet(a, b, c), L, M, a, b, c)
# Circle 4 and Intersections 4, 5, 8, 9
for al, be in product(CIRC, repeat=2):
    cm = circles_meet(al, be)
    common = [p for p in P if onc(p, al) and onc(p, be)]
    if al != be:
        for c, d in combinations(common, 2):
            for L in LINES:
                if on(al[0], L) and on(be[0], L): chk('circle4', not ss(c, d, L), al, be, c, d, L)
    onA_inB = [p for p in P if onc(p, al) and ins(p, be)]
    if onA_inB:
        if any((ins(q, al) or onc(q, al)) and outc(q, be) for q in P): chk('Int4', cm, al, be)
        if any(ins(q, al) and onc(q, be) for q in P): chk('Int5', cm, al, be)
    if len(common) >= 2 or (cm and al == be):
        for L in LINES:
            if on(al[0], L) and on(be[0], L):
                # each side of L must carry a common point (exact: use symmetric reflection argument numerically)
                (c1, r1), (c2, r2) = al, be
                import math
                if c1 == c2:
                    ok = True
                else:
                    D = math.sqrt(d2(c1, c2)); a_ = (r1 - r2 + D * D) / (2 * D); h2 = r1 - a_ * a_
                    ok = h2 > 1e-12
                chk('Int8/9 both sides', ok, al, be, L)

from collections import Counter
print('lines', len(LINES), 'circles', len(CIRC))
print('failures', len(fails), Counter(n for n, _ in fails))
for f in fails[:10]: print(f)
