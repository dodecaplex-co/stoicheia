"""Mutation test: drop or weaken a guard in an axiom and confirm the search finds a
counterexample.  Shows that the harness would have caught a false axiom, and that each
guard in the real axioms is doing work.
Usage: python3 -I mutations.py"""
import itertools
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *  # noqa

G = [(x, y) for x in range(-2, 3) for y in range(-2, 3)]
LINES = sorted({line_through(P, Q) for P, Q in itertools.combinations(G, 2)})
ON = {L: [P for P in G if on_line(P, L)] for L in LINES}
THRU = {P: [L for L in LINES if on_line(P, L)] for P in G}
G2 = [(x, y) for x in range(-4, 5) for y in range(-4, 5)]
CIRCS = [(x, y, R) for x in range(-1, 2) for y in range(-1, 2) for R in [1, 2, 4, 5, 8, 9, 10, 13]]
ONC = {c: [P for P in G2 if on_circle(P, c)] for c in CIRCS}


def in_or_on(P, c):
    return inside(P, c) or on_circle(P, c)


def first(gen):
    for x in gen:
        return x
    return None


M = []

# M1: Intersection 4 as printed in System E ("A on or inside alpha")
M.append(('Intersection 4 as printed (A on OR inside alpha)', first(
    (c1, c2, A, B) for c1, c2 in itertools.product(CIRCS, repeat=2) for A in G2 for B in G2
    if in_or_on(A, c1) and in_or_on(B, c1) and inside(A, c2) and outside(B, c2) and not circles_meet(c1, c2))))

# M2: triple_incidence2 without "D not on M"
M.append(('triple_incidence2 without D off M', first(
    (A, B, C, D, L, Mm, N) for A in G for L, Mm, N in itertools.product(THRU[A], repeat=3)
    for B in ON[L] for C in ON[Mm] for D in ON[N]
    if same_side(C, D, L) and not same_side(B, D, Mm) and B != A and not same_side(B, C, N))))

# M3: triple_incidence2 without "B != A"
M.append(('triple_incidence2 without B != A', first(
    (A, B, C, D, L, Mm, N) for A in G for L, Mm, N in itertools.product(THRU[A], repeat=3)
    for B in ON[L] for C in ON[Mm] for D in ON[N]
    if same_side(C, D, L) and not same_side(B, D, Mm) and not on_line(D, Mm) and not same_side(B, C, N))))

# M4: Circle 4 without alpha != beta
M.append(('not_same_side_of_circles_meet without alpha != beta', first(
    (c, C, D, L) for c in CIRCS for C, D in itertools.product(ONC[c], repeat=2) if C != D
    for L in [l for l in LINES if on_line(centre(c), l)] if same_side(C, D, L))))

# M5: inside_of_angle_add without L != M
M.append(('inside_of_angle_add without L != M', first(
    (A, B, C, D, L) for A in G for L in THRU[A] for B in ON[L] for C in ON[L] for D in G
    if A != B and A != C and not on_line(D, L)
    and feq(ang(B, A, C), ang(B, A, D) + ang(D, A, C)))))

# M6: Postulate 5 concluding the meeting point lies on the OTHER side
M.append(('Postulate5 with conclusion on the other side', first(
    (A, B, C, D) for A, B, C, D in itertools.product(G, repeat=4)
    if A != B and B != C and C != D and same_side(A, D, line_through(B, C))
    and ang(A, B, C) + ang(B, C, D) < math.pi - 1e-7)))

# M7: Pasch 4 without L != M
M.append(('pasch4 without L != M', first(
    (A, B, C, L) for B in G for L in THRU[B] for A, C in itertools.product(ON[L], repeat=2)
    if A != C and A != B and C != B and not between(A, B, C))))

# M8: Circle 1 with A "on or inside"
M.append(('between_of_inside_chord with A on-or-inside', first(
    (A, B, C, c) for c in CIRCS for B, C in itertools.product(ONC[c], repeat=2) if B != C
    for A in [B] if not between(B, A, C))))


# M9: superposition without the Triangle hypothesis (a degenerate "triangle")
def sup_fails(A, B, C):
    ab, bc, ca = length(A, B), length(B, C), length(C, A)
    if ab == 0:
        return True  # B' = D, then angle B'DC' is degenerate; and no C' off L at distance ca... check below
    x = (ab * ab + ca * ca - bc * bc) / (2 * ab)
    return ca * ca - x * x <= 1e-12  # C' would have to lie on L, not on H's side


M.append(('superposition applied to a degenerate (collinear) triangle', first(
    (A, B, C) for A, B, C in itertools.product(G, repeat=3) if not triangle(A, B, C) and A != B and sup_fails(A, B, C))))

# M10: Postulate 4 / Definition 10 without "not Collinear A B C"
M.append(('IsRightAngle without not-Collinear (C = B gives 0 = 0)', first(
    (A, B, C, D) for A, B, C, D in itertools.product(G, repeat=4)
    if between(A, B, D) and feq(ang(A, B, C), ang(C, B, D)) and not feq(ang(A, B, C), RA))))

# M11: line_circle_beyond without C != B
M.append(('line_circle_beyond without C != B', first(
    (B, c) for c in CIRCS for B in G2 if inside(B, c))))  # C = B: Between A B B is impossible

# M12: circles_meet_same_side without B off L
M.append(('circles_meet_same_side without B off L', first(
    (c, B) for c in CIRCS for B in [centre(c)])))  # B on L: SameSide A B L impossible

# M13: angle_eq_of_same_rays with "Between" in place of "not Between" for one arm
M.append(('angle_eq_of_same_rays with B, B\' on opposite rays', first(
    (A, B, B2, C) for A in G for L in THRU[A] for B, B2 in itertools.product(ON[L], repeat=2)
    for C in G if B != A and B2 != A and C != A and between(B, A, B2)
    and not feq(ang(B, A, C), ang(B2, A, C)))))

# M14: circles_meet (Intersection 5) with B on-or-inside alpha
M.append(('circles_meet with B on-or-inside alpha', first(
    (c1, c2, A, B) for c1, c2 in itertools.product(CIRCS, repeat=2) for A in ONC[c1] for B in ONC[c2]
    if in_or_on(B, c1) and inside(A, c2) and not circles_meet(c1, c2))))

# M15: line_meets_circle_of_opposite_sides weakened to "on the same side" -> should fail
M.append(('Intersection 2 with A, B on the same side', first(
    (A, B, L, c) for c in CIRCS for A in ONC[c] for B in ONC[c] for L in LINES
    if same_side(A, B, L) and not line_meets_circle(L, c))))

ok = 0
for name, w in M:
    status = 'counterexample found' if w is not None else 'NO counterexample (harness blind?)'
    ok += w is not None
    print(f"{name:62s} {status}\n      {w}")
print(f"{ok}/{len(M)} mutations caught")
