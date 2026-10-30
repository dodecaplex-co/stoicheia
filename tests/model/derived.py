"""Numerical properties retained independently of the axiom registries.

These predicates keep the guards and conclusions of their search.py checks: the eight retired
first, then the 31 prepared for retirement while all 79 axioms remain; and, kept beside
Circle 2, Circle 3 (`outside_of_between`), prepared in the same way for its retirement after
III.2; and Circle 1 (`between_of_inside_chord`), prepared in the same way for its retirement
after III.2 (#477) while it is still an axiom; and Metric 9 (`area_congruent`), prepared in
the same way for Common Notion 4 for figures to take its place among the axioms (#517).
The exhaustive and structured harnesses report them with a derived. prefix, even
while the corresponding declarations are still axioms. Their configurations and
results therefore survive removal of those laws from search.py and hyperbolic.py.
"""
import math

from model import (Fr, ang, area2, between, centre, circles_meet, d2, dot, feq, inside, is_centre,
                   lattice_on_line, line_meets_circle, lval, on_circle, on_line, opposite, outside,
                   same_side, sgn, sub)


def adjacent_eq_of_right(c):
    A, B, Cc, D, L = (c[k] for k in 'ABCDL')
    if not (on_line(A, L) and on_line(B, L) and between(A, Cc, B) and not on_line(D, L)):
        return None
    # exact right-angle test
    if dot(sub(A, Cc), sub(D, Cc)) != 0:
        return None
    return feq(ang(A, Cc, D), ang(D, Cc, B))


def not_same_side_of_circles_meet(c):
    A, B, Cc, D, L, al, be = (c[k] for k in ('A', 'B', 'C', 'D', 'L', 'al', 'be'))
    if not (al != be and on_circle(Cc, al) and on_circle(Cc, be) and on_circle(D, al) and on_circle(D, be)
            and Cc != D and is_centre(A, al) and is_centre(B, be) and on_line(A, L) and on_line(B, L)):
        return None
    return not same_side(Cc, D, L)


def centre_unique(c):
    if not (is_centre(c['A'], c['al']) and is_centre(c['B'], c['al'])):
        return None
    return c['A'] == c['B']


def in_or_on(P, c):
    return inside(P, c) or on_circle(P, c)


def inside_of_between(c):
    A, B, Cc, al = c['A'], c['B'], c['C'], c['al']
    if not (in_or_on(A, al) and in_or_on(B, al) and between(A, Cc, B)):
        return None
    return inside(Cc, al)


def outside_of_between(c):
    A, B, Cc, al = c['A'], c['B'], c['C'], c['al']
    if not (in_or_on(A, al) and not inside(Cc, al) and between(A, Cc, B)):
        return None
    return (not inside(B, al)) and (not on_circle(B, al))


def between_of_inside_chord(c):
    A, B, Cc, L, al = (c[k] for k in ('A', 'B', 'C', 'L', 'al'))
    if not (on_line(A, L) and on_line(B, L) and on_line(Cc, L) and inside(A, al) and on_circle(B, al)
            and on_circle(Cc, al) and B != Cc):
        return None
    return between(B, A, Cc)


def area_congruent(c):
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


def exists_point_outside_circle(c):
    al = c['al']
    ws = [(al[0] + al[2] + k, al[1]) for k in (1, 2, 3)]
    return all(outside(w, al) for w in ws)


def line_meets_circle_of_opposite_sides(c):
    A, B, L, al = c['A'], c['B'], c['L'], c['al']
    if not (in_or_on(A, al) and in_or_on(B, al) and opposite(A, B, L)):
        return None
    return line_meets_circle(L, al)


def _ti_hyp(c):
    A, B, Cc, D, L, M, N = (c[k] for k in 'ABCDLMN')
    return (on_line(A, L) and on_line(A, M) and on_line(A, N) and on_line(B, L) and on_line(Cc, M)
            and on_line(D, N))


def triple_incidence3(c):
    if not (_ti_hyp(c) and same_side(c['C'], c['D'], c['L']) and same_side(c['B'], c['C'], c['N'])
            and same_side(c['D'], c['E'], c['M']) and same_side(c['C'], c['E'], c['N'])):
        return None
    return same_side(c['C'], c['E'], c['L'])


def _angle_inside_hyp(c):
    A, B, Cc, D, L, M = (c[k] for k in 'ABCDLM')
    return (on_line(A, L) and on_line(A, M) and on_line(B, L) and on_line(Cc, M) and A != B and A != Cc
            and not on_line(D, L) and not on_line(D, M) and L != M)


def inside_of_angle_add(c):
    if not _angle_inside_hyp(c):
        return None
    A, B, Cc, D = c['A'], c['B'], c['C'], c['D']
    gap = ang(B, A, D) + ang(D, A, Cc) - ang(B, A, Cc)
    if abs(gap) > 1e-9:
        return None
    return same_side(B, D, c['M']) and same_side(Cc, D, c['L'])


# The 31 prepared for the second retirement while all 79 axioms remain, each the guard and
# conclusion of its search.py law, unchanged.


# Floating-point helpers, copied from search.py so that these predicates keep to themselves.
def fl(P):
    return (float(P[0]), float(P[1]))


def f_lval(P, L):
    return (L[0] * P[0] + L[1] * P[1] + L[2]) / math.hypot(L[0], L[1])


def f_on_circle(P, c):
    return abs(math.dist(P, fl(centre(c))) - math.sqrt(c[2])) < 1e-7


def f_same_side(P, Q, L):
    a, b = f_lval(P, L), f_lval(Q, L)
    return abs(a) > 1e-7 and abs(b) > 1e-7 and (a > 0) == (b > 0)


def f_opposite(P, Q, L):
    a, b = f_lval(P, L), f_lval(Q, L)
    return abs(a) > 1e-7 and abs(b) > 1e-7 and (a > 0) != (b > 0)


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


def _area_line_hyp(c):
    A, B, Cc, D, L = (c[k] for k in 'ABCDL')
    return (on_line(A, L) and on_line(B, L) and on_line(Cc, L) and A != B and A != Cc and B != Cc
            and not on_line(D, L))


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


def area_swap(c):
    A, B, Cc = c['A'], c['B'], c['C']
    return area2(A, B, Cc) == area2(A, Cc, B)


def between_of_area_add(c):
    if not _area_line_hyp(c):
        return None
    A, B, Cc, D = (c[k] for k in 'ABCD')
    if area2(A, Cc, D) + area2(D, Cc, B) != area2(A, D, B):
        return None
    return between(A, Cc, B)


def between_of_between_left(c):
    A, B, Cc, D = c['A'], c['B'], c['C'], c['D']
    if not (between(A, B, Cc) and between(A, D, B)):
        return None
    return between(A, D, Cc)


def between_of_between_right(c):
    A, B, Cc, D = c['A'], c['B'], c['C'], c['D']
    if not (between(A, B, Cc) and between(B, Cc, D)):
        return None
    return between(A, B, D)


def centre_inside(c):
    if not is_centre(c['A'], c['al']):
        return None
    return inside(c['A'], c['al'])


def circles_meet_of_on_inside_outside(c):
    A, B, al, be = c['A'], c['B'], c['al'], c['be']
    if not (on_circle(A, al) and in_or_on(B, al) and inside(A, be) and outside(B, be)):
        return None
    return circles_meet(al, be)


def circles_meet_opposite_side(c):
    return _cm_side(c, False)


def eq_of_len_eq_zero(c):
    if d2(c['A'], c['B']) != 0:
        return None
    return c['A'] == c['B']


def exists_point_between(c):
    B, Cc, L = c['B'], c['C'], c['L']
    if not (on_line(B, L) and on_line(Cc, L) and B != Cc):
        return None
    ws = [(B[0] + Fr(1, k) * (Cc[0] - B[0]), B[1] + Fr(1, k) * (Cc[1] - B[1])) for k in (2, 3, 4)]
    return all(on_line(w, L) and between(B, w, Cc) for w in ws)


def exists_point_on_circle(c):
    al = c['al']
    ws = [(float(al[0]) + math.sqrt(al[2]) * math.cos(t), float(al[1]) + math.sqrt(al[2]) * math.sin(t)) for t in (0.1, 0.2, 0.3)]
    return all(f_on_circle(w, al) for w in ws)


def exists_point_on_line_off_line(c):
    L, M = c['L'], c['M']
    if L == M:
        return None
    rng = c['_rng']
    ws = [lattice_on_line(L, rng, spread=10**6) for _ in range(5)]
    good = [w for w in ws if on_line(w, L) and not on_line(w, M)]
    return len(set(good)) >= 2


def exists_point_opposite_side(c):
    B, L = c['B'], c['L']
    if on_line(B, L):
        return None
    s = sgn(lval(B, L))
    v = lval(B, L)
    n2 = L[0] ** 2 + L[1] ** 2
    ws = [(B[0] - Fr(k * v, n2) * L[0], B[1] - Fr(k * v, n2) * L[1]) for k in (2, 3, 4)]
    return all(opposite(w, B, L) for w in ws)


def exists_point_same_side(c):
    B, L = c['B'], c['L']
    if on_line(B, L):
        return None
    s = sgn(lval(B, L))
    ws = [(B[0] + k * s * L[0], B[1] + k * s * L[1]) for k in (1, 2, 3)]
    return all(same_side(w, B, L) for w in ws)


def inside_not_on(c):
    if not inside(c['A'], c['al']):
        return None
    return not on_circle(c['A'], c['al'])


def inside_of_len_lt(c):
    A, B, Cc, al = c['A'], c['B'], c['C'], c['al']
    if not (is_centre(A, al) and on_circle(B, al) and d2(A, Cc) < d2(A, B)):
        return None
    return inside(Cc, al)


def len_lt_of_inside(c):
    A, B, Cc, al = c['A'], c['B'], c['C'], c['al']
    if not (is_centre(A, al) and on_circle(B, al) and inside(Cc, al)):
        return None
    return d2(A, Cc) < d2(A, B)


def line_meets_circle_of_inside(c):
    A, L, al = c['A'], c['L'], c['al']
    if not (inside(A, al) and on_line(A, L)):
        return None
    return line_meets_circle(L, al)


def ne_of_between(c):
    if not between(c['A'], c['B'], c['C']):
        return None
    return c['A'] != c['B']


def ne_of_between_ends(c):
    if not between(c['A'], c['B'], c['C']):
        return None
    return c['A'] != c['C']


def not_between_of_between_between(c):
    A, B, Cc, D = c['A'], c['B'], c['C'], c['D']
    if not (between(A, B, Cc) and between(A, B, D)):
        return None
    return not between(Cc, B, D)


def on_circle_of_len_eq(c):
    A, B, Cc, al = c['A'], c['B'], c['C'], c['al']
    if not (is_centre(A, al) and on_circle(B, al) and d2(A, Cc) == d2(A, B)):
        return None
    return on_circle(Cc, al)


def on_line_of_between(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (between(A, B, Cc) and on_line(A, L) and on_line(B, L)):
        return None
    return on_line(Cc, L)


def on_line_of_between_ends(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (between(A, B, Cc) and on_line(A, L) and on_line(Cc, L)):
        return None
    return on_line(B, L)


def pasch1(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (between(A, B, Cc) and same_side(A, Cc, L)):
        return None
    return same_side(A, B, L)


def pasch3(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if not (between(A, B, Cc) and on_line(B, L)):
        return None
    return not same_side(A, Cc, L)


def pasch4(c):
    A, B, Cc, L, M = (c[k] for k in 'ABCLM')
    if not (L != M and on_line(B, L) and on_line(B, M) and on_line(A, M) and on_line(Cc, M)
            and A != Cc and A != B and Cc != B and not same_side(A, Cc, L)):
        return None
    return between(A, B, Cc)


def same_side_or(c):
    A, B, Cc, L = c['A'], c['B'], c['C'], c['L']
    if on_line(A, L) or on_line(B, L) or on_line(Cc, L) or same_side(A, B, L):
        return None
    return same_side(A, Cc, L) or same_side(B, Cc, L)


def same_side_refl(c):
    if on_line(c['A'], c['L']):
        return None
    return same_side(c['A'], c['A'], c['L'])


def same_side_symm(c):
    if not same_side(c['A'], c['B'], c['L']):
        return None
    return same_side(c['B'], c['A'], c['L'])


def triple_incidence1(c):
    if not (_ti_hyp(c) and same_side(c['C'], c['D'], c['L']) and same_side(c['B'], c['C'], c['N'])):
        return None
    return not same_side(c['B'], c['D'], c['M'])


def triple_incidence2(c):
    if not (_ti_hyp(c) and same_side(c['C'], c['D'], c['L']) and not same_side(c['B'], c['D'], c['M'])
            and not on_line(c['D'], c['M']) and c['B'] != c['A']):
        return None
    return same_side(c['B'], c['C'], c['N'])


PROPERTIES = {
    'derived.adjacent_eq_of_right': adjacent_eq_of_right,
    'derived.not_same_side_of_circles_meet': not_same_side_of_circles_meet,
    'derived.centre_unique': centre_unique,
    'derived.inside_of_between': inside_of_between,
    'derived.outside_of_between': outside_of_between,
    'derived.between_of_inside_chord': between_of_inside_chord,
    'derived.area_congruent': area_congruent,
    'derived.exists_point_outside_circle': exists_point_outside_circle,
    'derived.line_meets_circle_of_opposite_sides': line_meets_circle_of_opposite_sides,
    'derived.triple_incidence3': triple_incidence3,
    'derived.inside_of_angle_add': inside_of_angle_add,
    'derived.area_swap': area_swap,
    'derived.between_of_area_add': between_of_area_add,
    'derived.between_of_between_left': between_of_between_left,
    'derived.between_of_between_right': between_of_between_right,
    'derived.centre_inside': centre_inside,
    'derived.circles_meet_of_on_inside_outside': circles_meet_of_on_inside_outside,
    'derived.circles_meet_opposite_side': circles_meet_opposite_side,
    'derived.eq_of_len_eq_zero': eq_of_len_eq_zero,
    'derived.exists_point_between': exists_point_between,
    'derived.exists_point_on_circle': exists_point_on_circle,
    'derived.exists_point_on_line_off_line': exists_point_on_line_off_line,
    'derived.exists_point_opposite_side': exists_point_opposite_side,
    'derived.exists_point_same_side': exists_point_same_side,
    'derived.inside_not_on': inside_not_on,
    'derived.inside_of_len_lt': inside_of_len_lt,
    'derived.len_lt_of_inside': len_lt_of_inside,
    'derived.line_meets_circle_of_inside': line_meets_circle_of_inside,
    'derived.ne_of_between': ne_of_between,
    'derived.ne_of_between_ends': ne_of_between_ends,
    'derived.not_between_of_between_between': not_between_of_between_between,
    'derived.on_circle_of_len_eq': on_circle_of_len_eq,
    'derived.on_line_of_between': on_line_of_between,
    'derived.on_line_of_between_ends': on_line_of_between_ends,
    'derived.pasch1': pasch1,
    'derived.pasch3': pasch3,
    'derived.pasch4': pasch4,
    'derived.same_side_or': same_side_or,
    'derived.same_side_refl': same_side_refl,
    'derived.same_side_symm': same_side_symm,
    'derived.triple_incidence1': triple_incidence1,
    'derived.triple_incidence2': triple_incidence2,
}
