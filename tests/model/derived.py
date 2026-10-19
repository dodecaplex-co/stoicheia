"""Numerical properties retained independently of the axiom registries.

These eight predicates keep the guards and conclusions of their search.py checks.
The exhaustive and structured harnesses report them with a derived. prefix, even
while the corresponding declarations are still axioms. Their configurations and
results therefore survive removal of those laws from search.py and hyperbolic.py.
"""
from model import (ang, between, dot, feq, inside, is_centre, line_meets_circle,
                   on_circle, on_line, opposite, outside, same_side, sub)


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


PROPERTIES = {
    'derived.adjacent_eq_of_right': adjacent_eq_of_right,
    'derived.not_same_side_of_circles_meet': not_same_side_of_circles_meet,
    'derived.centre_unique': centre_unique,
    'derived.inside_of_between': inside_of_between,
    'derived.exists_point_outside_circle': exists_point_outside_circle,
    'derived.line_meets_circle_of_opposite_sides': line_meets_circle_of_opposite_sides,
    'derived.triple_incidence3': triple_incidence3,
    'derived.inside_of_angle_add': inside_of_angle_add,
}
