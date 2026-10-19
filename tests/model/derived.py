"""Numerical properties retained independently of the axiom registries.

These four predicates keep the guards and conclusions of their search.py checks.
The exhaustive and structured harnesses report them with a derived. prefix, even
while the corresponding declarations are still axioms. Their configurations and
results therefore survive removal of those laws from search.py and hyperbolic.py.
"""
from model import ang, between, dot, feq, inside, is_centre, on_circle, on_line, same_side, sub


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


PROPERTIES = {
    'derived.adjacent_eq_of_right': adjacent_eq_of_right,
    'derived.not_same_side_of_circles_meet': not_same_side_of_circles_meet,
    'derived.centre_unique': centre_unique,
    'derived.inside_of_between': inside_of_between,
}
