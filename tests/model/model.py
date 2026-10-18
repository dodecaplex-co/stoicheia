"""Exact model of Stoicheia's undefined words in R^2.

Points: pairs of ints or Fractions.  Lines: normalized integer (a,b,c), a x + b y + c = 0.
Circles: (cx, cy, R) with R = radius^2 > 0.  Between: strict.  SameSide: open half-plane.
len = Euclidean distance, ang in [0, pi] (degenerate angle := 0), area = |cross|/2,
rightAngle = pi/2.  Magnitudes = non-negative reals.

read_laws() reads laws.toml, the names of the laws the harness checks.
"""
import math
import os
import random
from fractions import Fraction as Fr
from math import gcd

EPS = 1e-9
RA = math.pi / 2
LAWS_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'laws.toml')


def read_laws(path=LAWS_FILE):
    """laws.toml, as ({the axiom's name in the lock: the name of its law in the harness},
    the names of the laws that must fail in the hyperbolic plane).  Raises ValueError when
    the file cannot be read, or is anything but a [laws] table of names, no law named
    twice, and a [hyperbolic] table whose `fails` lists some of those axioms, each once."""
    import tomllib
    where = 'tests/model/laws.toml'
    try:
        with open(path, 'rb') as f:
            data = tomllib.load(f)
    except OSError as e:
        raise ValueError(f'{where} cannot be read ({e.strerror})') from None
    except tomllib.TOMLDecodeError as e:
        raise ValueError(f'{where} is not valid TOML: {e}') from None
    laws, hyperbolic = data.get('laws'), data.get('hyperbolic')
    fails = hyperbolic.get('fails') if isinstance(hyperbolic, dict) else None
    if (set(data) != {'laws', 'hyperbolic'} or not isinstance(hyperbolic, dict)
            or set(hyperbolic) != {'fails'}
            or not isinstance(laws, dict) or not all(isinstance(v, str) for v in laws.values())
            or not isinstance(fails, list) or not all(isinstance(k, str) for k in fails)):
        raise ValueError(f'{where}: expected a [laws] table of names and a [hyperbolic] table '
                         'holding `fails`, a list of names, and nothing else')
    if len(set(laws.values())) != len(laws):
        raise ValueError(f'{where} gives two axioms the same law')
    if len(set(fails)) != len(fails) or not set(fails) <= set(laws):
        raise ValueError(f"{where}: [hyperbolic]'s `fails` must name axioms of [laws], each once")
    return laws, {laws[k] for k in fails}


def sub(P, Q):
    return (P[0] - Q[0], P[1] - Q[1])


def cross(u, v):
    return u[0] * v[1] - u[1] * v[0]


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]


def d2(P, Q):
    u = sub(P, Q)
    return dot(u, u)


def _lcm(a, b):
    return a * b // gcd(a, b)


def norm_line(a, b, c):
    if any(isinstance(t, Fr) for t in (a, b, c)):
        den = 1
        for t in (a, b, c):
            den = _lcm(den, Fr(t).denominator)
        a, b, c = int(a * den), int(b * den), int(c * den)
    g = gcd(gcd(abs(a), abs(b)), abs(c))
    a, b, c = a // g, b // g, c // g
    if a < 0 or (a == 0 and b < 0):
        a, b, c = -a, -b, -c
    return (a, b, c)


def line_through(P, Q):
    assert P != Q
    a = Q[1] - P[1]
    b = P[0] - Q[0]
    c = -(a * P[0] + b * P[1])
    return norm_line(a, b, c)


def lval(P, L):
    return L[0] * P[0] + L[1] * P[1] + L[2]


def sgn(x):
    return (x > 0) - (x < 0)


def on_line(P, L):
    return lval(P, L) == 0


def same_side(P, Q, L):
    s = sgn(lval(P, L))
    return s != 0 and s == sgn(lval(Q, L))


def opposite(P, Q, L):
    return (not on_line(P, L)) and (not on_line(Q, L)) and (not same_side(P, Q, L))


def collinear(A, B, C):
    return cross(sub(B, A), sub(C, A)) == 0


def between(A, B, C):
    if A == C:
        return False
    if cross(sub(B, A), sub(C, A)) != 0:
        return False
    t = dot(sub(B, A), sub(C, A))
    return 0 < t < d2(A, C)


def centre(c):
    return (c[0], c[1])


def on_circle(P, c):
    return d2(P, centre(c)) == c[2]


def inside(P, c):
    return d2(P, centre(c)) < c[2]


def outside(P, c):
    return d2(P, centre(c)) > c[2]


def is_centre(P, c):
    return P == centre(c)


def length(A, B):
    return math.sqrt(float(d2(A, B)))


def ang(A, B, C):
    if A == B or C == B:
        return 0.0
    u = sub(A, B)
    v = sub(C, B)
    return math.atan2(abs(float(cross(u, v))), float(dot(u, v)))


def area2(A, B, C):
    """twice the area, exact"""
    return abs(cross(sub(B, A), sub(C, A)))


def feq(a, b, eps=EPS):
    return abs(a - b) < eps


def lines_meet(L, M):
    return L != M and (L[0] * M[1] - L[1] * M[0]) != 0


def line_meets_circle(L, c):
    v = lval(centre(c), L)
    return v * v < c[2] * (L[0] ** 2 + L[1] ** 2)


def circles_meet(c1, c2):
    """at least two common points (exact)"""
    if c1 == c2:
        return True
    s = d2(centre(c1), centre(c2)) - c1[2] - c2[2]
    return s * s < 4 * c1[2] * c2[2]


def triangle(A, B, C):
    return not collinear(A, B, C)


# ---------- lattice points on lines / circles / segments ----------

def egcd(a, b):
    if b == 0:
        return (a, 1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)


def lattice_on_line(L, rng, spread=6):
    a, b, c = L
    g, x, y = egcd(abs(a), abs(b))
    if c % g != 0:
        return rational_on_line(L, rng, spread)
    # a*x0 + b*y0 = -c
    x0 = x * (-c // g) * (1 if a >= 0 else -1)
    y0 = y * (-c // g) * (1 if b >= 0 else -1)
    assert a * x0 + b * y0 + c == 0
    dx, dy = -b // g, a // g
    # move base point near origin
    if dx != 0 or dy != 0:
        k0 = -round((x0 * dx + y0 * dy) / (dx * dx + dy * dy))
        x0, y0 = x0 + k0 * dx, y0 + k0 * dy
    k = rng.randint(-spread, spread)
    return (x0 + k * dx, y0 + k * dy)


def lattice_on_circle(c, rng):
    cx, cy, R = c
    if isinstance(R, Fr) or isinstance(cx, Fr) or isinstance(cy, Fr):
        return None
    r = math.isqrt(R)
    sols = []
    for dx in range(-r, r + 1):
        rem = R - dx * dx
        s = math.isqrt(rem)
        if s * s == rem:
            sols.append((cx + dx, cy + s))
            if s:
                sols.append((cx + dx, cy - s))
    return rng.choice(sols) if sols else None


def lattice_between(A, B, rng):
    dx, dy = B[0] - A[0], B[1] - A[1]
    if isinstance(dx, Fr) or isinstance(dy, Fr):
        return (Fr(A[0] + B[0]) / 2, Fr(A[1] + B[1]) / 2)
    g = gcd(abs(dx), abs(dy))
    if g <= 1:
        return ((Fr(A[0]) + B[0]) / 2, (Fr(A[1]) + B[1]) / 2)  # rational midpoint
    k = rng.randint(1, g - 1)
    return (A[0] + k * dx // g, A[1] + k * dy // g)


def fix(P):
    """turn integral Fractions back into ints so lattice helpers still apply"""
    return tuple(int(t) if isinstance(t, Fr) and t.denominator == 1 else t for t in P)


def rational_on_line(L, rng, spread=6):
    a, b, c = L
    t = rng.randint(-spread, spread)
    if b != 0:
        return fix((t, Fr(-(a * t + c), b)))
    return fix((Fr(-c, a), t))
