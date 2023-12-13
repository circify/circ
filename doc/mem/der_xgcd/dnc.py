#!/usr/bin/env python

from sage.misc.misc_c import prod
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

p = 31
F = GF(p)
R = PolynomialRing(F, "x")
x = R.gen(0)


def v(*xs):
    if len(xs) == 1 and isinstance(xs, list):
        xs = xs[0]
    return prod([x - a for a in xs])


def dgcd(p):
    g, s, t = p.xgcd(p.derivative())
    return g, s, t, s.factor(), t.factor()


f = v(2, 5, 7)
g = v(1, 3, 8)
print("f", f)
print("g", g)
_, fg, gf = f.xgcd(g)
print("fg", fg)
print("gf", gf)
_, fF, Ff = f.xgcd(f.derivative())
print("fF", fF)
print("Ff", Ff)
_, gG, Gg = g.xgcd(g.derivative())
print("gG", gG)
print("Gg", Gg)
h = f * g
print("h", h)
print("h", h.factor())
print("H", h.derivative().factor())
_, hH, Hh = h.xgcd(h.derivative())
print("hH", hH)
print("Hh", Hh)
c = Hh.coefficients()[-1]
print(dgcd(v(-1, -2, -3, -4, -5)))
print(dgcd(v(-1, -2, -3, -4)))
print(dgcd(v(-1, -2, -3)))
print(dgcd(v(-1, -2)))
