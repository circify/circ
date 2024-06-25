P = PolynomialRing(GF(17), "X")
X = P.gen(0)
p = (X-1)*(X-3)*(X-7)*(X-10)
p_prime = p.derivative()

def poly_gcd_ext_int(x, y, x_c_a, x_c_b, y_c_a, y_c_b):
    if x == 0:
        lc = y.leading_coefficient()
        return y/lc, y_c_a/lc, y_c_b/lc
    # x = a * x_c_a + b * x_c_b
    # y = a * y_c_a + b * y_c_b
    if x.degree() > y.degree():
        return poly_gcd_ext_int(y, x, y_c_a, y_c_b, x_c_a, x_c_b)
    # y = qx + r    r = y - qx
    q, r = y.quo_rem(x)
    r_c_a = y_c_a - q*x_c_a
    r_c_b = y_c_b - q*x_c_b
    return poly_gcd_ext_int(r, x, r_c_a, r_c_b, x_c_a, x_c_b)
    # (a, b) = (r, a)

def poly_gcd_ext(x, y):
    g, a, b = poly_gcd_ext_int(x, y, 1, 0, 0, 1)
    assert g == x.gcd(y)
    assert a * x + b * y == g
    return g, a, b

g, a, b = poly_gcd_ext(p, p_prime)
print(g)
print(a)
print(b)
print(a*p+b*p_prime)
