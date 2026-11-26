"""Verify the Taylor shift and the delta and eta cofactor rows against integer-input.ms."""

import argparse
from math import comb, prod
from pathlib import Path

from sympy import QQ
from sympy.polys.rings import ring

from check_sparse_cube_original_certificate import GENERATORS, VARIABLES, cube_moments, parse_polynomial


def equal(left, right, label):
    if left != right:
        raise ValueError(f"Failed exact polynomial comparison: {label}")


def verify(input_file):
    algebra, p, v1, v2, v3, s1, s2, s3, _ = ring(",".join(VARIABLES), QQ)
    v = (v1, v2, v3)
    s = (s1, s2, s3)
    q = 1-p
    lines = input_file.read_text(encoding="ascii").splitlines()
    if len(lines) != 11 or tuple(lines[0].split(",")) != VARIABLES or lines[1] != "0":
        raise ValueError("Expected the nine characteristic-zero Taylor input polynomials")
    # The eighth moment row here is F9. The ninth archived input is the
    # saturation equation, which is independent of the projection.
    original = [algebra.zero, algebra.zero] + [
        parse_polynomial(line.removesuffix(","), algebra) for line in lines[2:10]]

    def mass(values):
        first, second, target = values
        return p*first + q*second - target

    mu = (1+p)*QQ(1, 3)
    x = tuple((a-mu)*QQ(1, 3) for a in (algebra.one, algebra.zero, p))
    b = -(x[0]*x[1]+x[0]*x[2]+x[1]*x[2])
    c = prod(x)
    k = tuple(xi**2-b for xi in x)
    ell = p*q*QQ(1, 9)
    for xi in x:
        equal(xi**3-b*xi-c, algebra.zero, "centered mean cubic")
    equal(mass(x), algebra.zero, "L(X)")
    equal(mass(k), ell, "L(K)")
    equal(4*b**3-27*c**2, (p*q)**2*QQ(1, 729), "mean discriminant")

    shifted = [sum((comb(n, i)*(-mu)**(n-i)*original[i] for i in range(2, n+1)),
                   algebra.zero) for n in range(10)]
    direct = [cube_moments(3*xi, vi, si) for xi, vi, si in zip(x, v, s)]
    for n, values in enumerate(zip(*direct)):
        equal(mass(values), shifted[n], f"shift of archived generators at order {n}")
    print("All ten translated moments equal the binomial shifts of the archived F2 through F9.")

    # Store ell*delta, ell*v*, ell*(e,d,w,j), and ell^2*s*. All comparisons
    # below take place in the full original polynomial ring over Q.
    delta_num = 3*ell + mass(v)
    equal(3*delta_num, original[2], "delta row in F2")
    v_num = tuple(ell*vi-delta_num*ki for vi, ki in zip(v, k))
    e_num = v_num[0]-v_num[1]+3*ell*(k[0]-k[1])
    d_num = v_num[1]*QQ(1, 3) + ell*k[1] - e_num*x[1]
    for vi, xi, ki in zip(v_num, x, k):
        equal(vi, 3*(d_num+e_num*xi-ell*ki), "variance interpolation at each node")
    equal(mass(v_num), -3*ell**2, "L(v*) = -3 ell")

    w_num = mass(s)
    j_num = 3*(ell*(s[0]-s[1])-w_num*(k[0]-k[1]))
    s_num = tuple(e_num*(j_num+9*ell) + ell*j_num*xi + w_num*(d_num+ell*(b+ki))
                  for xi, ki in zip(x, k))
    vpart = mass(ki*(27*xi+3*si) for ki, xi, si in zip(k, x, s))
    # Removing ell^2 from the denominator of eta gives an explicit row in
    # F2,F3 because T2=F2 and T3=F3-3*mu*F2.
    eta_row = (vpart+9*mu*ell)*original[2] - 3*ell*original[3]
    for si, projected in zip(s, s_num):
        eta_num = ell**2*si-projected
        equal(27*eta_num, eta_row, "eta row in F2,F3 at each node")
        equal(9*eta_num, delta_num*vpart-ell*shifted[3], "eta in shifted coordinates")

    # Independently substitute the projected values into the explicit second
    # and third cube moments. The common denominators are ell and ell^3.
    projected2 = mass(9*xi**2*ell+3*vi for xi,vi in zip(x,v_num))
    projected3 = mass(27*xi**3*ell**3 + 27*xi*vi*ell**2 + 3*vi*si
                      for xi,vi,si in zip(x,v_num,s_num))
    equal(projected2, algebra.zero, "projected second moment")
    equal(projected3, algebra.zero, "projected third moment")
    print("Verified the delta row, the eta row at all three nodes, and projected orders two and three.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generators", type=Path, default=GENERATORS)
    verify(parser.parse_args().generators)
