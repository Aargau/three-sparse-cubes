"""Verify the generic moment, divided-difference and norm identities in the circuit builder."""
from math import comb

from sympy import QQ, ZZ
from sympy.polys.rings import ring

from build_sparse_cube_original_certificate import differences, geom, raw_cube_moments
from check_sparse_cube_original_certificate import cube_moments


def mean_equations(curvature, *, primitive=True):
    """Return orders four through nine and the open-set polynomial.

    In the basis (1, X, K), X^2=b+K, XK=c, and K^2=cX-bK.
    The three centered binomial means X are the roots of X^3-bX-c.
    """
    if curvature is None:
        domain, b, c, d, e, j, curvature = ring("b,c,d,e,j,w", QQ)
    else:
        domain, b, c, d, e, j = ring("b,c,d,e,j", QQ)
    zero = domain.zero
    one = domain.one
    x = (zero, one, zero)
    k = (zero, zero, one)

    def scale(value, coefficient):
        return tuple(term * coefficient for term in value)

    def add(*terms):
        return tuple(sum(entries, zero) for entries in zip(*terms))

    def multiply(left, right):
        a0, a1, a2 = left
        b0, b1, b2 = right
        return (
            a0*b0 + b*a1*b1 + c*(a1*b2 + a2*b1),
            a0*b1 + a1*b0 + c*a2*b2,
            a0*b2 + a2*b0 + a1*b1 - b*a2*b2,
        )

    variance = (3*d, 3*e, -3*one)
    skew = ((d+b)*curvature + e*(j+9), j, curvature*one)
    root_sum = add(skew, scale(x, 2))
    neg_root_product = add(variance, scale(multiply(x, x), -1),
                           scale(multiply(x, skew), -1))
    moments = [(one, zero, zero), x]
    for n in range(2, 10):
        moments.append(add(multiply(root_sum, moments[n-1]),
                           multiply(neg_root_product, moments[n-2])))

    def convolution(left, right, n):
        return add(*(scale(multiply(left[i], right[n-i]), comb(n, i))
                     for i in range(n+1)))

    square = [convolution(moments, moments, n) for n in range(10)]
    residuals = [convolution(square, moments, n)[2] for n in range(10)]
    if any(residuals[:4]):
        raise ValueError("The projected moments at orders zero through three must vanish")

    v = (d, e, -one)
    xv = multiply(v, x)
    kv = multiply(v, k)
    norm = (v[0]*(xv[1]*kv[2] - xv[2]*kv[1])
            - xv[0]*(v[1]*kv[2] - v[2]*kv[1])
            + kv[0]*(v[1]*xv[2] - v[2]*xv[1]))
    equations = residuals[4:]
    if primitive:
        equations = [poly.primitive()[1] for poly in equations]
    return domain, equations, (4*b**3-27*c**2)*norm


def check_symbolic_scaling():
    """Check every coefficient in the general-w physical scaling identities."""
    _, general, general_h = mean_equations(None, primitive=False)
    _, affine, affine_h = mean_equations(0, primitive=False)
    _, curved, curved_h = mean_equations(1, primitive=False)
    for n, (full, f0, f1) in enumerate(zip(general, affine, curved), 4):
        if not full.content() == f0.content() == f1.content() == 9:
            raise ValueError(f"Incorrect primitive content at order {n}")
        reconstructed = {}
        for powers, coefficient in f1.items():
            b, c, d, e, _ = powers
            w_degree = 2*b + 3*c + 2*d + e - (n-2)
            if w_degree < 0:
                raise ValueError(f"Unexpected negative curvature exponent at order {n}")
            reconstructed[(*powers, w_degree)] = coefficient
        if dict(full) != reconstructed:
            raise ValueError(f"The nonzero-chart scaling fails at order {n}")
        if dict(f0) != {m[:-1]:v for m,v in full.items() if m[-1] == 0}:
            raise ValueError(f"The zero-chart specialization fails at order {n}")
    if (general_h != general_h.ring.from_dict({(*m,0):v for m,v in curved_h.items()})
            or dict(affine_h) != dict(curved_h)
            or any(2*b + 3*c + 2*d + e != 12 for b,c,d,e,_ in curved_h)):
        raise ValueError("The open-set target must be independent of curvature and have weight 12")
    print("Verified all six general-w residuals coefficient by coefficient",
          [len(f) for f in general], "and the weight-12 open-set polynomial.")


def check():
    check_symbolic_scaling()
    # Independent fourth-order recurrence on the four frequencies of a cube.
    moments = raw_cube_moments()
    # The independent recurrence uses cube mean 3x. QQ(1,3) in that routine
    # needs a rational coefficient ring even though the output is integral.
    rational, rx, rv, rs = ring("x,v,s", QQ)
    independent = cube_moments(3*rx, rv, rs)
    if any(rational.from_dict(f) != h for f,h in zip(moments,independent)):
        raise ValueError("The two raw-cube recurrences disagree")

    _, x, base_v, base_s, k, delta, eta, w, z = ring("x,v,s,k,delta,eta,w,z", ZZ)
    # The formal z denotes d+b+K. This treats z and K as arbitrary. The same
    # identity therefore holds after evaluating at any of the three mean nodes.
    v, s = base_v+delta*k, base_s+eta
    flat = base_s-w*z
    def evaluate(poly, v, s):
        return sum(int(a)*x**i*v**j*s**k for (i,j,k),a in poly.items())
    for n, f in enumerate(moments):
        dv, ds, sw = differences(f, x, v, base_v, s, base_s, flat)
        g = evaluate(f, base_v, base_s)
        if evaluate(f, v, s) - g != delta*k*dv + eta*ds:
            raise ValueError(f"Off-chart correction failed at order {n}")
        if g - evaluate(f, base_v, flat) != w*z*sw:
            raise ValueError(f"Curvature difference failed at order {n}")

    _, v1, v2, v3, k1, k2, k3, delta = ring("v1,v2,v3,k1,k2,k3,t", ZZ)
    vs = (v1,v2,v3)
    projected = tuple(v-delta*k for v,k in zip(vs,(k1,k2,k3)))
    a,b,c = projected
    if v1*v2*v3-a*b*c != delta*(k1*b*c + v1*k2*c + v1*v2*k3):
        raise ValueError("Variance norm correction failed")

    r, h, w, b = ring("h,w,b", ZZ)
    for n in (7,8,229):
        if n == 229:
            if (h-1)*geom(h,r.one,n) != h**n-1:
                raise ValueError("Saturation correction failed")
        elif (h-w*b)*geom(h,w*b,n) != h**n-(w*b)**n:
            raise ValueError("Chart gluing failed")
    print("The two raw-cube recurrences agree symbolically through order nine.")
    print("Both divided differences hold at all ten orders over the integer polynomial ring.")
    print("The norm correction and the gluing and saturation identities hold symbolically.")


if __name__ == "__main__":
    check()
